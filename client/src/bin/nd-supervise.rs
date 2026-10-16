//! `nd-supervise SOCKET [--hide PATH]… -- PROGRAM [ARG]…`
//!
//! Binds SOCKET (mode 0600), starts PROGRAM confined by `sandbox` with every `--hide` path hidden
//! (CLIENT-8: the member's workspace, so the child cannot read the seed), and moves frames between
//! the socket's connections and the child's stdio (`mux`). It exits when the child does, with the
//! child's status; the service manager restarts the pair. Nothing is parsed but frame headers.

use std::ffi::OsString;
use std::fs;
use std::io;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{ExitCode, Stdio};

use nanodregg_client::mux::{self, MuxEnd};
use nanodregg_client::table;
use nanodregg_sandbox::{Policy, command};

const USAGE: &str = "usage: nd-supervise SOCKET [--hide PATH]... -- PROGRAM [ARG]...";

struct Args {
    socket: PathBuf,
    hidden: Vec<PathBuf>,
    program: OsString,
    args: Vec<OsString>,
}

fn parse(mut argv: impl Iterator<Item = OsString>) -> Result<Args, String> {
    let socket = PathBuf::from(argv.next().ok_or(USAGE)?);
    let mut hidden = Vec::new();
    loop {
        match argv.next() {
            Some(a) if a == "--hide" => hidden.push(PathBuf::from(argv.next().ok_or(USAGE)?)),
            Some(a) if a == "--" => break,
            _ => return Err(USAGE.into()),
        }
    }
    if hidden.is_empty() {
        return Err(
            "nd-supervise: refusing to start a child with nothing hidden (CLIENT-8)".into(),
        );
    }
    let program = argv.next().ok_or(USAGE)?;
    Ok(Args {
        socket,
        hidden,
        program,
        args: argv.collect(),
    })
}

/// Bind, replacing only a socket file nobody is listening on.
fn bind(path: &Path) -> io::Result<UnixListener> {
    match fs::symlink_metadata(path) {
        Ok(m) if m.file_type().is_socket() => match UnixStream::connect(path) {
            Ok(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::AddrInUse,
                    "a supervisor is already listening",
                ));
            }
            Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => fs::remove_file(path)?,
            Err(e) => return Err(e),
        },
        Ok(_) => return Err(io::Error::new(io::ErrorKind::AlreadyExists, "not a socket")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let listener = UnixListener::bind(path)?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    Ok(listener)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let a = parse(std::env::args_os().skip(1))?;
    let listener =
        bind(&a.socket).map_err(|e| format!("nd-supervise: {}: {e}", a.socket.display()))?;
    let args: Vec<&std::ffi::OsStr> = a.args.iter().map(OsString::as_os_str).collect();
    let mut child = command(&Policy { hidden: a.hidden }, &a.program, &args)
        .map_err(|e| format!("nd-supervise: {e}"))?
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("nd-supervise: spawn: {e}"))?;
    let (Some(child_in), Some(child_out)) = (child.stdin.take(), child.stdout.take()) else {
        return Err("nd-supervise: child stdio missing".into());
    };
    let end = mux::serve(listener, child_in, child_out, table::MUX);
    let _ = fs::remove_file(&a.socket);
    if let MuxEnd::ChildMalformed(ref e) = end {
        // A child that writes unroutable frames is broken; stop it (we hold its handle).
        let _ = child.kill();
        eprintln!("nd-supervise: child wrote an unroutable frame: {e}");
    }
    let status = child
        .wait()
        .map_err(|e| format!("nd-supervise: wait: {e}"))?;
    eprintln!("nd-supervise: {end:?}; child {status}");
    Ok(match (end, status.code()) {
        (MuxEnd::ChildMalformed(_), _) => ExitCode::from(70),
        (_, Some(c)) => ExitCode::from(u8::try_from(c).unwrap_or(1)),
        (_, None) => ExitCode::from(1),
    })
}
