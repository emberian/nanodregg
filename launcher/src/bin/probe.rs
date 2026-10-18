//! The launcher tests' grain (`launcher/tests/isolation.rs`, `launcher/tests/resident.rs`). Run as
//! `<grain>/pkg/probe`, with no arguments and an empty environment (the sandbox clears both), it
//! reads `probe.targets` beside itself (lines `NAME OP PATH`), tries each in order, and appends one
//! line per target to `<grain>/vol/probe.out` as soon as it is tried, so a test can follow it:
//! `NAME ok` (a `list` prints `ok` and the sorted names, comma-separated) or `NAME denied <errno
//! name>`. The ops:
//! - `read`, `write`, `list`: the file system;
//! - `connect`: open a unix socket (a resident's broker socket, HOSTING-17);
//! - `ask`: connect to a broker socket and send one ask (model `claude-m`, 10 tokens, `hello`),
//!   then print `ok reply <text>` (the reply text the Lean decider read, HOSTING-29), `ok status
//!   <status>` or `ok refused <broker refusal>`. Every byte received is
//!   appended to `<grain>/vol/probe.recv`, so the test can check that no key reached the grain;
//! - `wait`: wait (at most `WAIT`) until the file PATH exists, so a test can sequence the grain
//!   with what it does outside (`ok`, or `denied timeout`);
//! - `nd`: `NAME nd SOCK WORD...`: connect to a member socket (`nd --stdio` behind nd-supervise,
//!   HOSTING-20) and send the WORDs as one command (the mux child wire, the client's own frame
//!   and layout code), then print `ok <exit> <stdout>` (or `<stderr>` when the exit is not OK),
//!   newlines as `|`.
//!
//! It finds itself by argv[0] (no /proc under bwrap). Exit 3 when it cannot write its own volume.
//!
//! Run in `nd`'s place by nd-members (`launcher/tests/members.rs`, HOSTING-32) it is started as
//! `probe --stdio WS FOLLOW_SOCK HOST_SOCK`: then its directory is the member workspace WS, the one
//! path that child may write: `WS/probe.targets` in, `WS/probe.out` out, so a test reads what nd's
//! own confinement lets it touch.

use std::io::{ErrorKind, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use nanodregg_client::generated::layout::{Command, CommandReply};
use nanodregg_client::generated::{command_exit, follow_op, status};
use nanodregg_client::{frame, table};
use nanodregg_launcher::broker_generated::wire::{Answer, Ask};
use nanodregg_launcher::broker_generated::{read_frame, write_frame};

/// The longest a `wait` target waits.
const WAIT: Duration = Duration::from_secs(120);
/// The longest an `ask` waits for its answer.
const ASK: Duration = Duration::from_secs(60);

fn errno(e: &std::io::Error) -> String {
    let name = match e.kind() {
        ErrorKind::PermissionDenied => "EACCES/EPERM".to_string(),
        ErrorKind::NotFound => "ENOENT".to_string(),
        ErrorKind::ReadOnlyFilesystem => "EROFS".to_string(),
        ErrorKind::ConnectionRefused => "ECONNREFUSED".to_string(),
        k => format!("{k:?}"),
    };
    format!("denied {name}")
}

fn ask(path: &str, recv: &Path) -> String {
    let s = UnixStream::connect(path).and_then(|s| {
        s.set_read_timeout(Some(ASK))?;
        Ok(s)
    });
    let mut s = match s {
        Ok(s) => s,
        Err(e) => return errno(&e),
    };
    let Ok(a) = (Ask::Ask {
        model: b"claude-m".to_vec(),
        max_tokens: 10,
        system: vec![],
        roles: vec![0],
        texts: vec![b"hello".to_vec()],
    })
    .encode() else {
        return "bad-ask".into();
    };
    if write_frame(&mut s, &a).is_err() {
        return "denied write".into();
    }
    let f = match read_frame(&mut s) {
        Ok(f) => f,
        Err(e) => return format!("denied read {e:?}"),
    };
    let kept = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(recv)
        .and_then(|mut r| r.write_all(&f));
    if kept.is_err() {
        return "denied recv".into();
    }
    match Answer::decode(&f) {
        Ok(Answer::Reply { text }) => format!("ok reply {}", String::from_utf8_lossy(&text)),
        Ok(Answer::Status { status }) => format!("ok status {status}"),
        Ok(Answer::Refused { broker_refusal }) => format!("ok refused {}", broker_refusal.name()),
        Err(e) => format!("denied decode {e:?}"),
    }
}

/// One command through a member socket: `ok <exit> <text>`, the reply's stdout when the exit is
/// OK, else its stderr, newlines as `|`.
fn nd(rest: &str) -> String {
    let mut words = rest.split(' ');
    let Some(sock) = words.next() else {
        return "bad-nd".into();
    };
    let argv: Vec<Vec<u8>> = words.map(|w| w.as_bytes().to_vec()).collect();
    let mut s = match UnixStream::connect(sock).and_then(|s| {
        s.set_read_timeout(Some(table::REPLY))?;
        Ok(s)
    }) {
        Ok(s) => s,
        Err(e) => return errno(&e),
    };
    let Ok(c) = (Command { argv }).encode() else {
        return "bad-nd".into();
    };
    if frame::write(&mut s, table::LIMITS, follow_op::COMMAND, &c).is_err() {
        return "denied write".into();
    }
    let f = match frame::read(&mut s, table::LIMITS) {
        Ok(f) if f.op == status::OK => f,
        Ok(f) => return format!("denied op {}", f.op),
        Err(e) => return format!("denied read {e:?}"),
    };
    match CommandReply::decode(&f.payload) {
        Ok(r) => {
            let text = if r.exit == command_exit::OK {
                r.stdout
            } else {
                r.stderr
            };
            let text = String::from_utf8_lossy(&text).trim_end().replace('\n', "|");
            format!("ok {} {text}", r.exit)
        }
        Err(e) => format!("denied decode {e:?}"),
    }
}

fn wait(path: &str) -> String {
    let deadline = Instant::now() + WAIT;
    while Instant::now() < deadline {
        if Path::new(path).exists() {
            return "ok".into();
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    "denied timeout".into()
}

fn attempt(op: &str, path: &str, recv: &Path) -> String {
    let r = match op {
        "read" => std::fs::File::open(path).and_then(|mut f| {
            let mut b = Vec::new();
            f.read_to_end(&mut b).map(|_| ())
        }),
        "write" => std::fs::write(path, b"probe"),
        "connect" => UnixStream::connect(path).map(|_| ()),
        "ask" => return ask(path, recv),
        "wait" => return wait(path),
        "nd" => return nd(path),
        "list" => match std::fs::read_dir(path) {
            Ok(rd) => {
                let mut names: Vec<String> = rd
                    .filter_map(|e| e.ok())
                    .map(|e| e.file_name().to_string_lossy().into_owned())
                    .collect();
                names.sort();
                return format!("ok {}", names.join(","));
            }
            Err(e) => Err(e),
        },
        _ => return "bad-op".into(),
    };
    match r {
        Ok(()) => "ok".into(),
        Err(e) => errno(&e),
    }
}

fn main() -> ExitCode {
    let args: Vec<PathBuf> = std::env::args_os().map(PathBuf::from).collect();
    let (pkg, vol) = match args.as_slice() {
        [_, flag, ws, ..] if flag.as_os_str() == "--stdio" => (ws.clone(), ws.clone()),
        [me, ..] => {
            let (Some(pkg), Some(grain)) = (me.parent(), me.parent().and_then(Path::parent)) else {
                return ExitCode::from(2);
            };
            (pkg.to_path_buf(), grain.join("vol"))
        }
        [] => return ExitCode::from(2),
    };
    let Ok(targets) = std::fs::read_to_string(pkg.join("probe.targets")) else {
        return ExitCode::from(2);
    };
    let recv = vol.join("probe.recv");
    let Ok(mut out) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(vol.join("probe.out"))
    else {
        return ExitCode::from(3);
    };
    for line in targets.lines() {
        let mut f = line.splitn(3, ' ');
        if let (Some(name), Some(op), Some(path)) = (f.next(), f.next(), f.next()) {
            let v = attempt(op, path, &recv);
            if writeln!(out, "{name} {v}")
                .and_then(|()| out.flush())
                .is_err()
            {
                return ExitCode::from(3);
            }
        }
    }
    ExitCode::SUCCESS
}
