//! `nd-supervise SOCKET [--group GID [--peer UID]] (--hide|--read|--write|--exec|--connect PATH)… --
//! /ABS/PROGRAM [ARG]…` (`--peer`: only that uid in GID connects, others closed `peerRefused`)
//!
//! Binds SOCKET (mode 0600; with `--group GID`, mode 0660 group GID, refused unless SOCKET's
//! directory passes `custody::check_shared_dir` with group GID: HOSTING-17 §7's nd-hosted follower,
//! whose driver `nd` runs as another uid in that group), starts PROGRAM confined by `sandbox` (CLIENT-9: the child sees only
//! its program, the `--read`/`--write`/`--exec` paths and the platform floor; every `--hide` path,
//! the member's workspace first, must lie outside all of them, CLIENT-8), and moves frames between
//! the socket's connections and the child's stdio (`mux`). It exits when the child does, with the
//! child's status, or with one of its own (`Protocol.Exit`, emitted: refusedAtLaunch,
//! childUnroutable, childSignaled); the service manager restarts the pair. Nothing is parsed but frame headers.
//! SIGTERM (nd-members removing a resident, a unit's stop) stops the child, so every peer reads
//! `closed unreachable` (CLIENT-30), and then ends the supervisor as SIGTERM's default action would.

use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::process::{ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use nanodregg_client::generated::supervisor_exit as exit;
use nanodregg_client::mux::{self, MuxEnd};
use nanodregg_client::{sockets, table};
use nanodregg_sandbox::{Policy, command};
use signal_hook::consts::SIGTERM;
use signal_hook::iterator::Signals;
use signal_hook::low_level::emulate_default_handler;

const USAGE: &str = "usage: nd-supervise SOCKET [--group GID [--peer UID]] (--hide|--read|--write|--exec|--connect PATH)... -- /ABS/PROGRAM [ARG]...";

struct Args {
    socket: PathBuf,
    group: Option<u32>,
    peer: Option<(u32, u32)>,
    policy: Policy,
    program: OsString,
    args: Vec<OsString>,
}

fn parse(mut argv: impl Iterator<Item = OsString>) -> Result<Args, String> {
    let socket = PathBuf::from(argv.next().ok_or(USAGE)?);
    let mut policy = Policy::default();
    let mut group = None;
    let mut peer = None;
    loop {
        let list = match argv.next() {
            Some(a) if a == "--" => break,
            Some(a) if (a == "--group" && group.is_none()) || (a == "--peer" && peer.is_none()) => {
                let n = argv.next().ok_or(USAGE)?;
                let n: u32 = n.to_str().and_then(|n| n.parse().ok()).ok_or(USAGE)?;
                *if a == "--group" {
                    &mut group
                } else {
                    &mut peer
                } = Some(n);
                continue;
            }
            Some(a) => policy.list(&a).ok_or(USAGE)?,
            None => return Err(USAGE.into()),
        };
        list.push(PathBuf::from(argv.next().ok_or(USAGE)?));
    }
    if policy.hidden.is_empty() {
        return Err(
            "nd-supervise: refusing to start a child with nothing hidden (CLIENT-8)".into(),
        );
    }
    if peer.is_some() && group.is_none() {
        return Err("nd-supervise: --peer needs --group (the peer is (uid, gid))".into());
    }
    let program = argv.next().ok_or(USAGE)?;
    Ok(Args {
        socket,
        group,
        peer: peer.zip(group),
        policy,
        program,
        args: argv.collect(),
    })
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(exit::REFUSED_AT_LAUNCH)
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let a = parse(std::env::args_os().skip(1))?;
    // Law 4: every fd the mux may hold is one the kernel will give (CLIENT-28).
    let need = table::MUX.fds_max();
    if let Some(have) = rustix::process::getrlimit(rustix::process::Resource::Nofile).current
        && have < need
    {
        return Err(format!(
            "nd-supervise: RLIMIT_NOFILE {have} is below the {need} fds it may hold (CLIENT-28)"
        ));
    }
    let at = |e: std::io::Error| format!("nd-supervise: {}: {e}", a.socket.display());
    sockets::check_supervised(&a.socket, a.group).map_err(at)?;
    // Caught before the child exists, so no peer is ever served by a supervisor SIGTERM ends unheard.
    let mut term = Signals::new([SIGTERM]).map_err(|e| format!("nd-supervise: SIGTERM: {e}"))?;
    let args: Vec<&std::ffi::OsStr> = a.args.iter().map(OsString::as_os_str).collect();
    let mut child = command(&a.policy, &a.program, &args)
        .map_err(|e| format!("nd-supervise: {e}"))?
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("nd-supervise: spawn: {e}"))?;
    let (Some(child_in), Some(child_out)) = (child.stdin.take(), child.stdout.take()) else {
        return Err("nd-supervise: child stdio missing".into());
    };
    // Bound only now: every refusal above leaves no socket, and no peer waits on a missing child.
    let listener = sockets::bind_supervised(&a.socket, a.group).map_err(|e| {
        let _ = (child.kill(), child.wait());
        at(e)
    })?;
    let child = Arc::new(Mutex::new(child));
    let termed = Arc::new(AtomicBool::new(false));
    let (held, said) = (Arc::clone(&child), Arc::clone(&termed));
    std::thread::spawn(move || {
        if term.forever().next().is_some() {
            said.store(true, Ordering::SeqCst);
            eprintln!("nd-supervise: SIGTERM: stopping the child");
            // serving: the child's stdout closes, `serve` names every close; past it: the default
            match held.try_lock() {
                Ok(mut c) => drop(c.kill()),
                Err(_) => drop(emulate_default_handler(SIGTERM)),
            }
        }
    });
    let end = mux::serve_admitting(listener, child_in, child_out, table::MUX, a.peer);
    let _ = fs::remove_file(&a.socket);
    let mut child = child.lock().unwrap_or_else(PoisonError::into_inner);
    if let MuxEnd::ChildMalformed(ref e) = end {
        // A child that writes unroutable frames is broken; stop it (we hold its handle).
        let _ = child.kill();
        eprintln!("nd-supervise: child wrote an unroutable frame: {e}");
    }
    let status = child
        .wait()
        .map_err(|e| format!("nd-supervise: wait: {e}"))?;
    eprintln!("nd-supervise: {end:?}; child {status}");
    if termed.load(Ordering::SeqCst) {
        // stopped by SIGTERM: end as it would have ended us, the service manager's clean stop
        let _ = emulate_default_handler(SIGTERM);
    }
    // How a signal death reaches us is the mechanism's (sandbox::killed_by_signal).
    Ok(match (end, status.code()) {
        (MuxEnd::ChildMalformed(_), _) => ExitCode::from(exit::CHILD_UNROUTABLE),
        _ if nanodregg_sandbox::killed_by_signal(status) => ExitCode::from(exit::CHILD_SIGNALED),
        (_, Some(c)) => ExitCode::from(u8::try_from(c).unwrap_or(exit::CHILD_SIGNALED)),
        (_, None) => ExitCode::from(exit::CHILD_SIGNALED),
    })
}
