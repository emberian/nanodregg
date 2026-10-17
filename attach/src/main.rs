//! `nd-attach HOST_SOCK` — the box end of a friend's ssh channel (CLIENT-12 option B).
//!
//! The operator's `authorized_keys` runs it once per friend key:
//! `restrict,command="nd-attach /srv/nd/stores/<label>/host.sock" ssh-ed25519 …`. The friend's side
//! is the ordinary supervisor (`nd-supervise ws/host.sock … -- ssh -T box`), so stdin carries the
//! child-side frames `u32le conn ‖ byte ‖ payload` and stdout takes `u32le conn ‖ status ‖
//! payload`: the mux's own wire read the other way (law 1: one shape). Each new `conn` gets its own
//! connection to HOST_SOCK, at most `PEER_CONNECTIONS_MAX` at once (one ssh session is one process,
//! so the cap is per session; nothing here names the friend). Every end is named (PROTOCOL-22/23):
//! a conn past the cap is answered `closed full`, one HOST_SOCK refuses `closed unreachable`, a frame
//! for a conn that already ended `closed ended`; a hang-up from the friend's supervisor closes that
//! conn's upstream connection, frees its slot and is acknowledged by name; a `closed` from the box
//! ends the conn here and is relayed. It decides nothing about a request and exits when stdin ends.

use std::collections::HashMap;
use std::io::{self, Write};
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::process::ExitCode;
use std::sync::{Arc, Mutex, PoisonError};
use std::thread;

use nanodregg_client::frame::{self, FrameError};
use nanodregg_client::generated::{self as g, CloseReason, status};
use nanodregg_client::table;

type Open = Mutex<HashMap<u32, UnixStream>>;

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One conn-tagged frame to stdout; the lock keeps frames whole.
fn emit(out: &Mutex<io::Stdout>, conn: u32, st: u8, payload: &[u8]) -> Result<(), FrameError> {
    let max = table::LIMITS.frame_bytes_max.saturating_add(4);
    let mut o = lock(out);
    frame::write_body(&mut *o, max, &[&conn.to_le_bytes(), &[st], payload])?;
    o.flush().map_err(FrameError::Io)
}

fn closed(out: &Mutex<io::Stdout>, conn: u32, r: CloseReason) -> Result<(), FrameError> {
    emit(out, conn, status::CLOSED, r.name().as_bytes())
}

/// Forget `conn` and shut its upstream connection; whether it was open.
fn drop_conn(open: &Open, conn: u32) -> bool {
    lock(open)
        .remove(&conn)
        .map(|s| s.shutdown(Shutdown::Both))
        .is_some()
}

/// Box → friend for one conn: every reply, tagged, until the box closes it (relayed) or goes away
/// (`closed unreachable`, unless this end already dropped the conn).
fn relay(conn: u32, mut up: UnixStream, out: &Mutex<io::Stdout>, open: &Open) {
    while let Ok(f) = frame::read(&mut up, table::LIMITS) {
        if emit(out, conn, f.op, &f.payload).is_err() || f.op == status::CLOSED {
            drop_conn(open, conn);
            return;
        }
    }
    if drop_conn(open, conn) {
        let _ = closed(out, conn, CloseReason::Unreachable);
    }
}

fn run(sock: &str) -> Result<(), FrameError> {
    let out = Arc::new(Mutex::new(io::stdout()));
    let open: Arc<Open> = Arc::new(Mutex::new(HashMap::new()));
    let mut input = io::stdin().lock();
    // The friend's supervisor numbers conns upward from 0; one at or below this has been seen.
    let mut seen: Option<u32> = None;
    let max = table::LIMITS.frame_bytes_max.saturating_add(4);
    loop {
        let body = match frame::read_body(&mut input, max) {
            Ok(b) => b,
            Err(FrameError::Closed) => return Ok(()),
            Err(e) => return Err(e),
        };
        let Some((c, rest)) = body.split_first_chunk::<4>() else {
            return Err(FrameError::Truncated {
                wanted: 5,
                got: body.len(),
            });
        };
        let Some((&byte, payload)) = rest.split_first() else {
            return Err(FrameError::Truncated {
                wanted: 5,
                got: body.len(),
            });
        };
        let conn = u32::from_le_bytes(*c);
        if byte == g::HANGUP {
            // The friend's connection ended: free its slot, acknowledge by name (PROTOCOL-23).
            drop_conn(&open, conn);
            emit(&out, conn, status::CLOSED, payload)?;
            continue;
        }
        let up = lock(&open).get(&conn).and_then(|s| s.try_clone().ok());
        let mut up = match up {
            Some(s) => s,
            None if seen.is_some_and(|m| conn <= m) => {
                closed(&out, conn, CloseReason::Ended)?;
                continue;
            }
            None => {
                seen = Some(conn);
                if lock(&open).len() >= g::PEER_CONNECTIONS_MAX as usize {
                    closed(&out, conn, CloseReason::Full)?;
                    continue;
                }
                let Ok(s) = UnixStream::connect(sock) else {
                    closed(&out, conn, CloseReason::Unreachable)?;
                    continue;
                };
                let (Ok(keep), Ok(reader)) = (s.try_clone(), s.try_clone()) else {
                    closed(&out, conn, CloseReason::Unreachable)?;
                    continue;
                };
                lock(&open).insert(conn, keep);
                let (o, m) = (Arc::clone(&out), Arc::clone(&open));
                thread::spawn(move || relay(conn, reader, &o, &m));
                s
            }
        };
        if frame::write(&mut up, table::LIMITS, byte, payload).is_err() && drop_conn(&open, conn) {
            closed(&out, conn, CloseReason::Unreachable)?;
        }
    }
}

/// Exits are Lean's (`Protocol.SupervisorExit`, emitted): a bad argv is `refusedAtLaunch`, and a
/// frame from the friend's supervisor that cannot be routed is `childUnroutable` (this end is
/// that supervisor's child).
fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [sock] = args.as_slice() else {
        eprintln!("usage: nd-attach HOST_SOCK");
        return ExitCode::from(g::supervisor_exit::REFUSED_AT_LAUNCH);
    };
    match run(sock) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("nd-attach: {e}");
            ExitCode::from(g::supervisor_exit::CHILD_UNROUTABLE)
        }
    }
}
