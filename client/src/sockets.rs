//! The two sockets of a workspace as the step loop's [`Follow`] and [`Host`].

use std::fs;
use std::io;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;

use crate::frame::{self, Deadline, FrameError};
use crate::generated::{self as g, layout};
use crate::run::{Follow, Host, Outcome};
use std::time::Duration;

use crate::table::LIMITS;
use layout::Step;

fn io_err(e: FrameError) -> io::Error {
    match e {
        FrameError::Io(e) => e,
        e => io::Error::new(io::ErrorKind::InvalidData, e.to_string()),
    }
}

fn malformed(what: &str, r: layout::Refusal) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("{what}: {r:?}"))
}

/// One request and its reply within ONE `reply` (`replyMsMax`) from the first byte sent to the last
/// byte read, however the peer trickles (CLIENT-39); past it the error is `timeout` by name (the
/// step loop then treats a frozen call as lost: uncertain, settled by lookup).
fn exchange(s: &UnixStream, reply: Duration, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
    let timeout = |e: io::Error| match e.kind() {
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => {
            io::Error::new(io::ErrorKind::TimedOut, "timeout (replyMsMax)")
        }
        _ => e,
    };
    let mut d = Deadline::within(s, reply);
    frame::request(&mut d, LIMITS, op, payload)
        .map_err(io_err)
        .map_err(timeout)?;
    let f = frame::read(&mut d, LIMITS)
        .map_err(io_err)
        .map_err(timeout)?;
    wire_refused(f.op, &f.payload)?;
    Ok((f.op, f.payload))
}

/// A server's `refused wireVersion N expected M` (PROTOCOL-87) ends the exchange as the transport's
/// error, by that name: the server read nothing past the version, so no step of either side may take
/// the reply as a verdict on the request. It names the remedy, since no retry can succeed.
fn wire_refused(status: u8, payload: &[u8]) -> io::Result<()> {
    if status == g::status::REFUSED && payload.starts_with(b"wireVersion ") {
        return Err(io::Error::other(format!(
            "refused {}: this nd and the server it reached were built from different commits; run one build of both",
            String::from_utf8_lossy(payload)
        )));
    }
    Ok(())
}

/// `follow.sock`; each exchange bounded by its `Duration` (nd passes `table::REPLY`).
pub struct FollowSocket(UnixStream, Duration);

/// `host.sock`; each exchange bounded by its `Duration`.
pub struct HostSocket(UnixStream, Duration);

impl FollowSocket {
    /// Connect (through the confined child's connector, `sandbox::connect_unix`); each reply is
    /// waited for at most `reply`.
    pub fn connect(path: &Path, reply: Duration) -> io::Result<Self> {
        Ok(Self(nanodregg_sandbox::connect_unix(path)?, reply))
    }
    fn ask(&mut self, (op, payload): (u8, Vec<u8>)) -> io::Result<Step> {
        let (status, reply) = exchange(&self.0, self.1, op, &payload)?;
        step(status, &reply)
    }
}

/// Follow's reply as a step (the one reader nd's sockets and the trace replay, `tests/trace.rs`,
/// share). Follow answers every command, its own refusals included, with a
/// `done` step; any other status is follow refusing the frame itself, and is not rendered as a
/// verdict. A supervisor close is named by its emitted CloseReason name (PROTOCOL-22).
pub fn step(status: u8, reply: &[u8]) -> io::Result<Step> {
    if status != g::status::OK {
        let what = if status == g::status::CLOSED {
            "closed".to_string()
        } else {
            format!("status {status}:")
        };
        return Err(io::Error::other(format!(
            "{what} {}",
            String::from_utf8_lossy(reply)
        )));
    }
    Step::decode(reply).map_err(|r| malformed("step", r))
}

/// A `command` request: its op and its payload, bounded by `argvBytesMax`.
pub fn command(argv: &[Vec<u8>]) -> io::Result<(u8, Vec<u8>)> {
    let payload = layout::Command {
        argv: argv.to_vec(),
    }
    .encode()
    .map_err(|r| malformed("argv", r))?;
    if payload.len() as u64 > u64::from(g::ARGV_BYTES_MAX) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("argv: pastBound argvBytesMax ({} bytes)", payload.len()),
        ));
    }
    Ok((g::follow_op::COMMAND, payload))
}

/// A `resume` request.
pub fn resume(k: &[u8], outcome: &Outcome) -> io::Result<(u8, Vec<u8>)> {
    let payload = layout::Resume {
        k: k.to_vec(),
        result: outcome.result(),
    }
    .encode()
    .map_err(|r| malformed("resume", r))?;
    Ok((g::follow_op::RESUME, payload))
}

impl Follow for FollowSocket {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        self.ask(command(argv)?)
    }
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step> {
        self.ask(resume(k, outcome)?)
    }
}

impl HostSocket {
    /// Connect (through the confined child's connector, `sandbox::connect_unix`); each reply is
    /// waited for at most `reply`.
    pub fn connect(path: &Path, reply: Duration) -> io::Result<Self> {
        Ok(Self(nanodregg_sandbox::connect_unix(path)?, reply))
    }
}

impl Host for HostSocket {
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        exchange(&self.0, self.1, op, payload)
    }
}

/// nd-supervise's socket (CLIENT-21), checked before its child launches: with `group`, in a shared
/// directory of that group (`sharedDirRefused`, `groupMismatch`); live: refused; stale: removed.
pub fn check_supervised(path: &Path, group: Option<u32>) -> io::Result<()> {
    let refused = |what: String| io::Error::other(what);
    if let Some(g) = group {
        let dir = path.parent().unwrap_or(Path::new("."));
        match nanodregg_sandbox::custody::check_shared_dir(dir) {
            Ok(d) if d == g => {}
            Ok(d) => {
                return Err(refused(format!(
                    "groupMismatch: directory group {d}, not {g}"
                )));
            }
            Err(r) => return Err(refused(format!("sharedDirRefused: {r:?}"))),
        }
    }
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
    Ok(())
}

/// Bind it once the child exists, so an accepted peer always has a child to reach (CLIENT-28):
/// checked again, born owner-only (umask 0177), widened to 0660 only after its group is checked.
pub fn bind_supervised(path: &Path, group: Option<u32>) -> io::Result<UnixListener> {
    check_supervised(path, group)?;
    let umask = rustix::process::umask(rustix::fs::Mode::from_raw_mode(0o177));
    let bound = UnixListener::bind(path);
    rustix::process::umask(umask); // the child inherits the operator's umask, not ours
    let listener = bound?;
    // The setgid directory gives the socket its group (checked above): 0660 is that group's.
    let mode = if group.is_some() { 0o660 } else { 0o600 };
    fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
    Ok(listener)
}
