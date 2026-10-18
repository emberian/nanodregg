//! The two sockets of a workspace as the step loop's [`Follow`] and [`Host`].

use std::fs;
use std::io;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;

use crate::frame::{self, FrameError};
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

/// One request, one reply, each bounded by `replyMsMax`; past it the error is `timeout` by name
/// (the step loop then treats a frozen call as lost: uncertain, settled by lookup).
fn exchange(s: &mut UnixStream, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
    let timeout = |e: io::Error| match e.kind() {
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => {
            io::Error::new(io::ErrorKind::TimedOut, "timeout (replyMsMax)")
        }
        _ => e,
    };
    frame::write(s, LIMITS, op, payload)
        .map_err(io_err)
        .map_err(timeout)?;
    let f = frame::read(s, LIMITS).map_err(io_err).map_err(timeout)?;
    Ok((f.op, f.payload))
}

/// Connect, with both directions bounded by `reply` (nd passes `table::REPLY`, replyMsMax).
fn connect(path: &Path, reply: Duration) -> io::Result<UnixStream> {
    let s = UnixStream::connect(path)?;
    s.set_read_timeout(Some(reply))?;
    s.set_write_timeout(Some(reply))?;
    Ok(s)
}

/// `follow.sock`.
pub struct FollowSocket(UnixStream);

/// `host.sock`.
pub struct HostSocket(UnixStream);

impl FollowSocket {
    /// Connect; each reply is waited for at most `reply`.
    pub fn connect(path: &Path, reply: Duration) -> io::Result<Self> {
        connect(path, reply).map(Self)
    }
    fn ask(&mut self, (op, payload): (u8, Vec<u8>)) -> io::Result<Step> {
        let (status, reply) = exchange(&mut self.0, op, &payload)?;
        step(status, &reply)
    }
}

/// Follow's reply as a step. Follow answers every command, its own refusals included, with a
/// `done` step; any other status is follow refusing the frame itself, and is not rendered as a
/// verdict. A supervisor close is named by its emitted CloseReason name (PROTOCOL-22).
pub(crate) fn step(status: u8, reply: &[u8]) -> io::Result<Step> {
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
pub(crate) fn command(argv: &[Vec<u8>]) -> io::Result<(u8, Vec<u8>)> {
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
pub(crate) fn resume(k: &[u8], outcome: &Outcome) -> io::Result<(u8, Vec<u8>)> {
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
    /// Connect; each reply is waited for at most `reply`.
    pub fn connect(path: &Path, reply: Duration) -> io::Result<Self> {
        connect(path, reply).map(Self)
    }
}

impl Host for HostSocket {
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        exchange(&mut self.0, op, payload)
    }
}

/// nd-supervise's socket (CLIENT-21). Bind, replacing only a socket file nobody is listening on: 0600, or with `group` 0660 in a
/// shared directory of that group (`sharedDirRefused`, `groupMismatch` otherwise). The socket is
/// born owner-only (umask 0177) and widened only after its group is checked.
pub fn bind_supervised(path: &Path, group: Option<u32>) -> io::Result<UnixListener> {
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
    let umask = rustix::process::umask(rustix::fs::Mode::from_raw_mode(0o177));
    let bound = UnixListener::bind(path);
    rustix::process::umask(umask); // the child inherits the operator's umask, not ours
    let listener = bound?;
    // The setgid directory gives the socket its group (checked above): 0660 is that group's.
    let mode = if group.is_some() { 0o660 } else { 0o600 };
    fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
    Ok(listener)
}
