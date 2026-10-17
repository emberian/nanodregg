//! The two sockets of a workspace as the step loop's [`Follow`] and [`Host`].

use std::io;
use std::os::unix::net::UnixStream;
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
    fn ask(&mut self, op: u8, payload: &[u8]) -> io::Result<Step> {
        let (status, reply) = exchange(&mut self.0, op, payload)?;
        if status != g::status::OK {
            // Follow answers every command, its own refusals included, with a `done` step; any
            // other status is follow refusing the frame itself, and is not rendered as a verdict.
            // A supervisor close is named by its emitted CloseReason name (PROTOCOL-22).
            let what = if status == g::status::CLOSED {
                "closed".to_string()
            } else {
                format!("status {status}:")
            };
            return Err(io::Error::other(format!(
                "{what} {}",
                String::from_utf8_lossy(&reply)
            )));
        }
        Step::decode(&reply).map_err(|r| malformed("step", r))
    }
}

impl Follow for FollowSocket {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
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
        self.ask(g::follow_op::COMMAND, &payload)
    }
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step> {
        let payload = layout::Resume {
            k: k.to_vec(),
            result: outcome.result(),
        }
        .encode()
        .map_err(|r| malformed("resume", r))?;
        self.ask(g::follow_op::RESUME, &payload)
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
