//! The two sockets of a workspace as the step loop's [`Follow`] and [`Host`].

use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;

use crate::frame::{self, FrameError};
use crate::generated::{self as g, layout};
use crate::run::{Follow, Host, Outcome};
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

fn exchange(s: &mut UnixStream, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
    frame::write(s, LIMITS, op, payload).map_err(io_err)?;
    let f = frame::read(s, LIMITS).map_err(io_err)?;
    Ok((f.op, f.payload))
}

/// `follow.sock`.
pub struct FollowSocket(UnixStream);

/// `host.sock`.
pub struct HostSocket(UnixStream);

impl FollowSocket {
    /// Connect.
    pub fn connect(path: &Path) -> io::Result<Self> {
        UnixStream::connect(path).map(Self)
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
    /// Connect.
    pub fn connect(path: &Path) -> io::Result<Self> {
        UnixStream::connect(path).map(Self)
    }
}

impl Host for HostSocket {
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        exchange(&mut self.0, op, payload)
    }
}
