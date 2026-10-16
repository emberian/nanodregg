//! The two sockets of a workspace as the step loop's [`Follow`] and [`Host`].

use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;

use crate::frame::{self, FrameError};
use crate::generated as g;
use crate::run::{Follow, Host, Outcome, Step};
use crate::table::LIMITS;
use crate::wire;

fn io_err(e: FrameError) -> io::Error {
    match e {
        FrameError::Io(e) => e,
        e => io::Error::new(io::ErrorKind::InvalidData, e.to_string()),
    }
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
            // Follow refused the command itself; its payload is follow's own rendering.
            return Ok(Step::Done {
                exit: 1,
                stdout: Vec::new(),
                stderr: reply,
            });
        }
        wire::step(&reply).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))
    }
}

impl Follow for FollowSocket {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        let payload = wire::argv(argv)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e.to_string()))?;
        self.ask(g::follow_op::COMMAND, &payload)
    }
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step> {
        self.ask(g::follow_op::RESUME, &wire::resume(k, outcome))
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
