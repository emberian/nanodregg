//! One frame: a `u32` little-endian body length, then the body, which is one operation byte
//! followed by the payload. The body length counts the operation byte, so it is at least 1.
//!
//! The bound is the codec table's `frameBytesMax`, passed in as [`Limits`]. A length past the
//! bound is refused before any allocation; a stream that ends inside a frame is `Truncated`,
//! never a short frame. Time is bounded per REPLY, not per syscall, by [`Deadline`].
//!
//! The layout is Lean's (CLIENT-40): a frame is `Protocol.socketFrame` (`Stream.bytesOf`), its
//! length prefix `FRAME_LEN_BYTES` wide, its body read by `Protocol.bodyParts?`; the child wire's
//! body is `Host.Wire.decodeBody`'s `u32le conn ‖ byte ‖ payload` ([`child_parts`]). Each refusal
//! renders as Lean's verdict on the same bytes (`client/tests/vectors.rs`, the codec vectors'
//! `wire/frame` and `wire/child` rows).

use std::io::{self, ErrorKind, Read, Write};
use std::os::fd::AsFd;
use std::time::{Duration, Instant};

use rustix::event::{PollFd, PollFlags, Timespec, poll};

use crate::generated as g;

/// Reads and writes on `s` that fail `TimedOut` once `until` has passed, however the bytes trickle
/// (CLIENT-39, A18: a bound per reply; a per-syscall timeout let a peer sending one byte per 119 s
/// hold a 262 144-byte frame open for a year). Each call first polls for at most what is left. A
/// write moves at most `PIPE_BUF` bytes, which a ready pipe or socket takes without blocking. One
/// mechanism for every peer of ours: a socket, a decider's pipe, an upstream TCP stream.
pub struct Deadline<'a, S: AsFd> {
    s: &'a S,
    until: Instant,
}

impl<'a, S: AsFd> Deadline<'a, S> {
    /// A deadline `within` from now.
    pub fn within(s: &'a S, within: Duration) -> Self {
        Self::until(s, Instant::now() + within)
    }
    /// A deadline at `until`.
    pub fn until(s: &'a S, until: Instant) -> Self {
        Self { s, until }
    }
    fn ready(&self, flags: PollFlags) -> io::Result<()> {
        let left = self.until.saturating_duration_since(Instant::now());
        let timeout =
            Timespec::try_from(left).map_err(|_| io::Error::from(ErrorKind::InvalidInput))?;
        if left.is_zero() {
            return Err(ErrorKind::TimedOut.into());
        }
        match poll(&mut [PollFd::new(self.s, flags)], Some(&timeout)) {
            Ok(0) => Err(ErrorKind::TimedOut.into()),
            Ok(_) => Ok(()),
            Err(e) => Err(e.into()),
        }
    }
}

impl<S: AsFd> Read for Deadline<'_, S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.ready(PollFlags::IN)?;
        Ok(rustix::io::read(self.s, buf)?)
    }
}

impl<S: AsFd> Write for Deadline<'_, S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.ready(PollFlags::OUT)?;
        let n = buf.len().min(rustix::pipe::PIPE_BUF);
        Ok(rustix::io::write(self.s, &buf[..n])?)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The bounds a frame obeys. Built only from the generated operation table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Largest body (operation byte + payload) either side may send.
    pub frame_bytes_max: u32,
}

/// A decoded frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    /// The operation byte (a request's operation, or a reply's echo / refusal marker).
    pub op: u8,
    /// Everything after the operation byte.
    pub payload: Vec<u8>,
}

/// Why a frame was not read or not written. Each is a refusal by name.
#[derive(Debug)]
pub enum FrameError {
    /// The stream ended cleanly before the first byte of a frame.
    Closed,
    /// The stream ended inside a frame.
    Truncated {
        /// Where the missing part starts: 0 in the header, `FRAME_LEN_BYTES` in the body.
        offset: usize,
        /// Bytes the frame needed at this point.
        wanted: usize,
        /// Bytes that arrived.
        got: usize,
    },
    /// A body of length zero carries no operation byte.
    Empty,
    /// A child-wire body too short to hold a connection id and a byte (`Host.Wire`'s `badLength`).
    BadLength {
        /// The body's size.
        len: usize,
    },
    /// The body is longer than `frame_bytes_max`.
    PastBound {
        /// The length that was declared or asked for.
        len: u64,
        /// The bound in force.
        max: u32,
    },
    /// The transport failed.
    Io(io::Error),
}

impl std::fmt::Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closed => write!(f, "frame: closed"),
            Self::Truncated {
                offset,
                wanted,
                got,
            } => {
                write!(f, "frame: truncated ({got} of {wanted} bytes at {offset})")
            }
            Self::Empty => write!(f, "frame: empty body"),
            Self::BadLength { len } => write!(f, "frame: badLength ({len} bytes)"),
            Self::PastBound { len, max } => {
                write!(f, "frame: pastBound frameBytesMax ({len} > {max})")
            }
            Self::Io(e) => write!(f, "frame: {e}"),
        }
    }
}

impl std::error::Error for FrameError {}

/// The length prefix: Lean's `Bounds.frameLenBytes`, which must be a `u32`'s width (the build
/// fails here if Lean's frame stops being `Stream.bytesOf`'s `u32` length).
const HEADER: usize = g::FRAME_LEN_BYTES as usize;
const _: () = assert!(HEADER == size_of::<u32>());
/// The child wire's connection id: Lean's `Bounds.connBytes`, a `u32`'s width.
pub const CONN: usize = g::CONN_BYTES as usize;
const _: () = assert!(CONN == size_of::<u32>());

/// Read exactly `buf.len()` bytes; `Ok(n)` with `n < buf.len()` only at end of stream.
fn fill(r: &mut impl Read, buf: &mut [u8]) -> Result<usize, FrameError> {
    let mut got = 0;
    while got < buf.len() {
        match r.read(&mut buf[got..]) {
            Ok(0) => break,
            Ok(n) => got += n,
            Err(e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => return Err(FrameError::Io(e)),
        }
    }
    Ok(got)
}

/// Read one length-prefixed body of `1 ..= max` bytes.
pub fn read_body(r: &mut impl Read, max: u32) -> Result<Vec<u8>, FrameError> {
    let mut header = [0u8; HEADER];
    match fill(r, &mut header)? {
        0 => return Err(FrameError::Closed),
        HEADER => {}
        got => {
            return Err(FrameError::Truncated {
                offset: 0,
                wanted: HEADER,
                got,
            });
        }
    }
    let len = u32::from_le_bytes(header);
    let past = FrameError::PastBound {
        len: u64::from(len),
        max,
    };
    if len == 0 {
        return Err(FrameError::Empty);
    }
    if len > max {
        return Err(past);
    }
    let len = usize::try_from(len).map_err(|_| past)?;
    let mut body = vec![0u8; len];
    let got = fill(r, &mut body)?;
    if got != len {
        return Err(FrameError::Truncated {
            offset: HEADER,
            wanted: len,
            got,
        });
    }
    Ok(body)
}

/// The frame of one body made of `parts`, refusing a body past `max` (or empty): the one place a
/// length prefix is written.
pub fn encode_body(max: u32, parts: &[&[u8]]) -> Result<Vec<u8>, FrameError> {
    let total: u64 = parts.iter().map(|p| p.len() as u64).sum();
    if total == 0 {
        return Err(FrameError::Empty);
    }
    if total > u64::from(max) {
        return Err(FrameError::PastBound { len: total, max });
    }
    let len = u32::try_from(total).map_err(|_| FrameError::PastBound { len: total, max })?;
    let mut bytes = Vec::with_capacity(HEADER + parts.iter().map(|p| p.len()).sum::<usize>());
    bytes.extend_from_slice(&len.to_le_bytes());
    for part in parts {
        bytes.extend_from_slice(part);
    }
    assert_eq!(
        bytes.len() as u64,
        HEADER as u64 + total,
        "frame layout: header + body"
    );
    Ok(bytes)
}

/// Write one body made of `parts`, in a single `write_all`, refusing a body past `max` (or empty)
/// before writing anything.
pub fn write_body(w: &mut impl Write, max: u32, parts: &[&[u8]]) -> Result<(), FrameError> {
    let bytes = encode_body(max, parts)?;
    w.write_all(&bytes).map_err(FrameError::Io)?;
    w.flush().map_err(FrameError::Io)
}

/// Read one frame.
pub fn read(r: &mut impl Read, limits: Limits) -> Result<Frame, FrameError> {
    let mut body = read_body(r, limits.frame_bytes_max)?;
    let payload = body.split_off(1);
    Ok(Frame {
        op: body[0],
        payload,
    })
}

/// Write one frame, refusing a body past the bound before writing anything.
pub fn write(w: &mut impl Write, limits: Limits, op: u8, payload: &[u8]) -> Result<(), FrameError> {
    write_body(w, limits.frame_bytes_max, &[&[op], payload])
}

/// The child wire's bound for a client frame bound: the body plus the connection id.
pub fn child_max(limits: Limits) -> u32 {
    limits.frame_bytes_max.saturating_add(g::CONN_BYTES)
}

/// What a child-wire body holds (`Host.Wire.decodeBody`): the connection id, the op or status byte,
/// the payload; `BadLength` when it is too short to hold the first two.
pub fn child_parts(body: &[u8]) -> Result<(u32, u8, &[u8]), FrameError> {
    let bad = || FrameError::BadLength { len: body.len() };
    let (conn, rest) = body.split_first_chunk::<CONN>().ok_or_else(bad)?;
    let (&byte, payload) = rest.split_first().ok_or_else(bad)?;
    Ok((u32::from_le_bytes(*conn), byte, payload))
}

/// The child-wire frame `conn ‖ byte ‖ payload` under `max` (`Host.Wire.encodeFrame`).
pub fn child_frame(max: u32, conn: u32, byte: u8, payload: &[u8]) -> Result<Vec<u8>, FrameError> {
    encode_body(max, &[&conn.to_le_bytes(), &[byte], payload])
}

/// Write one child-wire frame in a single `write_all`.
pub fn write_child(
    w: &mut impl Write,
    max: u32,
    conn: u32,
    byte: u8,
    payload: &[u8],
) -> Result<(), FrameError> {
    let bytes = child_frame(max, conn, byte, payload)?;
    w.write_all(&bytes).map_err(FrameError::Io)?;
    w.flush().map_err(FrameError::Io)
}
