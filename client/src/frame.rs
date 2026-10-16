//! One frame: a `u32` little-endian body length, then the body, which is one operation byte
//! followed by the payload. The body length counts the operation byte, so it is at least 1.
//!
//! The bound is the codec table's `frameBytesMax`, passed in as [`Limits`]. A length past the
//! bound is refused before any allocation; a stream that ends inside a frame is `Truncated`,
//! never a short frame.

use std::io::{self, ErrorKind, Read, Write};

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
        /// Bytes the frame needed at this point.
        wanted: usize,
        /// Bytes that arrived.
        got: usize,
    },
    /// A body of length zero carries no operation byte.
    Empty,
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
            Self::Truncated { wanted, got } => write!(f, "frame: truncated ({got} of {wanted} bytes)"),
            Self::Empty => write!(f, "frame: empty body"),
            Self::PastBound { len, max } => write!(f, "frame: pastBound frameBytesMax ({len} > {max})"),
            Self::Io(e) => write!(f, "frame: {e}"),
        }
    }
}

impl std::error::Error for FrameError {}

const HEADER: usize = 4;

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
        got => return Err(FrameError::Truncated { wanted: HEADER, got }),
    }
    let len = u32::from_le_bytes(header);
    let past = FrameError::PastBound { len: u64::from(len), max };
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
        return Err(FrameError::Truncated { wanted: len, got });
    }
    Ok(body)
}

/// Write one body made of `parts`, in a single `write_all`, refusing a body past `max` (or empty)
/// before writing anything.
pub fn write_body(w: &mut impl Write, max: u32, parts: &[&[u8]]) -> Result<(), FrameError> {
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
    assert_eq!(bytes.len() as u64, HEADER as u64 + total, "frame layout: header + body");
    w.write_all(&bytes).map_err(FrameError::Io)?;
    w.flush().map_err(FrameError::Io)
}

/// Read one frame.
pub fn read(r: &mut impl Read, limits: Limits) -> Result<Frame, FrameError> {
    let mut body = read_body(r, limits.frame_bytes_max)?;
    let payload = body.split_off(1);
    Ok(Frame { op: body[0], payload })
}

/// Write one frame, refusing a body past the bound before writing anything.
pub fn write(w: &mut impl Write, limits: Limits, op: u8, payload: &[u8]) -> Result<(), FrameError> {
    write_body(w, limits.frame_bytes_max, &[&[op], payload])
}
