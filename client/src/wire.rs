//! The step layouts of proposals/client.md §2, read and written by hand — a twin with an expiry
//! (decisions/client.md CLIENT-10): it is deleted the day PROTOCOL/CODEC commit the step layout
//! and Emit/Rust.lean emits its reader. Every length is checked against the frame it came in.
//!
//! - command payload: `u32le count ‖ (u32le len ‖ bytes)*`
//! - step (a follow reply with status ok): `u8 tag ‖ …`
//!   `done ‖ u8 exit ‖ bytes stdout ‖ bytes stderr`, `sign ‖ bytes message ‖ k…`,
//!   `host ‖ u8 op ‖ bytes payload ‖ k…`, `submit ‖ bytes call ‖ k…`
//! - resume payload: `bytes k ‖ result…` (a signature, or `u8 status ‖ payload`)
//!
//! where `bytes x` is `u32le len ‖ x`.

use crate::generated as g;
use crate::run::{Outcome, Step};

/// Why a step could not be read. A malformed step is refused, never guessed at.
#[derive(Debug, PartialEq, Eq)]
pub enum WireError {
    /// The payload ended inside a field.
    Truncated,
    /// The tag is not one the table names.
    UnknownStep(u8),
    /// The `done` step carried bytes after its fields.
    Trailing,
    /// The argv is longer than `ARGV_BYTES_MAX` (or has more than `u32::MAX` items).
    ArgvPastBound,
}

impl std::fmt::Display for WireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Truncated => write!(f, "step: truncated"),
            Self::UnknownStep(t) => write!(f, "step: unknown tag {t}"),
            Self::Trailing => write!(f, "step: trailing bytes"),
            Self::ArgvPastBound => write!(f, "argv: pastBound argvBytesMax"),
        }
    }
}

impl std::error::Error for WireError {}

fn put(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), WireError> {
    let len = u32::try_from(bytes.len()).map_err(|_| WireError::ArgvPastBound)?;
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(bytes);
    Ok(())
}

/// The `command` payload for `argv`, refused past `ARGV_BYTES_MAX`.
pub fn argv(argv: &[Vec<u8>]) -> Result<Vec<u8>, WireError> {
    let count = u32::try_from(argv.len()).map_err(|_| WireError::ArgvPastBound)?;
    let mut out = count.to_le_bytes().to_vec();
    for a in argv {
        put(&mut out, a)?;
        if out.len() as u64 > u64::from(g::ARGV_BYTES_MAX) {
            return Err(WireError::ArgvPastBound);
        }
    }
    Ok(out)
}

/// The `resume` payload.
pub fn resume(k: &[u8], outcome: &Outcome) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 + k.len() + 64);
    out.extend_from_slice(&(k.len() as u32).to_le_bytes());
    out.extend_from_slice(k);
    match outcome {
        Outcome::Signature(s) => out.extend_from_slice(s),
        Outcome::Reply { status, payload } => {
            out.push(*status);
            out.extend_from_slice(payload);
        }
    }
    out
}

struct Cursor<'a>(&'a [u8]);

impl<'a> Cursor<'a> {
    fn byte(&mut self) -> Result<u8, WireError> {
        let (&b, rest) = self.0.split_first().ok_or(WireError::Truncated)?;
        self.0 = rest;
        Ok(b)
    }
    fn bytes(&mut self) -> Result<Vec<u8>, WireError> {
        let (len, rest) = self
            .0
            .split_first_chunk::<4>()
            .ok_or(WireError::Truncated)?;
        let len = u32::from_le_bytes(*len) as usize;
        if rest.len() < len {
            return Err(WireError::Truncated);
        }
        let (field, rest) = rest.split_at(len);
        self.0 = rest;
        Ok(field.to_vec())
    }
    fn rest(self) -> Vec<u8> {
        self.0.to_vec()
    }
}

/// Read one step.
pub fn step(payload: &[u8]) -> Result<Step, WireError> {
    let mut c = Cursor(payload);
    let tag = c.byte()?;
    Ok(match tag {
        t if t == g::step::DONE => {
            let exit = c.byte()?;
            let stdout = c.bytes()?;
            let stderr = c.bytes()?;
            if !c.0.is_empty() {
                return Err(WireError::Trailing);
            }
            Step::Done {
                exit,
                stdout,
                stderr,
            }
        }
        t if t == g::step::SIGN => {
            let message = c.bytes()?;
            Step::Sign {
                message,
                k: c.rest(),
            }
        }
        t if t == g::step::HOST => {
            let op = c.byte()?;
            let payload = c.bytes()?;
            Step::Host {
                op,
                payload,
                k: c.rest(),
            }
        }
        t if t == g::step::SUBMIT => {
            let call = c.bytes()?;
            Step::Submit { call, k: c.rest() }
        }
        t => return Err(WireError::UnknownStep(t)),
    })
}
