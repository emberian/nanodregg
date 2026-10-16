//! The life of one signed call, frozen on disk so a crash cannot change what was sent.
//!
//! An attempt is a directory. `call` holds the exact signed bytes and is written once. Before
//! each send a marker `sent.<n>` is written; a settlement is one file, `committed` or
//! `not-committed`, holding the Host's reply verbatim. The state is which files exist:
//!
//! | files                                 | state                  |
//! |---------------------------------------|------------------------|
//! | `call`                                | [`State::Signed`]      |
//! | `call`, `sent.*`                      | [`State::Uncertain`]   |
//! | `call`, `sent.*`, one settlement file | [`State::Settled`]     |
//!
//! A send whose reply did not arrive is uncertain, never failed: the only way out is a lookup of
//! the same bytes. A lookup that answers absent permits one more send of the same bytes, up to the
//! caller's bound. Nothing here re-signs or re-plans: whether the call committed is the Host's
//! answer, classified by the generated outcome table into a [`Settlement`].

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::fsx;

const CALL: &str = "call";
const COMMITTED: &str = "committed";
const NOT_COMMITTED: &str = "not-committed";
const SENT_PREFIX: &str = "sent.";

/// What a Host reply says, as classified by the generated outcome table (never by this crate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Settlement {
    /// The call is in the log.
    Committed(Vec<u8>),
    /// The call is definitively not in the log and never will be (a named refusal).
    NotCommitted(Vec<u8>),
    /// The Host cannot say (its append did not read back, it is reopening, the batch is contended).
    Unknown,
    /// Lookup only: the Host has no record of these bytes.
    Absent,
}

/// Which request the attempt needs sent; the caller maps it to an operation from the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Request {
    /// Send the frozen call for admission.
    Submit,
    /// Ask whether the frozen call is in the log.
    Lookup,
}

/// Where an attempt stands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum State {
    /// Frozen, never sent.
    Signed,
    /// Sent at least once; no settlement known.
    Uncertain {
        /// How many sends have been started.
        sends: u32,
    },
    /// Settled by the Host.
    Settled {
        /// Whether it committed.
        committed: bool,
        /// The Host's reply bytes.
        reply: Vec<u8>,
    },
}

/// Why an attempt could not proceed.
#[derive(Debug)]
pub enum AttemptError {
    /// `freeze` was asked for a directory that already holds an attempt.
    AlreadyFrozen,
    /// The directory holds no `call`.
    NotAnAttempt,
    /// The directory holds both settlements, or a settlement without a send.
    Inconsistent,
    /// The reply did not fit the request (an `Absent` answer to a submit).
    UnexpectedReply,
    /// Every permitted send was used and the call is still not settled.
    SendsExhausted {
        /// The bound in force.
        sends_max: u32,
    },
    /// The file system failed.
    Io(io::Error),
}

impl std::fmt::Display for AttemptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyFrozen => write!(f, "attempt: already frozen"),
            Self::NotAnAttempt => write!(f, "attempt: no call in this directory"),
            Self::Inconsistent => write!(f, "attempt: inconsistent directory"),
            Self::UnexpectedReply => write!(f, "attempt: reply does not answer the request"),
            Self::SendsExhausted { sends_max } => {
                write!(f, "attempt: uncertain after {sends_max} sends")
            }
            Self::Io(e) => write!(f, "attempt: {e}"),
        }
    }
}

impl std::error::Error for AttemptError {}

impl From<io::Error> for AttemptError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

/// One frozen call.
#[derive(Debug)]
pub struct Attempt {
    dir: PathBuf,
    call: Vec<u8>,
}

impl Attempt {
    /// Freeze `call` into the new directory `dir` (its parent must exist; `dir` must not).
    pub fn freeze(dir: &Path, call: &[u8]) -> Result<Self, AttemptError> {
        fs::create_dir(dir).map_err(|e| match e.kind() {
            io::ErrorKind::AlreadyExists => AttemptError::AlreadyFrozen,
            _ => AttemptError::Io(e),
        })?;
        if let Some(parent) = dir.parent() {
            fsx::sync_dir(parent)?;
        }
        fsx::create_once(dir, CALL, call)?;
        Ok(Self {
            dir: dir.to_path_buf(),
            call: call.to_vec(),
        })
    }

    /// Reopen the attempt in `dir` and read its state from the files present.
    pub fn load(dir: &Path) -> Result<(Self, State), AttemptError> {
        let call = fs::read(dir.join(CALL)).map_err(|e| match e.kind() {
            io::ErrorKind::NotFound => AttemptError::NotAnAttempt,
            _ => AttemptError::Io(e),
        })?;
        let sends = sends(dir)?;
        let committed = read_optional(&dir.join(COMMITTED))?;
        let not_committed = read_optional(&dir.join(NOT_COMMITTED))?;
        let state = match (committed, not_committed) {
            (Some(_), Some(_)) => return Err(AttemptError::Inconsistent),
            (Some(_), None) | (None, Some(_)) if sends == 0 => {
                return Err(AttemptError::Inconsistent);
            }
            (Some(reply), None) => State::Settled {
                committed: true,
                reply,
            },
            (None, Some(reply)) => State::Settled {
                committed: false,
                reply,
            },
            (None, None) if sends == 0 => State::Signed,
            (None, None) => State::Uncertain { sends },
        };
        Ok((
            Self {
                dir: dir.to_path_buf(),
                call,
            },
            state,
        ))
    }

    /// The frozen signed bytes.
    pub fn call(&self) -> &[u8] {
        &self.call
    }

    /// Advance from `state` until settled, sending through `exchange`, which performs one
    /// request/reply on the transport and returns the table's classification of the reply.
    /// A transport error inside `exchange` must be reported as [`Settlement::Unknown`].
    /// Returns the final state: `Settled`, or `Uncertain` when the Host could not say.
    pub fn drive(
        &self,
        mut state: State,
        sends_max: u32,
        mut exchange: impl FnMut(Request, &[u8]) -> Settlement,
    ) -> Result<State, AttemptError> {
        loop {
            state = match state {
                State::Settled { .. } => return Ok(state),
                State::Signed => self.send(0, sends_max, &mut exchange)?,
                State::Uncertain { sends } => match exchange(Request::Lookup, &self.call) {
                    Settlement::Committed(reply) => self.settle(true, reply)?,
                    Settlement::NotCommitted(reply) => self.settle(false, reply)?,
                    Settlement::Unknown => return Ok(State::Uncertain { sends }),
                    Settlement::Absent => self.send(sends, sends_max, &mut exchange)?,
                },
            };
        }
    }

    fn send(
        &self,
        sends: u32,
        sends_max: u32,
        exchange: &mut impl FnMut(Request, &[u8]) -> Settlement,
    ) -> Result<State, AttemptError> {
        if sends >= sends_max {
            return Err(AttemptError::SendsExhausted { sends_max });
        }
        // The marker is durable before a byte leaves: a crash from here on loads as uncertain.
        fsx::create_once(&self.dir, &format!("{SENT_PREFIX}{sends}"), &[])?;
        let sends = sends + 1;
        match exchange(Request::Submit, &self.call) {
            Settlement::Committed(reply) => self.settle(true, reply),
            Settlement::NotCommitted(reply) => self.settle(false, reply),
            Settlement::Unknown => Ok(State::Uncertain { sends }),
            Settlement::Absent => Err(AttemptError::UnexpectedReply),
        }
    }

    fn settle(&self, committed: bool, reply: Vec<u8>) -> Result<State, AttemptError> {
        fsx::create_once(
            &self.dir,
            if committed { COMMITTED } else { NOT_COMMITTED },
            &reply,
        )?;
        Ok(State::Settled { committed, reply })
    }
}

/// The number of sends started: the markers must be exactly `sent.0 .. sent.(n-1)`.
fn sends(dir: &Path) -> Result<u32, AttemptError> {
    let mut seen = Vec::new();
    for entry in fs::read_dir(dir)? {
        let name = entry?.file_name();
        let Some(name) = name.to_str() else { continue };
        if let Some(n) = name.strip_prefix(SENT_PREFIX) {
            seen.push(n.parse::<u32>().map_err(|_| AttemptError::Inconsistent)?);
        }
    }
    seen.sort_unstable();
    let count = u32::try_from(seen.len()).map_err(|_| AttemptError::Inconsistent)?;
    if seen.iter().zip(0u32..).any(|(&n, i)| n != i) {
        return Err(AttemptError::Inconsistent);
    }
    Ok(count)
}

fn read_optional(path: &Path) -> Result<Option<Vec<u8>>, AttemptError> {
    match fs::read(path) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(AttemptError::Io(e)),
    }
}
