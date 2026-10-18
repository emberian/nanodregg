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
//! WHAT to send next is not decided here: it is `Protocol.Attempt.next` (PROTOCOL-17), emitted as
//! [`crate::generated::attempt::next`], a function of whether a send remains and of the last
//! request with what its reply said. This module only performs the action it names and keeps the
//! files. So a send whose reply did not arrive is never failed, only looked up; a lookup that
//! answers absent permits another send of the same bytes while sends remain; a lookup the Host
//! cannot answer ends the run uncertain (the next run looks up again). A submit answered `declined`
//! (refused by name and NOT recorded, so not final: PROTOCOL-41) ends the run with the attempt OPEN:
//! no settlement file is written, so it reloads as uncertain and the next run looks it up. Nothing
//! here re-signs or re-plans.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::fsx;
use crate::generated::attempt::{self as table, Action, Request, Seen};

const CALL: &str = "call";
const COMMITTED: &str = "committed";
const NOT_COMMITTED: &str = "not-committed";
const SENT_PREFIX: &str = "sent.";

/// What a Host reply says, as classified by the generated outcome table (never by this crate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Settlement {
    /// The call is in the log.
    Committed(Vec<u8>),
    /// The call is definitively not in the log and never will be (a FINAL named refusal: recorded,
    /// or past its window).
    NotCommitted(Vec<u8>),
    /// Submit only: refused by name and not recorded, so not final (`declined`, PROTOCOL-41). The
    /// same bytes may still be admitted later.
    Declined(Vec<u8>),
    /// The Host said it cannot say (`uncertain`: its append did not read back).
    Unknown,
    /// Lookup only: the Host has no record of these bytes.
    Absent,
    /// No reply: the transport failed, timed out (`replyMsMax`), or the reply was unreadable.
    Lost,
}

impl Settlement {
    fn seen(&self) -> Seen {
        match self {
            Self::Committed(_) => Seen::Committed,
            Self::NotCommitted(_) => Seen::Refused,
            Self::Declined(_) => Seen::Declined,
            Self::Unknown => Seen::Unknown,
            Self::Absent => Seen::Absent,
            Self::Lost => Seen::Lost,
        }
    }
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
    /// This run's submit was `declined` (PROTOCOL-41): not settled, the attempt stays open. Never
    /// read from disk: on disk it is exactly [`State::Uncertain`] (its `sent.*` markers, no
    /// settlement), so the next run looks it up.
    Declined {
        /// How many sends have been started.
        sends: u32,
        /// The Host's reply bytes (the refusal's name).
        reply: Vec<u8>,
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
    /// `Attempt.next` ended the attempt without a settlement: `absent` (every permitted send was
    /// used and the Host has no record of the call) or `badReply` (an `absent` answer to a submit).
    Ended(Action),
    /// The file system failed.
    Io(io::Error),
}

impl std::fmt::Display for AttemptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyFrozen => write!(f, "attempt: already frozen"),
            Self::NotAnAttempt => write!(f, "attempt: no call in this directory"),
            Self::Inconsistent => write!(f, "attempt: inconsistent directory"),
            Self::Ended(a) => write!(f, "attempt: {}", a.name()),
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

    /// Advance from `state`, performing what `Attempt.next` names, until it names an end. Each
    /// request goes through `exchange`, which performs one request/reply on the transport and
    /// returns the table's classification of the reply (a transport failure is
    /// [`Settlement::Lost`]). Returns `Settled`, or `Uncertain` when the Host could not say; the
    /// table's theorem `next_after_lookup` bounds a run at `2 · sends_max` requests, and the loop
    /// is bounded by that number again.
    pub fn drive(
        &self,
        state: State,
        sends_max: u32,
        mut exchange: impl FnMut(Request, &[u8]) -> Settlement,
    ) -> Result<State, AttemptError> {
        let (mut sends, mut last) = match state {
            State::Settled { .. } => return Ok(state),
            State::Signed => (0, None),
            // Reloaded after a send: its reply is lost to this run.
            State::Uncertain { sends } | State::Declined { sends, .. } => {
                (sends, Some((Request::Submit, Seen::Lost)))
            }
        };
        let mut reply = Vec::new();
        for _ in 0..=2 * u64::from(sends_max) {
            let request = match table::next(sends < sends_max, last) {
                Action::Committed => return self.settle(true, reply),
                Action::Refused => return self.settle(false, reply),
                Action::Uncertain => return Ok(State::Uncertain { sends }),
                // Not final: nothing is written, so the attempt reloads as uncertain.
                Action::Declined => return Ok(State::Declined { sends, reply }),
                end @ (Action::Absent | Action::BadReply) => return Err(AttemptError::Ended(end)),
                Action::Submit => {
                    // The marker is durable before a byte leaves: a crash from here on loads as
                    // uncertain.
                    fsx::create_once(&self.dir, &format!("{SENT_PREFIX}{sends}"), &[])?;
                    sends += 1;
                    Request::Submit
                }
                Action::Lookup => Request::Lookup,
            };
            let s = exchange(request, &self.call);
            last = Some((request, s.seen()));
            if let Settlement::Committed(r)
            | Settlement::NotCommitted(r)
            | Settlement::Declined(r) = s
            {
                reply = r;
            }
        }
        Ok(State::Uncertain { sends })
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
