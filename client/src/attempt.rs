//! The life of one signed call, frozen on disk so a crash cannot change what was sent.
//!
//! An attempt is a directory. `call` holds the exact signed bytes and is written once. Before
//! each send a marker `sent.<n>` is written. The settlement is one file, `settled`, holding the
//! three lines the member's OWN follow printed for `receipt CALL` (PROTOCOL-46): the receipt, the
//! head it was checked against, and the `settle` verdict. Never the Host's reply: the Host's status
//! byte only steers the loop (when to look up, when to resend the same bytes). The state is which
//! files exist; any other file refuses to load:
//!
//! | files                         | state                 |
//! |-------------------------------|-----------------------|
//! | `call`                        | [`State::Signed`]     |
//! | `call`, `sent.*`              | [`State::Uncertain`]  |
//! | `call`, `sent.*`, `settled`   | [`State::Settled`]    |
//!
//! WHAT to do next is `Protocol.Attempt.next`, emitted as [`crate::generated::attempt::next`];
//! this module performs the action it names and keeps the files. A Host's claimed final (`ok`,
//! `refused`) is `confirm`ed, and a lookup's `absent` with no send left is `probe`d, both by the
//! member's follow; only its `committed` or `refused` writes `settled`. Every other end (declined,
//! open, contradicted, uncertain, badReply) leaves the attempt open on disk, so the next run looks
//! it up again. Which verdict a `settle` line names is the generated `settle_seen`, not this crate.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::fsx;
use crate::generated::attempt::{self as table, Action, Request, Seen};

const CALL: &str = "call";
const SETTLED: &str = "settled";
const SENT_PREFIX: &str = "sent.";

/// Follow's answer to `receipt CALL`: exactly the three lines `receipt HEX`, `head STEPS HEIGHT
/// ROOTS`, `settle VERDICT`, the verdict named by the generated `settle_seen` (its first word).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receipt {
    /// `settle_seen` of the verdict.
    pub seen: Seen,
    /// The settle line after `settle ` (`committed H TD`, `refused CODE`, `expired`, `open`,
    /// `forgotten`): what follow is handed at the submit step, unread here.
    pub verdict: String,
    /// The three lines, verbatim: what `settled` holds.
    pub lines: Vec<u8>,
}

impl Receipt {
    /// Read follow's stdout; `None` unless it is exactly the three lines and the table names the
    /// verdict.
    pub fn read(stdout: &[u8]) -> Option<Self> {
        let text = std::str::from_utf8(stdout).ok()?;
        let lines: Vec<&str> = text.strip_suffix('\n')?.split('\n').collect();
        let [receipt, head, settle] = lines[..] else {
            return None;
        };
        receipt.strip_prefix("receipt ")?;
        head.strip_prefix("head ")?;
        let verdict = settle.strip_prefix("settle ")?;
        Some(Self {
            seen: table::settle_seen(verdict.split(' ').next()?)?,
            verdict: verdict.to_string(),
            lines: stdout.to_vec(),
        })
    }
}

/// What one request came back with: the table's `Seen`, and for a Host request its reply payload,
/// for a `confirm` / `probe` follow's [`Receipt`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    /// A Host reply classified by its status (a hint, never a settlement), with its payload.
    Host(Seen, Vec<u8>),
    /// The member's own follow answered `receipt CALL`.
    Follow(Receipt),
    /// No answer: the transport failed, timed out (`replyMsMax`), or the answer was unreadable.
    Lost,
}

impl Reply {
    fn seen(&self) -> Seen {
        match self {
            Self::Host(s, _) => *s,
            Self::Follow(r) => r.seen,
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
    /// This run ended without a final: `declined`, `open`, `contradicted`, `uncertain` or
    /// `badReply`. Never read from disk: on disk it is exactly [`State::Uncertain`].
    Open {
        /// How many sends have been started.
        sends: u32,
        /// The table's end.
        end: Action,
        /// What follow is told: a declined refusal's name, or `HOSTSAID FOLLOWSAID` for a
        /// contradiction; empty otherwise.
        payload: Vec<u8>,
    },
    /// Settled by the member's own follow.
    Settled {
        /// Whether it committed.
        committed: bool,
        /// Follow's receipt, head and verdict.
        receipt: Receipt,
    },
}

/// Why an attempt could not proceed.
#[derive(Debug)]
pub enum AttemptError {
    /// `freeze` was asked for a directory that already holds an attempt.
    AlreadyFrozen,
    /// The directory holds no `call`.
    NotAnAttempt,
    /// The directory holds a file of no attempt, a settlement without a send, a gap in its
    /// markers, or a settlement that is not a final verdict.
    Inconsistent,
    /// The file system failed.
    Io(io::Error),
}

impl std::fmt::Display for AttemptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyFrozen => write!(f, "attempt: already frozen"),
            Self::NotAnAttempt => write!(f, "attempt: no call in this directory"),
            Self::Inconsistent => write!(f, "attempt: inconsistent directory"),
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

/// A verdict that ends an attempt: `committed` or `refused` (with `expired`), by the table.
fn final_of(r: &Receipt) -> Option<bool> {
    match r.seen {
        Seen::Committed => Some(true),
        Seen::Refused => Some(false),
        _ => None,
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

    /// Reopen the attempt in `dir` and read its state from the files present; a settlement is
    /// re-read through [`Receipt::read`] and must be a final verdict.
    pub fn load(dir: &Path) -> Result<(Self, State), AttemptError> {
        let call = fs::read(dir.join(CALL)).map_err(|e| match e.kind() {
            io::ErrorKind::NotFound => AttemptError::NotAnAttempt,
            _ => AttemptError::Io(e),
        })?;
        let (sends, settled) = scan(dir)?;
        let state = match (sends, settled) {
            (0, true) => return Err(AttemptError::Inconsistent),
            (0, false) => State::Signed,
            (sends, false) => State::Uncertain { sends },
            (_, true) => {
                let receipt = Receipt::read(&fs::read(dir.join(SETTLED))?)
                    .ok_or(AttemptError::Inconsistent)?;
                let committed = final_of(&receipt).ok_or(AttemptError::Inconsistent)?;
                State::Settled { committed, receipt }
            }
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
    /// request goes through `exchange`: `submit` / `lookup` to the Host, `confirm` / `probe` as
    /// follow's `receipt CALL`. A run makes at most `2 · sends_max` Host requests and one follow
    /// request (the table's bound), and the loop is bounded by that number again.
    pub fn drive<E: From<AttemptError>>(
        &self,
        state: State,
        sends_max: u32,
        mut exchange: impl FnMut(Request, &[u8]) -> Result<Reply, E>,
    ) -> Result<State, E> {
        let (mut sends, mut last) = match state {
            State::Settled { .. } => return Ok(state),
            State::Signed => (0, None),
            // Reloaded after a send: its reply is lost to this run.
            State::Uncertain { sends } | State::Open { sends, .. } => {
                (sends, Some((Request::Submit, Seen::Lost)))
            }
        };
        // The Host's last payload (a declined refusal's name), the Host's last claim, follow's
        // last receipt.
        let (mut hinted, mut claimed, mut receipt) = (Vec::new(), None, None::<Receipt>);
        for _ in 0..=2 * u64::from(sends_max) + 1 {
            let request = match table::next(sends < sends_max, last) {
                end @ (Action::Committed | Action::Refused) => {
                    let r = receipt.take().ok_or(AttemptError::Inconsistent)?;
                    return Ok(self.settle(end == Action::Committed, r)?);
                }
                Action::Submit => {
                    // The marker is durable before a byte leaves: a crash from here on loads as
                    // uncertain.
                    fsx::create_once(&self.dir, &format!("{SENT_PREFIX}{sends}"), &[])
                        .map_err(AttemptError::Io)?;
                    sends += 1;
                    Request::Submit
                }
                Action::Lookup => Request::Lookup,
                Action::Confirm => Request::Confirm,
                Action::Probe => Request::Probe,
                end => {
                    let payload = match (end, &receipt) {
                        (Action::Declined, _) => hinted,
                        (Action::Contradicted, Some(r)) => {
                            let host = claimed.map_or("", Seen::name);
                            format!("{host} {}", r.seen.name()).into_bytes()
                        }
                        _ => Vec::new(),
                    };
                    return Ok(State::Open {
                        sends,
                        end,
                        payload,
                    });
                }
            };
            let reply = exchange(request, &self.call)?;
            last = Some((request, reply.seen()));
            match reply {
                Reply::Host(seen, payload) => {
                    if matches!(seen, Seen::Committed | Seen::Refused) {
                        claimed = Some(seen);
                    }
                    hinted = payload;
                }
                Reply::Follow(r) => receipt = Some(r),
                Reply::Lost => {}
            }
        }
        Ok(State::Open {
            sends,
            end: Action::Uncertain,
            payload: Vec::new(),
        })
    }

    /// Write `settled` from follow's receipt (the table names committed or refused only after a
    /// `confirm` / `probe` whose verdict was that).
    fn settle(&self, committed: bool, receipt: Receipt) -> Result<State, AttemptError> {
        fsx::create_once(&self.dir, SETTLED, &receipt.lines)?;
        Ok(State::Settled { committed, receipt })
    }
}

/// `(sends, settled)`: the markers must be exactly `sent.0 .. sent.(n-1)`, and no file but
/// `call`, the markers and `settled` may be present (an older layout refuses to load).
fn scan(dir: &Path) -> Result<(u32, bool), AttemptError> {
    let (mut seen, mut settled) = (Vec::new(), false);
    for entry in fs::read_dir(dir)? {
        let name = entry?.file_name();
        let name = name.to_str().ok_or(AttemptError::Inconsistent)?;
        if let Some(n) = name.strip_prefix(SENT_PREFIX) {
            seen.push(n.parse::<u32>().map_err(|_| AttemptError::Inconsistent)?);
        } else if name == SETTLED {
            settled = true;
        } else if name != CALL {
            return Err(AttemptError::Inconsistent);
        }
    }
    seen.sort_unstable();
    let count = u32::try_from(seen.len()).map_err(|_| AttemptError::Inconsistent)?;
    if seen.iter().zip(0u32..).any(|(&n, i)| n != i) {
        return Err(AttemptError::Inconsistent);
    }
    Ok((count, settled))
}
