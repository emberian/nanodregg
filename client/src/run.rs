//! One command: execute the steps `host follow` asks for until it says done (CLIENT-2, HOST-9).
//!
//! The order of steps, what is signed and what is printed are follow's. This loop only performs a
//! step and hands its result back with the continuation, under two bounds from the table: steps
//! per command and sends per frozen call. A step is the generated codec's value
//! ([`crate::generated::layout::Step`], byte for byte `Protocol.Frames`); this module never
//! sees step bytes.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::attempt::{Attempt, AttemptError, Receipt, Reply, State};
use crate::custody::{Custody, CustodyError, Rotation};
use crate::generated::attempt::{Action, Request, Seen};
use crate::generated::layout::{CustodyRefused, PrecommitResult, Refusal, Step};

/// What a performed step hands back to follow (PROTOCOL-21): `u8 status ‖ payload`. Custody
/// answers `ok ‖ SignResult | PrecommitResult` or `refused ‖ CustodyRefused`; a Host reply is
/// passed verbatim. Follow, not this crate, renders a refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// Status byte.
    pub status: u8,
    /// Payload.
    pub payload: Vec<u8>,
}

impl Outcome {
    /// The `result` field of `resume` (`Protocol.resumeLayout`).
    pub fn result(&self) -> Vec<u8> {
        [&[self.status][..], &self.payload].concat()
    }
}

/// The follow socket, as the generated codec presents it.
pub trait Follow {
    /// Start a command with its raw argv.
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step>;
    /// Resume after a step.
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step>;
}

/// The host socket: one request, one reply `(status, payload)`.
pub trait Host {
    /// Exchange one frame.
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)>;
}

/// The table values this loop needs (all generated; none chosen here).
#[derive(Clone, Copy, Debug)]
pub struct Table {
    /// `Bounds.stepsPerCommandMax`.
    pub steps_max: u32,
    /// `Bounds.sendsMax`.
    pub sends_max: u32,
    /// `Op.submit.code`.
    pub submit: u8,
    /// `Op.lookup.code`.
    pub lookup: u8,
    /// `Status.ok.code`.
    pub ok: u8,
    /// `Status.refused.code`.
    pub refused: u8,
    /// `Status.absent.code`.
    pub absent: u8,
    /// `Status.uncertain.code`.
    pub uncertain: u8,
    /// `Status.declined.code` (PROTOCOL-41).
    pub declined: u8,
    /// `CommandExit.ok.code`: the only exit of `receipt CALL` that carries a receipt.
    pub exit_ok: u8,
    /// `CommandExit.hostContradicted.code` (PROTOCOL-46).
    pub host_contradicted: u8,
}

/// A finished command: `(exit, stdout, stderr)`.
pub type Done = (u8, Vec<u8>, Vec<u8>);

/// Why a command stopped without follow's `done`.
#[derive(Debug)]
pub enum RunError {
    /// Follow asked for more than `steps_max` steps.
    StepsExhausted,
    /// The follow socket failed.
    Follow(io::Error),
    /// The host socket failed during a `host` step (no call was at stake: a `submit` step's
    /// transport failures are the attempt's `Uncertain`, not this).
    Host(io::Error),
    /// An attempt could not be frozen, loaded or driven.
    Attempt(AttemptError),
    /// Custody could not sign or settle a rotation.
    Custody(CustodyError),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StepsExhausted => write!(f, "stepsPerCommandMax reached"),
            Self::Follow(e) => write!(f, "follow: {e}"),
            Self::Host(e) => write!(f, "host: {e}"),
            Self::Attempt(e) => write!(f, "{e}"),
            Self::Custody(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for RunError {}

impl From<AttemptError> for RunError {
    fn from(e: AttemptError) -> Self {
        Self::Attempt(e)
    }
}

/// A Host reply as a HINT for the attempt loop, by status byte alone: it steers when to look up
/// and when to resend, and never settles (PROTOCOL-46).
fn hint(t: &Table, reply: io::Result<(u8, Vec<u8>)>) -> Reply {
    let seen = match reply {
        Ok((s, _)) if s == t.ok => Seen::Committed,
        Ok((s, _)) if s == t.refused => Seen::Refused,
        Ok((s, _)) if s == t.declined => Seen::Declined,
        Ok((s, _)) if s == t.absent => Seen::Absent,
        Ok((s, _)) if s == t.uncertain => Seen::Unknown,
        // A transport failure, a timeout (replyMsMax), or a status the table does not name
        // (`closed`): no reply this run.
        _ => return Reply::Lost,
    };
    Reply::Host(seen, reply.map(|(_, p)| p).unwrap_or_default())
}

/// `confirm` / `probe`: the member's own follow runs `receipt CALL` (catching up over host.sock
/// under custody's envelope signatures) and prints the receipt, the head it checked it against and
/// the verdict. Anything but those three lines under exit ok is no answer.
fn receipt(
    call: &[u8],
    follow: &mut impl Follow,
    host: &mut impl Host,
    custody: &Custody,
    t: &Table,
) -> Result<Reply, RunError> {
    let hex: String = call.iter().map(|b| format!("{b:02x}")).collect();
    match command(
        &[b"receipt".to_vec(), hex.into_bytes()],
        follow,
        host,
        custody,
        None,
        t,
    ) {
        Ok((exit, stdout, _)) if exit == t.exit_ok => {
            Ok(Receipt::read(&stdout).map_or(Reply::Lost, Reply::Follow))
        }
        Ok(_) | Err(RunError::Follow(_) | RunError::Host(_) | RunError::StepsExhausted) => {
            Ok(Reply::Lost)
        }
        Err(e) => Err(e),
    }
}

/// Drive `attempt` from `state` until the table names an end: Host requests over host.sock,
/// `confirm` / `probe` through [`receipt`].
fn drive(
    attempt: &Attempt,
    state: State,
    follow: &mut impl Follow,
    host: &mut impl Host,
    custody: &Custody,
    t: &Table,
) -> Result<State, RunError> {
    attempt.drive(state, t.sends_max, |r, bytes| match r {
        Request::Submit => Ok(hint(t, host.exchange(t.submit, bytes))),
        Request::Lookup => Ok(hint(t, host.exchange(t.lookup, bytes))),
        Request::Confirm | Request::Probe => receipt(bytes, follow, host, custody, t),
    })
}

/// Finish an armed rotation before anything is signed: drive its attempt (CLIENT-3) and hand
/// custody a settlement only from the member's own receipt (PROTOCOL-46). A Host contradicted by
/// that receipt ends the run `hostContradicted`; anything else unsettled leaves the rotation armed
/// and the command goes on under the current key.
fn reconcile(
    custody: &Custody,
    attempts: &Path,
    follow: &mut impl Follow,
    host: &mut impl Host,
    t: &Table,
) -> Result<Option<Done>, RunError> {
    let Some((n, _)) = custody.armed().map_err(RunError::Custody)? else {
        return Ok(None);
    };
    let dir = attempts.join(n.to_string());
    let (attempt, state) = Attempt::load(&dir)?;
    match drive(&attempt, state, follow, host, custody, t)? {
        State::Settled { committed, .. } => custody.settle(committed).map_err(RunError::Custody)?,
        State::Open {
            end: Action::Contradicted,
            payload,
            ..
        } => {
            let said = String::from_utf8_lossy(&payload);
            let line = format!("hostContradicted {said} (attempt {})\n", dir.display());
            return Ok(Some((t.host_contradicted, Vec::new(), line.into_bytes())));
        }
        _ => {}
    }
    Ok(None)
}

/// Run one command to follow's `done`, an armed rotation reconciled first.
pub fn run(
    argv: &[Vec<u8>],
    follow: &mut impl Follow,
    host: &mut impl Host,
    custody: &Custody,
    attempts: &Path,
    t: Table,
) -> Result<Done, RunError> {
    match reconcile(custody, attempts, follow, host, &t)? {
        Some(ended) => Ok(ended),
        None => command(argv, follow, host, custody, Some(attempts), &t),
    }
}

/// Perform follow's steps until `done`. Without `attempts` (a `receipt` inside an attempt) follow
/// may only ask to sign and to read.
fn command(
    argv: &[Vec<u8>],
    follow: &mut impl Follow,
    host: &mut impl Host,
    custody: &Custody,
    attempts: Option<&Path>,
    t: &Table,
) -> Result<Done, RunError> {
    // Set by `signNext`; the next `submit` is that rotation's attempt (CLIENT-13).
    let mut rotation: Option<Rotation> = None;
    let mut step = follow.command(argv).map_err(RunError::Follow)?;
    for _ in 0..t.steps_max {
        if attempts.is_none() && matches!(step, Step::SignNext { .. } | Step::Precommit { .. }) {
            return Err(nested());
        }
        let (k, outcome) = match step {
            Step::Done {
                exit,
                stdout,
                stderr,
            } => return Ok((exit, stdout, stderr)),
            Step::Sign { message, k } => (
                k,
                custody_result(t, custody.sign(&message).map(|s| s.encode()))?,
            ),
            Step::SignIncoming { message, k } => (
                k,
                custody_result(t, custody.sign_incoming(&message).map(|s| s.encode()))?,
            ),
            Step::SignNext { message, k } => {
                let signed = custody.sign_next(&message).map(|(s, r)| {
                    rotation = Some(r);
                    s.encode()
                });
                (k, custody_result(t, signed)?)
            }
            Step::Precommit { k } => {
                let result = custody.precommit().map(|(next, pending)| {
                    PrecommitResult {
                        next: next.to_vec(),
                        pending: pending.to_vec(),
                    }
                    .encode()
                });
                (k, custody_result(t, result)?)
            }
            Step::Host { op, payload, k } => {
                let (status, payload) =
                    host.exchange(op.code(), &payload).map_err(RunError::Host)?;
                (k, Outcome { status, payload })
            }
            Step::Submit { call, k } => {
                let attempts = attempts.ok_or_else(nested)?;
                let (n, dir) = fresh(attempts).map_err(AttemptError::Io)?;
                let attempt = Attempt::freeze(&dir, &call)?;
                // Armed after the freeze and before the first send: a crash between the two
                // leaves an unsent attempt and nothing armed.
                let armed = rotation.take();
                if let Some(r) = &armed {
                    custody.arm(n, r).map_err(RunError::Custody)?;
                }
                // follow is told the table's end and the member's own verdict (PROTOCOL-46);
                // custody settles only on that verdict, and stays armed on any other end.
                let (end, payload) = match drive(&attempt, State::Signed, follow, host, custody, t)?
                {
                    State::Settled { committed, receipt } => {
                        if armed.is_some() {
                            custody.settle(committed).map_err(RunError::Custody)?;
                        }
                        let end = if committed {
                            Action::Committed
                        } else {
                            Action::Refused
                        };
                        (end, receipt.verdict.into_bytes())
                    }
                    State::Open { end, payload, .. } => (end, payload),
                    State::Signed | State::Uncertain { .. } => (Action::Uncertain, Vec::new()),
                };
                (
                    k,
                    Outcome {
                        status: end.code(),
                        payload,
                    },
                )
            }
        };
        step = follow.resume(&k, &outcome).map_err(RunError::Follow)?;
    }
    Err(RunError::StepsExhausted)
}

/// A `receipt` inside an attempt that asks follow's loop to rotate or submit: not an answer.
fn nested() -> RunError {
    RunError::Follow(io::Error::other(
        "receipt: follow asked to rotate or submit",
    ))
}

/// Custody's answer as follow reads it: `ok ‖ result`, or `refused ‖ CustodyRefused` naming why
/// (PROTOCOL-21). Custody's own refusals are results, never an nd exit.
fn custody_result(
    t: &Table,
    r: Result<Result<Vec<u8>, Refusal>, CustodyError>,
) -> Result<Outcome, RunError> {
    let (status, payload) = match r {
        Ok(bytes) => (t.ok, encoded(bytes)?),
        Err(e) => {
            let refused = CustodyRefused {
                refusal: e.refusal(),
            };
            (t.refused, encoded(refused.encode())?)
        }
    };
    Ok(Outcome { status, payload })
}

/// A custody result's encoding (fixed-size keys and signatures: a refusal is a custody bug).
fn encoded(r: Result<Vec<u8>, Refusal>) -> Result<Vec<u8>, RunError> {
    r.map_err(|r| RunError::Custody(CustodyError::Io(io::Error::other(format!("{r:?}")))))
}

/// A new attempt `(n, attempts/<n>)`, n one past the largest present.
fn fresh(attempts: &Path) -> io::Result<(u64, PathBuf)> {
    let mut next = 0u64;
    for entry in fs::read_dir(attempts)? {
        if let Some(n) = entry?
            .file_name()
            .to_str()
            .and_then(|s| s.parse::<u64>().ok())
        {
            next = next.max(n.saturating_add(1));
        }
    }
    Ok((next, attempts.join(next.to_string())))
}
