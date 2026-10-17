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

use crate::attempt::{Attempt, AttemptError, Request, Settlement, State};
use crate::custody::{Custody, CustodyError, Rotation};
use crate::generated::layout::SignResult;
use crate::generated::layout::Step;

/// What a performed step hands back to follow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Custody's answer to a `sign` step: the encoded `SignResult` (key, next, signature).
    Signed(Vec<u8>),
    /// The Host's reply: status byte and payload, verbatim.
    Reply {
        /// Status byte.
        status: u8,
        /// Payload.
        payload: Vec<u8>,
    },
}

impl Outcome {
    /// The `result` field of `resume` (`Protocol.resumeLayout`): the signature, or the Host's
    /// reply frame body as it arrived (`u8 status ‖ payload`, the shape [`crate::frame`] reads).
    pub fn result(&self) -> Vec<u8> {
        match self {
            Self::Signed(s) => s.clone(),
            Self::Reply { status, payload } => [&[*status][..], payload].concat(),
        }
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
}

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
    /// A step custody cannot answer yet (its result layout is not emitted).
    RotationStep(&'static str),
    /// The attempt is still uncertain; its directory is named so a later run resumes it.
    Uncertain(PathBuf),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StepsExhausted => write!(f, "stepsPerCommandMax reached"),
            Self::Follow(e) => write!(f, "follow: {e}"),
            Self::Host(e) => write!(f, "host: {e}"),
            Self::Attempt(e) => write!(f, "{e}"),
            Self::Custody(e) => write!(f, "{e}"),
            Self::RotationStep(s) => write!(f, "custody does not perform {s} yet"),
            Self::Uncertain(p) => write!(
                f,
                "uncertain: the call in {} may or may not have committed",
                p.display()
            ),
        }
    }
}

impl std::error::Error for RunError {}

/// The classification of a Host reply, by status byte alone.
fn settlement(t: &Table, reply: io::Result<(u8, Vec<u8>)>) -> Settlement {
    match reply {
        Ok((s, p)) if s == t.ok => Settlement::Committed(p),
        Ok((s, p)) if s == t.refused => Settlement::NotCommitted(p),
        Ok((s, _)) if s == t.absent => Settlement::Absent,
        // `uncertain`, an unknown status, or a transport failure: the Host could not say.
        _ => Settlement::Unknown,
    }
}

/// Drive `attempt` from `state` over host.sock until it settles or the Host cannot say.
fn drive(
    attempt: &Attempt,
    state: State,
    host: &mut impl Host,
    t: &Table,
) -> Result<State, RunError> {
    attempt
        .drive(state, t.sends_max, |r, bytes| {
            let op = match r {
                Request::Submit => t.submit,
                Request::Lookup => t.lookup,
            };
            settlement(t, host.exchange(op, bytes))
        })
        .map_err(RunError::Attempt)
}

/// Finish an armed rotation before anything is signed: settle its attempt (a lookup if it was
/// sent; CLIENT-3) and hand the settlement to custody, which alone advances its keys. Still
/// uncertain: the rotation stays armed and the command goes on under the current key.
fn reconcile(
    custody: &Custody,
    attempts: &Path,
    host: &mut impl Host,
    t: &Table,
) -> Result<(), RunError> {
    let Some((n, _)) = custody.armed().map_err(RunError::Custody)? else {
        return Ok(());
    };
    let (attempt, state) =
        Attempt::load(&attempts.join(n.to_string())).map_err(RunError::Attempt)?;
    if let State::Settled { committed, .. } = drive(&attempt, state, host, t)? {
        custody.settle(committed).map_err(RunError::Custody)?;
    }
    Ok(())
}

/// Run one command to follow's `done`.
pub fn run(
    argv: &[Vec<u8>],
    follow: &mut impl Follow,
    host: &mut impl Host,
    custody: &Custody,
    attempts: &Path,
    t: Table,
) -> Result<(u8, Vec<u8>, Vec<u8>), RunError> {
    reconcile(custody, attempts, host, &t)?;
    // Set by `signNext`; the next `submit` is that rotation's attempt (CLIENT-13).
    let mut rotation: Option<Rotation> = None;
    let mut step = follow.command(argv).map_err(RunError::Follow)?;
    for _ in 0..t.steps_max {
        let (k, outcome) = match step {
            Step::Done {
                exit,
                stdout,
                stderr,
            } => return Ok((exit, stdout, stderr)),
            Step::Sign { message, k } => {
                let signed = custody.sign(&message).map_err(RunError::Custody)?;
                (k, Outcome::Signed(encoded(&signed)?))
            }
            Step::Signnext { message, k } => {
                let (signed, r) = custody.sign_next(&message).map_err(RunError::Custody)?;
                rotation = Some(r);
                (k, Outcome::Signed(encoded(&signed)?))
            }
            // Its result layout (precommitResultLayout) is not emitted yet; no hand-written codec.
            Step::Precommit { .. } => return Err(RunError::RotationStep("precommit")),
            Step::Host { op, payload, k } => {
                let (status, payload) =
                    host.exchange(op.code(), &payload).map_err(RunError::Host)?;
                (k, Outcome::Reply { status, payload })
            }
            Step::Submit { call, k } => {
                let (n, dir) =
                    fresh(attempts).map_err(|e| RunError::Attempt(AttemptError::Io(e)))?;
                let attempt = Attempt::freeze(&dir, &call).map_err(RunError::Attempt)?;
                // Armed after the freeze and before the first send: a crash between the two
                // leaves an unsent attempt and nothing armed.
                let armed = rotation.take();
                if let Some(r) = &armed {
                    custody.arm(n, r).map_err(RunError::Custody)?;
                }
                match drive(&attempt, State::Signed, host, &t)? {
                    State::Settled { committed, reply } => {
                        if armed.is_some() {
                            custody.settle(committed).map_err(RunError::Custody)?;
                        }
                        let status = if committed { t.ok } else { t.refused };
                        (
                            k,
                            Outcome::Reply {
                                status,
                                payload: reply,
                            },
                        )
                    }
                    State::Signed | State::Uncertain { .. } => {
                        return Err(RunError::Uncertain(dir));
                    }
                }
            }
        };
        step = follow.resume(&k, &outcome).map_err(RunError::Follow)?;
    }
    Err(RunError::StepsExhausted)
}

/// The encoded `SignResult` (three bounded fields; a refusal would be a custody bug).
fn encoded(s: &SignResult) -> Result<Vec<u8>, RunError> {
    s.encode().map_err(|r| {
        RunError::Custody(CustodyError::Io(io::Error::other(format!(
            "signResult: {r:?}"
        ))))
    })
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
