//! The residents frames, as their two consumers read them (HOSTING-26, HOSTING-30): keybroker and
//! nd-members each ask their Lean decider which resident grains the World holds, and each reads the
//! decider's end, with this one code (CLIENT-29: one consumer shape, never a second parser).

use std::process::{ChildStdin, ChildStdout, ExitStatus};
use std::time::{Duration, Instant};

use nanodregg_client::frame::Deadline;

use crate::broker_generated::wire::{Request, Verdict};
use crate::broker_generated::{ANSWER_MS_MAX, decider_exit, read_frame, write_frame};

/// `Broker.Bounds.answerMsMax`: one decider answer's deadline.
pub const ANSWER: Duration = Duration::from_millis(ANSWER_MS_MAX as u64);

/// A Lean decider's two pipes, as both its consumers hold them. Every question is one exchange: its
/// frames written and one verdict read under ONE deadline, `within` (`ANSWER`) from the first byte
/// (CLIENT-39, A18: a decider that is alive and silent wedged keybroker and nd-members for good). A
/// decider that misses it, or whose bytes do not decode, is LOST: a late or half-read verdict would
/// put the next answer out of step, so nothing is read from it again and every later exchange is
/// `None`. Its consumer then ends by the decider's own end or `deciderLost`, by name.
pub struct Decider {
    din: ChildStdin,
    dout: ChildStdout,
    within: Duration,
    lost: bool,
}

impl Decider {
    /// The pipes of a decider whose every answer is due `within` of its question.
    pub fn new(din: ChildStdin, dout: ChildStdout, within: Duration) -> Self {
        Self {
            din,
            dout,
            within,
            lost: false,
        }
    }

    /// Write `frames` and read the one verdict they ask for, within the deadline; `None` (and lost
    /// for good) past it or on bytes that are no verdict.
    pub fn exchange(&mut self, frames: &[&[u8]]) -> Option<Verdict> {
        if self.lost {
            return None;
        }
        let until = Instant::now() + self.within;
        let (din, dout) = (&self.din, &self.dout);
        let got = (|| {
            let mut w = Deadline::until(din, until);
            for f in frames {
                write_frame(&mut w, f).ok()?;
            }
            Verdict::decode(&read_frame(&mut Deadline::until(dout, until)).ok()?).ok()
        })();
        self.lost = got.is_none();
        got
    }

    /// Whether a past exchange lost it.
    pub fn lost(&self) -> bool {
        self.lost
    }
}

/// The socket names the decider answers to `residents` (`Controller.dirOf` of each resident grain
/// the World holds), or `None` when it cannot be reached, is lost, or answers anything else.
pub fn ask(d: &mut Decider, at_ms: u64) -> Option<Vec<Vec<u8>>> {
    let req = Request::Residents { at_ms }.encode().ok()?;
    match d.exchange(&[&req])? {
        Verdict::Residents { names } => Some(names),
        _ => None,
    }
}

/// How a decider's process ended, read by its exit status.
#[derive(Debug, PartialEq, Eq)]
pub enum DeciderEnd {
    /// a code Lean's `DeciderExit` names (`decider_exit::ALL`): the decider's own end, passed through
    Own(u8),
    /// killed by a signal (`nanodregg_sandbox::killed_by_signal`: the OOM killer, an operator),
    /// restartable
    Signaled,
    /// any other code: the mechanism's (the confinement step, a missing program), which a restart meets
    /// again (HOSTING-23; VACUITY-READER-H4: 137 must not read as the mechanism)
    Mechanism(i32),
}

/// The end `status` names.
pub fn decider_end(status: ExitStatus) -> DeciderEnd {
    match status.code() {
        _ if nanodregg_sandbox::killed_by_signal(status) => DeciderEnd::Signaled,
        None => DeciderEnd::Signaled,
        Some(c) => match u8::try_from(c) {
            Ok(b) if decider_exit::ALL.contains(&b) => DeciderEnd::Own(b),
            _ => DeciderEnd::Mechanism(c),
        },
    }
}
