//! The residents frames, as their two consumers read them (HOSTING-26, HOSTING-30): keybroker and
//! nd-members each ask their Lean decider which resident grains the World holds, and each reads the
//! decider's end, with this one code (CLIENT-29: one consumer shape, never a second parser).

use std::io::{Read, Write};
use std::process::ExitStatus;

use crate::broker_generated::wire::{Request, Verdict};
use crate::broker_generated::{decider_exit, read_frame, write_frame};

/// The socket names the decider answers to `residents` (`Controller.dirOf` of each resident grain
/// the World holds), or `None` when it cannot be reached or answers anything else.
pub fn ask(din: &mut impl Write, dout: &mut impl Read, at_ms: u64) -> Option<Vec<Vec<u8>>> {
    let req = Request::Residents { at_ms }.encode().ok()?;
    write_frame(din, &req).ok()?;
    din.flush().ok()?;
    match Verdict::decode(&read_frame(dout).ok()?).ok()? {
        Verdict::Residents { names } => Some(names),
        _ => None,
    }
}

/// How a decider's process ended, read by its exit status.
#[derive(Debug, PartialEq, Eq)]
pub enum DeciderEnd {
    /// a code Lean's `DeciderExit` names (`decider_exit::ALL`): the decider's own end, passed through
    Own(u8),
    /// killed by a signal (under bwrap, a code of 128 or more IS one: the OOM killer), restartable
    Signaled,
    /// any other code: the mechanism's (bwrap's setup, a missing program), which a restart meets
    /// again (HOSTING-23; VACUITY-READER-H4: 137 must not read as the mechanism)
    Mechanism(i32),
}

/// The end `status` names.
pub fn decider_end(status: ExitStatus) -> DeciderEnd {
    match status.code() {
        None => DeciderEnd::Signaled,
        Some(c) if c >= 128 => DeciderEnd::Signaled,
        Some(c) => match u8::try_from(c) {
            Ok(b) if decider_exit::ALL.contains(&b) => DeciderEnd::Own(b),
            _ => DeciderEnd::Mechanism(c),
        },
    }
}
