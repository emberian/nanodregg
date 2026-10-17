//! `grain-launch`'s plumbing. The controller (Lean, `Hosting.Cli`) decides which grain runs under
//! which plan; this crate turns each frame into exactly one `nanodregg_sandbox::command` call, keeps
//! one child per grain, and reports what the OS did. The frames and their bounds are
//! `generated.rs`, printed from `Hosting/Wire.lean` (`lake exe emit-hosting`).
//!
//! Laws the controller's memory relies on (`Hosting/Loop.lean`): one child per grain (a second
//! launch for a grain whose child is up ends the launcher, `duplicateLaunch`); reports in the
//! order things happened, on one pipe; when the controller's pipe closes, every child is killed
//! and reaped before the launcher exits.

#[allow(missing_docs)]
pub mod generated;

/// The provider-key broker's frames (`Hosting/BrokerWire.lean`, `lake exe emit-broker`).
#[allow(missing_docs)]
pub mod broker_generated;

use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};

use generated::wire::LaunchFailure;
use nanodregg_sandbox::{ConfineError, Policy};

/// A plan path (the joined, Lean-checked bytes) under the operator's hosting root.
pub fn under(root: &Path, rel: &[u8]) -> PathBuf {
    root.join(OsStr::from_bytes(rel))
}

/// The `sandbox::Policy` of a launch frame, every path joined onto `root`. Nothing is added,
/// dropped or reordered: the plan is Lean's.
pub fn policy(
    root: &Path,
    read: &[Vec<u8>],
    write: &[Vec<u8>],
    exec: &[Vec<u8>],
    hidden: &[Vec<u8>],
) -> Policy {
    let all = |ps: &[Vec<u8>]| ps.iter().map(|p| under(root, p)).collect();
    Policy {
        read: all(read),
        write: all(write),
        exec: all(exec),
        hidden: all(hidden),
    }
}

/// A grain name is a single directory-name component of lowercase ASCII letters, digits and `-`
/// (Lean's `labelOk`, which `plan` checks). The launcher names PID files by it, so it asserts the
/// premise where the bytes enter rather than trusting it.
pub fn grain_name_ok(g: &[u8]) -> bool {
    !g.is_empty()
        && g.len() <= 64
        && g.iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
}

/// Why the sandbox refused, as the wire names it (`Hosting.LaunchFailure`). Exhaustive: a new
/// `ConfineError` case does not compile here until Lean names it.
pub fn failure_of(e: &ConfineError) -> LaunchFailure {
    match e {
        ConfineError::Unsupported => LaunchFailure::Unsupported,
        ConfineError::MechanismMissing(_) => LaunchFailure::MechanismMissing,
        ConfineError::UnnameablePath(_) => LaunchFailure::UnnameablePath,
        ConfineError::PathMissing(..) => LaunchFailure::PathMissing,
        ConfineError::ProgramNotAbsolute(_) => LaunchFailure::ProgramNotAbsolute,
        ConfineError::ProgramOutside { .. } => LaunchFailure::ProgramOutside,
        ConfineError::Exposed { .. } => LaunchFailure::Exposed,
    }
}
