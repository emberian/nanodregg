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

/// The residents frames and a decider's end, as keybroker and nd-members both read them.
pub mod residents;

use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};

use generated::wire::LaunchFailure;
use nanodregg_sandbox::{ConfineError, Policy};

/// Write `WHO: LINE` to stderr in ONE write. Every launcher process shares its stderr with
/// children of other languages (the controller, the deciders, nd-supervise), and `eprintln!` writes a
/// line in pieces (prefix, body, newline) that another process's line can land between: GATES-6 read
/// `keybroker: hosting-broker: keybrokerGone sockDir …`, GATES-9 `grain-launch: hosting-drive:
/// launcherGone` then `foreignPath …`. A pipe write of at most `PIPE_BUF` bytes (4096 on Linux, where
/// the launcher runs) is never interleaved; a line past it (a path near `PATH_MAX`) can be.
pub fn say(who: &str, line: &str) {
    use std::io::Write;
    let _ = std::io::stderr().write_all(format!("{who}: {line}\n").as_bytes());
}

/// A plan path (the joined, Lean-checked bytes) under the operator's hosting root.
pub fn under(root: &Path, rel: &[u8]) -> PathBuf {
    root.join(OsStr::from_bytes(rel))
}

/// The paths of one launch frame, as Lean planned them (relative, joined, clean).
pub struct PlanPaths<'a> {
    /// read, under the hosting root
    pub read: &'a [Vec<u8>],
    /// read and write, under the hosting root
    pub write: &'a [Vec<u8>],
    /// executable, under the hosting root
    pub exec: &'a [Vec<u8>],
    /// sockets, under the BROKER root (HOSTING-17 §6)
    pub broker: &'a [Vec<u8>],
    /// sockets, under the MEMBER root (HOSTING-20, HOSTING-25)
    pub member: &'a [Vec<u8>],
    /// hidden, under the hosting root
    pub hidden: &'a [Vec<u8>],
}

/// The operator's three roots a launch frame's paths are joined onto.
pub struct Roots<'a> {
    /// the hosting root: read, write, exec, hidden and the program
    pub root: &'a Path,
    /// the broker root (keybroker's SOCKDIR): the `broker` sockets
    pub broker: &'a Path,
    /// the member root: the `member` sockets
    pub member: &'a Path,
}

/// The `sandbox::Policy` of a launch frame: every path joined onto the hosting root, except the two
/// socket lists, each joined onto its own root (`connect` = the broker sockets, then the member
/// sockets). Nothing is added, dropped or reordered: the plan is Lean's.
pub fn policy(r: &Roots<'_>, p: &PlanPaths<'_>) -> Policy {
    let all = |base: &Path, ps: &[Vec<u8>]| ps.iter().map(|q| under(base, q)).collect::<Vec<_>>();
    let mut connect = all(r.broker, p.broker);
    connect.extend(all(r.member, p.member));
    Policy {
        read: all(r.root, p.read),
        write: all(r.root, p.write),
        exec: all(r.root, p.exec),
        hidden: all(r.root, p.hidden),
        connect,
    }
}

/// HOSTING-17 §8, HOSTING-25: the hosting, broker and member roots are pairwise disjoint trees (on
/// Linux every directory a grain may see is a connect grant to the sockets in it), compared after
/// canonicalizing.
pub fn roots_disjoint(r: &Roots<'_>) -> bool {
    pairwise_apart(&[r.root, r.broker, r.member])
}

/// No path of `ps` lies under (or is) another: the roots are pairwise disjoint trees. The one
/// comparison grain-launch's and nd-members' root checks share (HOSTING-32); callers canonicalize.
pub fn pairwise_apart(ps: &[&Path]) -> bool {
    ps.iter().enumerate().all(|(i, a)| {
        ps[i + 1..]
            .iter()
            .all(|b| !(a.starts_with(b) || b.starts_with(a)))
    })
}

/// The first path of a launch frame that is not the launched grain's own, or `None`: the program,
/// read, write and exec paths must lie under `worlds/<label>/grains/<grain>/`, and each socket of
/// either root must be `<grain>/<name>` (one name, no further component). Lean's launches never break
/// this (`Hosting.Proofs.reconcile_launch_named`); a frame that does is a defect in the controller,
/// and another grain's socket is another grain's identity, so grain-launch ends `foreignPath`
/// instead of resolving it (HOSTING-25). Hidden paths are exempt: they name what the grain must
/// not see.
pub fn foreign_path<'a>(
    label: &[u8],
    grain: &[u8],
    program: &'a [u8],
    p: &PlanPaths<'a>,
) -> Option<&'a [u8]> {
    let own = [b"worlds/".as_slice(), label, b"/grains/", grain, b"/"].concat();
    let under_own = |e: &[u8]| e.len() > own.len() && e.starts_with(&own);
    let own_socket = |e: &[u8]| {
        e.len() > grain.len() + 1
            && e.starts_with(grain)
            && e[grain.len()] == b'/'
            && !e[grain.len() + 1..].contains(&b'/')
    };
    std::iter::once(program)
        .chain(
            p.read
                .iter()
                .chain(p.write)
                .chain(p.exec)
                .map(Vec::as_slice),
        )
        .find(|e| !under_own(e))
        .or_else(|| {
            p.broker
                .iter()
                .chain(p.member)
                .map(Vec::as_slice)
                .find(|e| !own_socket(e))
        })
}

/// A grain name is a single directory-name component of lowercase ASCII letters, digits and `-`
/// (Lean's `labelOk`, which `plan` checks). The launcher names PID files by it, so it asserts the
/// premise where the bytes enter rather than trusting it.
pub fn grain_name_ok(g: &[u8]) -> bool {
    !g.is_empty()
        && g.len() <= broker_generated::GRAIN_NAME_MAX as usize
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
        ConfineError::ConnectTooMany(_) => LaunchFailure::ConnectTooMany,
        ConfineError::ConnectLink(_) => LaunchFailure::ConnectLink,
        ConfineError::ConnectNotSocket(_) => LaunchFailure::ConnectNotSocket,
        ConfineError::ConnectOwner { .. } => LaunchFailure::ConnectOwner,
        ConfineError::ConnectMode { .. } => LaunchFailure::ConnectMode,
        ConfineError::ConnectDir(_) => LaunchFailure::ConnectDir,
        ConfineError::ConnectOverlap { .. } => LaunchFailure::ConnectOverlap,
        ConfineError::SocketInGrant(_) => LaunchFailure::SocketInGrant,
        ConfineError::GrantUnlisted(_) => LaunchFailure::GrantUnlisted,
    }
}

/// A grain's argv (HOSTING-27): its launch frame's paths joined exactly as [`policy`] joins them, in
/// `Plan` order: the program, then for each of read, write, exec, broker and member its count and its
/// paths. Hidden paths are not passed (they name what the grain must not see). The sandbox clears the
/// environment and a confined grain has no /proc, so argv is how it learns where it is. The resident
/// (`Hosting.Resident.place`) accepts only its own plan joined onto three roots, so a field passed
/// out of order here is refused there by name (`argvNotPlan`).
pub fn plan_argv(r: &Roots<'_>, program: &[u8], p: &PlanPaths<'_>) -> Vec<OsString> {
    let mut v = vec![under(r.root, program).into_os_string()];
    for (base, ps) in [
        (r.root, p.read),
        (r.root, p.write),
        (r.root, p.exec),
        (r.broker, p.broker),
        (r.member, p.member),
    ] {
        v.push(ps.len().to_string().into());
        v.extend(ps.iter().map(|q| under(base, q).into_os_string()));
    }
    v
}
