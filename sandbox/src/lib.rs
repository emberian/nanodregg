//! One confinement shape for every child nanodregg launches: the Lean Host, `host follow`, a hosted
//! resident. The child sees NOTHING but what its policy allows (CLIENT-9): its program, the paths
//! it may read, write or execute, and the platform's runtime floor (the loader and the system
//! libraries). Everything else, the member's workspace and seed first, is absent. The policy is an
//! input; this crate turns it into the platform's mechanism and refuses to launch where it has
//! none. There is no unconfined fallback.
//!
//! The policy also names what must stay hidden (CLIENT-8). With deny-by-default nothing needs a
//! deny rule; `hidden` is the invariant checked before launch: a policy whose allowed paths cover a
//! hidden path, or lie inside one, is refused by name (`Exposed`), never launched.
//!
//! - macOS: `sandbox-exec` with `(deny default)` and allow rules for exactly the policy's paths.
//!   No network, no IPC, no fork, no exec but the policy's, no sysctl but `hw.ncpu`.
//! - Linux: `bwrap` with every namespace unshared and nothing mounted but the policy's paths, the
//!   floor, `/dev` and `/proc`. NEVER RUN: only `cargo check --target x86_64-unknown-linux-gnu`.
//!
//! Paths are canonicalized first (macOS checks real paths: `/var` is `/private/var`). The child's
//! environment is cleared on both platforms.

use std::ffi::OsStr;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

/// What a confined child may touch, and what it must never see.
#[derive(Clone, Debug, Default)]
pub struct Policy {
    /// Directories or files the child may read (and list).
    pub read: Vec<PathBuf>,
    /// Directories or files the child may read and write (the Store).
    pub write: Vec<PathBuf>,
    /// Directories or files the child may execute besides its program (a runtime that re-execs
    /// itself). The program itself is always readable and executable.
    pub exec: Vec<PathBuf>,
    /// Paths that must lie outside everything above (the member's workspace). Each must exist.
    pub hidden: Vec<PathBuf>,
}

/// Why a child was not launched.
#[derive(Debug)]
pub enum ConfineError {
    /// This platform has no confinement mechanism nanodregg trusts.
    Unsupported,
    /// The confinement program (`bwrap`, `sandbox-exec`) is not at its fixed path.
    MechanismMissing(&'static str),
    /// A path cannot be named safely to the mechanism (not UTF-8, or a quote or backslash).
    UnnameablePath(PathBuf),
    /// A policy path does not exist (allowing or hiding nothing would pass silently).
    PathMissing(PathBuf, io::Error),
    /// The program is not an absolute path (a search of `PATH` would choose it).
    ProgramNotAbsolute(PathBuf),
    /// An allowed path (or the floor) covers a hidden path or lies inside one (CLIENT-8).
    Exposed {
        /// The hidden path.
        hidden: PathBuf,
        /// The allowed path that reaches it.
        allowed: PathBuf,
    },
}

impl std::fmt::Display for ConfineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported => write!(f, "confine: no confinement on this platform"),
            Self::MechanismMissing(p) => write!(f, "confine: {p} is missing"),
            Self::UnnameablePath(p) => write!(f, "confine: cannot name {}", p.display()),
            Self::PathMissing(p, e) => write!(f, "confine: {}: {e}", p.display()),
            Self::ProgramNotAbsolute(p) => {
                write!(f, "confine: program {} is not absolute", p.display())
            }
            Self::Exposed { hidden, allowed } => write!(
                f,
                "confine: exposed: {} reaches hidden {}",
                allowed.display(),
                hidden.display()
            ),
        }
    }
}

impl std::error::Error for ConfineError {}

#[cfg(target_os = "linux")]
const MECHANISM: &str = "/usr/bin/bwrap";
#[cfg(target_os = "macos")]
const MECHANISM: &str = "/usr/bin/sandbox-exec";

/// What every child may read on macOS: the root directory's listing (dyld aborts without it), the
/// system libraries and the dyld shared cache, and the kernel's randomness (the Lean runtime opens
/// `/dev/urandom` at start). Measured 2026-10-16 on macOS 27.0.1 by bisecting a `(deny default)`
/// profile until `/bin/cat` and a lake-built Lean exe ran.
#[cfg(target_os = "macos")]
const FLOOR: [(&str, bool); 4] = [
    ("/", false),
    ("/dev/urandom", false),
    ("/usr/lib", true),
    ("/System/Volumes/Preboot/Cryptexes", true),
];

/// The same floor on Linux, as read-only binds (`true`: bound only if present).
#[cfg(target_os = "linux")]
const FLOOR: [(&str, bool); 4] = [
    ("/usr", false),
    ("/lib", true),
    ("/lib64", true),
    ("/etc/ld.so.cache", true),
];

fn canonical(path: &Path) -> Result<PathBuf, ConfineError> {
    let real = path
        .canonicalize()
        .map_err(|e| ConfineError::PathMissing(path.to_path_buf(), e))?;
    match real.to_str() {
        Some(t) if !t.contains(['"', '\\']) => Ok(real),
        _ => Err(ConfineError::UnnameablePath(real)),
    }
}

fn all(paths: &[PathBuf]) -> Result<Vec<PathBuf>, ConfineError> {
    paths.iter().map(|p| canonical(p)).collect()
}

/// `a` and `b` share a branch: one is the other or an ancestor of it (component-wise).
fn overlap(a: &Path, b: &Path) -> bool {
    a.starts_with(b) || b.starts_with(a)
}

/// The policy with every path canonical, checked against its hidden set.
struct Resolved {
    program: PathBuf,
    read: Vec<PathBuf>,
    write: Vec<PathBuf>,
    exec: Vec<PathBuf>,
}

fn resolve(policy: &Policy, program: &OsStr) -> Result<Resolved, ConfineError> {
    let program = Path::new(program);
    if !program.is_absolute() {
        return Err(ConfineError::ProgramNotAbsolute(program.to_path_buf()));
    }
    let r = Resolved {
        program: canonical(program)?,
        read: all(&policy.read)?,
        write: all(&policy.write)?,
        exec: all(&policy.exec)?,
    };
    let floor = FLOOR.iter().map(|(p, _)| PathBuf::from(p));
    let allowed: Vec<PathBuf> = [r.program.clone()]
        .into_iter()
        .chain(r.read.iter().cloned())
        .chain(r.write.iter().cloned())
        .chain(r.exec.iter().cloned())
        .chain(floor)
        .collect();
    for hidden in all(&policy.hidden)? {
        // `/` in the macOS floor is its listing only (a literal), so it exposes no file under it.
        if let Some(a) = allowed
            .iter()
            .find(|a| a.as_os_str() != "/" && overlap(a, &hidden))
        {
            return Err(ConfineError::Exposed {
                hidden,
                allowed: a.clone(),
            });
        }
    }
    Ok(r)
}

/// The command that runs `program args…` under `policy`.
pub fn command(policy: &Policy, program: &OsStr, args: &[&OsStr]) -> Result<Command, ConfineError> {
    let r = resolve(policy, program)?;
    let mut c = platform(&r)?;
    if !Path::new(MECHANISM).is_file() {
        return Err(ConfineError::MechanismMissing(MECHANISM));
    }
    c.env_clear().arg("--").arg(&r.program).args(args);
    Ok(c)
}

#[cfg(target_os = "macos")]
fn platform(r: &Resolved) -> Result<Command, ConfineError> {
    // Every path is canonical and contains no quote or backslash (`canonical`).
    let lit = |p: &Path| format!(" (literal \"{}\")", p.display());
    let sub = |p: &Path| format!(" (subpath \"{}\")", p.display());
    let mut read = lit(&r.program);
    let mut meta = String::new();
    for (p, subtree) in FLOOR {
        read += &if subtree {
            sub(Path::new(p))
        } else {
            lit(Path::new(p))
        };
    }
    for p in r.read.iter().chain(&r.exec).chain(&r.write) {
        read += &sub(p);
    }
    // Resolving an allowed path (realpath, dyld) stats each of its ancestors.
    let all = [&r.program]
        .into_iter()
        .chain(&r.read)
        .chain(&r.exec)
        .chain(&r.write);
    for p in all {
        for a in p.ancestors().skip(1) {
            meta += &lit(a);
        }
    }
    // The Lean runtime sizes its task manager from `hw.ncpu`; denied, `IO.asTask .dedicated`
    // runs inline and a resident that reads stdin on a task never answers before EOF (measured
    // 2026-10-16 with `host follow`: no reply until stdin closed; allowing exactly this name fixes
    // it, and no other sysctl is needed).
    let mut profile =
        String::from("(version 1)(deny default)(allow sysctl-read (sysctl-name \"hw.ncpu\"))");
    profile += &format!("(allow process-exec{}", lit(&r.program));
    for p in &r.exec {
        profile += &sub(p);
    }
    profile += ")";
    profile += &format!("(allow file-read*{read})(allow file-read-metadata{meta})");
    if !r.write.is_empty() {
        let write: String = r.write.iter().map(|p| sub(p)).collect();
        profile += &format!("(allow file-write*{write})");
    }
    let mut c = Command::new(MECHANISM);
    c.arg("-p").arg(profile);
    Ok(c)
}

#[cfg(target_os = "linux")]
fn platform(r: &Resolved) -> Result<Command, ConfineError> {
    let mut c = Command::new(MECHANISM);
    c.args([
        "--die-with-parent",
        "--new-session",
        "--unshare-all",
        "--disable-userns",
        "--cap-drop",
        "ALL",
        "--clearenv",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
    ]);
    for (p, optional) in FLOOR {
        c.args([
            if optional {
                "--ro-bind-try"
            } else {
                "--ro-bind"
            },
            p,
            p,
        ]);
    }
    for p in [&r.program].into_iter().chain(&r.read).chain(&r.exec) {
        c.arg("--ro-bind").arg(p).arg(p);
    }
    for p in &r.write {
        c.arg("--bind").arg(p).arg(p);
    }
    Ok(c)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
const FLOOR: [(&str, bool); 0] = [];

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
const MECHANISM: &str = "/nonexistent";

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn platform(_: &Resolved) -> Result<Command, ConfineError> {
    Err(ConfineError::Unsupported)
}
