//! One confinement shape for every child nanodregg launches: the Lean Host, `host follow`, a hosted
//! resident. The policy (what is hidden) is an input; this crate only turns it into the platform's
//! mechanism and refuses to launch where it has none. There is no unconfined fallback.
//!
//! - Linux: `bwrap` with every namespace unshared, the root bound read-only, and each hidden path
//!   covered by an empty tmpfs.
//! - macOS: `sandbox-exec` with a profile denying reads and writes under each hidden path.
//!
//! Hidden paths are canonicalized first (macOS checks real paths: `/var` is `/private/var`).

use std::ffi::OsStr;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

/// What a confined child must not see.
#[derive(Clone, Debug, Default)]
pub struct Policy {
    /// Directories (or files) the child can neither read nor write.
    pub hidden: Vec<PathBuf>,
}

/// Why a child was not launched.
#[derive(Debug)]
pub enum ConfineError {
    /// This platform has no confinement mechanism nanodregg trusts.
    Unsupported,
    /// The confinement program (`bwrap`, `sandbox-exec`) is not at its fixed path.
    MechanismMissing(&'static str),
    /// A hidden path cannot be named safely to the mechanism (not UTF-8, or a quote or backslash).
    UnnameablePath(PathBuf),
    /// A hidden path does not exist (hiding nothing would pass silently).
    HiddenPathMissing(PathBuf, io::Error),
}

impl std::fmt::Display for ConfineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported => write!(f, "confine: no confinement on this platform"),
            Self::MechanismMissing(p) => write!(f, "confine: {p} is missing"),
            Self::UnnameablePath(p) => write!(f, "confine: cannot name {}", p.display()),
            Self::HiddenPathMissing(p, e) => write!(f, "confine: hidden path {}: {e}", p.display()),
        }
    }
}

impl std::error::Error for ConfineError {}

#[cfg(target_os = "linux")]
const MECHANISM: &str = "/usr/bin/bwrap";
#[cfg(target_os = "macos")]
const MECHANISM: &str = "/usr/bin/sandbox-exec";

fn canonical(path: &Path) -> Result<String, ConfineError> {
    let real = path.canonicalize().map_err(|e| ConfineError::HiddenPathMissing(path.to_path_buf(), e))?;
    let text = real.to_str().ok_or_else(|| ConfineError::UnnameablePath(real.clone()))?;
    if text.contains(['"', '\\']) {
        return Err(ConfineError::UnnameablePath(real));
    }
    Ok(text.to_owned())
}

/// The command that runs `program args…` under `policy`.
pub fn command(policy: &Policy, program: &OsStr, args: &[&OsStr]) -> Result<Command, ConfineError> {
    let hidden = policy.hidden.iter().map(|p| canonical(p)).collect::<Result<Vec<_>, _>>()?;
    platform(&hidden, program, args)
}

#[cfg(target_os = "macos")]
fn platform(hidden: &[String], program: &OsStr, args: &[&OsStr]) -> Result<Command, ConfineError> {
    if !Path::new(MECHANISM).is_file() {
        return Err(ConfineError::MechanismMissing(MECHANISM));
    }
    let mut profile = String::from("(version 1)(allow default)");
    for p in hidden {
        profile.push_str(&format!("(deny file-read* file-write* (subpath \"{p}\"))"));
    }
    let mut c = Command::new(MECHANISM);
    c.arg("-p").arg(profile).arg("--").arg(program).args(args);
    Ok(c)
}

#[cfg(target_os = "linux")]
fn platform(hidden: &[String], program: &OsStr, args: &[&OsStr]) -> Result<Command, ConfineError> {
    if !Path::new(MECHANISM).is_file() {
        return Err(ConfineError::MechanismMissing(MECHANISM));
    }
    let mut c = Command::new(MECHANISM);
    c.args([
        "--die-with-parent", "--new-session", "--unshare-all", "--disable-userns", "--cap-drop", "ALL",
        "--clearenv", "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
    ]);
    for p in hidden {
        c.args(["--tmpfs", p]);
    }
    c.arg("--").arg(program).args(args);
    Ok(c)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn platform(_: &[String], _: &OsStr, _: &[&OsStr]) -> Result<Command, ConfineError> {
    Err(ConfineError::Unsupported)
}
