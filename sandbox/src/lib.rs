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
//! - Linux: the child confines ITSELF between fork and exec (`linux`, CLIENT-48): Landlock for the
//!   file system (rules on descriptors opened at launch), seccomp for the system calls (no socket
//!   can be made, no process forked, no exec but the policy's), `no_new_privs`, its own session and
//!   a parent-death signal. No helper program, no namespace, no mount: it composes with a service
//!   manager's own sandbox (systemd's `RestrictNamespaces=yes` stays on). A `connect` entry is
//!   reached through the connector the launcher hands it ([`connect_unix`]).
//!
//! Paths are canonicalized first (macOS checks real paths: `/var` is `/private/var`). The child's
//! environment is cleared on both platforms.

mod connect;
#[cfg(target_os = "linux")]
mod connector;
pub mod custody;
#[cfg(target_os = "linux")]
mod linux;

pub use connect::CONNECT_MAX;

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
    /// itself). The program must lie under (or be) a `read` or `exec` entry, after canonicalizing:
    /// a symlinked program does not widen the policy to its target (`ProgramOutside`).
    pub exec: Vec<PathBuf>,
    /// Paths that must lie outside everything above (the member's workspace). Each must exist.
    pub hidden: Vec<PathBuf>,
    /// Unix sockets the child may connect to, at most [`CONNECT_MAX`] (HOSTING-17 §5). Each is
    /// checked before launch; Linux exposes its parent directory (which must hold that socket and
    /// nothing else: the socket's owner keeps it so), macOS allows connecting to that path alone.
    pub connect: Vec<PathBuf>,
}

impl Policy {
    /// The list a launcher flag names (`--read`, `--write`, `--exec`, `--hide`, `--connect`): the one
    /// reading of a policy's flag words, nd-supervise's argv and `nd --join`'s spawner (CLIENT-26).
    pub fn list(&mut self, flag: &std::ffi::OsStr) -> Option<&mut Vec<PathBuf>> {
        Some(match flag.to_str()? {
            "--read" => &mut self.read,
            "--write" => &mut self.write,
            "--exec" => &mut self.exec,
            "--hide" => &mut self.hidden,
            "--connect" => &mut self.connect,
            _ => return None,
        })
    }
}

/// Why a child was not launched.
#[derive(Debug)]
pub enum ConfineError {
    /// This platform has no confinement mechanism nanodregg trusts.
    Unsupported,
    /// The mechanism is absent: `sandbox-exec` not at its fixed path (macOS); a kernel without
    /// Landlock ABI 3, or a seccomp program that cannot be built for this architecture (Linux).
    MechanismMissing(&'static str),
    /// The connector of a child with `connect` entries could not be made (Linux).
    Connector(io::Error),
    /// A path cannot be named safely to the mechanism (not UTF-8, or a quote or backslash).
    UnnameablePath(PathBuf),
    /// A policy path does not exist (allowing or hiding nothing would pass silently).
    PathMissing(PathBuf, io::Error),
    /// The program is not an absolute path (a search of `PATH` would choose it).
    ProgramNotAbsolute(PathBuf),
    /// The program's canonical path is under no `read` or `exec` entry (a link pointing out).
    ProgramOutside {
        /// The program as given.
        program: PathBuf,
        /// Where it resolves.
        canonical: PathBuf,
    },
    /// More than [`CONNECT_MAX`] connect entries.
    ConnectTooMany(usize),
    /// A connect entry is a symbolic link.
    ConnectLink(PathBuf),
    /// A connect entry is not a unix socket.
    ConnectNotSocket(PathBuf),
    /// A connect socket is neither the euid's nor in the egid's group.
    ConnectOwner {
        /// The socket.
        path: PathBuf,
        /// Its owner.
        uid: u32,
        /// Its group.
        gid: u32,
    },
    /// A connect socket's mode is not exactly 0600 (the euid's) or 0660 (another uid's, our group).
    ConnectMode {
        /// The socket.
        path: PathBuf,
        /// Its mode.
        mode: u32,
    },
    /// A directory above a connect socket is not owned by root, the euid or the socket's owner, or
    /// another can write it.
    ConnectDir(PathBuf),
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
            Self::Connector(e) => write!(f, "confine: connector: {e}"),
            Self::UnnameablePath(p) => write!(f, "confine: cannot name {}", p.display()),
            Self::PathMissing(p, e) => write!(f, "confine: {}: {e}", p.display()),
            Self::ProgramOutside { program, canonical } => write!(
                f,
                "confine: program {} resolves to {}, outside every read and exec path",
                program.display(),
                canonical.display()
            ),
            Self::ProgramNotAbsolute(p) => {
                write!(f, "confine: program {} is not absolute", p.display())
            }
            Self::ConnectTooMany(n) => {
                write!(f, "confine: {n} connect entries (at most {CONNECT_MAX})")
            }
            Self::ConnectLink(p) => write!(f, "confine: connect {} is a link", p.display()),
            Self::ConnectNotSocket(p) => {
                write!(f, "confine: connect {} is not a socket", p.display())
            }
            Self::ConnectOwner { path, uid, gid } => {
                write!(f, "confine: connect {} is {uid}:{gid}", path.display())
            }
            Self::ConnectMode { path, mode } => {
                write!(f, "confine: connect {} has mode {mode:o}", path.display())
            }
            Self::ConnectDir(p) => write!(
                f,
                "confine: connect: directory {} is not trusted",
                p.display()
            ),
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

/// Whether a confined child was killed by a signal. Both mechanisms leave the child in its own
/// place (sandbox-exec execs the program; on Linux the program IS the child), so a signal death is
/// seen as one, never as an exit code (bwrap's `128 + N` is gone with bwrap, CLIENT-48). Plant:
/// client/tests/supervise.rs `a_confined_child_killed_by_a_signal_is_child_signaled`.
pub fn killed_by_signal(status: std::process::ExitStatus) -> bool {
    use std::os::unix::process::ExitStatusExt;
    status.signal().is_some()
}

/// Write `WHO: LINE` to stderr in ONE write, and never panic. Every launcher process shares its
/// stderr with children of other languages (the controller, the deciders, nd-supervise), and
/// `eprintln!` writes a line in pieces (prefix, body, newline) that another process's line can land
/// between: GATES-6 read `keybroker: hosting-broker: keybrokerGone sockDir …`, GATES-9
/// `grain-launch: hosting-drive: launcherGone` then `foreignPath …`. A pipe write of at most
/// `PIPE_BUF` bytes (4096 on Linux) is never interleaved; a line past it (a path near `PATH_MAX`) can
/// be. And `eprintln!` PANICS when stderr is gone: nd-supervise's SIGTERM thread died in its first
/// line when its parent's stderr pipe had no reader, so it never stopped its child (CLIENT-38,
/// measured): a dead stderr loses the line, never the process's end.
pub fn say(who: &str, line: &str) {
    say_line(&format!("{who}: {line}"));
}

/// [`say`] for a line that already names its writer.
pub fn say_line(line: &str) {
    use std::io::Write;
    let _ = std::io::stderr().write_all(format!("{line}\n").as_bytes());
}

/// Shared fate with the parent (CLIENT-38, A19). Every binary of ours calls this first in `main`, so
/// a parent that dies without stopping it (a test process killed by SIGKILL, a crashed nd-members)
/// takes it along: it is sent SIGTERM, the stop a service manager sends, which nd-supervise answers
/// by naming every close (CLIENT-30) and every other binary takes as its default end. Its confined
/// children follow it (on Linux their own step sets SIGKILL as their parent-death signal; on macOS
/// EOF on stdin).
///
/// A platform fact (law 2). Linux: `PR_SET_PDEATHSIG` (rustix's safe wrapper), which fires when the
/// THREAD that spawned this process exits: a spawner keeps the child on the thread that owns it. A
/// parent that died between the spawn and this call is caught by `getppid` differing across the
/// call; one that died before the first `getppid` (inside exec and runtime start) is not. macOS has
/// no parent-death signal: a thread compares `getppid` every [`ORPHAN_POLL`] and raises the same
/// SIGTERM on a change (the parent PROCESS, not its thread).
pub fn die_with_parent() -> io::Result<()> {
    use rustix::process::{Signal, getpid, getppid, kill_process};
    let parent = getppid();
    let orphaned = move || getppid() != parent;
    let stop = || kill_process(getpid(), Signal::TERM);
    #[cfg(target_os = "linux")]
    {
        rustix::process::set_parent_process_death_signal(Some(Signal::TERM))?;
        if orphaned() {
            stop()?;
        }
    }
    #[cfg(not(target_os = "linux"))]
    std::thread::Builder::new()
        .name("orphan-watch".into())
        .spawn(move || {
            while !orphaned() {
                std::thread::sleep(ORPHAN_POLL);
            }
            let _ = stop();
        })?;
    Ok(())
}

/// How often a process without a parent-death signal (macOS) compares its parent (a liveness
/// interval of the watch, not a protocol bound).
#[cfg(not(target_os = "linux"))]
pub const ORPHAN_POLL: std::time::Duration = std::time::Duration::from_millis(200);

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

pub(crate) fn canonical(path: &Path) -> Result<PathBuf, ConfineError> {
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
    /// The connect sockets: as the policy names them, and canonical.
    connect: Vec<(PathBuf, PathBuf)>,
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
        connect: Vec::new(),
    };
    if policy.connect.len() > CONNECT_MAX {
        return Err(ConfineError::ConnectTooMany(policy.connect.len()));
    }
    let mut r = r;
    for p in &policy.connect {
        r.connect.push((p.clone(), connect::entry(p)?));
    }
    if !r
        .read
        .iter()
        .chain(&r.exec)
        .any(|a| r.program.starts_with(a))
    {
        return Err(ConfineError::ProgramOutside {
            program: program.to_path_buf(),
            canonical: r.program.clone(),
        });
    }
    #[cfg(target_os = "linux")]
    let floor: Vec<PathBuf> = linux::FLOOR.iter().map(PathBuf::from).collect();
    #[cfg(not(target_os = "linux"))]
    let floor: Vec<PathBuf> = FLOOR.iter().map(|(p, _)| PathBuf::from(p)).collect();
    let floor = floor.into_iter();
    let allowed: Vec<PathBuf> = [r.program.clone()]
        .into_iter()
        .chain(r.read.iter().cloned())
        .chain(r.write.iter().cloned())
        .chain(r.exec.iter().cloned())
        .chain(r.connect.iter().map(|(_, s)| s.clone()))
        .chain(floor)
        .collect();
    // An executable FILE granted to run (the program, an `exec` file) exposes that one inode, read
    // and executed, never the tree around it: both mechanisms grant it alone (a Landlock rule on its
    // descriptor; a sandbox-exec literal). So it may lie inside a hidden tree: a Host under
    // `/home` runs with `/home` hidden (TESTGROUND-4). It may not be or contain a hidden path, and
    // a file without an execute bit (a seed is 0600) gets no such pass.
    let runnable: Vec<&PathBuf> = [&r.program]
        .into_iter()
        .chain(&r.exec)
        .filter(|p| {
            use std::os::unix::fs::PermissionsExt;
            std::fs::metadata(p).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
        })
        .collect();
    for hidden in all(&policy.hidden)? {
        // `/` in the macOS floor is its listing only (a literal), so it exposes no file under it.
        let inside_only =
            |a: &PathBuf| runnable.contains(&a) && a != &hidden && a.starts_with(&hidden);
        if let Some(a) = allowed
            .iter()
            .find(|a| a.as_os_str() != "/" && overlap(a, &hidden) && !inside_only(a))
        {
            return Err(ConfineError::Exposed {
                hidden,
                allowed: a.clone(),
            });
        }
    }
    Ok(r)
}

/// The command that runs `program args…` under `policy`, its environment cleared.
pub fn command(policy: &Policy, program: &OsStr, args: &[&OsStr]) -> Result<Command, ConfineError> {
    let r = resolve(policy, program)?;
    #[cfg(target_os = "linux")]
    let mut c = linux::command(&r)?;
    #[cfg(not(target_os = "linux"))]
    let mut c = {
        let mut c = platform(&r)?;
        if !Path::new(MECHANISM).is_file() {
            return Err(ConfineError::MechanismMissing(MECHANISM));
        }
        c.env_clear().arg("--").arg(&r.program);
        c
    };
    c.args(args);
    Ok(c)
}

/// A unix stream socket connected to `path`: through the connector when this process is a confined
/// Linux child with `connect` entries (`ND_CONNECTOR` names it; the launcher connects only to its
/// policy's entries, anything else is `EACCES`), else a plain connect (macOS, where sandbox-exec
/// filters the connect itself, and every unconfined caller). The socket is blocking.
pub fn connect_unix(path: &Path) -> io::Result<std::os::unix::net::UnixStream> {
    #[cfg(target_os = "linux")]
    if let Some(c) = connector::get()? {
        let s = std::os::unix::net::UnixStream::from(c.ask(path)?);
        s.set_nonblocking(false)?;
        return Ok(s);
    }
    std::os::unix::net::UnixStream::connect(path)
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
    for (s, _) in &r.connect {
        profile += &format!(
            "(allow network-outbound (remote unix-socket (path-literal \"{}\")))",
            s.display()
        );
    }
    let mut c = Command::new(MECHANISM);
    c.arg("-p").arg(profile);
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
