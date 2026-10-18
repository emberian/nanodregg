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
//! - Linux: `bwrap` with every namespace unshared (the user namespace for certain, nested ones
//!   disabled) and nothing mounted but the policy's paths, the floor and `/dev`. First run on hbox
//!   (Ubuntu 24.10) 2026-10-17.
//!
//! Paths are canonicalized first (macOS checks real paths: `/var` is `/private/var`). The child's
//! environment is cleared on both platforms.

mod connect;
pub mod custody;

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
    /// The confinement program (`bwrap`, `sandbox-exec`) is not at its fixed path.
    MechanismMissing(&'static str),
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
    /// A connect directory lies under or contains a read, write or exec entry: on Linux the entry
    /// would grant connect to every socket the directory ever holds (`CONNECT_FILTERED`).
    ConnectOverlap {
        /// The connect socket's directory.
        connect: PathBuf,
        /// The file grant it overlaps.
        allowed: PathBuf,
    },
    /// A read, write or exec entry holds a unix socket at launch (this one): the grant would be a
    /// connect grant on Linux.
    SocketInGrant(PathBuf),
    /// A directory under a read, write or exec entry cannot be listed, so a socket in it is unseen.
    GrantUnlisted(PathBuf),
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
            Self::ConnectOverlap { connect, allowed } => write!(
                f,
                "confine: connect directory {} overlaps grant {}",
                connect.display(),
                allowed.display()
            ),
            Self::GrantUnlisted(p) => write!(f, "confine: cannot list grant {}", p.display()),
            Self::SocketInGrant(p) => write!(f, "confine: a grant holds socket {}", p.display()),
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

/// A platform fact (charter law 2, CLIENT-9): whether the mechanism filters EXEC. macOS
/// `sandbox-exec` does (`process-exec` is allowed only for the program and `exec`). Linux `bwrap`
/// does not: it only decides what is mounted, so every program under the read-only floor (/usr)
/// runs inside, and `Policy::exec` bounds what is VISIBLE there, not what may run. Plant:
/// tests/confine.rs `exec_is_filtered_exactly_where_the_platform_says`.
#[cfg(target_os = "macos")]
pub const EXEC_FILTERED: bool = true;
/// See the macOS row.
#[cfg(target_os = "linux")]
pub const EXEC_FILTERED: bool = false;
/// No mechanism, no launch, so nothing runs at all.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub const EXEC_FILTERED: bool = true;

/// A platform fact (charter law 2, CLIENT-20): whether the mechanism filters CONNECT to unix
/// sockets. macOS `sandbox-exec` does (`(deny default)`; `network-outbound` is allowed only to the
/// `connect` paths). Linux `bwrap` does not: a child connects to every path socket in a directory
/// of its view (measured on hbox under nd-bwrap), so `connect` there bounds what is VISIBLE, and
/// `ConnectOverlap` and `SocketInGrant` keep sockets out of file grants. Plant: tests/connect.rs
/// `connect_is_filtered_exactly_where_the_platform_says`.
#[cfg(target_os = "macos")]
pub const CONNECT_FILTERED: bool = true;
/// See the macOS row.
#[cfg(target_os = "linux")]
pub const CONNECT_FILTERED: bool = false;
/// No mechanism, no launch.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub const CONNECT_FILTERED: bool = true;

/// A platform fact (charter law 2): how the mechanism reports a child killed by a signal. macOS
/// `sandbox-exec` execs the program in its own place, so a signal death is seen as one (no exit
/// code). Linux `bwrap` stays the parent and turns the inner death into its own exit `128 + N`
/// (measured by OPS-2 on hbox: SIGXFSZ → 153, SIGKILL → 137). So on Linux a status of 128 or more
/// IS a signal death; a confined child's own code can then not be read above 127 (the Host's stay
/// below 64, `Host.Proofs.Exit`). Plant: client/tests/supervise.rs
/// `a_confined_child_killed_by_a_signal_is_child_signaled`.
pub fn killed_by_signal(status: std::process::ExitStatus) -> bool {
    use std::os::unix::process::ExitStatusExt;
    status.signal().is_some()
        || (cfg!(target_os = "linux") && status.code().is_some_and(|c| c >= 128))
}

#[cfg(target_os = "linux")]
/// Not `/usr/bin/bwrap`: Ubuntu 24.04+ (`kernel.apparmor_restrict_unprivileged_userns = 1`) gives an
/// unprivileged user namespace no capabilities, so the distro bwrap fails `setting up uid map:
/// Permission denied`. The mechanism is a root-owned copy of the distro ELF at this path with its
/// own AppArmor profile granting `userns` to this path alone (`sandbox/apparmor/nd-bwrap`, installed
/// by the operator); the global sysctl is untouched. Missing: `MechanismMissing`, never a fallback.
const MECHANISM: &str = "/usr/local/libexec/nd-bwrap";
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
const FLOOR: [(&str, bool); 5] = [
    ("/usr", false),
    ("/lib", true),
    ("/lib64", true),
    ("/bin", true),
    ("/etc/ld.so.cache", true),
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
    /// The connect sockets, canonical, and the directories that expose them.
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
        r.connect.push(connect::entry(p)?);
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
    let floor: Vec<PathBuf> = FLOOR.iter().map(|(p, _)| PathBuf::from(p)).collect();
    let grants: Vec<&PathBuf> = [&r.program]
        .into_iter()
        .chain(&r.read)
        .chain(&r.write)
        .chain(&r.exec)
        .collect();
    for (_, dir) in &r.connect {
        if let Some(a) = grants.iter().find(|a| overlap(a, dir)) {
            return Err(ConfineError::ConnectOverlap {
                connect: dir.clone(),
                allowed: (*a).clone(),
            });
        }
    }
    // A grant under the floor adds nothing the floor does not already show, so it is not scanned.
    for g in grants
        .iter()
        .filter(|g| !floor.iter().any(|f| g.starts_with(f)))
    {
        connect::socket_in(g)?;
    }
    let floor = floor.into_iter();
    let allowed: Vec<PathBuf> = [r.program.clone()]
        .into_iter()
        .chain(r.read.iter().cloned())
        .chain(r.write.iter().cloned())
        .chain(r.exec.iter().cloned())
        .chain(r.connect.iter().map(|(_, d)| d.clone()))
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

#[cfg(target_os = "linux")]
fn platform(r: &Resolved) -> Result<Command, ConfineError> {
    let mut c = Command::new(MECHANISM);
    c.args([
        "--die-with-parent",
        "--new-session",
        "--unshare-all",
        // `--unshare-all` only TRIES the user namespace; `--disable-userns` needs it for certain.
        "--unshare-user",
        "--disable-userns",
        "--cap-drop",
        "ALL",
        "--clearenv",
        // A Lean child needs /dev (measured: without it `host follow` closes at its first frame).
        // It needs no /proc: the runtime sizes its pool by sched_getaffinity, the Linux twin of
        // macOS hw.ncpu, which bwrap does not filter (measured: the real round trip and the 3 s
        // plant are green without /proc), so /proc is not mounted.
        "--dev",
        "/dev",
    ]);
    // A merged-/usr system has `/lib -> usr/lib` (and /lib64, /bin): the link is recreated, never
    // bound (binding it would bind its target a second time under another name).
    for (p, optional) in FLOOR {
        match std::fs::read_link(p) {
            Ok(target) => {
                c.arg("--symlink").arg(target).arg(p);
            }
            Err(_) => {
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
        }
    }
    for p in [&r.program].into_iter().chain(&r.read).chain(&r.exec) {
        c.arg("--ro-bind").arg(p).arg(p);
    }
    for p in &r.write {
        c.arg("--bind").arg(p).arg(p);
    }
    // The socket's DIRECTORY, so a restarted server's new socket is the one seen (HOSTING-17 §4).
    for (_, d) in &r.connect {
        c.arg("--ro-bind").arg(d).arg(d);
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
