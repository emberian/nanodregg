//! Linux: the child confines ITSELF between fork and exec (CLIENT-48, CLIENT-52): no helper
//! program, no namespace, no mount. The launcher prepares everything before the fork: a Landlock
//! ruleset whose rules hold `O_PATH` descriptors opened component by component without following a
//! link (so a grant is the inode the policy was checked against), two seccomp programs, and for a
//! policy with `connect` entries the child's end of its connector. In the child, before `execve`,
//! the step makes only system calls on what was built: `setsid`, the parent-death signal, every
//! inherited descriptor but stdio and the connector marked close-on-exec, `no_new_privs`,
//! `landlock_restrict_self`, two `seccomp` installs. The child can undo none of it (the
//! parent-death signal included: `prctl` is limited to naming threads).
//!
//! What this is: CONTAINMENT OF NAMED RESOURCES AND OPERATION FAMILIES. A compromised child runs
//! whatever instructions it likes inside these bounds; it may destroy its own write grant, consume
//! its CPU, memory and disk up to the service manager's limits, and use every descriptor it holds.
//! It is not a guarantee that attacker-controlled instructions cannot run.
//!
//! - Files (Landlock; ABI 3 required, `Policy::landlock_abi` raises it): read on the floor, the
//!   program, `read` and `exec`; execute on the program, the `exec` entries and the runtime
//!   manifest's loader ([`LOADERS`], no file is parsed to find one); read, write, create and remove
//!   under `write`, never execute there, never a socket, fifo or device node. Fresh opens elsewhere
//!   are EACCES. Not mediated by Landlock, so refused by seccomp: chmod and timestamp changes of
//!   any kind (`fchmod*`, `chmod`, `utimensat`), chown, xattrs. Names stay visible to `stat`.
//! - Sockets: none can be created (`socket`, `socketpair`), `connect`, `bind`, `listen`, `accept`
//!   and `sendmsg` are refused, `sendto` only without an address; TCP handled with no rule (ABI
//!   4+), abstract sockets and signals scoped (ABI 6). A `connect` entry is reached through the
//!   CONNECTOR: the child sends the path on `ND_CONNECTOR`; the launcher connects, if and only if
//!   it is one of the policy's entries, through the socket directory's descriptor opened at launch
//!   (a replaced ancestor does not redirect it), refuses a name that is no longer a socket, checks
//!   the server's peer credentials against the socket's owner at launch, and hands the connected
//!   socket back over `SCM_RIGHTS`. Asks are rate-bounded and a reply the child does not read ends
//!   its connector.
//! - Descriptors: only 0, 1, 2 and the connector survive `execve`.
//! - Processes: `clone` only with glibc's exact thread flags; `clone3` and `io_uring_*` ENOSYS;
//!   `kill`/`tgkill` only of itself; no ptrace, mount, namespace, bpf, keyring, perf, userfaultfd,
//!   memfd, execveat, SysV IPC. `fcntl`, `ioctl`, `prctl`, `setsockopt`, `arch_prctl` are limited
//!   to the operations the runtimes were measured to use (strace of the Lean Host, nd, Python and
//!   dash under the plants, 2026-10-27); no `F_SETOWN`/`F_SETSIG`/`O_ASYNC`/leases/notify.
//!   Everything else is EPERM.
//! - It needs no `openat2` (systemd's `RestrictSUIDSGID=yes` answers it ENOSYS, TENANT-2).

use std::collections::BTreeMap;
use std::io::{self, IoSlice, IoSliceMut};
use std::mem::MaybeUninit;
use std::os::fd::{AsFd, AsRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::CommandExt;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use landlock::{
    ABI, Access, AccessFs, AccessNet, BitFlags, CompatLevel, Compatible, PathBeneath, Ruleset,
    RulesetAttr, RulesetCreated, RulesetCreatedAttr, RulesetStatus, Scope,
};
use rustix::fs::{FileType, Mode, OFlags};
use rustix::net::{
    AddressFamily, RecvAncillaryBuffer, RecvAncillaryMessage, RecvFlags, SendAncillaryBuffer,
    SendAncillaryMessage, SendFlags, SocketAddrUnix, SocketFlags, SocketType,
};
use seccompiler::{
    BpfProgram, SeccompAction, SeccompCmpArgLen, SeccompCmpOp, SeccompCondition, SeccompFilter,
    SeccompRule,
};

use crate::{ConfineError, Resolved};

/// The environment variable that names the connector descriptor in a child with `connect` entries.
pub const CONNECTOR_ENV: &str = "ND_CONNECTOR";

/// The longest path a connector ask may carry (a `sun_path` holds at most 107 bytes and a NUL).
const ASK_MAX: usize = 108;

/// Connector asks one child may make per second; past it the connector waits out the second.
const ASKS_PER_SECOND: u32 = 64;

/// What every child may read: the system libraries and the loader's cache.
pub(crate) const FLOOR: [&str; 5] = ["/usr", "/lib", "/lib64", "/bin", "/etc/ld.so.cache"];

/// THE RUNTIME MANIFEST: the ELF loaders a child may execute besides its program and `exec`
/// entries, by the platform's fixed name (glibc's `PT_INTERP`). Nothing reads an executable to find
/// its interpreter: a program with another loader, or a script, names it in `exec`.
#[cfg(target_arch = "x86_64")]
pub(crate) const LOADERS: [&str; 1] = ["/lib64/ld-linux-x86-64.so.2"];
/// See the x86_64 manifest.
#[cfg(target_arch = "aarch64")]
pub(crate) const LOADERS: [&str; 1] = ["/lib/ld-linux-aarch64.so.1"];
/// See the x86_64 manifest.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub(crate) const LOADERS: [&str; 0] = [];

/// The device nodes a child may open, and whether it may write them. The Lean runtime opens
/// `/dev/urandom` at start; `/dev/null` is every runtime's sink.
const DEVICES: [(&str, bool); 4] = [
    ("/dev/null", true),
    ("/dev/zero", false),
    ("/dev/random", false),
    ("/dev/urandom", false),
];

/// The newest ABI whose rights are asked for (signal and abstract-socket scoping).
pub(crate) const ABI_WANTED: u32 = 6;
const ABI_WANTED_L: ABI = ABI::V6;
/// The ABI a kernel must have, or nothing launches: file read, write, execute, rename across
/// directories (V2) and truncate (V3). A policy may require more (`Policy::landlock_abi`).
pub(crate) const ABI_REQUIRED: u32 = 3;
const ABI_REQUIRED_L: ABI = ABI::V3;

fn landlock_missing<E>(_: E) -> ConfineError {
    ConfineError::MechanismMissing("landlock")
}

/// The Landlock ABI this kernel offers (0: none), from `landlock_create_ruleset(NULL, 0, VERSION)`.
pub(crate) fn landlock_abi() -> u32 {
    static A: OnceLock<u32> = OnceLock::new();
    *A.get_or_init(|| {
        // SAFETY: the version query takes no pointer it dereferences (NULL, size 0) and only
        // returns an integer; it creates no descriptor.
        #[allow(unsafe_code)]
        let v = unsafe {
            libc::syscall(
                libc::SYS_landlock_create_ruleset,
                std::ptr::null::<u8>(),
                0usize,
                1u32,
            )
        };
        u32::try_from(v).unwrap_or(0)
    })
}

fn read_access(file: bool) -> BitFlags<AccessFs> {
    let r = AccessFs::from_read(ABI_WANTED_L) & !AccessFs::Execute;
    if file {
        r & AccessFs::from_file(ABI_WANTED_L)
    } else {
        r
    }
}

fn exec_access(file: bool) -> BitFlags<AccessFs> {
    read_access(file) | AccessFs::Execute
}

fn write_access(file: bool) -> BitFlags<AccessFs> {
    let w = AccessFs::from_all(ABI_WANTED_L)
        & !(AccessFs::Execute
            | AccessFs::MakeSock
            | AccessFs::MakeFifo
            | AccessFs::MakeChar
            | AccessFs::MakeBlock
            | AccessFs::IoctlDev);
    if file {
        w & AccessFs::from_file(ABI_WANTED_L)
    } else {
        w
    }
}

/// `path` (absolute, canonical) opened `O_PATH`, one component at a time, never following a link:
/// the inode reached is the one the policy named, or the open fails (`PathMissing`). A component
/// that became a link since the policy was resolved is refused (`ELOOP`).
pub(crate) fn open_exact(path: &Path) -> Result<OwnedFd, ConfineError> {
    let missing = |e: rustix::io::Errno| ConfineError::PathMissing(path.to_path_buf(), e.into());
    let flags = OFlags::PATH | OFlags::NOFOLLOW | OFlags::CLOEXEC;
    let mut at =
        rustix::fs::open("/", flags | OFlags::DIRECTORY, Mode::empty()).map_err(missing)?;
    for c in path.components() {
        match c {
            Component::RootDir => continue,
            Component::Normal(n) => {
                let next = rustix::fs::openat(&at, n, flags, Mode::empty()).map_err(missing)?;
                let t = FileType::from_raw_mode(rustix::fs::fstat(&next).map_err(missing)?.st_mode);
                if t == FileType::Symlink {
                    return Err(missing(rustix::io::Errno::LOOP));
                }
                at = next;
            }
            _ => return Err(missing(rustix::io::Errno::INVAL)),
        }
    }
    Ok(at)
}

fn is_dir(fd: &OwnedFd) -> bool {
    rustix::fs::fstat(fd).is_ok_and(|s| FileType::from_raw_mode(s.st_mode) == FileType::Directory)
}

/// The canonical paths of the manifest's loaders present on this system.
pub(crate) fn loaders() -> Vec<PathBuf> {
    LOADERS
        .iter()
        .filter_map(|l| Path::new(l).canonicalize().ok())
        .collect()
}

/// The ruleset of one launch.
fn ruleset(r: &Resolved) -> Result<RulesetCreated, ConfineError> {
    type Rights = fn(bool) -> BitFlags<AccessFs>;
    let mut rules: Vec<(PathBuf, Rights)> = Vec::new();
    for p in FLOOR {
        // a merged-/usr link (/lib -> usr/lib) is granted as its target, already under /usr
        if let Ok(c) = Path::new(p).canonicalize() {
            rules.push((c, read_access));
        }
    }
    for l in loaders() {
        rules.push((l, exec_access));
    }
    rules.push((r.program.clone(), exec_access));
    rules.extend(r.read.iter().map(|p| (p.clone(), read_access as Rights)));
    rules.extend(r.exec.iter().map(|p| (p.clone(), exec_access as Rights)));
    rules.extend(r.write.iter().map(|p| (p.clone(), write_access as Rights)));
    let mut rs = Ruleset::default()
        .set_compatibility(CompatLevel::HardRequirement)
        .handle_access(AccessFs::from_all(ABI_REQUIRED_L))
        .map_err(landlock_missing)?
        .set_compatibility(CompatLevel::BestEffort)
        .handle_access(AccessFs::from_all(ABI_WANTED_L))
        .map_err(landlock_missing)?
        .handle_access(AccessNet::from_all(ABI_WANTED_L))
        .map_err(landlock_missing)?
        .scope(Scope::from_all(ABI_WANTED_L))
        .map_err(landlock_missing)?
        .create()
        .map_err(landlock_missing)?;
    for (dev, write) in DEVICES {
        if let Ok(fd) = open_exact(Path::new(dev)) {
            let a = if write {
                AccessFs::ReadFile | AccessFs::WriteFile
            } else {
                AccessFs::ReadFile.into()
            };
            rs = rs
                .add_rule(PathBeneath::new(fd, a))
                .map_err(landlock_missing)?;
        }
    }
    for (p, access) in rules {
        let fd = open_exact(&p)?;
        let file = !is_dir(&fd);
        rs = rs
            .add_rule(PathBeneath::new(fd, access(file)))
            .map_err(landlock_missing)?;
    }
    Ok(rs)
}

/// `SO_RCVTIMEO`/`SO_SNDTIMEO`, old and new (time64) numbers (asm-generic, both arches).
const SOCKET_TIMEOUTS: [u64; 4] = [20, 21, 66, 67];

/// glibc's `pthread_create` clone flags (`sysdeps/unix/sysv/linux/clone-internal`), the only clone
/// the runtimes make (measured: every confined clone, 2026-10-27).
const THREAD_FLAGS: u64 = (libc::CLONE_VM
    | libc::CLONE_FS
    | libc::CLONE_FILES
    | libc::CLONE_SIGHAND
    | libc::CLONE_THREAD
    | libc::CLONE_SYSVSEM
    | libc::CLONE_SETTLS
    | libc::CLONE_PARENT_SETTID
    | libc::CLONE_CHILD_CLEARTID) as u64;

fn rule(conds: Vec<(u8, SeccompCmpOp, u64)>) -> Option<SeccompRule> {
    let c: Option<Vec<_>> = conds
        .into_iter()
        .map(|(a, op, v)| SeccompCondition::new(a, SeccompCmpArgLen::Qword, op, v).ok())
        .collect();
    SeccompRule::new(c?).ok()
}

fn eq(arg: u8, v: u64) -> (u8, SeccompCmpOp, u64) {
    (arg, SeccompCmpOp::Eq, v)
}

fn syscall_rules() -> Option<Vec<(i64, Vec<SeccompRule>)>> {
    use libc::*;
    let any = |n: c_long| (n, Vec::new());
    let mut v: Vec<(i64, Vec<SeccompRule>)> = [
        // file I/O on what the ruleset allows (no chmod, utimes, chown or xattr call: Landlock
        // does not mediate them)
        SYS_read,
        SYS_write,
        SYS_readv,
        SYS_writev,
        SYS_pread64,
        SYS_pwrite64,
        SYS_preadv,
        SYS_pwritev,
        SYS_preadv2,
        SYS_pwritev2,
        SYS_lseek,
        SYS_close,
        SYS_close_range,
        SYS_dup,
        SYS_dup3,
        SYS_flock,
        SYS_fsync,
        SYS_fdatasync,
        SYS_ftruncate,
        SYS_truncate,
        SYS_fallocate,
        SYS_sync_file_range,
        SYS_fadvise64,
        SYS_openat,
        SYS_openat2,
        SYS_newfstatat,
        SYS_fstat,
        SYS_statx,
        SYS_readlinkat,
        SYS_getdents64,
        SYS_faccessat,
        SYS_faccessat2,
        SYS_mkdirat,
        SYS_unlinkat,
        SYS_renameat2,
        SYS_linkat,
        SYS_symlinkat,
        SYS_getcwd,
        SYS_chdir,
        SYS_fchdir,
        SYS_statfs,
        SYS_fstatfs,
        SYS_copy_file_range,
        SYS_sendfile,
        SYS_splice,
        SYS_umask,
        // memory
        SYS_mmap,
        SYS_munmap,
        SYS_mprotect,
        SYS_mremap,
        SYS_madvise,
        SYS_brk,
        SYS_msync,
        SYS_mincore,
        SYS_membarrier,
        // threads, time, identity
        SYS_futex,
        SYS_set_robust_list,
        SYS_get_robust_list,
        SYS_rseq,
        SYS_set_tid_address,
        SYS_gettid,
        SYS_getpid,
        SYS_getppid,
        SYS_getpgid,
        SYS_getsid,
        SYS_sched_yield,
        SYS_sched_getaffinity,
        SYS_sched_getparam,
        SYS_sched_getscheduler,
        SYS_sched_get_priority_max,
        SYS_sched_get_priority_min,
        SYS_nanosleep,
        SYS_clock_nanosleep,
        SYS_clock_gettime,
        SYS_clock_getres,
        SYS_gettimeofday,
        SYS_getrandom,
        SYS_exit,
        SYS_exit_group,
        SYS_sigaltstack,
        SYS_rt_sigaction,
        SYS_rt_sigprocmask,
        SYS_rt_sigreturn,
        SYS_rt_sigsuspend,
        SYS_rt_sigtimedwait,
        SYS_restart_syscall,
        SYS_getuid,
        SYS_geteuid,
        SYS_getgid,
        SYS_getegid,
        SYS_getresuid,
        SYS_getresgid,
        SYS_getgroups,
        SYS_uname,
        SYS_getrlimit,
        SYS_getrusage,
        SYS_sysinfo,
        SYS_times,
        SYS_getitimer,
        SYS_setitimer,
        // waiting on descriptors
        SYS_ppoll,
        SYS_pselect6,
        SYS_epoll_create1,
        SYS_epoll_ctl,
        SYS_epoll_pwait,
        SYS_epoll_pwait2,
        SYS_eventfd2,
        SYS_pipe2,
        SYS_timerfd_create,
        SYS_timerfd_settime,
        SYS_timerfd_gettime,
        SYS_signalfd4,
        // the sockets it was handed (none can be made): receive, shut down, inspect
        SYS_recvfrom,
        SYS_recvmsg,
        SYS_recvmmsg,
        SYS_shutdown,
        SYS_getsockopt,
        SYS_getsockname,
        SYS_getpeername,
        // the exec that starts the program (Landlock decides which file), libc's clone3 probe
        // and io_uring's (both answered ENOSYS by the first filter)
        SYS_execve,
        SYS_clone3,
        SYS_io_uring_setup,
        SYS_io_uring_enter,
        SYS_io_uring_register,
    ]
    .into_iter()
    .map(any)
    .collect();
    #[cfg(target_arch = "x86_64")]
    v.extend(
        [
            SYS_open,
            SYS_stat,
            SYS_lstat,
            SYS_access,
            SYS_readlink,
            SYS_mkdir,
            SYS_rmdir,
            SYS_unlink,
            SYS_rename,
            SYS_renameat,
            SYS_link,
            SYS_symlink,
            SYS_dup2,
            SYS_poll,
            SYS_select,
            SYS_epoll_create,
            SYS_epoll_wait,
            SYS_eventfd,
            SYS_pipe,
            SYS_signalfd,
            SYS_getpgrp,
            SYS_time,
            SYS_alarm,
            SYS_getdents,
        ]
        .into_iter()
        .map(any),
    );
    #[cfg(target_arch = "x86_64")]
    v.push((SYS_arch_prctl, vec![rule(vec![eq(0, 0x1002)])?])); // ARCH_SET_FS: the TLS base
    #[cfg(target_arch = "aarch64")]
    v.push(any(SYS_renameat));
    // A thread, never a process, with exactly glibc's thread flags.
    v.push((SYS_clone, vec![rule(vec![eq(0, THREAD_FLAGS)])?]));
    // getrlimit's successor on itself only (pid 0).
    v.push((SYS_prlimit64, vec![rule(vec![eq(0, 0)])?]));
    // Signals to itself only: `kill` of its own pid or its own group (0: `setsid` made the group
    // itself alone), `tgkill` of its own thread group. The pid is written over `SELF` by the step.
    v.push((
        SYS_kill,
        vec![rule(vec![eq(0, 0)])?, rule(vec![eq(0, SELF)])?],
    ));
    v.push((SYS_tgkill, vec![rule(vec![eq(0, SELF)])?]));
    // fcntl: descriptor flags, status flags without O_ASYNC, dup, record locks. No F_SETOWN(_EX),
    // F_SETSIG, F_SETLEASE, F_NOTIFY, F_SETPIPE_SZ, seals.
    let mut fcntl = Vec::new();
    for cmd in [
        F_GETFD,
        F_SETFD,
        F_GETFL,
        F_DUPFD,
        F_DUPFD_CLOEXEC,
        F_GETLK,
        F_SETLK,
        F_SETLKW,
        F_OFD_GETLK,
        F_OFD_SETLK,
        F_OFD_SETLKW,
    ] {
        fcntl.push(rule(vec![eq(1, cmd as u64)])?);
    }
    fcntl.push(rule(vec![
        eq(1, F_SETFL as u64),
        (2, SeccompCmpOp::MaskedEq(O_ASYNC as u64), 0),
    ])?);
    v.push((SYS_fcntl, fcntl));
    // ioctl: is-a-terminal, non-blocking and close-on-exec toggles.
    let mut ioctl = Vec::new();
    for req in [TCGETS, FIONBIO, FIOCLEX, FIONCLEX] {
        ioctl.push(rule(vec![eq(1, req)])?);
    }
    v.push((SYS_ioctl, ioctl));
    // prctl: naming threads only; the parent-death signal cannot be cleared.
    v.push((
        SYS_prctl,
        vec![
            rule(vec![eq(0, PR_SET_NAME as u64)])?,
            rule(vec![eq(0, PR_GET_NAME as u64)])?,
        ],
    ));
    // setsockopt: a handed socket's read and write timeouts.
    let mut sso = Vec::new();
    for opt in SOCKET_TIMEOUTS {
        sso.push(rule(vec![eq(1, SOL_SOCKET as u64), eq(2, opt)])?);
    }
    v.push((SYS_setsockopt, sso));
    // sendto without a destination (send on a connected socket); no sendmsg, no sendmmsg.
    v.push((SYS_sendto, vec![rule(vec![eq(4, 0)])?]));
    Some(v)
}

/// The stand-in for the child's own pid in the allow-list: above every pid (`pid_max` is at most
/// 2^22), and no other instruction of the program compares with it.
const SELF: u64 = 0x7EAD_BEEF;

/// The two seccomp programs, built once per process: the `ENOSYS` answers (`clone3`, `io_uring`),
/// then the allow-list (everything else `EPERM`).
fn filters() -> Result<&'static [BpfProgram; 2], ConfineError> {
    static F: OnceLock<Option<[BpfProgram; 2]>> = OnceLock::new();
    let built = F.get_or_init(|| {
        let arch = std::env::consts::ARCH.try_into().ok()?;
        let nosys: BTreeMap<i64, Vec<SeccompRule>> = [
            libc::SYS_clone3,
            libc::SYS_io_uring_setup,
            libc::SYS_io_uring_enter,
            libc::SYS_io_uring_register,
        ]
        .into_iter()
        .map(|n| (n, Vec::new()))
        .collect();
        let nosys = SeccompFilter::new(
            nosys,
            SeccompAction::Allow,
            SeccompAction::Errno(libc::ENOSYS as u32),
            arch,
        )
        .ok()?;
        let allow = SeccompFilter::new(
            syscall_rules()?.into_iter().collect(),
            SeccompAction::Errno(libc::EPERM as u32),
            SeccompAction::Allow,
            arch,
        )
        .ok()?;
        Some([nosys.try_into().ok()?, allow.try_into().ok()?])
    });
    built
        .as_ref()
        .ok_or(ConfineError::MechanismMissing("seccomp"))
}

/// What the child does to itself between fork and exec. Only system calls on what the parent
/// built: no allocation on any path (an error is a bare errno), no lock.
struct Step {
    parent: rustix::process::Pid,
    ruleset: Option<RulesetCreated>,
    /// This launch's copy, so the step can write its pid over `SELF`.
    filters: [BpfProgram; 2],
    connector: Option<OwnedFd>,
}

fn errno(e: i32) -> io::Error {
    io::Error::from_raw_os_error(e)
}

impl Step {
    fn run(&mut self) -> io::Result<()> {
        use rustix::process::{Signal, getppid, set_parent_process_death_signal, setsid};
        setsid()?;
        set_parent_process_death_signal(Some(Signal::KILL))?;
        // The parent died between the fork and the line above: the signal will never come.
        if getppid() != Some(self.parent) {
            return Err(errno(libc::ESRCH));
        }
        // The descriptor inventory: every descriptor above stdio closes at exec, but the connector.
        // SAFETY: close_range with CLOSE_RANGE_CLOEXEC only sets a flag on descriptors this
        // process holds; it takes no pointer.
        #[allow(unsafe_code)]
        let r = unsafe {
            libc::syscall(
                libc::SYS_close_range,
                3u32,
                u32::MAX,
                libc::CLOSE_RANGE_CLOEXEC,
            )
        };
        if r != 0 {
            return Err(io::Error::last_os_error());
        }
        if let Some(c) = &self.connector {
            rustix::io::fcntl_setfd(c, rustix::io::FdFlags::empty())?;
        }
        let rs = self.ruleset.take().ok_or_else(|| errno(libc::EALREADY))?;
        let st = rs.restrict_self().map_err(|_| errno(libc::EPERM))?;
        if st.ruleset == RulesetStatus::NotEnforced || !st.no_new_privs {
            return Err(errno(libc::EPERM));
        }
        let me = rustix::process::getpid().as_raw_nonzero().get() as u32;
        for ins in self.filters.iter_mut().flatten() {
            if u64::from(ins.k) == SELF {
                ins.k = me;
            }
        }
        for f in &self.filters {
            seccompiler::apply_filter(f).map_err(|_| errno(libc::EPERM))?;
        }
        Ok(())
    }
}

/// The launcher may hold no privilege a child could inherit: not root, no permitted or effective
/// capability (`Privileged`). NoNewPrivs then keeps it so across exec.
pub(crate) fn unprivileged() -> Result<(), ConfineError> {
    let caps = rustix::thread::capabilities(None)
        .map_err(|e| ConfineError::Privileged(format!("capget: {e}")))?;
    if rustix::process::geteuid().is_root() {
        return Err(ConfineError::Privileged("euid 0".into()));
    }
    if !caps.permitted.is_empty() || !caps.effective.is_empty() {
        return Err(ConfineError::Privileged(format!(
            "capabilities permitted {:?} effective {:?}",
            caps.permitted, caps.effective
        )));
    }
    Ok(())
}

/// One connect grant as the connector holds it: the names a child may ask for, the socket
/// directory's descriptor (opened exactly at launch), the socket's name in it, and its owner.
struct Grant {
    names: Vec<Vec<u8>>,
    dir: OwnedFd,
    name: PathBuf,
    owner: u32,
}

/// The command that runs `r.program` confining itself first.
pub(crate) fn command(r: &Resolved, need_abi: u32) -> Result<Command, ConfineError> {
    unprivileged()?;
    let have = landlock_abi();
    if have < need_abi.max(ABI_REQUIRED) {
        return Err(ConfineError::LandlockAbi {
            have,
            need: need_abi.max(ABI_REQUIRED),
        });
    }
    let filters = filters()?;
    let ruleset = ruleset(r)?;
    let mut c = Command::new(&r.program);
    c.env_clear();
    let connector = if r.connect.is_empty() {
        None
    } else {
        let mut grants = Vec::new();
        for (given, sock) in &r.connect {
            let (Some(parent), Some(name)) = (sock.parent(), sock.file_name()) else {
                return Err(ConfineError::ConnectNotSocket(sock.clone()));
            };
            let dir = open_exact(parent)?;
            let owner = rustix::fs::statat(&dir, name, rustix::fs::AtFlags::SYMLINK_NOFOLLOW)
                .map_err(|e| ConfineError::PathMissing(sock.clone(), e.into()))?
                .st_uid;
            grants.push(Grant {
                names: vec![
                    given.as_os_str().as_bytes().to_vec(),
                    sock.as_os_str().as_bytes().to_vec(),
                ],
                dir,
                name: PathBuf::from(name),
                owner,
            });
        }
        let (ours, theirs) = rustix::net::socketpair(
            AddressFamily::UNIX,
            SocketType::SEQPACKET,
            SocketFlags::CLOEXEC,
            None,
        )
        .map_err(|e| ConfineError::Connector(e.into()))?;
        // Never 0..=2: the child's stdio is set up over those numbers before the step runs.
        let theirs = rustix::io::fcntl_dupfd_cloexec(&theirs, 3)
            .map_err(|e| ConfineError::Connector(e.into()))?;
        c.env(CONNECTOR_ENV, theirs.as_raw_fd().to_string());
        std::thread::Builder::new()
            .name("nd-connector".into())
            .spawn(move || serve(&ours, &grants))
            .map_err(ConfineError::Connector)?;
        Some(theirs)
    };
    let mut step = Step {
        parent: rustix::process::getpid(),
        ruleset: Some(ruleset),
        filters: filters.clone(),
        connector,
    };
    // SAFETY: `Step::run` makes only system calls on values built before the fork (the ruleset's
    // descriptor, the BPF programs, the connector descriptor) and allocates nothing on any path,
    // which is what a child of a multi-threaded parent may do before `execve`.
    #[allow(unsafe_code)]
    unsafe {
        c.pre_exec(move || step.run());
    }
    Ok(c)
}

/// The connector's parent side: answer each ask until every copy of the child's end is closed
/// (the child ended, or the command was dropped unspawned), or the child stops reading replies.
fn serve(ours: &OwnedFd, grants: &[Grant]) {
    let mut ask = [0u8; ASK_MAX + 1];
    let (mut window, mut asks) = (Instant::now(), 0u32);
    loop {
        let n = match rustix::net::recv(ours, &mut ask, RecvFlags::TRUNC) {
            Ok((_, 0)) | Err(_) => return,
            Ok((_, n)) => n,
        };
        asks += 1;
        if asks > ASKS_PER_SECOND {
            let left = Duration::from_secs(1).saturating_sub(window.elapsed());
            std::thread::sleep(left);
            (window, asks) = (Instant::now(), 1);
        } else if window.elapsed() >= Duration::from_secs(1) {
            (window, asks) = (Instant::now(), 1);
        }
        let asked = &ask[..n.min(ask.len())];
        let granted = grants
            .iter()
            .find(|g| g.names.iter().any(|x| x.as_slice() == asked));
        let dialed = match granted {
            Some(g) if n <= ASK_MAX => dial(g),
            _ => Err(rustix::io::Errno::ACCESS),
        };
        let (code, fd) = match &dialed {
            Ok(fd) => (0u32, Some(fd.as_fd())),
            Err(e) => (e.raw_os_error() as u32, None),
        };
        let fds = fd.as_slice();
        let mut space = [MaybeUninit::uninit(); rustix::cmsg_space!(ScmRights(1))];
        let mut control = SendAncillaryBuffer::new(&mut space);
        if !fds.is_empty() {
            control.push(SendAncillaryMessage::ScmRights(fds));
        }
        let bytes = code.to_le_bytes();
        // DONTWAIT: a child that asks without reading its replies loses its connector.
        if rustix::net::sendmsg(
            ours,
            &[IoSlice::new(&bytes)],
            &mut control,
            SendFlags::DONTWAIT,
        )
        .is_err()
        {
            return;
        }
    }
}

/// One non-blocking connect through the grant's directory descriptor (`/proc/self/fd/N/NAME`: the
/// directory inode opened at launch, whatever is renamed over its ancestors since), as
/// `nd_unix_connect` makes it: a full backlog is `EAGAIN` at once. The name must still be a socket
/// (`ECONNREFUSED` for a link or anything else) and the server must run as the socket's owner at
/// launch (`EACCES` otherwise).
fn dial(g: &Grant) -> rustix::io::Result<OwnedFd> {
    let st = rustix::fs::statat(&g.dir, &g.name, rustix::fs::AtFlags::SYMLINK_NOFOLLOW)?;
    if FileType::from_raw_mode(st.st_mode) != FileType::Socket {
        return Err(rustix::io::Errno::CONNREFUSED);
    }
    let mut at = PathBuf::from(format!("/proc/self/fd/{}", g.dir.as_raw_fd()));
    at.push(&g.name);
    let fd = rustix::net::socket_with(
        AddressFamily::UNIX,
        SocketType::STREAM,
        SocketFlags::CLOEXEC | SocketFlags::NONBLOCK,
        None,
    )?;
    rustix::net::connect(&fd, &SocketAddrUnix::new(&at)?)?;
    if rustix::net::sockopt::socket_peercred(&fd)?.uid.as_raw() != g.owner {
        return Err(rustix::io::Errno::ACCESS);
    }
    Ok(fd)
}

/// How long a child waits for the connector's reply to one ask (`ETIMEDOUT` past it).
pub(crate) const ASK_TIMEOUT: Duration = Duration::from_secs(30);

/// One reply from the connector: its length, the errno it carries, the socket it passed.
fn reply(connector: &OwnedFd, end: Instant) -> io::Result<(usize, u32, Option<OwnedFd>)> {
    loop {
        let left = end.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(errno(libc::ETIMEDOUT));
        }
        let t = rustix::event::Timespec::try_from(left).map_err(|_| errno(libc::EINVAL))?;
        let mut pf = [rustix::event::PollFd::new(
            connector,
            rustix::event::PollFlags::IN,
        )];
        match rustix::event::poll(&mut pf, Some(&t)) {
            Ok(0) | Err(rustix::io::Errno::INTR) => continue,
            Ok(_) => break,
            Err(e) => return Err(e.into()),
        }
    }
    let mut code = [0u8; 4];
    let mut space = [MaybeUninit::uninit(); rustix::cmsg_space!(ScmRights(1))];
    let mut control = RecvAncillaryBuffer::new(&mut space);
    let got = rustix::net::recvmsg(
        connector,
        &mut [IoSliceMut::new(&mut code)],
        &mut control,
        RecvFlags::CMSG_CLOEXEC,
    )?;
    let mut fd = None;
    for m in control.drain() {
        if let RecvAncillaryMessage::ScmRights(mut fds) = m {
            fd = fd.or(fds.next());
        }
    }
    Ok((got.bytes, u32::from_le_bytes(code), fd))
}

/// The child's side of the connector: the socket at `path`, if the launcher's policy grants it.
/// `owed` counts replies to asks that timed out: each is read and dropped first, so a late reply
/// never answers this ask.
pub(crate) fn ask(connector: &OwnedFd, owed: &mut u32, path: &Path) -> io::Result<OwnedFd> {
    let p = path.as_os_str().as_bytes();
    if p.is_empty() || p.len() > ASK_MAX {
        return Err(io::Error::from_raw_os_error(libc::ENAMETOOLONG));
    }
    let end = Instant::now() + ASK_TIMEOUT;
    while *owed > 0 {
        drop(reply(connector, end)?);
        *owed -= 1;
    }
    rustix::net::send(connector, p, SendFlags::empty())?;
    let (bytes, code, fd) = match reply(connector, end) {
        Err(e) if e.raw_os_error() == Some(libc::ETIMEDOUT) => {
            *owed += 1;
            return Err(e);
        }
        r => r?,
    };
    if bytes != 4 {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "connector closed",
        ));
    }
    match (code, fd) {
        (0, Some(fd)) => Ok(fd),
        (0, None) => Err(io::Error::other("connector sent no socket")),
        (e, _) => Err(io::Error::from_raw_os_error(e as i32)),
    }
}
