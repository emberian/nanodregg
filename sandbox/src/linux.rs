//! Linux: the child confines ITSELF between fork and exec, so no helper program, no namespace and
//! no mount stand between it and its parent (CLIENT-48). Everything the step needs is prepared in
//! the parent before the fork: a Landlock ruleset whose rules hold `O_PATH` descriptors of the
//! policy's paths (an inode granted at launch stays the grant, whatever is renamed or linked over
//! its name later), two seccomp programs, and for a policy with `connect` entries the child's end
//! of its connector. In the child, before `execve`, the step only makes system calls on what is
//! already built: `setsid`, the parent-death signal, `no_new_privs`, `landlock_restrict_self`,
//! `seccomp`. All of it is inherited across `execve` and can never be undone by the child.
//!
//! - Files: Landlock (unprivileged; ABI 3 required, newer rights taken where the kernel has them).
//!   Read rights on the floor, the program, `read` and `exec`; execute rights on the program, the
//!   `exec` entries and the program's interpreters (its `#!` line, its ELF loader); read, write,
//!   create and remove under `write`, never execute there and never a socket, fifo or device
//!   node. Denied: `EACCES`. A path's metadata (`stat`) stays visible; its contents do not.
//! - Sockets: no socket can be created (`socket`, `socketpair` are refused by seccomp) and TCP
//!   bind and connect are handled by Landlock with no rule (ABI 4+), so the only sockets the child
//!   has are the ones it is handed. A `connect` entry is reached through the CONNECTOR: the child
//!   sends the path on the descriptor named by `ND_CONNECTOR`, the parent connects to it if, and
//!   only if, it is one of the policy's entries, and hands the connected socket back over
//!   `SCM_RIGHTS` (or the connect's errno). The parent connects anew on every ask, so a restarted
//!   server's new socket is the one reached (HOSTING-17 §4). Clients: `crate::connect_unix` and
//!   `Host/c/sock.c` (`nd_unix_connect`), the same wire.
//! - Processes: `clone` only with `CLONE_THREAD` (threads, never a child process); `clone3` is
//!   `ENOSYS` so libc falls back to `clone`; `execve` passes seccomp and Landlock decides which file
//!   it may run. No `kill` of another process, no ptrace, no mount or namespace call, no
//!   `io_uring` (`ENOSYS`: its requests would bypass this filter), no SysV IPC, no keyring, no
//!   `bpf`, `perf_event_open`, `userfaultfd`, `memfd_create`, `execveat`. Everything not listed is
//!   `EPERM`. Where the kernel has Landlock ABI 6, signals and abstract unix sockets are scoped to
//!   the child's own domain as well.
//! - It needs no `openat2`: systemd's `RestrictSUIDSGID=yes` answers it `ENOSYS` (TENANT-2), and
//!   Landlock is enforced inside the kernel's own path walk, whatever call opens.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::{self, IoSlice, IoSliceMut, Read};
use std::mem::MaybeUninit;
use std::os::fd::{AsFd, AsRawFd, OwnedFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use landlock::{
    ABI, Access, AccessFs, AccessNet, BitFlags, CompatLevel, Compatible, PathBeneath, PathFd,
    Ruleset, RulesetAttr, RulesetCreated, RulesetCreatedAttr, RulesetStatus, Scope,
};
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

/// What every child may read: the system libraries and the loader's cache.
pub(crate) const FLOOR: [&str; 5] = ["/usr", "/lib", "/lib64", "/bin", "/etc/ld.so.cache"];

/// The device nodes a child may open, and whether it may write them. The Lean runtime opens
/// `/dev/urandom` at start; `/dev/null` is every runtime's sink.
const DEVICES: [(&str, bool); 4] = [
    ("/dev/null", true),
    ("/dev/zero", false),
    ("/dev/random", false),
    ("/dev/urandom", false),
];

/// The newest ABI whose rights are asked for; a kernel with fewer gives what it has (best effort),
/// except the floor below.
const ABI_WANTED: ABI = ABI::V6;
/// The ABI a kernel must have, or nothing launches (`MechanismMissing("landlock")`): file read,
/// write, execute, rename across directories (V2) and truncate (V3).
const ABI_REQUIRED: ABI = ABI::V3;

fn landlock_missing<E>(_: E) -> ConfineError {
    ConfineError::MechanismMissing("landlock")
}

fn read_access(file: bool) -> BitFlags<AccessFs> {
    let r = AccessFs::from_read(ABI_WANTED) & !AccessFs::Execute;
    if file {
        r & AccessFs::from_file(ABI_WANTED)
    } else {
        r
    }
}

fn exec_access(file: bool) -> BitFlags<AccessFs> {
    read_access(file) | AccessFs::Execute
}

fn write_access(file: bool) -> BitFlags<AccessFs> {
    let w = AccessFs::from_all(ABI_WANTED)
        & !(AccessFs::Execute
            | AccessFs::MakeSock
            | AccessFs::MakeFifo
            | AccessFs::MakeChar
            | AccessFs::MakeBlock
            | AccessFs::IoctlDev);
    if file {
        w & AccessFs::from_file(ABI_WANTED)
    } else {
        w
    }
}

/// The interpreters the kernel opens to run `program`: its `#!` interpreter (and that one's), its
/// ELF `PT_INTERP` loader. Each must be executable in the child as the program itself is.
fn interpreters(program: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut at = program.to_path_buf();
    for _ in 0..3 {
        let next = match interpreter(&at) {
            Some(p) => p,
            None => break,
        };
        let Ok(next) = next.canonicalize() else { break };
        if out.contains(&next) {
            break;
        }
        out.push(next.clone());
        at = next;
    }
    out
}

/// One interpreter of `path`: the first word of a `#!` line, or a 64-bit little-endian ELF's
/// `PT_INTERP`. Unreadable or anything else: none (the kernel then refuses the exec on its own).
fn interpreter(path: &Path) -> Option<PathBuf> {
    let mut head = Vec::new();
    std::fs::File::open(path)
        .ok()?
        .take(4096)
        .read_to_end(&mut head)
        .ok()?;
    if let Some(line) = head.strip_prefix(b"#!") {
        let line = line.split(|b| *b == b'\n').next()?;
        let word = line
            .split(|b| *b == b' ' || *b == b'\t')
            .find(|w| !w.is_empty())?;
        return Some(PathBuf::from(OsString::from_vec(word.to_vec())));
    }
    if head.get(..6)? != b"\x7fELF\x02\x01" {
        return None;
    }
    let u16_at = |o: usize| Some(u16::from_le_bytes(head.get(o..o + 2)?.try_into().ok()?));
    let u64_at = |b: &[u8], o: usize| Some(u64::from_le_bytes(b.get(o..o + 8)?.try_into().ok()?));
    let phoff = usize::try_from(u64_at(&head, 0x20)?).ok()?;
    let (entsize, count) = (usize::from(u16_at(0x36)?), usize::from(u16_at(0x38)?));
    let mut f = std::fs::File::open(path).ok()?;
    let mut table = vec![0u8; entsize.checked_mul(count)?];
    std::io::Seek::seek(&mut f, std::io::SeekFrom::Start(phoff as u64)).ok()?;
    f.read_exact(&mut table).ok()?;
    for ph in table.chunks(entsize) {
        // PT_INTERP = 3: p_offset at 8, p_filesz at 32.
        if u32::from_le_bytes(ph.get(..4)?.try_into().ok()?) == 3 {
            let (off, len) = (u64_at(ph, 8)?, usize::try_from(u64_at(ph, 32)?).ok()?);
            let mut name = vec![0u8; len.min(4096)];
            std::io::Seek::seek(&mut f, std::io::SeekFrom::Start(off)).ok()?;
            f.read_exact(&mut name).ok()?;
            let name = name.split(|b| *b == 0).next()?;
            return Some(PathBuf::from(OsString::from_vec(name.to_vec())));
        }
    }
    None
}

/// The rights of one grant kind, for a file (`true`) or a directory.
type Rights = fn(bool) -> BitFlags<AccessFs>;

/// The ruleset of one launch, every rule holding an `O_PATH` descriptor opened now.
fn ruleset(r: &Resolved) -> Result<RulesetCreated, ConfineError> {
    let mut rules: Vec<(PathBuf, Rights)> = Vec::new();
    for p in FLOOR {
        if Path::new(p).exists() {
            rules.push((p.into(), read_access));
        }
    }
    rules.push((r.program.clone(), exec_access));
    for p in interpreters(&r.program) {
        rules.push((p, exec_access));
    }
    rules.extend(r.read.iter().map(|p| (p.clone(), read_access as Rights)));
    rules.extend(r.exec.iter().map(|p| (p.clone(), exec_access as Rights)));
    rules.extend(r.write.iter().map(|p| (p.clone(), write_access as Rights)));
    let mut rs = Ruleset::default()
        .set_compatibility(CompatLevel::HardRequirement)
        .handle_access(AccessFs::from_all(ABI_REQUIRED))
        .map_err(landlock_missing)?
        .set_compatibility(CompatLevel::BestEffort)
        .handle_access(AccessFs::from_all(ABI_WANTED))
        .map_err(landlock_missing)?
        .handle_access(AccessNet::from_all(ABI_WANTED))
        .map_err(landlock_missing)?
        .scope(Scope::from_all(ABI_WANTED))
        .map_err(landlock_missing)?
        .create()
        .map_err(landlock_missing)?;
    for (dev, write) in DEVICES {
        if let Ok(fd) = PathFd::new(dev) {
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
        let fd = PathFd::new(&p)
            .map_err(|e| ConfineError::PathMissing(p.clone(), io::Error::other(e.to_string())))?;
        let file = !p.is_dir();
        rs = rs
            .add_rule(PathBeneath::new(fd, access(file)))
            .map_err(landlock_missing)?;
    }
    Ok(rs)
}

fn syscall_rules() -> Vec<(i64, Vec<SeccompRule>)> {
    use libc::*;
    let any = |n: c_long| (n, Vec::new());
    let mut v: Vec<(i64, Vec<SeccompRule>)> = [
        // file I/O on what the ruleset allows
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
        SYS_fcntl,
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
        SYS_fchmod,
        SYS_fchmodat,
        SYS_utimensat,
        SYS_getcwd,
        SYS_chdir,
        SYS_fchdir,
        SYS_statfs,
        SYS_fstatfs,
        SYS_copy_file_range,
        SYS_sendfile,
        SYS_splice,
        SYS_umask,
        SYS_ioctl,
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
        // threads, time, signals to itself, identity
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
        SYS_prctl,
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
        SYS_setrlimit,
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
        // the sockets it was handed (none can be made)
        SYS_sendto,
        SYS_recvfrom,
        SYS_sendmsg,
        SYS_recvmsg,
        SYS_sendmmsg,
        SYS_recvmmsg,
        SYS_shutdown,
        SYS_getsockopt,
        SYS_setsockopt,
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
            SYS_chmod,
            SYS_dup2,
            SYS_poll,
            SYS_select,
            SYS_epoll_create,
            SYS_epoll_wait,
            SYS_eventfd,
            SYS_pipe,
            SYS_signalfd,
            SYS_arch_prctl,
            SYS_getpgrp,
            SYS_time,
            SYS_alarm,
            SYS_getdents,
        ]
        .into_iter()
        .map(any),
    );
    #[cfg(target_arch = "aarch64")]
    v.push(any(SYS_renameat));
    // A thread, never a process: CLONE_THREAD must be set (clone's first argument on both arches).
    let thread = SeccompCondition::new(
        0,
        SeccompCmpArgLen::Qword,
        SeccompCmpOp::MaskedEq(CLONE_THREAD as u64),
        CLONE_THREAD as u64,
    )
    .and_then(|c| SeccompRule::new(vec![c]));
    if let Ok(rule) = thread {
        v.push((SYS_clone, vec![rule]));
    }
    // getrlimit's successor on itself only (pid 0): another process's limits are not its own.
    let own = SeccompCondition::new(0, SeccompCmpArgLen::Qword, SeccompCmpOp::Eq, 0)
        .and_then(|c| SeccompRule::new(vec![c]));
    if let Ok(rule) = own {
        v.push((SYS_prlimit64, vec![rule]));
    }
    // Signals to itself only: `kill` of its own pid or its own group (0; `setsid` made the group
    // itself alone), `tgkill` of its own thread group (raise, abort). The pid is not known until
    // the child exists, so the program carries `SELF` and the step writes the pid over it.
    let is = |arg, value| {
        SeccompCondition::new(arg, SeccompCmpArgLen::Dword, SeccompCmpOp::Eq, value)
            .and_then(|c| SeccompRule::new(vec![c]))
    };
    if let (Ok(zero), Ok(me)) = (is(0, 0), is(0, SELF)) {
        v.push((SYS_kill, vec![zero, me]));
    }
    if let Ok(me) = is(0, SELF) {
        v.push((SYS_tgkill, vec![me]));
    }
    v
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
            syscall_rules().into_iter().collect(),
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
/// built: no allocation, no lock (the parent may have other threads, frozen mid-allocation).
struct Step {
    parent: rustix::process::Pid,
    ruleset: Option<RulesetCreated>,
    /// This launch's copy, so the step can write its pid over `SELF`.
    filters: [BpfProgram; 2],
    connector: Option<OwnedFd>,
}

impl Step {
    fn run(&mut self) -> io::Result<()> {
        use rustix::process::{Signal, getppid, set_parent_process_death_signal, setsid};
        setsid()?;
        set_parent_process_death_signal(Some(Signal::KILL))?;
        // The parent died between the fork and the line above: the signal will never come.
        if getppid() != Some(self.parent) {
            return Err(io::Error::other("parent died"));
        }
        if let Some(c) = &self.connector {
            rustix::io::fcntl_setfd(c, rustix::io::FdFlags::empty())?;
        }
        let rs = self
            .ruleset
            .take()
            .ok_or_else(|| io::Error::other("ruleset spent"))?;
        let st = rs
            .restrict_self()
            .map_err(|_| io::Error::other("landlock"))?;
        if st.ruleset == RulesetStatus::NotEnforced || !st.no_new_privs {
            return Err(io::Error::other("landlock not enforced"));
        }
        let me = rustix::process::getpid().as_raw_nonzero().get() as u32;
        for ins in self.filters.iter_mut().flatten() {
            if u64::from(ins.k) == SELF {
                ins.k = me;
            }
        }
        for f in &self.filters {
            seccompiler::apply_filter(f).map_err(|_| io::Error::other("seccomp"))?;
        }
        Ok(())
    }
}

/// The command that runs `r.program` confining itself first.
pub(crate) fn command(r: &Resolved) -> Result<Command, ConfineError> {
    let filters = filters()?;
    let ruleset = ruleset(r)?;
    let mut c = Command::new(&r.program);
    c.env_clear();
    let connector = if r.connect.is_empty() {
        None
    } else {
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
        let grants: Vec<(Vec<Vec<u8>>, PathBuf)> = r
            .connect
            .iter()
            .map(|(given, sock)| {
                let names = vec![
                    given.as_os_str().as_bytes().to_vec(),
                    sock.as_os_str().as_bytes().to_vec(),
                ];
                (names, sock.clone())
            })
            .collect();
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
    // descriptor, the BPF programs, the connector descriptor) and allocates nothing on its success
    // path, which is what a child of a multi-threaded parent may do before `execve`.
    #[allow(unsafe_code)]
    unsafe {
        c.pre_exec(move || step.run());
    }
    Ok(c)
}

/// The connector's parent side: answer each ask until every copy of the child's end is closed
/// (the child ended, or the command was dropped unspawned).
fn serve(ours: &OwnedFd, grants: &[(Vec<Vec<u8>>, PathBuf)]) {
    let mut ask = [0u8; ASK_MAX + 1];
    loop {
        let n = match rustix::net::recv(ours, &mut ask, RecvFlags::empty()) {
            Ok((0, _)) | Err(_) => return,
            Ok((n, _)) => n,
        };
        let asked = &ask[..n.min(ask.len())];
        let granted = grants
            .iter()
            .find(|(names, _)| names.iter().any(|g| g.as_slice() == asked));
        let dialed = match granted {
            Some((_, sock)) if n <= ASK_MAX => dial(sock),
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
        if rustix::net::sendmsg(
            ours,
            &[IoSlice::new(&bytes)],
            &mut control,
            SendFlags::empty(),
        )
        .is_err()
        {
            return;
        }
    }
}

/// One non-blocking connect, as `nd_unix_connect` makes it: a full backlog is `EAGAIN` at once.
fn dial(sock: &Path) -> rustix::io::Result<OwnedFd> {
    let fd = rustix::net::socket_with(
        AddressFamily::UNIX,
        SocketType::STREAM,
        SocketFlags::CLOEXEC | SocketFlags::NONBLOCK,
        None,
    )?;
    rustix::net::connect(&fd, &SocketAddrUnix::new(sock)?)?;
    Ok(fd)
}

/// The child's side of the connector: the socket at `path`, if the launcher's policy grants it.
pub(crate) fn ask(connector: &OwnedFd, path: &Path) -> io::Result<OwnedFd> {
    let p = path.as_os_str().as_bytes();
    if p.len() > ASK_MAX {
        return Err(io::Error::from_raw_os_error(libc::ENAMETOOLONG));
    }
    rustix::net::send(connector, p, SendFlags::empty())?;
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
    if got.bytes != 4 {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "connector closed",
        ));
    }
    match (u32::from_le_bytes(code), fd) {
        (0, Some(fd)) => Ok(fd),
        (0, None) => Err(io::Error::other("connector sent no socket")),
        (e, _) => Err(io::Error::from_raw_os_error(e as i32)),
    }
}
