//! The sandbox's negative plant (CLIENT-52): run as a confined child, it ATTEMPTS one operation the
//! policy must refuse and prints what the kernel answered, so `sandbox/tests/probe.rs` can assert
//! that each refusal is the sandbox's (the same operation run unconfined, by the same uid, is not
//! refused). Every target is one the test made: a file in its own scratch tree, or the probe's own
//! parent (the test, or nd-supervise under `deploy/live/confined-unit.sh`). Signals are signal 0
//! (the permission check, nothing delivered), modes and owners are rewritten to what they are.
//!
//! `sandbox-probe OP [ARG]...` prints one line, `ok [DETAIL]` or `refused ERRNO`, and exits 0.
//! `sandbox-probe script FILE OUT` runs each line `NAME OP [ARG]...` of FILE and appends
//! `NAME ok|refused ERRNO` to OUT as it goes (the run under nd-supervise, whose stdout is the
//! frame pipe). The ops:
//! - `chmod`, `fchmodat`, `fchmodat2`, `utimes`, `utimensat`, `chown`, `setxattr` PATH: the
//!   metadata calls Landlock does not mediate, on a file outside the write grant (seccomp: EPERM);
//! - `fchmod` PATH: the same on a file the child may write;
//! - `open` PATH: a read open outside the grants (Landlock: EACCES);
//! - `mkfifo` PATH: a fifo inside the write grant (Landlock: EACCES);
//! - `kill-parent`, `tgkill-parent`, `sigqueue-parent`, `pidfd-parent`, `kill-all`: signal 0 to
//!   the parent, or to every process (seccomp: EPERM);
//! - `setown-parent`, `setown-ex-parent`, `setsig`, `async`: `fcntl` arranging kernel-sent signals
//!   on a pipe (seccomp: EPERM);
//! - `pdeathsig-clear`: `prctl(PR_SET_PDEATHSIG, 0)` (seccomp: EPERM);
//! - `fd` N: `fcntl(N, F_GETFD)` on a descriptor the launcher held open without close-on-exec
//!   (EBADF: the step closed it at exec);
//! - `socket`, `socketpair`, `memfd`, `clone-process`, `io-uring`: what a child may not create;
//! - `connect` PATH: through the connector (`nanodregg_sandbox::connect_unix`), then the server's
//!   first line (`ok LINE`);
//! - `exec-written` DIR: write a copy of this program into DIR (mode 0700 at creation) and exec it
//!   (Landlock: EACCES); the copy, run, prints `ok exec`;
//! - `loader-written` DIR: the same copy handed to the ELF loader as its argument (the loader maps
//!   it: Landlock does not mediate mmap, so standalone it RUNS; a unit's `NoExecPaths` refuses it);
//! - `noop [OUT]`: prints `ok exec`, or appends it to OUT (what a copy runs).
//!
//! It is a plant: it makes raw system calls (one `unsafe` helper) so each attempt is exactly the
//! call named, never a libc fallback.
#![allow(unsafe_code)]

#[cfg(target_os = "linux")]
fn main() -> std::process::ExitCode {
    linux::main()
}

#[cfg(not(target_os = "linux"))]
fn main() -> std::process::ExitCode {
    println!("refused unsupported");
    std::process::ExitCode::from(2)
}

#[cfg(target_os = "linux")]
mod linux {
    use std::ffi::{CString, OsStr, OsString};
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::ffi::OsStrExt;
    use std::path::Path;
    use std::process::ExitCode;

    /// The loader the runtime manifest names (`sandbox/src/linux.rs`, `LOADERS`).
    #[cfg(target_arch = "x86_64")]
    const LOADER: &str = "/lib64/ld-linux-x86-64.so.2";
    #[cfg(target_arch = "aarch64")]
    const LOADER: &str = "/lib/ld-linux-aarch64.so.1";
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    const LOADER: &str = "";

    type R = Result<String, i32>;

    /// `fcntl` commands libc 0.2.190 does not name (asm-generic `fcntl.h`, both arches).
    const F_SETSIG: libc::c_long = 10;
    const F_SETOWN_EX: libc::c_long = 15;

    /// One raw system call; `Err(errno)` on failure.
    fn sys(n: libc::c_long, a: [libc::c_long; 5]) -> Result<libc::c_long, i32> {
        // SAFETY: every caller passes pointers to live, NUL-terminated or correctly sized buffers
        // it owns for the duration of the call (or none); the kernel validates the rest.
        let r = unsafe { libc::syscall(n, a[0], a[1], a[2], a[3], a[4]) };
        if r < 0 {
            Err(std::io::Error::last_os_error().raw_os_error().unwrap_or(0))
        } else {
            Ok(r)
        }
    }

    fn c(p: &OsStr) -> CString {
        CString::new(p.as_bytes()).unwrap_or_default()
    }

    fn name(e: i32) -> String {
        let n = match e {
            libc::EPERM => "EPERM",
            libc::EACCES => "EACCES",
            libc::EBADF => "EBADF",
            libc::ENOSYS => "ENOSYS",
            libc::ENOENT => "ENOENT",
            libc::EINVAL => "EINVAL",
            libc::ESRCH => "ESRCH",
            libc::ELOOP => "ELOOP",
            libc::ENOTTY => "ENOTTY",
            libc::ECONNREFUSED => "ECONNREFUSED",
            libc::ETIMEDOUT => "ETIMEDOUT",
            libc::EOPNOTSUPP => "EOPNOTSUPP",
            libc::EROFS => "EROFS",
            _ => return format!("E{e}"),
        };
        n.to_string()
    }

    fn mode_of(p: &CString) -> Result<libc::c_long, i32> {
        let mut st = std::mem::MaybeUninit::<libc::stat>::zeroed();
        sys(
            libc::SYS_newfstatat,
            [
                libc::AT_FDCWD as _,
                p.as_ptr() as _,
                st.as_mut_ptr() as _,
                0,
                0,
            ],
        )?;
        // SAFETY: newfstatat succeeded, so it filled the buffer.
        let st = unsafe { st.assume_init() };
        Ok(libc::c_long::from(st.st_mode & 0o7777))
    }

    /// A pipe's read end, for the `fcntl` ops.
    fn pipe() -> Result<libc::c_long, i32> {
        let mut fds = [0i32; 2];
        sys(
            libc::SYS_pipe2,
            [fds.as_mut_ptr() as _, libc::O_CLOEXEC as _, 0, 0, 0],
        )?;
        Ok(libc::c_long::from(fds[0]))
    }

    fn parent() -> libc::c_long {
        libc::c_long::from(std::os::unix::process::parent_id())
    }

    /// A copy of this program at DIR/probe-copy, created 0700 (no chmod: the create's mode).
    fn copy_self(dir: &OsStr) -> Result<CString, i32> {
        let me = std::env::args_os().next().unwrap_or_default();
        let bytes = std::fs::read(&me).map_err(|e| e.raw_os_error().unwrap_or(0))?;
        let dst = Path::new(dir).join("probe-copy");
        let d = c(dst.as_os_str());
        let _ = sys(
            libc::SYS_unlinkat,
            [libc::AT_FDCWD as _, d.as_ptr() as _, 0, 0, 0],
        );
        let fd = sys(
            libc::SYS_openat,
            [
                libc::AT_FDCWD as _,
                d.as_ptr() as _,
                (libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_CLOEXEC) as _,
                0o700,
                0,
            ],
        )?;
        let mut off = 0usize;
        while off < bytes.len() {
            let n = sys(
                libc::SYS_write,
                [
                    fd,
                    bytes[off..].as_ptr() as _,
                    (bytes.len() - off) as _,
                    0,
                    0,
                ],
            )?;
            off += n as usize;
        }
        sys(libc::SYS_close, [fd, 0, 0, 0, 0])?;
        Ok(d)
    }

    fn exec(prog: &CString, argv: &[&CString]) -> R {
        let mut v: Vec<*const libc::c_char> = argv.iter().map(|a| a.as_ptr()).collect();
        v.push(std::ptr::null());
        let env: [*const libc::c_char; 1] = [std::ptr::null()];
        // flush before the image is replaced
        let _ = std::io::stdout().flush();
        sys(
            libc::SYS_execve,
            [prog.as_ptr() as _, v.as_ptr() as _, env.as_ptr() as _, 0, 0],
        )?;
        Ok("returned".into())
    }

    fn connect(p: &OsStr) -> R {
        let s = nanodregg_sandbox::connect_unix(Path::new(p))
            .map_err(|e| e.raw_os_error().unwrap_or(libc::EIO))?;
        s.set_read_timeout(Some(std::time::Duration::from_secs(10)))
            .map_err(|e| e.raw_os_error().unwrap_or(libc::EIO))?;
        let mut line = String::new();
        BufReader::new(s)
            .read_line(&mut line)
            .map_err(|e| e.raw_os_error().unwrap_or(libc::EIO))?;
        Ok(line.trim().to_string())
    }

    /// One op; `Ok(detail)` or `Err(errno)`.
    pub(super) fn attempt(op: &str, args: &[OsString], out: Option<&OsStr>) -> R {
        let arg = |i: usize| args.get(i).map(OsString::as_os_str).unwrap_or_default();
        let p = c(arg(0));
        let pp = p.as_ptr() as libc::c_long;
        let at = libc::AT_FDCWD as libc::c_long;
        let me = (
            libc::c_long::from(rustix::process::getuid().as_raw()),
            libc::c_long::from(rustix::process::getgid().as_raw()),
        );
        let ok = |_| String::new();
        match op {
            "noop" => match arg(0) {
                o if o.is_empty() => Ok("exec".into()),
                // the copy run from a script: its result goes where the script's lines go
                o => {
                    let mut f = std::fs::OpenOptions::new()
                        .append(true)
                        .open(o)
                        .map_err(|e| e.raw_os_error().unwrap_or(libc::EIO))?;
                    let _ = writeln!(f, "ok exec");
                    std::process::exit(0)
                }
            },
            #[cfg(target_arch = "x86_64")]
            "chmod" => sys(libc::SYS_chmod, [pp, mode_of(&p).unwrap_or(0o600), 0, 0, 0]).map(ok),
            "fchmodat" => sys(
                libc::SYS_fchmodat,
                [at, pp, mode_of(&p).unwrap_or(0o600), 0, 0],
            )
            .map(ok),
            // fchmodat2 (Linux 6.6), by number: libc 0.2.190 names it on neither arch
            "fchmodat2" => sys(452, [at, pp, mode_of(&p).unwrap_or(0o600), 0, 0]).map(ok),
            "fchmod" => {
                let fd = sys(
                    libc::SYS_openat,
                    [at, pp, (libc::O_RDWR | libc::O_CLOEXEC) as _, 0, 0],
                )?;
                sys(
                    libc::SYS_fchmod,
                    [fd, mode_of(&p).unwrap_or(0o600), 0, 0, 0],
                )
                .map(ok)
            }
            #[cfg(target_arch = "x86_64")]
            "utimes" => sys(libc::SYS_utimes, [pp, 0, 0, 0, 0]).map(ok),
            "utimensat" => sys(libc::SYS_utimensat, [at, pp, 0, 0, 0]).map(ok),
            "chown" => sys(libc::SYS_fchownat, [at, pp, me.0, me.1, 0]).map(ok),
            "setxattr" => {
                let (n, v) = (c(OsStr::new("user.nd-probe")), b"1");
                sys(
                    libc::SYS_setxattr,
                    [pp, n.as_ptr() as _, v.as_ptr() as _, 1, 0],
                )
                .map(ok)
            }
            "open" => sys(
                libc::SYS_openat,
                [at, pp, (libc::O_RDONLY | libc::O_CLOEXEC) as _, 0, 0],
            )
            .map(ok),
            "mkfifo" => sys(
                libc::SYS_mknodat,
                [at, pp, (libc::S_IFIFO | 0o600) as _, 0, 0],
            )
            .map(ok),
            "kill-parent" => sys(libc::SYS_kill, [parent(), 0, 0, 0, 0]).map(ok),
            "kill-all" => sys(libc::SYS_kill, [-1, 0, 0, 0, 0]).map(ok),
            "tgkill-parent" => sys(libc::SYS_tgkill, [parent(), parent(), 0, 0, 0]).map(ok),
            "sigqueue-parent" => {
                let mut info = [0u8; 128];
                // si_signo 0, si_errno 0, si_code SI_QUEUE (-1): a user-queued signal
                info[8..12].copy_from_slice(&(-1i32).to_ne_bytes());
                sys(
                    libc::SYS_rt_sigqueueinfo,
                    [parent(), 0, info.as_ptr() as _, 0, 0],
                )
                .map(ok)
            }
            "pidfd-parent" => sys(libc::SYS_pidfd_open, [parent(), 0, 0, 0, 0]).map(ok),
            "setown-parent" => sys(
                libc::SYS_fcntl,
                [pipe()?, libc::F_SETOWN as _, parent(), 0, 0],
            )
            .map(ok),
            "setown-ex-parent" => {
                // struct f_owner_ex { int type; pid_t pid; }: F_OWNER_PID
                let own: [i32; 2] = [1, parent() as i32];
                sys(
                    libc::SYS_fcntl,
                    [pipe()?, F_SETOWN_EX, own.as_ptr() as _, 0, 0],
                )
                .map(ok)
            }
            "setsig" => sys(
                libc::SYS_fcntl,
                [pipe()?, F_SETSIG, libc::SIGUSR1 as _, 0, 0],
            )
            .map(ok),
            "async" => sys(
                libc::SYS_fcntl,
                [pipe()?, libc::F_SETFL as _, libc::O_ASYNC as _, 0, 0],
            )
            .map(ok),
            "pdeathsig-clear" => {
                sys(libc::SYS_prctl, [libc::PR_SET_PDEATHSIG as _, 0, 0, 0, 0]).map(ok)
            }
            "fd" => {
                let n: libc::c_long = arg(0)
                    .to_str()
                    .and_then(|s| s.parse().ok())
                    .ok_or(libc::EINVAL)?;
                sys(libc::SYS_fcntl, [n, libc::F_GETFD as _, 0, 0, 0]).map(ok)
            }
            "socket" => sys(
                libc::SYS_socket,
                [libc::AF_UNIX as _, libc::SOCK_STREAM as _, 0, 0, 0],
            )
            .map(ok),
            "socketpair" => {
                let mut fds = [0i32; 2];
                sys(
                    libc::SYS_socketpair,
                    [
                        libc::AF_UNIX as _,
                        libc::SOCK_STREAM as _,
                        0,
                        fds.as_mut_ptr() as _,
                        0,
                    ],
                )
                .map(ok)
            }
            "memfd" => {
                let n = c(OsStr::new("nd-probe"));
                sys(
                    libc::SYS_memfd_create,
                    [n.as_ptr() as _, libc::MFD_CLOEXEC as _, 0, 0, 0],
                )
                .map(ok)
            }
            "clone-process" => {
                // a process (SIGCHLD, no CLONE_THREAD); a child that exists exits at once
                let pid = sys(libc::SYS_clone, [libc::SIGCHLD as _, 0, 0, 0, 0])?;
                if pid == 0 {
                    // SAFETY: the forked child leaves at once without touching shared state.
                    unsafe { libc::_exit(0) }
                }
                let _ = sys(libc::SYS_wait4, [pid, 0, 0, 0, 0]);
                Ok(String::new())
            }
            "io-uring" => {
                let params = [0u8; 120];
                sys(libc::SYS_io_uring_setup, [1, params.as_ptr() as _, 0, 0, 0]).map(ok)
            }
            "connect" => connect(arg(0)),
            "exec-written" => {
                let copy = copy_self(arg(0))?;
                let o = c(out.unwrap_or_default());
                exec(&copy, &[&copy, &c(OsStr::new("noop")), &o])
            }
            "loader-written" => {
                let copy = copy_self(arg(0))?;
                let ld = c(OsStr::new(LOADER));
                let o = c(out.unwrap_or_default());
                exec(&ld, &[&ld, &copy, &c(OsStr::new("noop")), &o])
            }
            _ => Err(libc::EINVAL),
        }
    }

    fn line(r: R) -> String {
        match r {
            Ok(d) if d.is_empty() => "ok".into(),
            Ok(d) => format!("ok {d}"),
            Err(e) => format!("refused {}", name(e)),
        }
    }

    pub(super) fn main() -> ExitCode {
        let a: Vec<OsString> = std::env::args_os().skip(1).collect();
        let Some(op) = a.first().and_then(|o| o.to_str()) else {
            return ExitCode::from(2);
        };
        if op == "script" {
            let (Some(file), Some(out)) = (a.get(1), a.get(2)) else {
                return ExitCode::from(2);
            };
            let Ok(text) = std::fs::read_to_string(file) else {
                return ExitCode::from(2);
            };
            let Ok(mut o) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(out)
            else {
                return ExitCode::from(3);
            };
            for l in text.lines() {
                let w: Vec<OsString> = l.split(' ').map(OsString::from).collect();
                let (Some(n), Some(op)) = (w.first(), w.get(1).and_then(|o| o.to_str())) else {
                    continue;
                };
                // written before an exec op replaces the image: the line names what was tried
                let _ = write!(o, "{} ", n.to_string_lossy());
                let _ = o.flush();
                let r = line(attempt(op, &w[2..], Some(out)));
                let _ = writeln!(o, "{r}");
                let _ = o.flush();
            }
            return ExitCode::SUCCESS;
        }
        println!("{}", line(attempt(op, &a[1..], None)));
        ExitCode::SUCCESS
    }
}
