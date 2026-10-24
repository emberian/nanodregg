//! The test harness every crate's integration tests share (ROOT 2026-10-17, law 1 applied to the
//! harness): one answer to "where is the Lean exe", one to "where are `nd` and `nd-supervise`", one
//! supervised host. Its scope: what a second crate would otherwise copy; what has one caller stays
//! with its caller. Every path is absolute and canonical, and a missing one FAILS the calling test
//! by name (an `assert!` naming the build to run); nothing here ever skips.
//!
//! A dev-dependency only. Its `assert!`s are test failures, which is why it may panic.

use std::cell::RefCell;
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// The repository root (this crate's parent directory).
pub fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// A fresh scratch directory `name` (mode 0700, canonical) under a base whose directory chain the
/// custody reads accept (owned by the euid or root, writable by no one else; sshd's StrictModes):
/// `$ND_SCRATCH`, else `$HOME/.cache/nd-t`. Not `/tmp` (sticky but world-writable) and not a
/// target dir (umask 002 leaves it group-writable on hbox). Short, so a socket path inside fits
/// sun_path. An old directory of the same name is removed first. The creating test thread removes
/// its scratch directories when it exits, including after a test panic.
struct ScratchDirs(RefCell<Vec<PathBuf>>);

impl Drop for ScratchDirs {
    fn drop(&mut self) {
        for path in self.0.get_mut().drain(..).rev() {
            let _ = std::fs::remove_dir_all(path);
        }
    }
}

thread_local! {
    static SCRATCH_DIRS: ScratchDirs = const { ScratchDirs(RefCell::new(Vec::new())) };
}

/// Create a guarded scratch directory for the current test thread.
pub fn scratch(name: &str) -> PathBuf {
    let base = std::env::var_os("ND_SCRATCH").map_or_else(
        || {
            let home = std::env::var_os("HOME").unwrap_or_default();
            assert!(
                !home.is_empty(),
                "plant: no HOME and no ND_SCRATCH for scratch"
            );
            PathBuf::from(home).join(".cache/nd-t")
        },
        PathBuf::from,
    );
    let d = base.join(name);
    let _ = std::fs::remove_dir_all(&d);
    let made = mkdirs(&d);
    assert!(made.is_ok(), "plant: scratch {}: {made:?}", d.display());
    let d = canonical(&d);
    SCRATCH_DIRS.with(|dirs| dirs.0.borrow_mut().push(d.clone()));
    d
}

/// `mkdir -p` with every created directory mode 0700 (whatever the umask), so a test's workspace
/// passes the custody reads' directory-chain check.
pub fn mkdirs(p: &Path) -> std::io::Result<()> {
    std::fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(p)
}

/// The lake-built Lean exe `name`: `$ND_LEAN_BIN/name` (gates/runs.py sets it to the judged tree's
/// bin directory), else this tree's `.lake/build/bin/name`. Missing FAILS by name.
pub fn lean_bin(name: &str) -> PathBuf {
    let dir = std::env::var_os("ND_LEAN_BIN")
        .map_or_else(|| repo().join(".lake/build/bin"), PathBuf::from);
    lean_bin_in(&dir, name)
}

/// The Lean exe `name` in the bin directory `dir`; missing FAILS by name.
pub fn lean_bin_in(dir: &Path, name: &str) -> PathBuf {
    let p = dir.join(name);
    assert!(
        p.is_file(),
        "plant: no lake-built {name} at {} (run `lake build {name}`)",
        p.display()
    );
    canonical(&p)
}

fn canonical(p: &Path) -> PathBuf {
    match p.canonicalize() {
        Ok(c) => c,
        Err(e) => panic!("plant: {}: {e}", p.display()),
    }
}

/// How long building the client binaries may take before the calling test fails `buildTimedOut`
/// (a liveness deadline under a loaded judge slot, not a measurement).
pub const BUILD_DEADLINE: Duration = Duration::from_secs(900);

/// The client binaries, built once per test process from this tree's sources into their own
/// target directory (`<target>/devtools-bins`), so they are never stale and the build never waits
/// on the outer `cargo test`'s lock. A failed build FAILS by name with cargo's stderr tail.
fn client_bins() -> &'static Path {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let target = std::env::var_os("CARGO_TARGET_DIR")
            .map_or_else(|| repo().join("target"), PathBuf::from)
            .join("devtools-bins");
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| env!("CARGO").into());
        let child = Command::new(cargo)
            .args(["build", "--offline", "--quiet", "-p", "nanodregg-client"])
            .args(["--bin", "nd", "--bin", "nd-supervise", "--target-dir"])
            .arg(&target)
            .current_dir(repo())
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn();
        let mut child = match child {
            Ok(c) => c,
            Err(e) => panic!("buildFailed: cargo did not start: {e}"),
        };
        let mut err = child.stderr.take();
        let reader = std::thread::spawn(move || {
            let mut text = String::new();
            if let Some(e) = err.as_mut() {
                let _ = std::io::Read::read_to_string(e, &mut text);
            }
            text
        });
        let deadline = Instant::now() + BUILD_DEADLINE;
        let status = loop {
            match child.try_wait() {
                Ok(Some(st)) => break Some(st),
                Ok(None) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(200))
                }
                _ => break None,
            }
        };
        if status.is_none() {
            let _ = child.kill();
            let _ = child.wait();
        }
        let text = reader.join().unwrap_or_default();
        let tail: Vec<&str> = text.lines().rev().take(30).collect();
        let tail = tail.into_iter().rev().collect::<Vec<_>>().join("\n");
        match status {
            Some(st) if st.success() => target.join("debug"),
            Some(st) => panic!("buildFailed: nd and nd-supervise ({st}):\n{tail}"),
            None => panic!("buildTimedOut: nd and nd-supervise past {BUILD_DEADLINE:?}:\n{tail}"),
        }
    })
}

/// The `nd` built from this tree.
pub fn nd() -> PathBuf {
    client_bin("nd")
}

/// The `nd-supervise` built from this tree.
pub fn nd_supervise() -> PathBuf {
    client_bin("nd-supervise")
}

fn client_bin(name: &str) -> PathBuf {
    let p = client_bins().join(name);
    assert!(p.is_file(), "plant: no {name} at {}", p.display());
    canonical(&p)
}

/// A process this test started, stopped by its own handle when dropped, even when an assertion
/// fails. Its pid is also in `pid_file` while it lives, so a test process that dies without
/// dropping it leaves the pid for a human, never a pattern to kill by.
pub struct Supervisor {
    child: Child,
    pid_file: PathBuf,
}

impl Supervisor {
    /// Hold `child`, writing its pid to `pid_file`.
    pub fn hold(child: Child, pid_file: PathBuf) -> Self {
        let wrote = std::fs::write(&pid_file, format!("{}\n", child.id()));
        let s = Self { child, pid_file };
        assert!(
            wrote.is_ok(),
            "plant: pid file {}: {wrote:?}",
            s.pid_file.display()
        );
        s
    }
}

impl Supervisor {
    /// The held process, for a test that wires its stdio itself.
    pub fn child(&mut self) -> &mut Child {
        &mut self.child
    }
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = std::fs::remove_file(&self.pid_file);
    }
}

/// `nd-supervise SOCK --hide HIDE --write STORE --exec HOST -- HOST ARGS…` with the given
/// `nd-supervise` (a client test passes its own `CARGO_BIN_EXE`, any other crate
/// [`nd_supervise`]), null stdio, pid in `SOCK.pid`; waited on until it binds. Not bound within
/// 20 s FAILS by name (`neverBound`), a liveness deadline, not a measurement.
pub fn supervise_host(
    nd_supervise: &Path,
    sock: &Path,
    hide: &Path,
    store: &Path,
    args: &[&str],
) -> Supervisor {
    let host = lean_bin("host");
    let child = Command::new(nd_supervise)
        .arg(sock)
        .arg("--hide")
        .arg(hide)
        .arg("--write")
        .arg(store)
        .arg("--exec")
        .arg(&host)
        .arg("--")
        .arg(&host)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn();
    let child = match child {
        Ok(c) => c,
        Err(e) => panic!("plant: {}: {e}", nd_supervise.display()),
    };
    let mut pid = sock.as_os_str().to_owned();
    pid.push(".pid");
    let s = Supervisor::hold(child, pid.into());
    let deadline = Instant::now() + Duration::from_secs(20);
    while UnixStream::connect(sock).is_err() {
        assert!(
            Instant::now() < deadline,
            "neverBound: the supervisor never bound {}",
            sock.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
    s
}

/// One process as `/proc` saw it: its pid and its start time (clock ticks after boot), so a pid the
/// kernel has since given to another process is never taken for it (CLIENT-38's plants).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proc {
    /// The pid.
    pub pid: u32,
    /// `/proc/PID/stat` field 22.
    pub start: u64,
}

/// `(ppid, start, zombie)` of `pid` from `/proc/PID/stat`, `None` when it is gone. The fields after
/// the command name (which may hold spaces and parentheses) start after its last `)`.
fn stat(pid: u32) -> Option<(u32, u64, bool)> {
    let s = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    let rest = s.get(s.rfind(')')? + 2..)?;
    let f: Vec<&str> = rest.split(' ').collect();
    Some((
        f.get(1)?.parse().ok()?,
        f.get(19)?.parse().ok()?,
        f.first() == Some(&"Z"),
    ))
}

/// Every live descendant of `pid` (its children, theirs, …) from one walk of `/proc`. Linux only:
/// a plant that cannot walk `/proc` FAILS by name.
pub fn descendants(pid: u32) -> Vec<Proc> {
    let entries = std::fs::read_dir("/proc");
    assert!(entries.is_ok(), "plant: /proc: {entries:?}");
    let all: Vec<(u32, u32, u64)> = entries
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| e.file_name().to_str()?.parse::<u32>().ok())
        .filter_map(|p| stat(p).filter(|s| !s.2).map(|(pp, st, _)| (p, pp, st)))
        .collect();
    let mut out: Vec<Proc> = Vec::new();
    let mut frontier = vec![pid];
    while let Some(parent) = frontier.pop() {
        for &(p, pp, start) in &all {
            if pp == parent && !out.iter().any(|o| o.pid == p) {
                out.push(Proc { pid: p, start });
                frontier.push(p);
            }
        }
    }
    out
}

/// Whether `p` is still that process and not a zombie.
pub fn alive(p: Proc) -> bool {
    stat(p.pid).is_some_and(|(_, start, zombie)| start == p.start && !zombie)
}

/// The processes of `procs` still alive after waiting up to `within` (polled every 50 ms).
pub fn survivors(procs: &[Proc], within: Duration) -> Vec<Proc> {
    let deadline = Instant::now() + within;
    loop {
        let left: Vec<Proc> = procs.iter().copied().filter(|&p| alive(p)).collect();
        if left.is_empty() || Instant::now() >= deadline {
            return left;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Stop each of `procs` that is still the process it was (pid AND start time): a plant's teardown
/// of the processes it started, by their own pids, never by a pattern.
pub fn stop_all(procs: &[Proc]) {
    for &p in procs {
        if let (true, Some(pid)) = (
            alive(p),
            rustix::process::Pid::from_raw(i32::try_from(p.pid).unwrap_or(0)),
        ) {
            let _ = rustix::process::kill_process(pid, rustix::process::Signal::KILL);
        }
    }
}

/// The scratch directories this thread made ([`scratch`]), for a process whose own guard will
/// never run (one a plant kills by SIGKILL) to hand to the plant that removes them.
pub fn scratch_dirs() -> Vec<PathBuf> {
    SCRATCH_DIRS.with(|d| d.0.borrow().clone())
}
