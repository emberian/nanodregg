//! What the process-starting tests share: a supervisor held by its handle, and the python the
//! scripted children run on, with the paths its sandbox policy must allow.
#![allow(clippy::unwrap_used, dead_code)] // a plant that cannot set up is a failed plant
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

/// Stops the supervisor this test started, by its own handle, even when an assertion fails; its
/// stdio is not inherited, so a leaked one could not hold the test runner's pipes either.
pub struct Supervisor(pub Child);
impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// The real python executable and its prefix. The framework python re-execs itself inside its
/// prefix, so the prefix is both `--read` and `--exec`; `-I` keeps the cwd off `sys.path`.
pub fn python() -> (PathBuf, PathBuf) {
    let out = Command::new("python3")
        .args([
            "-I",
            "-c",
            "import os,sys;print(os.path.realpath(sys.executable));print(os.path.realpath(sys.prefix))",
        ])
        .output()
        .unwrap();
    let text = String::from_utf8(out.stdout).unwrap();
    let mut lines = text.lines().map(PathBuf::from);
    (lines.next().unwrap(), lines.next().unwrap())
}

/// `nd-supervise SOCK --hide HIDE --write W… --read/--exec PREFIX -- python -I -c SCRIPT ARG…`,
/// waited on until it binds (10 s deadline, 50 ms sleeps).
pub fn supervise(
    sock: &Path,
    hide: &Path,
    write: &[&Path],
    script: &str,
    args: &[&Path],
) -> Supervisor {
    let (py, prefix) = python();
    let mut c = Command::new(env!("CARGO_BIN_EXE_nd-supervise"));
    c.arg(sock).arg("--hide").arg(hide);
    for w in write {
        c.arg("--write").arg(w);
    }
    c.arg("--read")
        .arg(&prefix)
        .arg("--exec")
        .arg(&prefix)
        .arg("--");
    c.arg(&py).args(["-I", "-c", script]).args(args);
    let s = Supervisor(
        c.stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let deadline = Instant::now() + Duration::from_secs(10);
    while UnixStream::connect(sock).is_err() {
        assert!(
            Instant::now() < deadline,
            "supervisor never bound {}",
            sock.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
    s
}

/// The lake-built Lean `host`: `$ND_HOST_EXE`, else this tree's `.lake/build/bin/host`. Missing,
/// the calling plant FAILS by name (`lake build host`); it never skips.
pub fn lean_host() -> PathBuf {
    let p = std::env::var_os("ND_HOST_EXE").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("../.lake/build/bin/host"),
        PathBuf::from,
    );
    assert!(
        p.is_file(),
        "plant: no lake-built host at {} (run `lake build host`)",
        p.display()
    );
    p.canonicalize().unwrap()
}
