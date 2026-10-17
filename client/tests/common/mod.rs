//! What the client's scripted-child tests share: the python the scripted children run on, with the
//! paths its sandbox policy must allow (the supervisor's holder is devtools').
#![allow(clippy::unwrap_used, dead_code)] // a plant that cannot set up is a failed plant
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub use nanodregg_devtools::Supervisor;
use std::time::{Duration, Instant};

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
    // The mux tells the child each connection's end (`HANGUP`, generated): every script may read
    // it as `HANGUP` and must skip such frames (the wait-for-bind probe above makes one).
    let script = format!("HANGUP = {}\n{script}", nanodregg_client::generated::HANGUP);
    c.arg(&py).args(["-I", "-c", &script]).args(args);
    let mut pid = sock.as_os_str().to_owned();
    pid.push(".pid");
    let s = Supervisor::hold(
        c.stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
        pid.into(),
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
