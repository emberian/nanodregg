//! CLIENT-38 (A19): a process of ours dies with the parent that spawned it. nd-supervise is started
//! by an intermediate `sh` (as a test process or nd-members starts it), with a confined child; the
//! `sh` is killed by SIGKILL, so nothing unwinds and no `Drop` runs, which is how the 336
//! supervisors of 10-23 were left. Within the bound, nd-supervise and every process under it are
//! gone. Before CLIENT-38 they lived on (the plant: drop `die_with_parent` from nd-supervise).
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant

use std::io::{BufRead, BufReader};
use std::os::unix::net::UnixStream;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use nanodregg_devtools::{descendants, nd_supervise, scratch, stop_all, survivors};

#[test]
fn a_supervisor_whose_parent_is_killed_ends_with_its_child() {
    let d = scratch(&format!("orph{}", std::process::id()));
    let sock = d.join("s.sock");
    let hide = d.join("hidden");
    nanodregg_devtools::mkdirs(&hide).unwrap();
    // `sh` stands for the parent: it starts nd-supervise in the background, prints its pid, waits.
    let mut sh = Command::new("/bin/sh")
        .arg("-c")
        .arg("\"$@\" </dev/null >/dev/null 2>&1 & echo $!; wait")
        .arg("sh")
        .arg(nd_supervise())
        .arg(&sock)
        .arg("--hide")
        .arg(&hide)
        .args(["--exec", "/usr/bin/sleep", "--", "/usr/bin/sleep", "600"])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(sh.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    let sup: u32 = line.trim().parse().unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    while UnixStream::connect(&sock).is_err() {
        assert!(Instant::now() < deadline, "neverBound: {}", sock.display());
        std::thread::sleep(Duration::from_millis(50));
    }
    let tree = descendants(sh.id());
    assert!(
        tree.iter().any(|p| p.pid == sup) && tree.len() >= 2,
        "plant: nd-supervise {sup} and its confined child under sh: {tree:?}"
    );
    sh.kill().unwrap();
    sh.wait().unwrap();
    let left = survivors(&tree, Duration::from_secs(10));
    stop_all(&left);
    assert!(
        left.is_empty(),
        "outlived their killed parent: {left:?} of {tree:?}"
    );
}

/// CLIENT-38's second finding (MEASURED): nd-supervise's SIGTERM thread printed its first line with
/// `eprintln!`, which panics when stderr has no reader (its parent died, and the parent held the
/// pipe), so the thread died before it stopped the child and nd-supervise ran on. With the reader
/// gone, SIGTERM still ends it, by SIGTERM (CLIENT-30), within the bound.
#[test]
fn sigterm_stops_a_supervisor_whose_stderr_has_no_reader() {
    let d = scratch(&format!("orpe{}", std::process::id()));
    let sock = d.join("s.sock");
    let hide = d.join("hidden");
    nanodregg_devtools::mkdirs(&hide).unwrap();
    let mut sup = Command::new(nd_supervise())
        .arg(&sock)
        .arg("--hide")
        .arg(&hide)
        .args(["--exec", "/usr/bin/sleep", "--", "/usr/bin/sleep", "600"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    while UnixStream::connect(&sock).is_err() {
        assert!(Instant::now() < deadline, "neverBound: {}", sock.display());
        std::thread::sleep(Duration::from_millis(50));
    }
    let tree = descendants(sup.id());
    drop(sup.stderr.take());
    let pid = rustix::process::Pid::from_raw(i32::try_from(sup.id()).unwrap()).unwrap();
    rustix::process::kill_process(pid, rustix::process::Signal::TERM).unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    let status = loop {
        if let Some(s) = sup.try_wait().unwrap() {
            break Some(s);
        }
        if Instant::now() >= deadline {
            break None;
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    if status.is_none() {
        let _ = sup.kill();
        let _ = sup.wait();
    }
    stop_all(&survivors(&tree, Duration::from_secs(5)));
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(
        status.and_then(|s| s.signal()),
        Some(15),
        "nd-supervise did not end by SIGTERM with no stderr reader: {status:?}"
    );
}
