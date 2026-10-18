//! Host.Sock's contracts (`Host/c/sock.c`, HOST-52), each by name (`cargo:launcher:sock`). The Lean
//! `host-sock-probe` is the client. This test holds the peer, a listener that does one thing per
//! case, and reads the probe's lines (`connect ok`, `wN ok`, `rN M`, `<step> err <text>`, then
//! `alive`).
//!
//! Refuses:
//! - EOF: a peer that closes gives a read of 0 bytes (`r16 0`), never an error.
//! - timeout: a peer holds the connection and sends nothing. The read ends `timeout` within the
//!   probe's 400 ms deadline.
//! - EINTR: glibc's SIGSETXID (33), which every Lean exe catches (HOST-14 measured SigCgt), is sent
//!   to each of the probe's threads every 200 ms while it reads from a silent peer with a 1500 ms
//!   deadline. The read still ends exactly `timeout`, no sooner than the deadline and less than
//!   1 s after it. Two hand mutations go red here, quoted in HOST-52: reporting EINTR
//!   (`poll: Interrupted system call (errno 4)`), and restarting the deadline per retry (the
//!   elapsed bound breaks).
//! - read max 0 is refused `readMaxZero`, so an empty read means only EOF. Above 16 MiB is refused
//!   `readMaxPastBound`.
//! - paths, before any socket is made: the empty path is `pathEmpty`; a path with a NUL is
//!   `pathNul`; a path of exactly sizeof(sun_path) = 108 bytes is `pathTooLong` and creates
//!   nothing. CONTROL: 107 bytes connects.
//! - a zero timeout is refused `timeoutZero` at connect.
//! - a peer that shuts its reading side mid-write: an 8 MiB write ends exactly
//!   `send: Broken pipe (errno 32)`, and the probe prints `alive` and exits 0. Lean's runtime
//!   already ignores SIGPIPE (measured), so this pins the composite. It is not a tooth for
//!   MSG_NOSIGNAL, which sock.c keeps so as not to rest on a runtime internal.
//! - an absent path gives `connect: … (errno 2)`.
//! - a full backlog: a listener with backlog 1 that never accepts. Linux queues backlog + 1
//!   connects and answers the next non-blocking AF_UNIX connect at once with
//!   `connect: … (errno 11)`, well inside the probe's 2000 ms deadline. CONTROL: at least one
//!   connect is queued first.
//! - CONTROL: an echo peer gives `w4 ok`, `r4 4`, so each refusal above belongs to its own case.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

use std::io::{Read, Write};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use nanodregg_devtools::lean_bin;
use rustix::net::{AddressFamily, SocketAddrUnix, SocketType};

/// A scratch directory short enough for socket paths, removed on drop.
struct Dir(PathBuf);

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn dir() -> Dir {
    let d = nanodregg_devtools::scratch(&format!("sk{}", std::process::id()));
    assert!(
        d.as_os_str().len() < 80,
        "plant: {} is too long",
        d.display()
    );
    Dir(d)
}

/// Run the probe against `path` with timeout `ms`: its stdout lines and its exit code.
fn probe(path: &Path, ms: u32, ops: &[&str]) -> (Vec<String>, Option<i32>) {
    let o = Command::new(lean_bin("host-sock-probe"))
        .arg(path)
        .arg(ms.to_string())
        .args(ops)
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&o.stdout);
    (out.lines().map(str::to_owned).collect(), o.status.code())
}

/// A listener at `d/name` whose first accepted connection is handed to `peer` on its own thread.
fn listen(d: &Path, name: &str, peer: fn(UnixStream)) -> PathBuf {
    let p = d.join(name);
    let l = UnixListener::bind(&p).unwrap();
    thread::spawn(move || {
        if let Ok((c, _)) = l.accept() {
            peer(c);
        }
    });
    p
}

fn hold(c: UnixStream) {
    thread::sleep(Duration::from_secs(4));
    drop(c);
}

/// Send signal 33 to every thread of `pid`; how many sends succeeded.
fn sigsetxid(pid: u32) -> usize {
    let Ok(tasks) = std::fs::read_dir(format!("/proc/{pid}/task")) else {
        return 0;
    };
    tasks
        .filter_map(Result::ok)
        .filter(|t| {
            Command::new("/usr/bin/kill")
                .args(["-s", "33"])
                .arg(t.file_name())
                .stderr(Stdio::null())
                .status()
                .is_ok_and(|s| s.success())
        })
        .count()
}

#[test]
fn host_sock_contracts_by_name() {
    let d = dir();
    let d = &d.0;

    // CONTROL: an echo peer
    let p = listen(d, "echo", |mut c| {
        let mut b = [0u8; 4];
        if c.read_exact(&mut b).is_ok() {
            let _ = c.write_all(&b);
        }
        thread::sleep(Duration::from_millis(500));
    });
    let (l, code) = probe(&p, 2000, &["w4", "r4"]);
    assert_eq!(
        l,
        ["connect ok", "w4 ok", "r4 4", "alive"],
        "control: the echo"
    );
    assert_eq!(code, Some(0));

    // EOF
    let p = listen(d, "eof", drop::<UnixStream>);
    let (l, _) = probe(&p, 2000, &["r16"]);
    assert_eq!(l, ["connect ok", "r16 0", "alive"], "EOF is an empty read");

    // timeout, bounded by the deadline
    let p = listen(d, "hold", hold);
    let t = Instant::now();
    let (l, _) = probe(&p, 400, &["r16"]);
    assert_eq!(
        l,
        ["connect ok", "r16 err timeout", "alive"],
        "a silent peer"
    );
    assert!(
        t.elapsed() < Duration::from_millis(2500),
        "the read outlived its deadline: {:?}",
        t.elapsed()
    );

    // EINTR: retried on what is left of the deadline
    let p = listen(d, "intr", hold);
    let t = Instant::now();
    let child = Command::new(lean_bin("host-sock-probe"))
        .arg(&p)
        .arg("1500")
        .arg("r16")
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut sent = 0;
    for _ in 0..6 {
        thread::sleep(Duration::from_millis(200));
        sent += sigsetxid(child.id());
    }
    let o = child.wait_with_output().unwrap();
    let took = t.elapsed();
    let lines: Vec<String> = String::from_utf8_lossy(&o.stdout)
        .lines()
        .map(str::to_owned)
        .collect();
    assert!(
        sent >= 3,
        "EINTR control: signal 33 reached the probe {sent} times"
    );
    assert_eq!(
        lines,
        ["connect ok", "r16 err timeout", "alive"],
        "EINTR: a signalled read"
    );
    assert_eq!(o.status.code(), Some(0), "EINTR: the probe died");
    assert!(
        took >= Duration::from_millis(1500) && took < Duration::from_millis(2500),
        "EINTR: the deadline did not hold across retries: {took:?}"
    );

    // read sizes
    let p = listen(d, "zero", hold);
    let (l, _) = probe(&p, 400, &["r0"]);
    assert_eq!(l, ["connect ok", "r0 err readMaxZero", "alive"]);
    let p = listen(d, "big", hold);
    let (l, _) = probe(&p, 400, &["r16777217"]);
    assert_eq!(l, ["connect ok", "r16777217 err readMaxPastBound", "alive"]);

    // paths, refused before any socket is made; CONTROL: 107 bytes connects
    let (l, _) = probe(Path::new(""), 400, &[]);
    assert_eq!(l, ["connect err pathEmpty", "alive"]);
    let (l, _) = probe(
        Path::new(&format!("nul:{}", d.join("echo").display())),
        400,
        &[],
    );
    assert_eq!(l, ["connect err pathNul", "alive"]);
    let base = d.display().to_string().len() + 1;
    let fits = d.join("f".repeat(107 - base));
    assert_eq!(fits.as_os_str().len(), 107);
    let _l = UnixListener::bind(&fits).unwrap();
    let (l, _) = probe(&fits, 400, &[]);
    assert_eq!(
        l,
        ["connect ok", "alive"],
        "control: a 107-byte path connects"
    );
    let long = d.join("x".repeat(108 - base));
    assert_eq!(long.as_os_str().len(), 108);
    let (l, _) = probe(&long, 400, &["r1"]);
    assert_eq!(l, ["connect err pathTooLong", "alive"]);
    assert!(
        std::fs::symlink_metadata(&long).is_err(),
        "an overlong path left something behind"
    );

    // a zero timeout
    let (l, _) = probe(&fits, 0, &[]);
    assert_eq!(l, ["connect err timeoutZero", "alive"]);

    // a peer that shuts its reading side mid-write: EPIPE, named; the process lives
    let p = listen(d, "half", |mut c| {
        let mut b = [0u8; 10];
        let _ = c.read_exact(&mut b);
        let _ = c.shutdown(Shutdown::Read);
        thread::sleep(Duration::from_secs(4));
    });
    let (l, code) = probe(&p, 5000, &["w8388608"]);
    assert_eq!(
        l,
        [
            "connect ok",
            "w8388608 err send: Broken pipe (errno 32)",
            "alive"
        ],
        "mid-write"
    );
    assert_eq!(code, Some(0), "mid-write: the process did not exit 0");

    // an absent path
    let (l, _) = probe(&d.join("absent"), 400, &["r1"]);
    assert_eq!(
        l,
        [
            "connect err connect: No such file or directory (errno 2)",
            "alive"
        ]
    );

    // a full backlog: refused at once, not at the deadline
    let p = d.join("full");
    let fd = rustix::net::socket(AddressFamily::UNIX, SocketType::STREAM, None).unwrap();
    rustix::net::bind(&fd, &SocketAddrUnix::new(&p).unwrap()).unwrap();
    rustix::net::listen(&fd, 1).unwrap();
    let mut refused = None;
    for i in 0..8 {
        let t = Instant::now();
        let (l, _) = probe(&p, 2000, &[]);
        if l.first().is_some_and(|f| f.starts_with("connect err")) {
            refused = Some((i, l, t.elapsed()));
            break;
        }
        assert_eq!(l, ["connect ok", "alive"], "backlog: connect {i}");
    }
    let (i, l, took) = refused.expect("backlog: eight connects all queued on a backlog of 1");
    assert!(
        i >= 1,
        "backlog control: no connect queued before the refusal"
    );
    assert_eq!(
        l,
        [
            "connect err connect: Resource temporarily unavailable (errno 11)",
            "alive"
        ],
        "backlog"
    );
    assert!(
        took < Duration::from_millis(1500),
        "backlog: the refusal waited for the deadline: {took:?}"
    );
    drop(fd);
}
