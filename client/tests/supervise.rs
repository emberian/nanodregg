//! The supervisor end to end: `nd-supervise` binds a socket, confines a child, and routes frames.
//! The child here answers each request with whether IT could read the member's seed — the
//! CLIENT-8 plant through the real binary: the answer must be "denied".
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::net::UnixStream;
use std::process::Command;
use std::time::Duration;

use nanodregg_client::{frame, table};

mod common;

const CHILD: &str = r#"
import struct, sys
seed = sys.argv[1]
i, o = sys.stdin.buffer, sys.stdout.buffer
while True:
    h = i.read(4)
    if len(h) < 4: break
    body = i.read(struct.unpack('<I', h)[0])
    conn, op = body[:4], body[4]
    if op == HANGUP: continue
    try:
        open(seed, 'rb').read(); answer = b'read'
    except OSError:
        answer = b'denied'
    out = conn + bytes([op + 1]) + answer
    o.write(struct.pack('<I', len(out)) + out); o.flush()
"#;

#[test]
fn supervised_child_answers_and_cannot_read_the_seed() {
    let ws = std::env::temp_dir().join(format!("nd-sup-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let ws = ws.canonicalize().unwrap();
    std::fs::write(ws.join("seed"), b"SEED").unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-{}.sock", std::process::id()));
    let _sup = common::supervise(&sock, &ws, &[], CHILD, &[&ws.join("seed")]);
    let mut c = UnixStream::connect(&sock).unwrap();
    c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    frame::write(&mut c, table::LIMITS, 5, b"").unwrap();
    let reply = frame::read(&mut c, table::LIMITS).unwrap();
    assert_eq!(reply.op, 6, "the reply came back on the asking connection");
    assert_eq!(reply.payload, b"denied", "isolation: child read the seed");
    let _ = std::fs::remove_file(&sock);
    std::fs::remove_dir_all(&ws).unwrap();
}

#[test]
fn nothing_hidden_is_refused() {
    let out = Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
        .args(["/tmp/nd-never.sock", "--", "/bin/true"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("nothing hidden"));
    assert_eq!(
        out.status.code(),
        Some(i32::from(
            nanodregg_client::generated::supervisor_exit::REFUSED_AT_LAUNCH
        )),
        "the supervisor's own exit is Protocol.Exit's, so a unit prevents its restart"
    );
}

/// The lake-built `host` this tree deploys (devtools' `lean_bin`). Missing is a failed plant,
/// never a skip: a confinement plant that ran no Lean child proves nothing about one.
/// The confinement plant runs a LEAN child (ASSEMBLY-perf ID-1). The real `host serve`, under
/// the real `nd-supervise`, must answer a frame within 3 s. Measured 2026-10-16 on 87c721e: under
/// the macOS FLOOR it answered nothing and still exited 0 at EOF, so every rc-only check passed;
/// the Lean runtime's thread count came from sysctl `hw.ncpu`, which `(deny default)` refuses.
/// Silence is the failure this names; any reply (a refusal included) passes.
#[test]
fn a_confined_lean_host_answers_within_the_deadline() {
    let host = nanodregg_devtools::lean_bin("host");
    let ws = std::env::temp_dir().join(format!("nd-sup-lean-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir_all(ws.join("ws")).unwrap();
    let ws = ws.canonicalize().unwrap();
    let store = ws.join("store");
    let g = Command::new(&host)
        .arg("genesis")
        .arg(&store)
        .arg("plant")
        .output()
        .unwrap();
    assert!(g.status.success(), "plant: genesis failed: {g:?}");
    let sock = std::env::temp_dir().join(format!("nd-sup-lean-{}.sock", std::process::id()));
    let mut c = Command::new(env!("CARGO_BIN_EXE_nd-supervise"));
    c.arg(&sock)
        .arg("--hide")
        .arg(ws.join("ws"))
        .arg("--exec")
        .arg(&host)
        .arg("--write")
        .arg(&store)
        .arg("--")
        .arg(&host)
        .arg("serve")
        .arg(&store);
    let mut pid = sock.as_os_str().to_owned();
    pid.push(".pid");
    let _sup = common::Supervisor::hold(
        c.stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap(),
        pid.into(),
    );
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    let mut conn = loop {
        if let Ok(s) = UnixStream::connect(&sock) {
            break s;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "supervisor never bound {}",
            sock.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    };
    conn.set_read_timeout(Some(Duration::from_secs(3))).unwrap();
    let t = std::time::Instant::now();
    frame::write(
        &mut conn,
        table::LIMITS,
        nanodregg_client::generated::host_op::READ,
        b"",
    )
    .unwrap();
    let reply = frame::read(&mut conn, table::LIMITS);
    let ms = t.elapsed().as_secs_f64() * 1e3;
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_dir_all(&ws);
    assert!(
        reply.is_ok(),
        "SILENT HANG: confined Lean host gave no reply within 3 s ({:?})",
        reply.err()
    );
    eprintln!("confined lean host replied in {ms:.1} ms");
}

/// A confined child killed by a signal ends the supervisor `childSignaled` (66), whatever the
/// mechanism (OPS-2 measured bwrap turning it into exit 128 + N; self-confined, the death reaches the
/// supervisor as the signal, CLIENT-48). The child kills itself with SIGKILL before reading a frame.
#[test]
fn a_confined_child_killed_by_a_signal_is_child_signaled() {
    let ws = std::env::temp_dir().join(format!("nd-sup-sig-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let ws = ws.canonicalize().unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-sig-{}.sock", std::process::id()));
    let out = Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
        .arg(&sock)
        .args(["--hide"])
        .arg(&ws)
        .args(["--exec", "/bin/sh", "--", "/bin/sh", "-c", "kill -KILL $$"])
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&sock);
    std::fs::remove_dir_all(&ws).unwrap();
    assert_eq!(
        out.status.code(),
        Some(i32::from(
            nanodregg_client::generated::supervisor_exit::CHILD_SIGNALED
        )),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// `nd-supervise SOCK [--group G] --hide WS --exec /usr/bin/cat -- /usr/bin/cat`, waited on until it
/// binds or exits; the exit status and stderr when it exits first.
fn launch_group(
    sock: &std::path::Path,
    ws: &std::path::Path,
    group: Option<u32>,
) -> Result<common::Supervisor, (Option<i32>, String)> {
    let mut c = Command::new(env!("CARGO_BIN_EXE_nd-supervise"));
    c.arg(sock);
    if let Some(g) = group {
        c.arg("--group").arg(g.to_string());
    }
    c.arg("--hide")
        .arg(ws)
        .args(["--exec", "/usr/bin/cat", "--", "/usr/bin/cat"]);
    let mut child = c
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    loop {
        if let Some(st) = child.try_wait().unwrap() {
            let mut e = String::new();
            std::io::Read::read_to_string(&mut child.stderr.take().unwrap(), &mut e).unwrap();
            return Err((st.code(), e));
        }
        if UnixStream::connect(sock).is_ok() {
            let mut pid = sock.as_os_str().to_owned();
            pid.push(".pid");
            return Ok(common::Supervisor::hold(child, pid.into()));
        }
        assert!(
            std::time::Instant::now() < deadline,
            "neverBound: {}",
            sock.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// HOSTING-17 §7: with `--group G` the socket is 0660 group G, only in a shared (02710, ours,
/// group G) directory; a non-setgid directory, another group, or a missing directory is refused at
/// launch by name. Control: without `--group` the socket is 0600.
#[test]
fn a_group_socket_binds_0660_only_in_a_shared_directory_of_that_group() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let root = nanodregg_devtools::scratch(&format!("sup-grp-{}", std::process::id()));
    let ws = root.join("ws");
    nanodregg_devtools::mkdirs(&ws).unwrap();
    let shared = root.join("f");
    nanodregg_devtools::mkdirs(&shared).unwrap();
    std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o2710)).unwrap();
    let g = std::fs::metadata(&shared).unwrap().gid();
    let sock = shared.join("follow.sock");
    let held = launch_group(&sock, &ws, Some(g))
        .map_err(|e| format!("{e:?}"))
        .unwrap();
    let m = std::fs::symlink_metadata(&sock).unwrap();
    assert_eq!((m.permissions().mode() & 0o7777, m.gid()), (0o660, g));
    drop(held);
    // Each refusal names a socket nothing has ever bound, so only the refused supervisor could
    // listen there. Reusing the held one's path raced (CLIENT-28 follow-up): it accepts
    // before it spawns its child, and killed mid-spawn its half-forked child holds the listener
    // until exec, so a connect to the stale path could succeed and read as "launched".
    let refused = |dir: &std::path::Path, group: u32, name: &str| {
        let sock = dir.join(format!("{name}.sock"));
        let (code, err) = launch_group(&sock, &ws, Some(group))
            .err()
            .unwrap_or_else(|| panic!("plant: {} launched", dir.display()));
        assert!(
            !sock.exists(),
            "{name}: refused, yet {} was bound",
            sock.display()
        );
        assert_eq!(
            code,
            Some(i32::from(
                nanodregg_client::generated::supervisor_exit::REFUSED_AT_LAUNCH
            ))
        );
        assert!(err.contains(name), "{name}: {err}");
    };
    refused(&shared, g + 1, "groupMismatch");
    let plain = root.join("p");
    nanodregg_devtools::mkdirs(&plain).unwrap();
    std::fs::set_permissions(&plain, std::fs::Permissions::from_mode(0o710)).unwrap();
    refused(&plain, g, "sharedDirRefused");
    refused(&root.join("missing"), g, "sharedDirRefused");
    // Control: the default is owner-only.
    let own = root.join("o");
    nanodregg_devtools::mkdirs(&own).unwrap();
    let held = launch_group(&own.join("s.sock"), &ws, None)
        .map_err(|e| format!("{e:?}"))
        .unwrap();
    assert_eq!(
        std::fs::symlink_metadata(own.join("s.sock"))
            .unwrap()
            .permissions()
            .mode()
            & 0o7777,
        0o600
    );
    drop(held);
    let _ = std::fs::remove_dir_all(&root);
}

/// HOSTING-20: `--peer UID` (with `--group GID`) admits only a peer whose (uid, gid) is (UID, GID);
/// any other connection is closed `peerRefused` before a frame is read. Control: our own uid is
/// served. `--peer` without `--group` refuses to launch.
#[test]
fn a_peer_outside_uid_and_group_is_closed_peer_refused() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let root = nanodregg_devtools::scratch(&format!("sup-peer-{}", std::process::id()));
    let (ws, shared) = (root.join("ws"), root.join("p"));
    nanodregg_devtools::mkdirs(&ws).unwrap();
    nanodregg_devtools::mkdirs(&shared).unwrap();
    std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o2710)).unwrap();
    let me = std::fs::metadata(&shared).unwrap();
    let run = |peer: u32, name: &str| {
        let sock = shared.join(name);
        let child = Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
            .arg(&sock)
            .args([
                "--group",
                &me.gid().to_string(),
                "--peer",
                &peer.to_string(),
            ])
            .arg("--hide")
            .arg(&ws)
            .args(["--exec", "/usr/bin/cat", "--", "/usr/bin/cat"])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        let held = common::Supervisor::hold(child, root.join(format!("{name}.pid")));
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        let mut c = loop {
            if let Ok(c) = UnixStream::connect(&sock) {
                break c;
            }
            assert!(std::time::Instant::now() < deadline, "neverBound");
            std::thread::sleep(Duration::from_millis(50));
        };
        c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
        let _ = frame::write(&mut c, table::LIMITS, 5, b"x");
        let f = frame::read(&mut c, table::LIMITS).unwrap();
        drop(held);
        (f.op, f.payload)
    };
    assert_eq!(
        run(me.uid(), "own.sock"),
        (5, b"x".to_vec()),
        "control: our uid is served"
    );
    assert_eq!(
        run(me.uid() + 1, "other.sock"),
        (
            nanodregg_client::generated::status::CLOSED,
            b"peerRefused".to_vec()
        )
    );
    let o = Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
        .args(["/tmp/nd-never.sock", "--peer", "1", "--hide"])
        .arg(&ws)
        .args(["--", "/usr/bin/true"])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&o.stderr).contains("--peer needs --group"));
    let _ = std::fs::remove_dir_all(&root);
}

/// The supervisor's open fds and threads, from /proc (Linux).
#[cfg(target_os = "linux")]
fn held(pid: u32) -> (u64, u64) {
    let fds = std::fs::read_dir(format!("/proc/{pid}/fd"))
        .unwrap()
        .count();
    let status = std::fs::read_to_string(format!("/proc/{pid}/status")).unwrap();
    let threads = status
        .lines()
        .find_map(|l| l.strip_prefix("Threads:"))
        .unwrap();
    (fds as u64, threads.trim().parse().unwrap())
}

/// `held(pid)` once it reads `want`, or what it read at the 10 s deadline (100 ms sleeps).
#[cfg(target_os = "linux")]
fn settled(pid: u32, want: (u64, u64)) -> (u64, u64) {
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    loop {
        let now = held(pid);
        if now == want || std::time::Instant::now() >= deadline {
            return now;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// CLIENT-28 (PERF-1 FINDING 1: the writer's supervisor gained 252 fds over 120 commands, then
/// dropped connections without a word at RLIMIT_NOFILE). The real supervisor, counted from /proc:
/// after 200 connections that asked and left it holds exactly the fds and threads it held before
/// them; with `CONNECTIONS_MAX` connections open at once it holds at most `MUX.fds_max()` fds and two
/// threads per connection, and one more connection is answered `full`.
#[cfg(target_os = "linux")]
#[test]
fn every_connection_gives_back_its_fds_and_threads() {
    use nanodregg_client::generated as g;
    let ws = std::env::temp_dir().join(format!("nd-sup-fds-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let ws = ws.canonicalize().unwrap();
    std::fs::write(ws.join("seed"), b"SEED").unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-fds-{}.sock", std::process::id()));
    let mut sup = common::supervise(&sock, &ws, &[], CHILD, &[&ws.join("seed")]);
    let pid = sup.child().id();
    let connect = || {
        let mut c = UnixStream::connect(&sock).unwrap();
        c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
        frame::write(&mut c, table::LIMITS, 5, b"").unwrap();
        assert_eq!(frame::read(&mut c, table::LIMITS).unwrap().op, 6);
        c
    };
    drop(connect());
    std::thread::sleep(Duration::from_millis(500));
    let before = held(pid);
    for _ in 0..200 {
        drop(connect());
    }
    let after = settled(pid, before);
    let open: Vec<UnixStream> = (0..table::MUX.connections_max).map(|_| connect()).collect();
    let peak = held(pid);
    let mut past = UnixStream::connect(&sock).unwrap();
    past.set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let full = frame::read(&mut past, table::LIMITS).unwrap();
    drop(open);
    let end = settled(pid, before);
    let _ = std::fs::remove_file(&sock);
    std::fs::remove_dir_all(&ws).unwrap();
    assert_eq!(after, before, "(fds, threads) after 200 connections ended");
    let per_conn = 2 * u64::from(table::MUX.connections_max);
    assert!(
        peak.0 <= table::MUX.fds_max() && peak.1 <= before.1 + per_conn,
        "{} open: {peak:?} past the bound ({} fds, {before:?} + {per_conn} threads)",
        table::MUX.connections_max,
        table::MUX.fds_max()
    );
    assert_eq!(
        (full.op, full.payload.as_slice()),
        (g::status::CLOSED, g::CloseReason::Full.name().as_bytes())
    );
    assert_eq!(end, before, "(fds, threads) after every connection ended");
}

/// CLIENT-28: with RLIMIT_NOFILE below the fds it may hold (`MUX.fds_max()`), the supervisor
/// refuses to start, by name, rather than refuse connections it counted as admissible.
#[test]
fn an_fd_limit_below_the_bound_is_refused_at_launch() {
    let sock = std::env::temp_dir().join(format!("nd-sup-nofile-{}.sock", std::process::id()));
    let out = Command::new("sh")
        .arg("-c")
        .arg(format!(
            "ulimit -n {} && exec \"$0\" \"$1\" --hide /nonexistent -- /bin/true",
            table::MUX.fds_max() - 1
        ))
        .arg(env!("CARGO_BIN_EXE_nd-supervise"))
        .arg(&sock)
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&sock);
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("RLIMIT_NOFILE"),
        "{out:?}"
    );
    assert_eq!(
        out.status.code(),
        Some(i32::from(
            nanodregg_client::generated::supervisor_exit::REFUSED_AT_LAUNCH
        ))
    );
}

/// CLIENT-28 (ROOT, law 7): a child that dies leaves no peer with a bare EOF. The child answers A,
/// then exits on B's request: A (idle) and B (in flight) both read `closed unreachable`.
#[test]
fn a_child_that_dies_is_named_unreachable_to_every_peer() {
    const DIES: &str = r#"
import struct, sys
i, o = sys.stdin.buffer, sys.stdout.buffer
asked = 0
while True:
    h = i.read(4)
    if len(h) < 4: break
    body = i.read(struct.unpack('<I', h)[0])
    if body[4] == HANGUP: continue
    asked += 1
    if asked == 2: sys.exit(3)
    out = body[:4] + bytes([body[4] + 1])
    o.write(struct.pack('<I', len(out)) + out); o.flush()
"#;
    let ws = std::env::temp_dir().join(format!("nd-sup-dies-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-dies-{}.sock", std::process::id()));
    let _sup = common::supervise(&sock, &ws, &[], DIES, &[]);
    let open = || {
        let c = UnixStream::connect(&sock).unwrap();
        c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
        c
    };
    let (mut a, mut b) = (open(), open());
    frame::write(&mut a, table::LIMITS, 5, b"").unwrap();
    assert_eq!(frame::read(&mut a, table::LIMITS).unwrap().op, 6);
    frame::write(&mut b, table::LIMITS, 5, b"").unwrap();
    for s in [&mut a, &mut b] {
        let f = frame::read(s, table::LIMITS).unwrap();
        assert_eq!(
            (f.op, f.payload.as_slice()),
            (
                nanodregg_client::generated::status::CLOSED,
                &b"unreachable"[..]
            )
        );
    }
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_dir_all(&ws);
}

/// CLIENT-30 (cv 01a1507c-722d): SIGTERM, as nd-members sends a removed resident's supervisor and a
/// unit's stop sends every process, leaves no peer with a bare EOF. The child answers A and holds
/// B's request: on SIGTERM A (idle) and B (in flight) both read `closed unreachable`, the socket
/// is gone, and the supervisor ends by SIGTERM itself, as before it handled the signal.
#[test]
fn sigterm_names_every_peer_unreachable_and_ends_by_sigterm() {
    use std::os::unix::process::ExitStatusExt;
    const HOLDS: &str = r#"
import struct, sys
i, o = sys.stdin.buffer, sys.stdout.buffer
asked = 0
while True:
    h = i.read(4)
    if len(h) < 4: break
    body = i.read(struct.unpack('<I', h)[0])
    if body[4] == HANGUP: continue
    asked += 1
    if asked == 2: continue
    out = body[:4] + bytes([body[4] + 1])
    o.write(struct.pack('<I', len(out)) + out); o.flush()
"#;
    let ws = std::env::temp_dir().join(format!("nd-sup-term-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-term-{}.sock", std::process::id()));
    let mut sup = common::supervise(&sock, &ws, &[], HOLDS, &[]);
    let open = || {
        let c = UnixStream::connect(&sock).unwrap();
        c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
        c
    };
    let (mut a, mut b) = (open(), open());
    frame::write(&mut a, table::LIMITS, 5, b"").unwrap();
    assert_eq!(frame::read(&mut a, table::LIMITS).unwrap().op, 6);
    frame::write(&mut b, table::LIMITS, 5, b"").unwrap();
    std::thread::sleep(Duration::from_millis(300));
    let pid = sup.child().id().to_string();
    assert!(
        Command::new("kill")
            .args(["-TERM", &pid])
            .status()
            .unwrap()
            .success()
    );
    for s in [&mut a, &mut b] {
        let f = frame::read(s, table::LIMITS).unwrap();
        assert_eq!(
            (f.op, f.payload.as_slice()),
            (
                nanodregg_client::generated::status::CLOSED,
                &b"unreachable"[..]
            )
        );
    }
    let status = sup.child().wait().unwrap();
    let bound = sock.exists();
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_dir_all(&ws);
    assert_eq!(
        status.signal(),
        Some(15),
        "the supervisor's own end: {status}"
    );
    assert!(!bound, "{} outlived the supervisor", sock.display());
}

/// CLIENT-28 (ROOT): the socket is bound only once the child exists, so a launch refused before
/// it (here the policy: the hidden path is readable, `Exposed`) leaves no socket for a peer to wait on.
#[test]
fn a_launch_refused_before_the_child_leaves_no_socket() {
    let ws = std::env::temp_dir().join(format!("nd-sup-exposed-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&ws);
    std::fs::create_dir(&ws).unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-exposed-{}.sock", std::process::id()));
    let out = Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
        .arg(&sock)
        .arg("--hide")
        .arg(&ws)
        .arg("--read")
        .arg(&ws)
        .args(["--exec", "/usr/bin/cat", "--", "/usr/bin/cat"])
        .output()
        .unwrap();
    let bound = sock.exists();
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_dir_all(&ws);
    assert_eq!(
        out.status.code(),
        Some(i32::from(
            nanodregg_client::generated::supervisor_exit::REFUSED_AT_LAUNCH
        )),
        "{out:?}"
    );
    assert!(
        !bound,
        "refused at launch, yet {} was bound",
        sock.display()
    );
}
