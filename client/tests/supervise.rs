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
/// mechanism makes of the death (OPS-2, hbox: bwrap exits 128 + N, so the unit saw 137/153, a code
/// in neither table). The child kills itself with SIGKILL before reading a frame.
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
    let refused = |dir: &std::path::Path, group: u32, name: &str| {
        let (code, err) = launch_group(&dir.join("follow.sock"), &ws, Some(group))
            .err()
            .unwrap_or_else(|| panic!("plant: {} launched", dir.display()));
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
