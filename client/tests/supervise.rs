//! The supervisor end to end: `nd-supervise` binds a socket, confines a child, and routes frames.
//! The child here answers each request with whether IT could read the member's seed — the
//! CLIENT-8 plant through the real binary: the answer must be "denied".
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::os::unix::net::UnixStream;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use nanodregg_client::{frame, table};

/// Stops the supervisor this test started, by its own handle, even when an assertion fails;
/// its stdio is not inherited, so a leaked one could not hold the test runner's pipes either.
struct Supervisor(std::process::Child);
impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

const CHILD: &str = r#"
import struct, sys
seed = sys.argv[1]
i, o = sys.stdin.buffer, sys.stdout.buffer
while True:
    h = i.read(4)
    if len(h) < 4: break
    body = i.read(struct.unpack('<I', h)[0])
    conn, op = body[:4], body[4]
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
    std::fs::write(ws.join("seed"), b"SEED").unwrap();
    let sock = std::env::temp_dir().join(format!("nd-sup-{}.sock", std::process::id()));
    let _sup = Supervisor(
        Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
            .arg(&sock)
            .arg("--hide")
            .arg(&ws)
            .arg("--")
            .args(["python3", "-c", CHILD])
            .arg(ws.join("seed"))
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut c = loop {
        if let Ok(c) = UnixStream::connect(&sock) {
            break c;
        }
        assert!(
            Instant::now() < deadline,
            "supervisor never bound its socket"
        );
        std::thread::sleep(Duration::from_millis(50));
    };
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
}
