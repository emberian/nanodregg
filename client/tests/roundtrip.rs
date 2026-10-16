//! The round trip through the real binaries: `nd` ⇄ `nd-supervise` ⇄ a scripted follow, and
//! `nd` ⇄ `nd-supervise` ⇄ a scripted host. Follow asks: host(read "challenge?") → sign
//! "observation" → submit "CALL" → done. The host answers the submit `uncertain`, so nd must look
//! the SAME bytes up, and the lookup answers committed. Both children are confined away from the
//! workspace (they cannot read the seed); follow verifies nothing here — it is a script.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

struct Supervisor(Child);
impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

const LIB: &str = r#"
import struct, sys
i, o = sys.stdin.buffer, sys.stdout.buffer
def frames():
    while True:
        h = i.read(4)
        if len(h) < 4: return
        b = i.read(struct.unpack('<I', h)[0]); yield b[:4], b[4], b[5:]
def reply(conn, status, payload):
    out = conn + bytes([status]) + payload
    o.write(struct.pack('<I', len(out)) + out); o.flush()
def bs(x): return struct.pack('<I', len(x)) + x
"#;

// follow: k is one byte, the step index. Steps per the table: done 0, sign 1, host 2, submit 3.
const FOLLOW: &str = r#"
log = open(sys.argv[1], 'ab')
for conn, op, p in frames():
    if op == 5:
        reply(conn, 0, bytes([2, 3]) + bs(b'challenge?') + b'\x01'); continue
    n = struct.unpack('<I', p[:4])[0]; k = p[4:4+n]; result = p[4+n:]
    log.write(bytes([k[0]]) + bs(result)); log.flush()
    if k == b'\x01': reply(conn, 0, bytes([1]) + bs(b'observation') + b'\x02')
    elif k == b'\x02': reply(conn, 0, bytes([3]) + bs(b'CALL') + b'\x03')
    else: reply(conn, 0, bytes([0, 0]) + bs(b'settled ' + bytes([result[0] + 48]) + b' ' + result[1:] + b'\n') + bs(b''))
"#;

// host: read → ok "challenge"; submit → uncertain; lookup → ok "receipt". Logs every request.
const HOST: &str = r#"
log = open(sys.argv[1], 'ab')
for conn, op, p in frames():
    log.write(bytes([op]) + bs(p)); log.flush()
    if op == 3: reply(conn, 0, b'challenge')
    elif op == 1: reply(conn, 2, b'')
    elif op == 2: reply(conn, 0, b'receipt')
"#;

fn supervise(sock: &Path, hide: &Path, script: &str, log: &Path) -> Supervisor {
    let s = Supervisor(
        Command::new(env!("CARGO_BIN_EXE_nd-supervise"))
            .arg(sock)
            .arg("--hide")
            .arg(hide)
            .arg("--")
            .args(["python3", "-c", &format!("{LIB}{script}")])
            .arg(log)
            .stdin(Stdio::null())
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

#[test]
fn challenge_sign_submit_lookup_done_through_the_binaries() {
    let root = std::env::temp_dir().join(format!("nd-rt-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let ws = root.join("ws");
    std::fs::create_dir_all(&ws).unwrap();
    let nd = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &ws)
            .args(args)
            .output()
            .unwrap()
    };
    assert!(nd(&["--init"]).status.success());
    let (flog, hlog) = (root.join("follow.log"), root.join("host.log"));
    let _f = supervise(&ws.join("follow.sock"), &ws, FOLLOW, &flog);
    let _h = supervise(&ws.join("host.sock"), &ws, HOST, &hlog);

    let out = nd(&["write", "note", "hi"]);
    assert!(
        out.status.success(),
        "nd failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, b"settled 0 receipt\n");

    // The host saw: read(challenge?), submit(CALL), lookup(CALL) — the same bytes, in that order.
    let h = std::fs::read(&hlog).unwrap();
    let rec = |op: u8, p: &[u8]| {
        let mut v = vec![op];
        v.extend((p.len() as u32).to_le_bytes());
        v.extend(p);
        v
    };
    assert_eq!(
        h,
        [rec(3, b"challenge?"), rec(1, b"CALL"), rec(2, b"CALL")].concat()
    );
    // Follow got the host's reply verbatim, then custody's signature over exactly "observation".
    let f = std::fs::read(&flog).unwrap();
    assert_eq!(
        &f[..15],
        &[&[1u8][..], &10u32.to_le_bytes(), &[0], b"challenge"].concat()[..]
    );
    assert_eq!(f[15], 2);
    assert_eq!(
        u32::from_le_bytes(f[16..20].try_into().unwrap()),
        64,
        "an Ed25519 signature"
    );
    // The attempt is frozen and settled on disk.
    assert_eq!(std::fs::read(ws.join("attempts/0/call")).unwrap(), b"CALL");
    assert_eq!(
        std::fs::read(ws.join("attempts/0/committed")).unwrap(),
        b"receipt"
    );
    drop((_f, _h));
    std::fs::remove_dir_all(&root).unwrap();
}
