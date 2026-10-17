//! STAND-IN: the round trip through the real client binaries, `nd` ⇄ `nd-supervise` ⇄ a scripted
//! follow and a scripted host (python, speaking the CODEC-8 layouts of `Protocol.Frames`). It is a
//! mirror of the layouts, not of HOST's machine: it is replaced by the run against `host serve` /
//! `host follow` once HOST commits those executables (CLIENT-LOG, next 1). Follow asks: host(read "challenge?") → sign
//! "observation" → submit "CALL" → done. The host answers the submit `uncertain`, so nd must look
//! the SAME bytes up, and the lookup answers committed. Both children are confined away from the
//! workspace and see only their python and the log directory (CLIENT-9); follow verifies nothing here — it is a script.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::process::Command;

mod common;
use common::supervise;
use nanodregg_client::generated::layout::SignResult;

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
        reply(conn, 0, bytes([2, 3]) + bs(b'challenge?') + bs(b'\x01')); continue
    n = struct.unpack('<I', p[:4])[0]; k = p[4:4+n]
    m = struct.unpack('<I', p[4+n:8+n])[0]; result = p[8+n:8+n+m]; assert len(p) == 8+n+m
    log.write(bytes([k[0]]) + bs(result)); log.flush()
    if k == b'\x01': reply(conn, 0, bytes([1]) + bs(b'observation') + bs(b'\x02'))
    elif k == b'\x02': reply(conn, 0, bytes([3]) + bs(b'CALL') + bs(b'\x03'))
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

#[test]
fn stand_in_follow_and_host_challenge_sign_submit_lookup_done_through_the_binaries() {
    let root = std::env::temp_dir().join(format!("nd-rt-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("ws")).unwrap();
    std::fs::create_dir_all(root.join("logs")).unwrap();
    let root = root.canonicalize().unwrap();
    let (ws, logs) = (root.join("ws"), root.join("logs"));
    let holding = root.join("holding");
    std::fs::create_dir(&holding).unwrap();
    std::fs::set_permissions(
        &holding,
        std::os::unix::fs::PermissionsExt::from_mode(0o700),
    )
    .unwrap();
    let nd = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &ws)
            .env("ND_HOLDING", &holding)
            .args(args)
            .output()
            .unwrap()
    };
    assert!(nd(&["--init"]).status.success());
    let (flog, hlog) = (logs.join("follow.log"), logs.join("host.log"));
    let follow = format!("{LIB}{FOLLOW}");
    let host = format!("{LIB}{HOST}");
    let _f = supervise(&ws.join("follow.sock"), &ws, &[&logs], &follow, &[&flog]);
    let _h = supervise(&ws.join("host.sock"), &ws, &[&logs], &host, &[&hlog]);

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
    // Custody's answer: SignResult = (current key, next key, Ed25519 signature), each u32le-prefixed.
    let seed = std::fs::read(ws.join("seed")).unwrap();
    let key = ed25519_dalek::SigningKey::from_bytes(&seed.try_into().unwrap());
    let next = std::fs::read(ws.join("next.pub")).unwrap();
    let n = u32::from_le_bytes(f[16..20].try_into().unwrap()) as usize;
    let got = SignResult::decode(&f[20..20 + n]).unwrap();
    assert_eq!(got.key, key.verifying_key().to_bytes(), "the current key");
    assert_eq!(got.next, next, "the precommitted next key");
    let sig = ed25519_dalek::Signature::from_slice(&got.signature).unwrap();
    key.verifying_key()
        .verify_strict(b"observation", &sig)
        .unwrap();
    // The attempt is frozen and settled on disk.
    assert_eq!(std::fs::read(ws.join("attempts/0/call")).unwrap(), b"CALL");
    assert_eq!(
        std::fs::read(ws.join("attempts/0/committed")).unwrap(),
        b"receipt"
    );
    drop((_f, _h));
    std::fs::remove_dir_all(&root).unwrap();
}
