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
use nanodregg_client::generated::layout::{PrecommitResult, SignResult};

const LIB: &str = r#"
import struct, sys
i, o = sys.stdin.buffer, sys.stdout.buffer
def frames():
    while True:
        h = i.read(4)
        if len(h) < 4: return
        b = i.read(struct.unpack('<I', h)[0])
        if b[4] != HANGUP: yield b[:4], b[4], b[5:]
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

// rotate: precommit → signNext "rotate" → submit "ROT" → done; logs each result by its k.
const ROTATE: &str = r#"
log = open(sys.argv[1], 'ab')
for conn, op, p in frames():
    if op == 5:
        reply(conn, 0, bytes([4]) + bs(b'\x01')); continue
    n = struct.unpack('<I', p[:4])[0]; k = p[4:4+n]
    m = struct.unpack('<I', p[4+n:8+n])[0]; result = p[8+n:8+n+m]; assert len(p) == 8+n+m
    log.write(bytes([k[0]]) + bs(result)); log.flush()
    if k == b'\x01': reply(conn, 0, bytes([5]) + bs(b'rotate') + bs(b'\x02'))
    elif k == b'\x02': reply(conn, 0, bytes([3]) + bs(b'ROT') + bs(b'\x03'))
    else: reply(conn, 0, bytes([0, 0]) + bs(b'rotated\n') + bs(b''))
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
    let root = nanodregg_devtools::scratch(&format!("nd-rt-{}", std::process::id()));
    nanodregg_devtools::mkdirs(&root.join("ws")).unwrap();
    nanodregg_devtools::mkdirs(&root.join("logs")).unwrap();
    let root = root.canonicalize().unwrap();
    let (ws, logs) = (root.join("ws"), root.join("logs"));
    let holding = root.join("holding");
    nanodregg_devtools::mkdirs(&holding).unwrap();
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
    let got = SignResult::decode(ok(&f[20..20 + n])).unwrap();
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

/// A custody result as follow receives it (PROTOCOL-21): `u8 status ‖ payload`, status ok.
fn ok(result: &[u8]) -> &[u8] {
    assert_eq!(
        result.first(),
        Some(&nanodregg_client::generated::status::OK),
        "custody result status"
    );
    &result[1..]
}

/// One logged result: `u8 k ‖ u32le n ‖ result[n]`, in order.
fn results(log: &[u8]) -> Vec<(u8, Vec<u8>)> {
    let (mut out, mut i) = (Vec::new(), 0);
    while i < log.len() {
        let n = u32::from_le_bytes(log[i + 1..i + 5].try_into().unwrap()) as usize;
        out.push((log[i], log[i + 5..i + 5 + n].to_vec()));
        i += 5 + n;
    }
    out
}

#[test]
fn stand_in_rotate_precommit_sign_next_submit_lookup_advances_custody_through_the_binaries() {
    let root = nanodregg_devtools::scratch(&format!("nd-rot-{}", std::process::id()));
    for d in ["ws", "logs", "holding"] {
        nanodregg_devtools::mkdirs(&root.join(d)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let (ws, logs, holding) = (root.join("ws"), root.join("logs"), root.join("holding"));
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
    let next0 = std::fs::read(ws.join("next.pub")).unwrap();
    let (flog, hlog) = (logs.join("follow.log"), logs.join("host.log"));
    let (follow, host) = (format!("{LIB}{ROTATE}"), format!("{LIB}{HOST}"));
    let _f = supervise(&ws.join("follow.sock"), &ws, &[&logs], &follow, &[&flog]);
    let _h = supervise(&ws.join("host.sock"), &ws, &[&logs], &host, &[&hlog]);

    let out = nd(&["rotate"]);
    assert!(
        out.status.success(),
        "nd failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, b"rotated\n");
    let r = results(&std::fs::read(&flog).unwrap());
    assert_eq!((r[0].0, r[1].0, r[2].0), (1, 2, 3));
    let pre = PrecommitResult::decode(ok(&r[0].1)).unwrap();
    assert_eq!(pre.next, next0, "precommit names the precommitted next key");
    let signed = SignResult::decode(ok(&r[1].1)).unwrap();
    assert_eq!((&signed.key, &signed.next), (&next0, &pre.pending));
    let vk = ed25519_dalek::VerifyingKey::from_bytes(&next0.clone().try_into().unwrap()).unwrap();
    let sig = ed25519_dalek::Signature::from_slice(&signed.signature).unwrap();
    vk.verify_strict(b"rotate", &sig).unwrap();
    // The host answered the submit uncertain; nd looked the same bytes up, then custody advanced.
    let seed = std::fs::read(ws.join("seed")).unwrap();
    let current = ed25519_dalek::SigningKey::from_bytes(&seed.try_into().unwrap());
    assert_eq!(
        current.verifying_key().to_bytes().to_vec(),
        next0,
        "the next key is current"
    );
    assert_eq!(std::fs::read(ws.join("next.pub")).unwrap(), pre.pending);
    assert!(!ws.join("rotation").exists() && !holding.join("pending").exists());
    drop((_f, _h));
    std::fs::remove_dir_all(&root).unwrap();
}
