//! The broker's refusal-by-name run (HOSTING-12, stage 1): a resident stand-in asks keybroker over
//! its own socket; every verdict is the Lean decider's (`hosting-broker`, with the allowance from
//! its `--drive` argument), and no byte the resident receives holds the operator's key.
//!
//! - start window: a costing ask is `overSpend` (the life forfeits it); `modelNotAllowed`,
//!   `tokensZero`, `requestTooLarge` (escaping 22 000 control bytes passes `bodyMax`) by name;
//! - next window: a grant reaches the fake upstream with the key in Lean's key header and Lean's
//!   body, and the resident gets the upstream's status and body;
//! - an upstream that echoes the key: `keyEchoed`, the answer withheld;
//! - a model whose slot has no key: `keyMissing`; a second connection while one is open: `busy`;
//! - identity is the socket: `r2`'s socket, with no allowance, is `noAllowance`;
//! - a key file of mode 0644: keybroker ends `keyFileMode` and opens no socket.
//!
//! CONTROL: the canary key is present in what the fake upstream received (so its absence from
//! the resident's bytes is not vacuous). Needs `ND_LEAN_BIN` (default `../.lake/build/bin`) to hold
//! `hosting-broker`.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use nanodregg_launcher::broker_generated::wire::{Answer, Ask, BrokerRefusal};
use nanodregg_launcher::broker_generated::{read_frame, write_frame};

const KEY: &[u8] = b"CANARY-sk-0123456789abcdef";
const WINDOW_MS: u64 = 3000;

fn lean_bin(name: &str) -> PathBuf {
    let dir = std::env::var_os("ND_LEAN_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../.lake/build/bin"));
    let p = dir.join(name);
    assert!(
        p.is_file(),
        "{} is not built (lake build {name}); no silent skip",
        p.display()
    );
    p.canonicalize().unwrap()
}

fn dir(name: &str) -> PathBuf {
    let d =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("kb-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(d.join("socks")).unwrap();
    fs::create_dir_all(d.join("pids")).unwrap();
    d.canonicalize().unwrap()
}

fn key_file(d: &Path, mode: u32) -> PathBuf {
    let p = d.join("keys");
    fs::write(&p, [b"7 ".as_slice(), KEY, b"\n"].concat()).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
    p
}

/// A fake provider: answers every request with `200` and a body, or (echo) with the request itself;
/// keeps every request it received.
fn upstream(echo: bool) -> (String, Arc<Mutex<Vec<Vec<u8>>>>) {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = l.local_addr().unwrap().to_string();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let s2 = Arc::clone(&seen);
    std::thread::spawn(move || {
        for c in l.incoming().take(64) {
            let Ok(mut c) = c else { continue };
            c.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
            let mut req = Vec::new();
            let mut buf = [0u8; 65536];
            // headers, then Content-Length bytes
            loop {
                let n = c.read(&mut buf).unwrap_or(0);
                if n == 0 {
                    break;
                }
                req.extend_from_slice(&buf[..n]);
                if let Some(h) = req.windows(4).position(|w| w == b"\r\n\r\n") {
                    let head = String::from_utf8_lossy(&req[..h]).to_string();
                    let len: usize = head
                        .lines()
                        .find_map(|l| l.strip_prefix("Content-Length: "))
                        .and_then(|v| v.trim().parse().ok())
                        .unwrap_or(0);
                    if req.len() >= h + 4 + len {
                        break;
                    }
                }
            }
            s2.lock().unwrap().push(req.clone());
            let body = if echo { req } else { b"{\"ok\":true}".to_vec() };
            let _ = c.write_all(
                &[
                    b"HTTP/1.0 200 OK\r\nContent-Length: ".as_slice(),
                    body.len().to_string().as_bytes(),
                    b"\r\n\r\n",
                    &body,
                ]
                .concat(),
            );
        }
    });
    (addr, seen)
}

struct Broker {
    child: Child,
    socks: PathBuf,
}

impl Drop for Broker {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// keybroker for resident `r1`: allowance window WINDOW_MS, cap 100000, maxTokens 100, models `m`
/// (slot 7, priced 1000 per 1000 tokens) and `n` (slot 9: no key).
fn start(d: &Path, keys: &Path, up: &str) -> Broker {
    let spec = format!("r1={WINDOW_MS}:100000:100:m/7/1000+n/9/1000");
    let child = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .arg(keys)
        .arg(d.join("socks"))
        .arg(d.join("pids"))
        .arg(up)
        .arg("r1,r2")
        .arg(lean_bin("hosting-broker"))
        .arg("--drive")
        .arg(spec)
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let socks = d.join("socks");
    let deadline = Instant::now() + Duration::from_secs(20);
    while !socks.join("r1.sock").exists() {
        assert!(Instant::now() < deadline, "keybroker opened no socket");
        std::thread::sleep(Duration::from_millis(20));
    }
    Broker { child, socks }
}

fn ask(model: &[u8], max_tokens: u32, text: &[u8]) -> Vec<u8> {
    Ask::Ask {
        model: model.to_vec(),
        max_tokens,
        system: vec![],
        roles: vec![0],
        texts: vec![text.to_vec()],
    }
    .encode()
    .unwrap()
}

/// Every byte the resident receives, kept for the canary check.
struct Resident {
    s: UnixStream,
    got: Vec<u8>,
}

impl Resident {
    fn connect(b: &Broker) -> Resident {
        Resident::connect_as(b, "r1")
    }
    fn connect_as(b: &Broker, name: &str) -> Resident {
        let s = UnixStream::connect(b.socks.join(format!("{name}.sock"))).unwrap();
        s.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
        Resident { s, got: Vec::new() }
    }
    fn ask(&mut self, a: &[u8]) -> Answer {
        write_frame(&mut self.s, a).unwrap();
        let f = read_frame(&mut self.s).unwrap();
        self.got.extend_from_slice(&f);
        Answer::decode(&f).unwrap()
    }
}

fn is_refused(a: &Answer, r: BrokerRefusal) -> bool {
    matches!(a, Answer::Refused { broker_refusal } if *broker_refusal == r)
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

/// Sleep until the operator clock is in a later window than `t0_ms` (bounded).
fn next_window(t0_ms: u64) {
    let now = || {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64
    };
    let deadline = Instant::now() + Duration::from_secs(10);
    while now() / WINDOW_MS <= t0_ms / WINDOW_MS {
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Wait (bounded) until the clock is in the first third of a window, so a broker started now and
/// asked at once is asked inside its start window.
fn early_in_window() -> u64 {
    let deadline = Instant::now() + Duration::from_secs(10);
    while now_ms() % WINDOW_MS > WINDOW_MS / 3 {
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(20));
    }
    now_ms()
}

fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}

#[test]
fn refusals_by_name_and_no_key_reaches_the_resident() {
    let d = dir("main");
    let keys = key_file(&d, 0o600);
    let (up, seen) = upstream(false);
    let t_before = early_in_window();
    let b = start(&d, &keys, &up);
    let mut r = Resident::connect(&b);

    // the start window is forfeit; the static refusals come before the meter
    let first = r.ask(&ask(b"m", 10, b"hi"));
    assert_eq!(
        now_ms() / WINDOW_MS,
        t_before / WINDOW_MS,
        "slow run (load): the start-window ask left its window before it was answered; re-run"
    );
    assert!(
        is_refused(&first, BrokerRefusal::OverSpend),
        "start window not forfeit"
    );
    assert!(is_refused(
        &r.ask(&ask(b"zz", 10, b"hi")),
        BrokerRefusal::ModelNotAllowed
    ));
    assert!(is_refused(
        &r.ask(&ask(b"m", 0, b"hi")),
        BrokerRefusal::TokensZero
    ));
    assert!(is_refused(
        &r.ask(&ask(b"m", 101, b"hi")),
        BrokerRefusal::TokensOver
    ));
    assert!(is_refused(
        &r.ask(&ask(b"m", 10, &[1u8; 22000])),
        BrokerRefusal::RequestTooLarge
    ));
    assert!(is_refused(&r.ask(b"\x07junk"), BrokerRefusal::BadAsk));

    // a second connection while this one is open
    let mut r2 = Resident::connect(&b);
    let busy = Answer::decode(&{
        let f = read_frame(&mut r2.s).unwrap();
        r2.got.extend_from_slice(&f);
        f
    })
    .unwrap();
    assert!(is_refused(&busy, BrokerRefusal::Busy));

    next_window(t_before);
    // identity is the socket: r2 has a socket but no allowance, so it is refused whatever it asks
    let mut other = Resident::connect_as(&b, "r2");
    assert!(is_refused(
        &other.ask(&ask(b"m", 10, b"hello")),
        BrokerRefusal::NoAllowance
    ));
    let a = r.ask(&ask(b"m", 10, b"hello"));
    match &a {
        Answer::Answer { status, body } => {
            assert_eq!(*status, 200);
            assert_eq!(body.as_slice(), b"{\"ok\":true}");
        }
        other => panic!("expected a grant, got {other:?}"),
    }
    assert!(is_refused(
        &r.ask(&ask(b"n", 10, b"hello")),
        BrokerRefusal::KeyMissing
    ));

    // CONTROL: the upstream got the key in Lean's header, and Lean's body
    let reqs = seen.lock().unwrap().clone();
    assert_eq!(reqs.len(), 1, "exactly one upstream call (the grant)");
    assert!(
        contains(&reqs[0], &[b"x-api-key: ".as_slice(), KEY].concat()),
        "control: key not sent upstream"
    );
    assert!(contains(&reqs[0], b"{\"model\":\"m\",\"max_tokens\":10,\"messages\":[{\"role\":\"user\",\"content\":\"hello\"}]}"));
    // and no byte the resident received holds it
    assert!(
        !contains(&r.got, KEY) && !contains(&r2.got, KEY) && !contains(&other.got, KEY),
        "the key reached the resident"
    );
}

#[test]
fn an_echoed_key_is_withheld() {
    let d = dir("echo");
    let keys = key_file(&d, 0o600);
    let (up, seen) = upstream(true);
    let t_before = early_in_window();
    let b = start(&d, &keys, &up);
    let mut r = Resident::connect(&b);
    assert_eq!(
        now_ms() / WINDOW_MS,
        t_before / WINDOW_MS,
        "slow run (load): keybroker started past its start window; re-run"
    );
    next_window(t_before);
    assert!(is_refused(
        &r.ask(&ask(b"m", 10, b"hello")),
        BrokerRefusal::KeyEchoed
    ));
    assert_eq!(
        seen.lock().unwrap().len(),
        1,
        "control: the upstream was called"
    );
    assert!(
        !contains(&r.got, KEY),
        "the echoed key reached the resident"
    );
}

#[test]
fn an_exposed_key_file_stops_keybroker_by_name() {
    let d = dir("mode");
    let keys = key_file(&d, 0o644);
    let out = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .arg(&keys)
        .arg(d.join("socks"))
        .arg(d.join("pids"))
        .arg("127.0.0.1:9")
        .arg("r1")
        .arg(lean_bin("hosting-broker"))
        .arg("--drive")
        .arg("r1=1000:1:1:m/7/1")
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // It must END, by name: still running after the deadline means it accepted the file.
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut kb = out;
    while kb.try_wait().unwrap().is_none() {
        if Instant::now() > deadline {
            let _ = kb.kill();
            let _ = kb.wait();
            panic!("keybroker accepted a 0644 key file (still running after 20 s)");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let out = kb.wait_with_output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("keybroker: keyFileMode"), "stderr: {err}");
    assert!(!d.join("socks/r1.sock").exists(), "a socket was opened");
}
