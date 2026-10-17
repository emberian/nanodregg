//! The broker's refusal-by-name run (HOSTING-12, HOSTING-13): a resident stand-in asks keybroker
//! over its own socket; every verdict is the Lean decider's (`hosting-broker`), which reads the
//! allowances from a REAL Store and follows it live: `host genesis` from custody's keys, `host serve`
//! under `nd-supervise`, and the operator's `nd install` / `create` / `invoke` of the `allowance`
//! package (world/hosting/Allowance). No byte the resident receives holds the operator's key.
//!
//! - start window: a costing ask is `overSpend` (the life forfeits it); `modelNotAllowed`,
//!   `tokensZero`, `requestTooLarge` (escaping 22 000 control bytes passes `bodyMax`) by name;
//! - next window: a grant reaches the fake upstream OVER TLS (keybroker dials the operator's
//!   address, 127.0.0.1, and verifies the certificate for Lean's host `api.anthropic.com` against
//!   the operator's anchor file, here the test's own CA) with the key in Lean's key header, Lean's
//!   `Host:` and Lean's body, and the resident gets the upstream's status and body;
//! - an upstream that echoes the key: `keyEchoed`, the answer withheld;
//! - a model whose slot has no key: `keyMissing` (Lean's, from the slots keybroker passed);
//!   two allowances for one resident and model: `allowanceAmbiguous`; a second connection while
//!   one is open: `busy`;
//! - identity is the socket: resident `02`'s socket, with no allowance, is `noAllowance`;
//! - live: the operator `set`s the `m` allowance (a new budget: the ask after it is `overSpend`),
//!   creates a second `m` allowance (`allowanceAmbiguous`) and revokes it, and revokes one of the
//!   two `a` allowances (the ask on `a` is granted again);
//! - TLS plants: an upstream whose certificate no anchor signs is `tlsCertificate`, and one whose
//!   certificate the CA signed for another host is `tlsHostname`; neither receives a request byte;
//! - a key file of mode 0644, an anchor file of mode 0666, a missing one, and one holding a key
//!   instead of certificates: keybroker ends `keyFileMode`, `anchorsMode`, `anchorsMissing`,
//!   `anchorsMalformed`, and opens no socket; the production bundle (deploy/tls/anchors.pem) is
//!   accepted whole.
//! - HOSTING-17: each resident's socket is SOCKDIR/<r>/broker.sock, 0660 with SOCKDIR's group (02710);
//!   a SOCKDIR or resident directory of the wrong mode, a stray file beside the socket, or a regular
//!   file at the socket path ends keybroker `sockDir` with no socket open; a broker serving another
//!   uid (PEER), or whose SOCKDIR's group is not the peer's gid, answers `peerRefused`. A restarted
//!   broker meets the last life's socket and binds again. A peer of the right gid and another uid
//!   needs a second uid: unrun on one-uid boxes, and the PEER plant tests the same comparison.
//!
//! CONTROL: the canary key is present in what the fake upstream received over real TLS (so its
//! absence from the resident's bytes is not vacuous, and the TLS refusals are not a broken client). The Lean exes (`hosting-broker`, `host`) and the client's
//! `nd` / `nd-supervise` come from `nanodregg_devtools`; a missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use nanodregg_devtools::{Supervisor, lean_bin, nd, nd_supervise, repo, supervise_host};
use nanodregg_launcher::broker_generated::wire::{Answer, Ask, BrokerRefusal};
use nanodregg_launcher::broker_generated::{read_frame, write_frame};
use rcgen::{BasicConstraints, CertificateParams, IsCa, Issuer, KeyPair};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};

const KEY: &[u8] = b"CANARY-sk-0123456789abcdef";
const WINDOW_MS: u64 = 3000;

/// A test's own scratch root, removed with its socket directory when the test ends.
struct Scratch {
    root: PathBuf,
    socks: PathBuf,
}

impl std::ops::Deref for Scratch {
    type Target = Path;
    fn deref(&self) -> &Path {
        &self.root
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
        let _ = fs::remove_dir_all(&self.socks);
    }
}

fn dir(name: &str) -> Scratch {
    let d = nanodregg_devtools::scratch(&format!("kb-{}-{name}", std::process::id()));
    nanodregg_devtools::mkdirs(&d.join("pids")).unwrap();
    // A Unix socket path is at most 107 bytes (sun_path), and a judge slot's target dir is deeper
    // than that: the sockets live in a short directory of this process's own.
    let socks = nanodregg_devtools::scratch(&format!("kb{}{name}", std::process::id()));
    sockdir(&socks);
    std::os::unix::fs::symlink(&socks, d.join("socks")).unwrap();
    Scratch {
        root: d.canonicalize().unwrap(),
        socks,
    }
}

/// SOCKDIR as HOSTING-17 requires it: this uid's, mode 02710 (made if absent).
fn sockdir(p: &Path) {
    nanodregg_devtools::mkdirs(p).unwrap();
    fs::set_permissions(p, fs::Permissions::from_mode(0o2710)).unwrap();
}

/// This process's uid and primary gid (of a directory it made, under a parent with no setgid bit).
fn me(d: &Path) -> (u32, u32) {
    let m = fs::metadata(d).unwrap();
    (m.uid(), m.gid())
}

/// A group of this process other than its primary one, if it has one (`/proc/self/status`).
fn other_group(primary: u32) -> Option<u32> {
    let st = fs::read_to_string("/proc/self/status").unwrap();
    let line = st.lines().find(|l| l.starts_with("Groups:"))?;
    line["Groups:".len()..]
        .split_whitespace()
        .filter_map(|g| g.parse().ok())
        .find(|g| *g != primary)
}

/// Lean's host for every `claude-…` model (`Broker.anthropic.host`).
const HOST: &str = "api.anthropic.com";

/// The test's own PKI: a CA (whose certificate is the operator's anchor file) and server
/// certificates for the fake upstream.
struct Pki {
    ca: Issuer<'static, KeyPair>,
    ca_pem: String,
}

impl Pki {
    fn new() -> Pki {
        let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
        params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
        let key = KeyPair::generate().unwrap();
        let ca_pem = params.self_signed(&key).unwrap().pem();
        Pki {
            ca: Issuer::new(params, key),
            ca_pem,
        }
    }
    /// The anchor file: the CA's certificate, mode `mode`.
    fn anchors(&self, d: &Path, mode: u32) -> PathBuf {
        let p = d.join("anchors.pem");
        fs::write(&p, &self.ca_pem).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
        p
    }
    /// A TLS 1.3 server with a certificate for `name`, signed by the CA, or (self_signed) by its
    /// own key.
    fn server(&self, name: &str, self_signed: bool) -> Arc<ServerConfig> {
        self.server_at(name, self_signed, &rustls::version::TLS13)
    }
    /// A server that speaks only `version`, with a certificate for `name`.
    fn server_at(
        &self,
        name: &str,
        self_signed: bool,
        version: &'static rustls::SupportedProtocolVersion,
    ) -> Arc<ServerConfig> {
        let key = KeyPair::generate().unwrap();
        let params = CertificateParams::new(vec![name.to_owned()]).unwrap();
        let cert = if self_signed {
            params.self_signed(&key).unwrap()
        } else {
            params.signed_by(&key, &self.ca).unwrap()
        };
        let der: CertificateDer<'static> = cert.der().clone();
        let pk = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.serialize_der()));
        Arc::new(
            ServerConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
                .with_protocol_versions(&[version])
                .unwrap()
                .with_no_client_auth()
                .with_single_cert(vec![der], pk)
                .unwrap(),
        )
    }
}

fn key_file(d: &Path, mode: u32) -> PathBuf {
    let p = d.join("keys");
    fs::write(&p, [b"7 ".as_slice(), KEY, b"\n"].concat()).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
    p
}

/// How the fake provider answers.
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    /// `200` and `{"ok":true}`, then `close_notify`
    Ok,
    /// `200` and the request itself (the key included), then `close_notify`
    Echo,
    /// `200` and `{"ok":true}`, then the TCP connection closes with no `close_notify`
    Truncate,
}

/// A fake provider over TLS with the server configuration `tls`, answering as `mode` says; keeps
/// every request it received. A connection whose handshake fails records nothing.
fn upstream(mode: Mode, tls: Arc<ServerConfig>) -> (String, Arc<Mutex<Vec<Vec<u8>>>>) {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = l.local_addr().unwrap().to_string();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let s2 = Arc::clone(&seen);
    std::thread::spawn(move || {
        for c in l.incoming().take(64) {
            let Ok(t) = c else { continue };
            t.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
            let mut c = StreamOwned::new(ServerConnection::new(Arc::clone(&tls)).unwrap(), t);
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
            if req.is_empty() {
                continue;
            }
            s2.lock().unwrap().push(req.clone());
            let body = if mode == Mode::Echo {
                req
            } else {
                b"{\"ok\":true}".to_vec()
            };
            let _ = c.write_all(
                &[
                    b"HTTP/1.0 200 OK\r\nContent-Length: ".as_slice(),
                    body.len().to_string().as_bytes(),
                    b"\r\n\r\n",
                    &body,
                ]
                .concat(),
            );
            if mode != Mode::Truncate {
                c.conn.send_close_notify();
            }
            let _ = c.flush();
        }
    });
    (addr, seen)
}

/// A real Store and the operator's custody: `host genesis` from custody's own keys, `host serve`
/// under `nd-supervise`; `run` is the operator's `nd`, which must succeed.
struct World {
    root: PathBuf,
    store: PathBuf,
    operator: String,
    pkg: String,
    ws: PathBuf,
    holding: PathBuf,
    _serve: Supervisor,
    _follow: Supervisor,
}

fn text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

impl World {
    fn nd(&self, args: &[&str]) -> Output {
        Command::new(nd())
            .env("ND_WORKSPACE", &self.ws)
            .env("ND_HOLDING", &self.holding)
            .args(args)
            .output()
            .unwrap()
    }
    fn run(&self, args: &[&str]) -> String {
        let o = self.nd(args);
        assert!(
            o.status.success(),
            "nd {args:?}: {}{}",
            text(&o),
            String::from_utf8_lossy(&o.stderr)
        );
        text(&o)
    }
    /// `nd create` of an allowance for `resident` (hex) on `model`, slot `slot`; its object id.
    fn allowance(&self, resident: &str, model: &str, slot: u32, cap: u64) -> String {
        let state = format!(
            "(record (cap {cap}) (keySlot {slot}) (maxTokens 100) (microPerKTok 1000) (model \"{model}\") (resident #{resident}) (revoked false) (windowMs {WINDOW_MS}))"
        );
        line(&self.run(&["create", "--pkg", &self.pkg, &state]), "id ").to_owned()
    }

    fn genesis(name: &str) -> World {
        // A short root: a Unix socket path must fit sun_path.
        let root = nanodregg_devtools::scratch(&format!("kbw{}{name}", std::process::id()));
        for d in ["ws", "holding", "stores"] {
            nanodregg_devtools::mkdirs(&root.join(d)).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let (ws, holding) = (root.join("ws"), root.join("holding"));
        let (store, fstore) = (root.join("stores/W"), root.join("stores/F"));
        fs::set_permissions(&holding, fs::Permissions::from_mode(0o700)).unwrap();
        let bare = |args: &[&str]| {
            Command::new(nd())
                .env("ND_WORKSPACE", &ws)
                .env("ND_HOLDING", &holding)
                .args(args)
                .output()
                .unwrap()
        };
        assert!(bare(&["--init"]).status.success(), "nd --init");
        let keys = text(&bare(&["--keys"]));
        // two Stores from one genesis: the writer's, and the operator's own for `host follow`
        let genesis = |s: &Path, nonce: Option<&str>| {
            let mut c = Command::new(lean_bin("host"));
            c.arg("genesis").arg(s).arg("nano");
            if let Some(n) = nonce {
                c.args(["--nonce", n]);
            }
            let o = c
                .args([line(&keys, "key "), line(&keys, "next ")])
                .output()
                .unwrap();
            assert!(
                o.status.success(),
                "genesis: {}",
                String::from_utf8_lossy(&o.stderr)
            );
            text(&o)
        };
        let g = genesis(&store, None);
        assert_eq!(
            genesis(&fstore, Some(line(&g, "nonce "))),
            g,
            "one genesis, two Stores"
        );
        let founder = line(&g, "founder 0 member ");
        let (operator, grant) = founder.split_once(" grant ").unwrap();
        let serve = supervise_host(
            &nd_supervise(),
            &ws.join("host.sock"),
            &ws,
            &store,
            &["serve", store.to_str().unwrap()],
        );
        let follow = supervise_host(
            &nd_supervise(),
            &ws.join("follow.sock"),
            &ws,
            &fstore,
            &["follow", fstore.to_str().unwrap(), operator, grant],
        );
        let mut w = World {
            root,
            store,
            operator: operator.to_owned(),
            pkg: String::new(),
            ws,
            holding,
            _serve: serve,
            _follow: follow,
        };
        let pkg_text = fs::read_to_string(repo().join("world/hosting/Allowance")).unwrap();
        w.pkg = line(&w.run(&["install", &pkg_text]), "id ").to_owned();
        w
    }
}

impl Drop for World {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct Broker {
    child: Child,
    socks: PathBuf,
}

impl Drop for Broker {
    // The sockets stay (the scratch removes them).
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// keybroker's argv as the emitted unit renders it (deploy/units/linux/nd-keybroker.service, from
/// Ops/Units.lean), every rendered word replaced by this test's value for that word: the ORDER is
/// the unit's, so a unit and a parser that disagree on it are red here (ROOT, 10-18; OPS-2's
/// fd1d4b2 class). A word with no test value, or a test value no word asks for, is red too.
fn rendered(values: &[(&str, &std::ffi::OsStr)]) -> Command {
    let unit = fs::read_to_string(repo().join("deploy/units/linux/nd-keybroker.service")).unwrap();
    let line = unit
        .lines()
        .find_map(|l| l.strip_prefix("ExecStart="))
        .expect("the unit has an ExecStart");
    let mut words = line.split(' ');
    assert_eq!(
        words.next(),
        Some("/opt/nd/bin/keybroker"),
        "the unit runs keybroker"
    );
    let mut c = Command::new(env!("CARGO_BIN_EXE_keybroker"));
    let mut used = 0;
    for w in words {
        let (_, v) = values
            .iter()
            .find(|(k, _)| *k == w)
            .unwrap_or_else(|| panic!("the unit's word {w} has no test value"));
        c.arg(v);
        used += 1;
    }
    assert_eq!(used, values.len(), "a test value the unit never asks for");
    c
}

/// The test's values for the unit's words.
#[allow(clippy::too_many_arguments)]
fn argv(
    keys: &Path,
    anchors: &Path,
    socks: &Path,
    pids: &Path,
    up: &str,
    store: &Path,
    operator: &str,
    residents: &str,
    peer: &str,
) -> Command {
    let decider = lean_bin("hosting-broker");
    rendered(&[
        ("/etc/nd/keybroker/provider.key", keys.as_os_str()),
        ("/etc/nd/keybroker/anchors.pem", anchors.as_os_str()),
        ("/run/nd-broker", socks.as_os_str()),
        ("/run/nd-keybroker", pids.as_os_str()),
        ("api.anthropic.com:443", std::ffi::OsStr::new(up)),
        ("/srv/nd/store", store.as_os_str()),
        ("${ND_OPERATOR}", std::ffi::OsStr::new(operator)),
        ("${ND_RESIDENTS}", std::ffi::OsStr::new(residents)),
        ("${ND_PEER}", std::ffi::OsStr::new(peer)),
        ("/opt/nd/bin/hosting-broker", decider.as_os_str()),
    ])
}

/// keybroker for residents `01` and `02` over the World `w`, trusting `anchors`, serving this uid.
fn start(d: &Path, keys: &Path, anchors: &Path, up: &str, w: &World) -> Broker {
    start_peer(d, keys, anchors, up, w, me(d).0)
}

/// `start`, serving the uid `peer`.
fn start_peer(d: &Path, keys: &Path, anchors: &Path, up: &str, w: &World, peer: u32) -> Broker {
    let socks = fs::read_link(d.join("socks")).unwrap();
    // the last life's sockets go first, so a socket seen below is this life's (keybroker's own
    // unlink of a stale socket is a_bad_socket_directory_stops_keybroker_by_name's control)
    for r in ["01", "02"] {
        let _ = fs::remove_file(socks.join(r).join("broker.sock"));
    }
    let child = argv(
        keys,
        anchors,
        &socks,
        &d.join("pids"),
        up,
        &w.store,
        &w.operator,
        "01,02",
        &peer.to_string(),
    )
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
    let mut child = child;
    let deadline = Instant::now() + Duration::from_secs(20);
    // bound and opened to the group (0660)
    let bound = |r: &str| {
        fs::symlink_metadata(socks.join(r).join("broker.sock"))
            .is_ok_and(|m| m.permissions().mode() & 0o7777 == 0o660)
    };
    while !bound("01") || !bound("02") {
        let ended = child.try_wait().unwrap().is_some();
        if ended || Instant::now() > deadline {
            let _ = child.kill();
            let out = child.wait_with_output().unwrap();
            panic!(
                "keybroker opened no socket: {}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
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
        Resident::connect_as(b, "01")
    }
    fn connect_as(b: &Broker, name: &str) -> Resident {
        let s = UnixStream::connect(b.socks.join(name).join("broker.sock")).unwrap();
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
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let (up, seen) = upstream(Mode::Ok, pki.server(HOST, false));
    // resident 01: model m (slot 7), n (slot 9: no key), and a twice (ambiguous)
    let w = World::genesis("main");
    let m = w.allowance("01", "claude-m", 7, 100_000);
    w.allowance("01", "claude-n", 9, 100_000);
    w.allowance("01", "claude-a", 7, 100_000);
    let a2 = w.allowance("01", "claude-a", 7, 100_000);
    let t_before = early_in_window();
    let b = start(&d, &keys, &anchors, &up, &w);
    let mut r = Resident::connect(&b);

    // the start window is forfeit; the static refusals come before the meter
    let first = r.ask(&ask(b"claude-m", 10, b"hi"));
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
    // a slot keybroker holds no key for is Lean's refusal, before the meter: not overSpend here
    assert!(is_refused(
        &r.ask(&ask(b"claude-n", 10, b"hi")),
        BrokerRefusal::KeyMissing
    ));
    assert!(is_refused(
        &r.ask(&ask(b"claude-m", 0, b"hi")),
        BrokerRefusal::TokensZero
    ));
    assert!(is_refused(
        &r.ask(&ask(b"claude-m", 101, b"hi")),
        BrokerRefusal::TokensOver
    ));
    assert!(is_refused(
        &r.ask(&ask(b"claude-m", 10, &[1u8; 22000])),
        BrokerRefusal::RequestTooLarge
    ));
    assert!(is_refused(&r.ask(b"\x07junk"), BrokerRefusal::BadAsk));
    assert!(is_refused(
        &r.ask(&ask(b"claude-a", 10, b"hi")),
        BrokerRefusal::AllowanceAmbiguous
    ));

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
    // identity is the socket: 02 has a socket but no allowance, so it is refused whatever it asks
    let mut other = Resident::connect_as(&b, "02");
    assert!(is_refused(
        &other.ask(&ask(b"claude-m", 10, b"hello")),
        BrokerRefusal::NoAllowance
    ));
    let a = r.ask(&ask(b"claude-m", 10, b"hello"));
    match &a {
        Answer::Answer { status, body } => {
            assert_eq!(*status, 200);
            assert_eq!(body.as_slice(), b"{\"ok\":true}");
        }
        other => panic!("expected a grant, got {other:?}"),
    }
    assert!(is_refused(
        &r.ask(&ask(b"claude-n", 10, b"hello")),
        BrokerRefusal::KeyMissing
    ));

    // live: the operator raises m's cap; the broker follows the Store at the next ask, and a
    // changed allowance is a new budget whose window is forfeit (HOSTING-13)
    w.run(&[
        "invoke",
        &m,
        "1",
        &format!("(record (cap 200000) (keySlot 7) (maxTokens 100) (microPerKTok 1000) (windowMs {WINDOW_MS}))"),
    ]);
    assert!(
        is_refused(
            &r.ask(&ask(b"claude-m", 10, b"hello")),
            BrokerRefusal::OverSpend
        ),
        "a changed allowance kept its meter"
    );
    // a second allowance on m CREATED while keybroker runs: the broker sees the born id
    let m2 = w.allowance("01", "claude-m", 7, 5);
    assert!(
        is_refused(
            &r.ask(&ask(b"claude-m", 10, b"hello")),
            BrokerRefusal::AllowanceAmbiguous
        ),
        "an allowance created live was not seen"
    );
    w.run(&["invoke", &m2, "0", "(record)"]);
    // the operator revokes the second `a`: the first, unchanged since the start window, grants
    w.run(&["invoke", &a2, "0", "(record)"]);
    match r.ask(&ask(b"claude-a", 10, b"hello")) {
        Answer::Answer { status, .. } => assert_eq!(status, 200),
        other => panic!("after the revoke, expected a grant on a, got {other:?}"),
    }

    // CONTROL: over real TLS the upstream got the key in Lean's header, Lean's host, and Lean's body
    let reqs = seen.lock().unwrap().clone();
    assert_eq!(
        reqs.len(),
        2,
        "exactly two upstream calls (the grants on m and on a)"
    );
    assert!(
        contains(&reqs[0], &[b"x-api-key: ".as_slice(), KEY].concat()),
        "control: key not sent upstream"
    );
    assert!(
        contains(&reqs[0], b"\r\nHost: api.anthropic.com\r\n"),
        "Host is not Lean's host"
    );
    assert!(contains(&reqs[0], b"{\"model\":\"claude-m\",\"max_tokens\":10,\"messages\":[{\"role\":\"user\",\"content\":\"hello\"}]}"));
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
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let (up, seen) = upstream(Mode::Echo, pki.server(HOST, false));
    let w = World::genesis("echo");
    w.allowance("01", "claude-m", 7, 100_000);
    let t_before = early_in_window();
    let b = start(&d, &keys, &anchors, &up, &w);
    let mut r = Resident::connect(&b);
    assert_eq!(
        now_ms() / WINDOW_MS,
        t_before / WINDOW_MS,
        "slow run (load): keybroker started past its start window; re-run"
    );
    next_window(t_before);
    assert!(is_refused(
        &r.ask(&ask(b"claude-m", 10, b"hello")),
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

/// keybroker over KEYS and ANCHORS with no World: how it ends (its stderr and exit code), within
/// 20 s.
fn ends(d: &Path, keys: &Path, anchors: &Path) -> (String, Option<i32>) {
    ends_over(d, keys, anchors, &d.join("no-store"))
}

/// keybroker over KEYS, ANCHORS and STORE: how it ends, within 20 s.
fn ends_over(d: &Path, keys: &Path, anchors: &Path, store: &Path) -> (String, Option<i32>) {
    let mut kb = argv(
        keys,
        anchors,
        &fs::read_link(d.join("socks")).unwrap(),
        &d.join("pids"),
        "127.0.0.1:9",
        store,
        "00",
        "01",
        &me(d).0.to_string(),
    )
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
    // It must END: still running after the deadline means it accepted what it was given.
    let deadline = Instant::now() + Duration::from_secs(20);
    while kb.try_wait().unwrap().is_none() {
        if Instant::now() > deadline {
            let _ = kb.kill();
            let _ = kb.wait();
            panic!("keybroker still running after 20 s");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let out = kb.wait_with_output().unwrap();
    (
        String::from_utf8_lossy(&out.stderr).into_owned(),
        out.status.code(),
    )
}

/// A file of mode 0644 holding `bytes`.
fn public_file(p: PathBuf, bytes: &[u8]) -> PathBuf {
    fs::write(&p, bytes).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(0o644)).unwrap();
    p
}

#[test]
fn exposed_or_malformed_custody_files_stop_keybroker_by_name() {
    let d = dir("mode");
    let pki = Pki::new();
    let open_keys = {
        let p = d.join("open-keys");
        fs::write(&p, [b"7 ".as_slice(), KEY, b"\n"].concat()).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o644)).unwrap();
        p
    };
    let keys = key_file(&d, 0o600);
    let anchors = pki.anchors(&d, 0o644);
    let open_anchors = {
        let p = d.join("open-anchors.pem");
        fs::copy(&anchors, &p).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o666)).unwrap();
        p
    };
    // the good CA certificate, then a key: a reader that skips what is not a certificate accepts it
    let key_pem = public_file(
        d.join("key.pem"),
        [
            pki.ca_pem.clone(),
            KeyPair::generate().unwrap().serialize_pem(),
        ]
        .concat()
        .as_bytes(),
    );
    // the good CA certificate, then a copy whose DER's first bytes are changed (still base64): a
    // reader that skips an anchor webpki refuses accepts it
    let bad = pki.ca_pem.replacen("MII", "MIJ", 1);
    let bad_pem = public_file(
        d.join("bad.pem"),
        [pki.ca_pem.clone(), bad.clone()].concat().as_bytes(),
    );
    assert_ne!(
        bad.as_bytes(),
        pki.ca_pem.as_bytes(),
        "the mutation happened"
    );
    let link_keys = d.join("link-keys");
    std::os::unix::fs::symlink(&keys, &link_keys).unwrap();
    let link_anchors = d.join("link-anchors.pem");
    std::os::unix::fs::symlink(&anchors, &link_anchors).unwrap();
    let bad_keys = {
        let p = d.join("bad-keys");
        fs::write(&p, b"seven KEY\n").unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o600)).unwrap();
        p
    };
    // a key file of the right mode in a directory its group may write (CLIENT-19's chain rule)
    let gw_keys = {
        let g = d.join("gw");
        nanodregg_devtools::mkdirs(&g).unwrap();
        fs::set_permissions(&g, fs::Permissions::from_mode(0o770)).unwrap();
        let p = g.join("keys");
        fs::write(&p, [b"7 ".as_slice(), KEY, b"\n"].concat()).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o600)).unwrap();
        p
    };
    // each ends by name on stderr and with Lean's code (Hosting.KeybrokerExit, all fatal)
    use nanodregg_launcher::broker_generated::keybroker_exit as k;
    let cases = [
        ("keyFileMode", k::KEY_FILE_MODE, &open_keys, &anchors),
        ("keyFileLink", k::KEY_FILE_LINK, &link_keys, &anchors),
        ("keyFileFormat", k::KEY_FILE_FORMAT, &bad_keys, &anchors),
        ("keyFileDir", k::KEY_FILE_DIR, &gw_keys, &anchors),
        ("anchorsLink", k::ANCHORS_LINK, &keys, &link_anchors),
        ("anchorsMode", k::ANCHORS_MODE, &keys, &open_anchors),
        (
            "anchorsMissing",
            k::ANCHORS_MISSING,
            &keys,
            &d.join("no-anchors.pem"),
        ),
        ("anchorsMalformed", k::ANCHORS_MALFORMED, &keys, &key_pem),
        ("anchorsMalformed", k::ANCHORS_MALFORMED, &keys, &bad_pem),
    ];
    for (want, code, k, a) in cases {
        let (err, got) = ends(&d, k, a);
        assert!(
            err.contains(&format!("keybroker: {want}\n")),
            "{want}: stderr: {err}"
        );
        assert_eq!(got, Some(i32::from(code)), "{want}: exit code");
        assert!(
            !d.join("socks/01/broker.sock").exists(),
            "{want}: a socket was opened"
        );
    }
    // CONTROL: the production bundle (deploy/tls/anchors.pem, OPS's pinned webpki roots) passes the
    // anchor checks whole, so keybroker goes on to start its decider (refused: the Store is missing).
    let prod = public_file(
        d.join("prod-anchors.pem"),
        &fs::read(repo().join("deploy/tls/anchors.pem")).unwrap(),
    );
    let (err, got) = ends(&d, &keys, &prod);
    assert!(
        err.contains("keybroker: deciderRefused"),
        "production anchors: stderr: {err}"
    );
    assert_eq!(
        got,
        Some(i32::from(k::DECIDER_REFUSED)),
        "production anchors: exit code"
    );
    // the decider's own end is passed through: over a STORE that exists but holds no Store (no key
    // file), the decider ends `store` (HOST's `badKey 0`, named, never an IO exception; DeciderExit,
    // fatal), and so does keybroker, with that code
    let empty = d.join("empty-store");
    nanodregg_devtools::mkdirs(&empty).unwrap();
    let (err, got) = ends_over(&d, &keys, &anchors, &empty);
    let store = nanodregg_launcher::broker_generated::decider_exit::STORE;
    assert!(
        err.contains(&format!("keybroker: deciderEnded {store}\n")),
        "pass-through: stderr: {err}"
    );
    assert_eq!(got, Some(i32::from(store)), "pass-through: exit code");
}

#[test]
fn an_unverified_upstream_is_refused_by_name_and_gets_no_byte() {
    let d = dir("tls");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let w = World::genesis("tls");
    w.allowance("01", "claude-m", 7, 100_000);
    // an upstream whose certificate no anchor signs; one the CA signed for another host; one that
    // speaks only TLS 1.2 (keybroker offers only 1.3); and one that answers in full but closes
    // without `close_notify` (an unauthenticated end: the answer could be truncated)
    for (cert, mode, want) in [
        (
            pki.server(HOST, true),
            Mode::Ok,
            BrokerRefusal::TlsCertificate,
        ),
        (
            pki.server("other.example", false),
            Mode::Ok,
            BrokerRefusal::TlsHostname,
        ),
        (
            pki.server_at(HOST, false, &rustls::version::TLS12),
            Mode::Ok,
            BrokerRefusal::TlsProtocol,
        ),
        (
            pki.server(HOST, false),
            Mode::Truncate,
            BrokerRefusal::TlsProtocol,
        ),
    ] {
        sockdir(&d.socks);
        let (up, seen) = upstream(mode, cert);
        let t0 = now_ms();
        let b = start(&d, &keys, &anchors, &up, &w);
        next_window(t0);
        let mut r = Resident::connect(&b);
        let a = r.ask(&ask(b"claude-m", 10, b"hello"));
        assert!(is_refused(&a, want), "expected {want:?}, got {a:?}");
        if mode == Mode::Truncate {
            // CONTROL: the request did reach it, and the answer it sent is withheld
            assert_eq!(
                seen.lock().unwrap().len(),
                1,
                "truncate: no request arrived"
            );
            assert!(
                !contains(&r.got, b"{\"ok\":true}"),
                "truncate: the unauthenticated answer was relayed"
            );
        } else {
            assert!(
                seen.lock().unwrap().is_empty(),
                "{want:?}: the upstream received a request"
            );
        }
        assert!(
            !contains(&r.got, KEY),
            "{want:?}: the key reached the resident"
        );
        drop(r);
        drop(b);
    }
}

#[test]
fn a_bad_socket_directory_stops_keybroker_by_name() {
    let d = dir("sockdir");
    let keys = key_file(&d, 0o600);
    let anchors = Pki::new().anchors(&d, 0o644);
    let k = nanodregg_launcher::broker_generated::keybroker_exit::SOCK_DIR;
    let socks = d.socks.clone();
    let r = socks.join("01");
    let reset = || {
        let _ = fs::remove_dir_all(&socks);
        sockdir(&socks);
    };
    let cases: [(&str, &dyn Fn()); 5] = [
        ("SOCKDIR 0700", &|| {
            fs::set_permissions(&socks, fs::Permissions::from_mode(0o700)).unwrap()
        }),
        ("SOCKDIR 0730 (group-writable)", &|| {
            fs::set_permissions(&socks, fs::Permissions::from_mode(0o2730)).unwrap()
        }),
        ("resident directory 0700", &|| {
            fs::create_dir(&r).unwrap();
            fs::set_permissions(&r, fs::Permissions::from_mode(0o700)).unwrap();
        }),
        ("a stray file beside the socket", &|| {
            fs::create_dir(&r).unwrap();
            fs::set_permissions(&r, fs::Permissions::from_mode(0o2710)).unwrap();
            fs::write(r.join("stray"), b"x").unwrap();
        }),
        ("a regular file at the socket path", &|| {
            fs::create_dir(&r).unwrap();
            fs::set_permissions(&r, fs::Permissions::from_mode(0o2710)).unwrap();
            fs::write(r.join("broker.sock"), b"x").unwrap();
        }),
    ];
    for (what, plant) in cases {
        reset();
        plant();
        let (err, got) = ends(&d, &keys, &anchors);
        assert!(err.contains("keybroker: sockDir "), "{what}: stderr: {err}");
        assert_eq!(got, Some(i32::from(k)), "{what}: exit code");
        let s = r.join("broker.sock");
        assert!(
            !fs::symlink_metadata(&s).is_ok_and(|m| m.file_type().is_socket()),
            "{what}: a socket was opened"
        );
    }
    // CONTROL: the same SOCKDIR made right passes the socket checks: keybroker starts its decider
    // (which ends `io`: the STORE holds no Store) and binds the socket
    reset();
    let empty = d.join("empty-store");
    nanodregg_devtools::mkdirs(&empty).unwrap();
    let (err, _) = ends_over(&d, &keys, &anchors, &empty);
    assert!(!err.contains("sockDir"), "control: stderr: {err}");
    let m = fs::symlink_metadata(r.join("broker.sock")).unwrap();
    assert!(m.file_type().is_socket(), "control: no socket bound");
    assert_eq!(
        m.permissions().mode() & 0o7777,
        0o660,
        "control: socket mode"
    );
    assert_eq!(m.gid(), me(&socks).1, "control: socket group");
    assert_eq!(
        fs::symlink_metadata(&r).unwrap().permissions().mode() & 0o7777,
        0o2710,
        "control: resident directory mode"
    );
    // CONTROL: the next life meets the last life's socket, unlinks it and binds again
    let (err, _) = ends_over(&d, &keys, &anchors, &empty);
    assert!(
        !err.contains("sockDir") && !err.contains("keybroker: socket "),
        "restart: stderr: {err}"
    );
    let again = fs::symlink_metadata(r.join("broker.sock")).unwrap();
    assert!(again.file_type().is_socket(), "restart: no socket bound");
}

#[test]
fn a_peer_of_another_uid_or_group_is_refused_by_name() {
    let d = dir("peer");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let (up, seen) = upstream(Mode::Ok, pki.server(HOST, false));
    let w = World::genesis("peer");
    w.allowance("01", "claude-m", 7, 100_000);
    let (uid, gid) = me(&d);
    let first = |b: &Broker| {
        let mut r = Resident::connect(b);
        r.ask(&ask(b"claude-m", 10, b"hi"))
    };
    // CONTROL: this uid with SOCKDIR's group is served (a decision, not peerRefused)
    let b = start(&d, &keys, &anchors, &up, &w);
    let a = first(&b);
    assert!(
        !is_refused(&a, BrokerRefusal::PeerRefused),
        "control: refused {a:?}"
    );
    drop(b);
    // a broker serving another uid
    let b = start_peer(&d, &keys, &anchors, &up, &w, uid.wrapping_add(1));
    let mut r = Resident::connect(&b);
    let f = read_frame(&mut r.s).unwrap();
    assert!(
        is_refused(&Answer::decode(&f).unwrap(), BrokerRefusal::PeerRefused),
        "another uid: not peerRefused"
    );
    drop(r);
    drop(b);
    // SOCKDIR's group is not the peer's gid
    match other_group(gid) {
        Some(g) => {
            let _ = fs::remove_dir_all(&d.socks);
            sockdir(&d.socks);
            std::os::unix::fs::chown(&d.socks, None, Some(g)).unwrap();
            fs::set_permissions(&d.socks, fs::Permissions::from_mode(0o2710)).unwrap();
            let b = start(&d, &keys, &anchors, &up, &w);
            let mut r = Resident::connect(&b);
            let f = read_frame(&mut r.s).unwrap();
            assert!(
                is_refused(&Answer::decode(&f).unwrap(), BrokerRefusal::PeerRefused),
                "another group: not peerRefused"
            );
        }
        None => eprintln!("unrun: this uid has no supplementary group for the group plant"),
    }
    assert!(
        seen.lock().unwrap().is_empty(),
        "a refused peer reached the upstream"
    );
}
