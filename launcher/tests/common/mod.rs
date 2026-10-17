//! What the launcher's integration tests share (`broker.rs`, `resident.rs`): a real Store under the
//! operator's custody (`World`), the test's own PKI and fake TLS provider, keybroker started with
//! the emitted unit's argv, and a resident stand-in. Each test crate uses its own subset.
#![allow(dead_code)]

use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
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

pub const KEY: &[u8] = b"CANARY-sk-0123456789abcdef";
pub const WINDOW_MS: u64 = 3000;

/// A test's own scratch root, removed with its socket directory when the test ends.
pub struct Scratch {
    pub root: PathBuf,
    pub socks: PathBuf,
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

pub fn dir(name: &str) -> Scratch {
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
pub fn sockdir(p: &Path) {
    nanodregg_devtools::mkdirs(p).unwrap();
    fs::set_permissions(p, fs::Permissions::from_mode(0o2710)).unwrap();
}

/// This process's uid and primary gid (of a directory it made, under a parent with no setgid bit).
pub fn me(d: &Path) -> (u32, u32) {
    let m = fs::metadata(d).unwrap();
    (m.uid(), m.gid())
}

/// A group of this process other than its primary one, if it has one (`/proc/self/status`).
pub fn other_group(primary: u32) -> Option<u32> {
    let st = fs::read_to_string("/proc/self/status").unwrap();
    let line = st.lines().find(|l| l.starts_with("Groups:"))?;
    line["Groups:".len()..]
        .split_whitespace()
        .filter_map(|g| g.parse().ok())
        .find(|g| *g != primary)
}

/// Lean's host for every `claude-…` model (`Broker.anthropic.host`).
pub const HOST: &str = "api.anthropic.com";

/// The test's own PKI: a CA (whose certificate is the operator's anchor file) and server
/// certificates for the fake upstream.
pub struct Pki {
    pub ca: Issuer<'static, KeyPair>,
    pub ca_pem: String,
}

impl Pki {
    pub fn new() -> Pki {
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
    pub fn anchors(&self, d: &Path, mode: u32) -> PathBuf {
        let p = d.join("anchors.pem");
        fs::write(&p, &self.ca_pem).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
        p
    }
    /// A TLS 1.3 server with a certificate for `name`, signed by the CA, or (self_signed) by its
    /// own key.
    pub fn server(&self, name: &str, self_signed: bool) -> Arc<ServerConfig> {
        self.server_at(name, self_signed, &rustls::version::TLS13)
    }
    /// A server that speaks only `version`, with a certificate for `name`.
    pub fn server_at(
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

pub fn key_file(d: &Path, mode: u32) -> PathBuf {
    let p = d.join("keys");
    fs::write(&p, [b"7 ".as_slice(), KEY, b"\n"].concat()).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
    p
}

/// How the fake provider answers.
#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    /// `200` and `{"ok":true}`, then `close_notify`
    Ok,
    /// `200` and the request itself (the key included), then `close_notify`
    Echo,
    /// `200` and `{"ok":true}`, then the TCP connection closes with no `close_notify`
    Truncate,
}

/// A fake provider over TLS with the server configuration `tls`, answering as `mode` says; keeps
/// every request it received. A connection whose handshake fails records nothing.
pub fn upstream(mode: Mode, tls: Arc<ServerConfig>) -> (String, Arc<Mutex<Vec<Vec<u8>>>>) {
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
pub struct World {
    pub root: PathBuf,
    pub store: PathBuf,
    /// the operator's follower Store (`host follow`), the one a controller tails
    pub fstore: PathBuf,
    pub operator: String,
    pub pkg: String,
    pub ws: PathBuf,
    pub holding: PathBuf,
    pub _serve: Supervisor,
    pub _follow: Supervisor,
}

pub fn text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

pub fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

impl World {
    pub fn nd(&self, args: &[&str]) -> Output {
        Command::new(nd())
            .env("ND_WORKSPACE", &self.ws)
            .env("ND_HOLDING", &self.holding)
            .args(args)
            .output()
            .unwrap()
    }
    pub fn run(&self, args: &[&str]) -> String {
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
    pub fn allowance(&self, resident: &str, model: &str, slot: u32, cap: u64) -> String {
        let state = format!(
            "(record (cap {cap}) (keySlot {slot}) (maxTokens 100) (microPerKTok 1000) (model \"{model}\") (resident #{resident}) (revoked false) (windowMs {WINDOW_MS}))"
        );
        line(&self.run(&["create", "--pkg", &self.pkg, &state]), "id ").to_owned()
    }

    /// `nd install` of the package text at `rel` in the repository; its id.
    pub fn install(&self, rel: &str) -> String {
        let text = fs::read_to_string(repo().join(rel)).unwrap();
        line(&self.run(&["install", &text]), "id ").to_owned()
    }

    pub fn genesis(name: &str) -> World {
        World::genesis_following(name, None)
    }

    /// `genesis`, with the follower Store at `follow` (a directory that does not exist yet, whose
    /// parent does) instead of the World's own `stores/F`.
    pub fn genesis_following(name: &str, follow: Option<PathBuf>) -> World {
        // A short root: a Unix socket path must fit sun_path.
        let root = nanodregg_devtools::scratch(&format!("kbw{}{name}", std::process::id()));
        for d in ["ws", "holding", "stores"] {
            nanodregg_devtools::mkdirs(&root.join(d)).unwrap();
        }
        let root = root.canonicalize().unwrap();
        let (ws, holding) = (root.join("ws"), root.join("holding"));
        let store = root.join("stores/W");
        let fstore = follow.unwrap_or_else(|| root.join("stores/F"));
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
            fstore,
            operator: operator.to_owned(),
            pkg: String::new(),
            ws,
            holding,
            _serve: serve,
            _follow: follow,
        };
        w.pkg = w.install("world/hosting/Allowance");
        w
    }
}

impl Drop for World {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

pub struct Broker {
    pub child: Child,
    pub socks: PathBuf,
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
pub fn rendered(values: &[(&str, &std::ffi::OsStr)]) -> Command {
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
pub fn argv(
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

pub fn ask(model: &[u8], max_tokens: u32, text: &[u8]) -> Vec<u8> {
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
pub struct Resident {
    pub s: UnixStream,
    pub got: Vec<u8>,
}

impl Resident {
    pub fn connect(b: &Broker) -> Resident {
        Resident::connect_as(b, "01")
    }
    pub fn connect_as(b: &Broker, name: &str) -> Resident {
        let s = UnixStream::connect(b.socks.join(name).join("broker.sock")).unwrap();
        s.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
        Resident { s, got: Vec::new() }
    }
    pub fn ask(&mut self, a: &[u8]) -> Answer {
        write_frame(&mut self.s, a).unwrap();
        let f = read_frame(&mut self.s).unwrap();
        self.got.extend_from_slice(&f);
        Answer::decode(&f).unwrap()
    }
}

pub fn is_refused(a: &Answer, r: BrokerRefusal) -> bool {
    matches!(a, Answer::Refused { broker_refusal } if *broker_refusal == r)
}

pub fn contains(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

/// Sleep until the operator clock is in a later window than `t0_ms` (bounded).
pub fn next_window(t0_ms: u64) {
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
pub fn early_in_window() -> u64 {
    let deadline = Instant::now() + Duration::from_secs(10);
    while now_ms() % WINDOW_MS > WINDOW_MS / 3 {
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(20));
    }
    now_ms()
}

pub fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}
/// keybroker for `residents` over the World `w`, trusting `anchors`, serving the uid `peer`; its
/// sockets in `socks` (02710, this uid's), its PID files in `pids`. Waits (bounded) until every
/// resident's socket is bound at the mode that admits exactly `peer`: 0600 when `peer` is this
/// uid, else 0660 (HOSTING-17 §5, HOSTING-21).
#[allow(clippy::too_many_arguments)]
pub fn start_residents(
    socks: &Path,
    pids: &Path,
    keys: &Path,
    anchors: &Path,
    up: &str,
    w: &World,
    residents: &[&str],
    peer: u32,
) -> Broker {
    // the last life's sockets go first, so a socket seen below is this life's (keybroker's own
    // unlink of a stale socket is broker.rs's a_bad_socket_directory_stops_keybroker_by_name's control)
    for r in residents {
        let _ = fs::remove_file(socks.join(r).join("broker.sock"));
    }
    let mut child = argv(
        keys,
        anchors,
        socks,
        pids,
        up,
        &w.store,
        &w.operator,
        &residents.join(","),
        &peer.to_string(),
    )
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
    let mode = if peer == me(socks).0 { 0o600 } else { 0o660 };
    let deadline = Instant::now() + Duration::from_secs(20);
    let bound = |r: &str| {
        fs::symlink_metadata(socks.join(r).join("broker.sock"))
            .is_ok_and(|m| m.permissions().mode() & 0o7777 == mode)
    };
    while !residents.iter().all(|r| bound(r)) {
        let ended = child.try_wait().unwrap().is_some();
        if ended || Instant::now() > deadline {
            let _ = child.kill();
            let out = child.wait_with_output().unwrap();
            panic!(
                "keybroker opened no socket at mode {mode:o}: {}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    Broker {
        child,
        socks: socks.to_path_buf(),
    }
}

/// Put a copy of the executable `src` at `dst` without this process ever holding `dst` open for
/// writing. Tests run on parallel threads, and a thread that spawns a child copies this process's
/// file table into it; until that child execs, it holds every fd open at that moment (`O_CLOEXEC`
/// closes them only AT exec). If one of them is a write fd on `dst`, an exec of `dst` in that
/// window fails `ETXTBSY` (HOST-10 saw it once at the CONTROL's exec). `cp` holds the only write fd,
/// in its own process, and it has exited before `dst` is run.
pub fn place_exe(src: &Path, dst: &Path) {
    let st = Command::new("cp")
        .arg("--")
        .arg(src)
        .arg(dst)
        .stdin(Stdio::null())
        .status()
        .unwrap();
    assert!(
        st.success(),
        "plant: cp {} {}: {st}",
        src.display(),
        dst.display()
    );
}
