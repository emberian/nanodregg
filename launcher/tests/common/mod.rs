//! What the launcher's integration tests share (`broker.rs`, `resident.rs`, `resident_bell.rs`,
//! `members.rs`): a real Store under the
//! operator's custody (`World`), the test's own PKI and fake TLS provider, keybroker started with
//! the emitted unit's argv, and a resident stand-in. Each test crate uses its own subset.
#![allow(dead_code)]

use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use nanodregg_devtools::{Supervisor, lean_bin, nd, nd_supervise, repo, supervise_host};
use nanodregg_launcher::broker_generated::wire::{Answer, Ask, BrokerRefusal};
use nanodregg_launcher::broker_generated::{read_frame, write_frame};
use rcgen::{BasicConstraints, CertificateParams, IsCa, Issuer, KeyPair, PublicKeyData};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::{ServerConfig, ServerConnection, StreamOwned};

pub const KEY: &[u8] = b"CANARY-sk-0123456789abcdef";
pub const WINDOW_MS: u64 = 3000;
/// The reply text the fake provider's `Mode::Ok` body carries; the resident receives exactly this
/// (HOSTING-29: Lean reads it out of the provider's JSON).
pub const REPLY: &[u8] = b"hello back";
/// The fake provider's Anthropic-shaped answer: fields before and after `content`, a nested object.
pub const ANTHROPIC_BODY: &[u8] = b"{\"id\":\"msg_01\",\"type\":\"message\",\"role\":\"assistant\",\"model\":\"claude-m\",\"content\":[{\"type\":\"text\",\"text\":\"hello back\"}],\"stop_reason\":\"end_turn\",\"usage\":{\"input_tokens\":3,\"output_tokens\":2}}";

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
    // A Unix socket path is at most 107 bytes (sun_path) and a resident's socket directory is its
    // grain's 64 hex digits (HOSTING-26: keybroker serves the World's resident grains), so SOCKDIR
    // is as short as `Short`'s: one letter per test and this process's pid in base 36.
    let letter = match name {
        "main" => 'm',
        "echo" => 'e',
        "mode" => 'o',
        "tls" => 't',
        "sockdir" => 's',
        "peer" => 'p',
        "mech" => 'c',
        "sig" => 'g',
        "follow" => 'f',
        "reply" => 'y',
        "pin" => 'n',
        "pins" => 'i',
        // resident.rs's own `Short`s are r, m, f, q, p
        "res" => 'k',
        // resident_bell.rs's own `Short`s are b, n, e
        "bel" => 'l',
        // members.rs's held tree (CLIENT-38), in a process of its own
        "hold" => 'h',
        // broker.rs's lost deciders (CLIENT-39)
        "lost" => 'u',
        // agent_real.rs (HOSTING-52): the real provider, opt-in
        "real" => 'a',
        // certify.rs (HOSTING-56): the writer's certify slot
        "cert" => 'z',
        // certify.rs (OPS-21): a restored Store beside the certified-head record
        "rcert" => 'x',
        // agent_hole.rs (HOSTING-58): the fake provider's tour and the real one's
        "hole" => 'd',
        "holer" => 'v',
        // broker.rs's daily ask cap (HOSTING-62)
        "asks" => 'q',
        other => panic!("plant: dir({other}) has no socket-directory letter"),
    };
    let socks = short_dir(&letter.to_string());
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

/// A fake provider's TLS configuration and the pin of its leaf key: the lowercase hex SHA-256 of
/// its SubjectPublicKeyInfo, as an operator's PINS line names it (HOSTING-28).
pub struct Server {
    pub tls: Arc<ServerConfig>,
    pub pin: String,
}

/// The test's own PKI: a CA (whose certificate is the operator's anchor file) and server
/// certificates for the fake upstream. The operator's PINS file is `pins` beside the anchor file
/// (`argv_with` passes it): `anchors` writes it empty (every grant refused `pinMismatch`), `pin`
/// rewrites it to name the given servers' leaf keys for Lean's host.
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
        pins_file(d, b"");
        p
    }
    /// The operator's PINS file in `d`: `servers`' leaf keys, pinned for Lean's host.
    pub fn pin(&self, d: &Path, servers: &[&Server]) -> PathBuf {
        let text: String = servers
            .iter()
            .map(|s| format!("{HOST} {}\n", s.pin))
            .collect();
        pins_file(d, text.as_bytes())
    }
    /// A TLS 1.3 server with a certificate for `name`, signed by the CA, or (self_signed) by its
    /// own key.
    pub fn server(&self, name: &str, self_signed: bool) -> Server {
        self.server_at(name, self_signed, &rustls::version::TLS13)
    }
    /// A server that speaks only `version`, with a certificate for `name`.
    pub fn server_at(
        &self,
        name: &str,
        self_signed: bool,
        version: &'static rustls::SupportedProtocolVersion,
    ) -> Server {
        let key = KeyPair::generate().unwrap();
        let spki = ring::digest::digest(&ring::digest::SHA256, &key.subject_public_key_info());
        let pin: String = spki.as_ref().iter().map(|b| format!("{b:02x}")).collect();
        let params = CertificateParams::new(vec![name.to_owned()]).unwrap();
        let cert = if self_signed {
            params.self_signed(&key).unwrap()
        } else {
            params.signed_by(&key, &self.ca).unwrap()
        };
        let der: CertificateDer<'static> = cert.der().clone();
        let pk = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.serialize_der()));
        let tls = Arc::new(
            ServerConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
                .with_protocol_versions(&[version])
                .unwrap()
                .with_no_client_auth()
                .with_single_cert(vec![der], pk)
                .unwrap(),
        );
        Server { tls, pin }
    }
}

/// The operator's PINS file in `d` (`d/pins`, mode 0644) holding `bytes`.
pub fn pins_file(d: &Path, bytes: &[u8]) -> PathBuf {
    let p = d.join("pins");
    fs::write(&p, bytes).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(0o644)).unwrap();
    p
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
    /// `200` and `ANTHROPIC_BODY` (whose reply text is `REPLY`), then `close_notify`
    Ok,
    /// this status and this body, then `close_notify`
    Says(u16, &'static [u8]),
    /// `200` and the request itself (the key included), then `close_notify`
    Echo,
    /// `200` and `ANTHROPIC_BODY`, then the TCP connection closes with no `close_notify`
    Truncate,
}

/// Every request a fake provider received, in order.
pub type Seen = Arc<Mutex<Vec<Vec<u8>>>>;

/// A fake provider over TLS with the server configuration `tls`, answering as `mode` says; keeps
/// every request it received. A connection whose handshake fails records nothing.
pub fn upstream(mode: Mode, server: &Server) -> (String, Seen) {
    let (addr, seen, _) = upstream_held(mode, server);
    (addr, seen)
}

/// The longest a held reply waits for its release.
pub const HOLD_MAX: Duration = Duration::from_secs(60);

/// `upstream`, and a switch: while it is set, a request is recorded and its reply held back (at
/// most `HOLD_MAX`), so a test can end the asker after its ask was spent and before any answer.
pub fn upstream_held(mode: Mode, server: &Server) -> (String, Seen, Arc<AtomicBool>) {
    let hold = Arc::new(AtomicBool::new(false));
    let h2 = Arc::clone(&hold);
    let tls = Arc::clone(&server.tls);
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
            let held = Instant::now();
            while h2.load(Ordering::SeqCst) && held.elapsed() < HOLD_MAX {
                std::thread::sleep(Duration::from_millis(50));
            }
            let (status, body) = match mode {
                Mode::Echo => (200, req),
                Mode::Says(st, b) => (st, b.to_vec()),
                Mode::Ok | Mode::Truncate => (200, ANTHROPIC_BODY.to_vec()),
            };
            let _ = c.write_all(
                &[
                    format!("HTTP/1.0 {status} X\r\nContent-Length: ").as_bytes(),
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
    (addr, seen, hold)
}

/// A real Store and the operator's custody: `host genesis` from custody's own keys, `host serve`
/// under `nd-supervise`; `run` is the operator's `nd`, which must succeed.
pub struct World {
    pub root: PathBuf,
    pub store: PathBuf,
    /// the operator's follower Store (`host follow`), the one a controller tails
    pub fstore: PathBuf,
    pub operator: String,
    /// the founder's grant on the World (`genesis`'s `grant`), the parent of the operator's grants
    pub grant: String,
    /// `host genesis`'s arguments after STORE (`nano --nonce N KEY NEXT`) and what it printed, so a
    /// later Store of the same World can be made (`follower`)
    pub genesis_args: Vec<String>,
    pub genesis_out: String,
    pub pkg: String,
    /// `world/grain/Lifecycle`'s id
    pub lifecycle: String,
    /// two resident grains born at genesis (installed, never started): keybroker serves exactly the
    /// World's resident grains (HOSTING-26), so these are the sockets a broker test asks on
    pub r1: String,
    pub r2: String,
    pub ws: PathBuf,
    pub holding: PathBuf,
    /// the writer's socket, alone in a directory of its own: a confined connector sees the socket's
    /// directory (CLIENT-20), so it never sits in a workspace holding keys
    pub host_sock: PathBuf,
    pub _serve: Supervisor,
    pub _follow: Supervisor,
}

/// A member's own `nd` (not the operator's): its own workspace and holding, its follow socket and
/// the writer's host socket given explicitly.
pub fn member_nd(ws: &Path, holding: &Path, follow: &Path, host: &Path, args: &[&str]) -> Output {
    Command::new(nd())
        .env("ND_WORKSPACE", ws)
        .env("ND_HOLDING", holding)
        .env("ND_FOLLOW_SOCK", follow)
        .env("ND_HOST_SOCK", host)
        .args(args)
        .output()
        .unwrap()
}

pub fn both(o: &Output) -> String {
    format!("{}{}", text(o), String::from_utf8_lossy(&o.stderr))
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
            .env("ND_HOST_SOCK", &self.host_sock)
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
        self.allowance_w(resident, model, slot, cap, WINDOW_MS)
    }

    /// `allowance`, its window `window_ms` long.
    pub fn allowance_w(&self, resident: &str, model: &str, slot: u32, cap: u64, window_ms: u64) -> String {
        let state = format!(
            "(record (cap {cap}) (keySlot {slot}) (maxTokens 100) (microPerKTok 1000) (model \"{model}\") (resident #{resident}) (revoked false) (windowMs {window_ms}))"
        );
        line(&self.run(&["create", "--pkg", &self.pkg, &state]), "id ").to_owned()
    }

    /// A member's own follower: a Store of this World at `store` (made by `host genesis` with the
    /// World's nonce: it must print what the first genesis printed), followed by `host follow` as
    /// `member` through `grant` under `nd-supervise`, its socket `sock`, `hide` hidden.
    pub fn follower(
        &self,
        store: &Path,
        sock: &Path,
        hide: &Path,
        member: &str,
        grant: &str,
    ) -> Supervisor {
        let o = Command::new(lean_bin("host"))
            .arg("genesis")
            .arg(store)
            .args(&self.genesis_args)
            .output()
            .unwrap();
        assert_eq!(text(&o), self.genesis_out, "one genesis, another Store");
        supervise_host(
            &nd_supervise(),
            sock,
            hide,
            store,
            &["follow", store.to_str().unwrap(), member, grant],
        )
    }

    /// A resident grain born (installed) with entry `entry`: its id, its socket's name.
    pub fn resident(&self, entry: &str) -> String {
        let state = format!("(record (entry \"{entry}\") (kind resident) (phase installed))");
        line(
            &self.run(&["create", "--pkg", &self.lifecycle, &state]),
            "id ",
        )
        .to_owned()
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
        for d in ["ws", "holding", "stores", "run"] {
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
        let genesis_args: Vec<String> = [
            "nano",
            "--nonce",
            line(&g, "nonce "),
            line(&keys, "key "),
            line(&keys, "next "),
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let serve = supervise_host(
            &nd_supervise(),
            &root.join("run/host.sock"),
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
        let host_sock = root.join("run/host.sock");
        let mut w = World {
            root,
            store,
            fstore,
            operator: operator.to_owned(),
            grant: grant.to_owned(),
            genesis_args,
            genesis_out: g.clone(),
            pkg: String::new(),
            lifecycle: String::new(),
            r1: String::new(),
            r2: String::new(),
            ws,
            holding,
            host_sock,
            _serve: serve,
            _follow: follow,
        };
        w.pkg = w.install("world/hosting/Allowance");
        w.lifecycle = w.install("world/grain/Lifecycle");
        w.r1 = w.resident("r1");
        w.r2 = w.resident("r2");
        w
    }
}

impl Drop for World {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// A founder's own member (not a resident's: a resident's member socket is nd-members', `Members`):
/// an observe-on-the-World member enrolled by the operator, its one-record hosted custody in `ws`,
/// its own follower Store, and `nd --stdio` served on `sock` by nd-supervise, confined to write
/// `ws` and connect [host.sock, its follow socket] (CLIENT-24). One uid here: nd-supervise binds
/// 0600 with no `--group`/`--peer` (the deployment's 0660 group socket with its peer check is
/// CLIENT-21/24's, declared unrun across uids).
pub struct Member {
    /// the member's id (hex), the resident's identity in the World
    pub id: String,
    pub ws: PathBuf,
    pub sock: PathBuf,
    _follow: Supervisor,
    _stdio: Supervisor,
}

impl World {
    /// A hosted member's custody made in `ws` (`nd --init-hosted`, `init`; `holding` its holding),
    /// enrolled by the operator and granted `observe` on the World: its id and that grant.
    pub fn enrol(&self, ws: &Path, holding: &Path) -> (String, String) {
        for d in [ws, holding] {
            nanodregg_devtools::mkdirs(d).unwrap();
            fs::set_permissions(d, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let (op_follow, host) = (self.ws.join("follow.sock"), self.host_sock.clone());
        let o = member_nd(ws, holding, &op_follow, &host, &["--init-hosted"]);
        assert!(o.status.success(), "nd --init-hosted: {}", both(&o));
        let o = member_nd(ws, holding, &op_follow, &host, &["init", &self.operator]);
        assert!(o.status.success(), "nd init: {}", both(&o));
        let token = line(&text(&o), "join ").to_owned();
        let id = line(&self.run(&["enroll", &token]), "id ").to_owned();
        let observe = line(
            &self.run(&["grant", "world", &id, "observe", "--via", &self.grant]),
            "id ",
        )
        .to_owned();
        (id, observe)
    }

    /// Provision resident `name`'s member as the operator's provisioning step does (HOSTING-30,
    /// HOSTING-32): its custody in `MEMBERS/<name>` (`enrol`), its follower Store
    /// `STATE/<name>/store` from the World's genesis, and `STATE/<name>/follow` (`MEMBER GRANT`,
    /// 0600). The member's id. nd-members serves it from the next `residents` answer naming it.
    pub fn provision(&self, r: &Roots, name: &str) -> String {
        let holding = r.base.0.join(format!("{}.holding", &name[..8]));
        let (id, observe) = self.enrol(&r.members().join(name), &holding);
        let st = r.state().join(name);
        nanodregg_devtools::mkdirs(&st).unwrap();
        fs::set_permissions(&st, fs::Permissions::from_mode(0o700)).unwrap();
        let o = Command::new(lean_bin("host"))
            .arg("genesis")
            .arg(st.join("store"))
            .args(&self.genesis_args)
            .output()
            .unwrap();
        assert_eq!(text(&o), self.genesis_out, "one genesis, another Store");
        let f = st.join("follow");
        fs::write(&f, format!("{id} {observe}\n")).unwrap();
        fs::set_permissions(&f, fs::Permissions::from_mode(0o600)).unwrap();
        id
    }

    /// Enrol a founder's member in `ws` and serve its `nd --stdio` on `sock` (whose directory must
    /// exist); its follower Store at `store`, its follow socket `follow`, PID files in `pids`.
    pub fn member(
        &self,
        ws: &Path,
        follow: &Path,
        store: &Path,
        sock: &Path,
        pids: &Path,
    ) -> Member {
        let (id, observe) = self.enrol(ws, &ws.with_extension("holding"));
        let host = self.host_sock.clone();
        let follow_s = self.follower(store, follow, ws, &id, &observe);
        let nd_exe = nd().canonicalize().unwrap();
        let child = Command::new(nd_supervise())
            .arg(sock)
            // the operator's workspace (its custody), named hidden: nd-supervise starts no child
            // with nothing hidden (CLIENT-8)
            .arg("--hide")
            .arg(&self.ws)
            .arg("--write")
            .arg(ws)
            .arg("--exec")
            .arg(&nd_exe)
            .arg("--connect")
            .arg(&host)
            .arg("--connect")
            .arg(follow)
            .arg("--")
            .arg(&nd_exe)
            .arg("--stdio")
            .arg(ws)
            .arg(follow)
            .arg(&host)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(fs::File::create(pids.join("member-stdio.err")).unwrap())
            .spawn()
            .unwrap();
        let stdio = Supervisor::hold(child, pids.join("member-stdio.pid"));
        until(
            "the member socket",
            20,
            || UnixStream::connect(sock).is_ok(),
            &|| {
                format!(
                    "nd-supervise never bound {}: {}",
                    sock.display(),
                    fs::read_to_string(pids.join("member-stdio.err")).unwrap_or_default()
                )
            },
        );
        Member {
            id,
            ws: ws.to_path_buf(),
            sock: sock.to_path_buf(),
            _follow: follow_s,
            _stdio: stdio,
        }
    }
}

pub struct Broker {
    pub child: Child,
    pub socks: PathBuf,
    /// the residents whose sockets the test waited for (the first is `Resident::connect`'s)
    pub names: Vec<String>,
}

impl Drop for Broker {
    // The sockets stay (the scratch removes them).
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// The ExecStart of the emitted unit `deploy/units/linux/<unit>` (from Ops/Units.lean), which must
/// run `/opt/nd/bin/<exe>`, as a Command of `bin` with every rendered word after the program
/// replaced by this test's value for that word: the ORDER is the unit's, so a unit and a parser
/// that disagree on it are red here (ROOT, 10-18; OPS-2's fd1d4b2 class). A word with no test value,
/// or a test value no word asks for, is red too. A word the unit says twice takes one value.
pub fn unit_argv(unit: &str, exe: &str, bin: &str, values: &[(&str, &std::ffi::OsStr)]) -> Command {
    let text = fs::read_to_string(repo().join("deploy/units/linux").join(unit)).unwrap();
    let line = text
        .lines()
        .find_map(|l| l.strip_prefix("ExecStart="))
        .expect("the unit has an ExecStart");
    let mut words = line.split(' ');
    let prog = format!("/opt/nd/bin/{exe}");
    assert_eq!(words.next(), Some(prog.as_str()), "{unit} runs {exe}");
    let mut c = Command::new(bin);
    let mut used = std::collections::BTreeSet::new();
    for w in words {
        let (k, v) = values
            .iter()
            .find(|(k, _)| *k == w)
            .unwrap_or_else(|| panic!("{unit}'s word {w} has no test value"));
        c.arg(v);
        used.insert(*k);
    }
    assert_eq!(
        used.len(),
        values.len(),
        "a test value {unit} never asks for"
    );
    c
}

/// keybroker's argv as its emitted unit renders it (`unit_argv`).
pub fn rendered(values: &[(&str, &std::ffi::OsStr)]) -> Command {
    unit_argv(
        "nd-keybroker.service",
        "keybroker",
        env!("CARGO_BIN_EXE_keybroker"),
        values,
    )
}

/// The test's values for the unit's words. PINS is `pins` beside `anchors` (`Pki::anchors` writes
/// it, `Pki::pin` fills it).
#[allow(clippy::too_many_arguments)]
pub fn argv(
    keys: &Path,
    anchors: &Path,
    socks: &Path,
    pids: &Path,
    up: &str,
    store: &Path,
    operator: &str,
    peer: &str,
) -> Command {
    argv_with(
        keys,
        anchors,
        socks,
        pids,
        up,
        store,
        operator,
        peer,
        &lean_bin("hosting-broker"),
    )
}

/// `argv`, with `decider` for the unit's DECIDER.
#[allow(clippy::too_many_arguments)]
pub fn argv_with(
    keys: &Path,
    anchors: &Path,
    socks: &Path,
    pids: &Path,
    up: &str,
    store: &Path,
    operator: &str,
    peer: &str,
    decider: &Path,
) -> Command {
    let pins = anchors.with_file_name("pins");
    rendered(&[
        ("/etc/nd/keybroker/provider.key", keys.as_os_str()),
        ("/etc/nd/keybroker/anchors.pem", anchors.as_os_str()),
        ("/etc/nd/keybroker/pins", pins.as_os_str()),
        ("/run/nd-broker", socks.as_os_str()),
        ("/run/nd-keybroker", pids.as_os_str()),
        ("api.anthropic.com:443", std::ffi::OsStr::new(up)),
        ("/srv/nd/store", store.as_os_str()),
        ("${ND_OPERATOR}", std::ffi::OsStr::new(operator)),
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
        Resident::connect_as(b, &b.names[0])
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

/// The operator time keybroker started its decider at (`T0`, the decider's first argument, read from
/// its command line by the PID file keybroker wrote in `pids`): the start every allowance window is
/// forfeit from (`Broker.start`), as the broker saw it, not as the test guessed it.
pub fn decider_t0(pids: &Path) -> u64 {
    let pid = fs::read_to_string(pids.join("decider.pid")).unwrap();
    let cmd = fs::read(format!("/proc/{}/cmdline", pid.trim())).unwrap();
    let t0 = cmd.split(|b| *b == 0).nth(1).unwrap();
    std::str::from_utf8(t0).unwrap().parse().unwrap()
}

/// Wait until the operator clock is past the window keybroker started in (its decider's own T0,
/// `decider_t0`): the first window whose asks are not forfeit, however long the start took.
pub fn past_start_window(pids: &Path) {
    let t0 = decider_t0(pids);
    while now_ms() / WINDOW_MS <= t0 / WINDOW_MS {
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// CPU ticks (user and system) used so far by `pid` and every live process below it, from /proc.
pub fn tree_ticks(pid: u32) -> u64 {
    let mut stats: Vec<(u32, u32, u64)> = Vec::new();
    for e in fs::read_dir("/proc").into_iter().flatten().flatten() {
        let Some(p) = e.file_name().to_str().and_then(|n| n.parse::<u32>().ok()) else {
            continue;
        };
        let Ok(st) = fs::read_to_string(e.path().join("stat")) else {
            continue;
        };
        let Some(rest) = st.rsplit_once(')').map(|(_, r)| r) else {
            continue;
        };
        let f: Vec<&str> = rest.split_whitespace().collect();
        let n = |i: usize| f.get(i).and_then(|x| x.parse::<u64>().ok()).unwrap_or(0);
        stats.push((p, n(1) as u32, n(11) + n(12)));
    }
    let mut tree = vec![pid];
    let mut i = 0;
    while i < tree.len() {
        let parent = tree[i];
        tree.extend(stats.iter().filter(|s| s.1 == parent).map(|s| s.0));
        i += 1;
    }
    stats.iter().filter(|s| tree.contains(&s.0)).map(|s| s.2).sum()
}

/// Wait for `child` to end, its stderr read as it comes (a full pipe never stalls it). A hang is
/// `idle` with no CPU used by the child or any process below it while it has not ended: a loaded box
/// slows a run and still schedules it, so the bound is the run's own progress, never a fixed number
/// of wall-clock seconds from the spawn. Returns its status and its stderr.
pub fn wait_live(mut child: Child, what: &str, idle: Duration) -> (ExitStatus, String) {
    let mut err = child.stderr.take();
    let reader = std::thread::spawn(move || {
        let mut s = Vec::new();
        if let Some(e) = err.as_mut() {
            let _ = e.read_to_end(&mut s);
        }
        String::from_utf8_lossy(&s).into_owned()
    });
    let (mut ticks, mut since) = (tree_ticks(child.id()), Instant::now());
    let status = loop {
        if let Some(st) = child.try_wait().unwrap() {
            break st;
        }
        let t = tree_ticks(child.id());
        if t != ticks {
            (ticks, since) = (t, Instant::now());
        } else if since.elapsed() > idle {
            let _ = child.kill(); // our own child, by its handle
            let _ = child.wait();
            panic!(
                "{what} used no CPU for {} s and did not end (a hang, not a slow box): {}",
                idle.as_secs(),
                reader.join().unwrap_or_default()
            );
        }
        std::thread::sleep(Duration::from_millis(200));
    };
    (status, reader.join().unwrap_or_default())
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
/// keybroker over the World `w`, trusting `anchors`, serving the uid `peer`; its sockets in `socks`
/// (02710, this uid's), its PID files in `pids`. It serves the World's resident grains (HOSTING-26:
/// no operator list); this waits (bounded) until each of `residents` is bound at the mode that admits
/// exactly `peer`: 0600 when `peer` is this uid, else 0660 (HOSTING-17 §5, HOSTING-21).
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
        names: residents.iter().map(|r| r.to_string()).collect(),
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

/// A short scratch directory (`<prefix><pid in base 36>`): a socket path is at most 107 bytes and a
/// resident's directory name is 64 hex digits, so SOCKDIR must stay within 30 bytes. Removed on drop.
pub struct Short(pub PathBuf);

/// A short scratch directory `<prefix><pid in base 36>` (made fresh): a socket path is at most 107
/// bytes and a resident's directory name is 64 hex digits, so a socket root must stay within 30
/// bytes. The caller removes it.
pub fn short_dir(prefix: &str) -> PathBuf {
    let mut n = std::process::id();
    let mut tag = String::new();
    while n > 0 {
        tag.insert(0, char::from_digit(n % 36, 36).unwrap());
        n /= 36;
    }
    let p = nanodregg_devtools::scratch(&format!("{prefix}{tag}"));
    assert!(
        p.as_os_str().len() + 1 + 64 + "/broker.sock".len() <= 107,
        "plant: {} is too long for a socket path",
        p.display()
    );
    p
}

impl Short {
    pub fn new(prefix: &str) -> Short {
        Short(short_dir(prefix))
    }
}

impl Drop for Short {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A scratch tree removed on drop (also when an assertion fails).
pub struct Gone(pub PathBuf);

impl Drop for Gone {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Wait (bounded: a liveness deadline, a miss renders `hang`, never a verdict) until `ok()`.
pub fn until(what: &str, secs: u64, mut ok: impl FnMut() -> bool, log: &dyn Fn() -> String) {
    let deadline = Instant::now() + Duration::from_secs(secs);
    while !ok() {
        assert!(
            Instant::now() < deadline,
            "hang: {what} not within {secs} s:\n{}",
            log()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// grain-launch's argv as its emitted unit renders it (`unit_argv`).
pub fn grain_launch_rendered(values: &[(&str, &std::ffi::OsStr)]) -> Command {
    unit_argv(
        "nd-grain-launch@.service",
        "grain-launch",
        env!("CARGO_BIN_EXE_grain-launch"),
        values,
    )
}

/// The roots one nd-members runs over, removed on drop: MEMBER (02710, this uid's) and FOLLOW
/// (0700), short enough for a socket path under a 64-digit name; MEMBERS, STATE (0700) and PIDS in
/// a scratch tree of their own, disjoint from the World's and the hosted tree (HOSTING-32).
pub struct Roots {
    pub member: Short,
    pub follow: Short,
    pub base: Gone,
}

impl Roots {
    pub fn new(tag: char) -> Roots {
        let member = Short::new(&format!("M{tag}"));
        sockdir(&member.0);
        let follow = Short::new(&format!("F{tag}"));
        fs::set_permissions(&follow.0, fs::Permissions::from_mode(0o700)).unwrap();
        let base = Gone(nanodregg_devtools::scratch(&format!(
            "ndm{}{tag}",
            std::process::id()
        )));
        for d in ["members", "state", "pids"] {
            nanodregg_devtools::mkdirs(&base.0.join(d)).unwrap();
        }
        fs::set_permissions(base.0.join("state"), fs::Permissions::from_mode(0o700)).unwrap();
        Roots {
            member,
            follow,
            base,
        }
    }
    pub fn members(&self) -> PathBuf {
        self.base.0.join("members")
    }
    pub fn state(&self) -> PathBuf {
        self.base.0.join("state")
    }
    pub fn pids(&self) -> PathBuf {
        self.base.0.join("pids")
    }
    pub fn sock(&self, name: &str) -> PathBuf {
        self.member.0.join(name).join("nd.sock")
    }
    pub fn follow_sock(&self, name: &str) -> PathBuf {
        self.follow.0.join(name).join("follow.sock")
    }
}

/// nd-members' argv as its emitted unit renders it (deploy/units/linux/nd-members@.service), over
/// `w` and `r`, serving uid `peer`, its decider the real `hosting-residents` over the writer's
/// Store. The unit hides the operator's custody (`/etc/nd`) and `/home`: here the operator's
/// workspace and its holding (this test's scratch lives under `/home`).
pub fn members_rendered(w: &World, r: &Roots, peer: u32) -> Command {
    let peer = peer.to_string();
    let (residents, nd_exe) = (lean_bin("hosting-residents"), nd());
    let (supervise, host) = (nd_supervise(), lean_bin("host"));
    let (members, state, pids) = (r.members(), r.state(), r.pids());
    unit_argv(
        "nd-members@.service",
        "nd-members",
        env!("CARGO_BIN_EXE_nd-members"),
        &[
            ("/run/nd-member", r.member.0.as_os_str()),
            ("/srv/nd-members/%i/members", members.as_os_str()),
            ("/srv/nd-members/%i/follow", state.as_os_str()),
            ("/run/nd-member-follow", r.follow.0.as_os_str()),
            ("/run/nd-members-%i", pids.as_os_str()),
            ("/run/nd/host.sock", w.host_sock.as_os_str()),
            ("${ND_PEER}", std::ffi::OsStr::new(&peer)),
            ("/opt/nd/bin/nd-supervise", supervise.as_os_str()),
            ("/opt/nd/bin/nd", nd_exe.as_os_str()),
            ("/opt/nd/bin/host", host.as_os_str()),
            ("/srv/nd/store", w.store.as_os_str()),
            ("--hide", std::ffi::OsStr::new("--hide")),
            ("/etc/nd", w.ws.as_os_str()),
            ("/home", w.holding.as_os_str()),
            ("--", std::ffi::OsStr::new("--")),
            ("/opt/nd/bin/hosting-residents", residents.as_os_str()),
        ],
    )
}

/// A running nd-members. Dropped: nd-members stopped by its handle, then each child it left by
/// the pid in its PID file (a SIGKILLed nd-members cleans nothing up).
pub struct Members {
    pub run: Option<Logged>,
    pub pids: PathBuf,
}

impl Members {
    /// nd-members on its rendered unit's argv (`members_rendered`).
    pub fn start(w: &World, r: &Roots, peer: u32) -> Members {
        Members::spawn(members_rendered(w, r, peer), r)
    }
    /// nd-members on the argv `c`, its PID file and children's PID files under `r`.
    pub fn spawn(c: Command, r: &Roots) -> Members {
        Members {
            run: Some(Logged::spawn(c, r.base.0.join("nd-members.pid"))),
            pids: r.pids(),
        }
    }
    pub fn log(&self) -> String {
        self.run.as_ref().map(Logged::log).unwrap_or_default()
    }
    pub fn pid(&self, file: &str) -> Option<i32> {
        fs::read_to_string(self.pids.join(file))
            .ok()
            .and_then(|s| s.trim().parse().ok())
    }
}

impl Drop for Members {
    fn drop(&mut self) {
        drop(self.run.take());
        for e in fs::read_dir(&self.pids).into_iter().flatten().flatten() {
            if let Some(pid) = fs::read_to_string(e.path())
                .ok()
                .and_then(|s| s.trim().parse::<i32>().ok())
                .and_then(rustix::process::Pid::from_raw)
            {
                let _ = rustix::process::kill_process(pid, rustix::process::Signal::KILL);
            }
        }
    }
}

/// A child whose stderr is collected as it arrives (grain-launch's: its launch and report lines).
pub struct Logged {
    /// stopped by its handle (the pid in its PID file) when dropped
    _held: Supervisor,
    err: Arc<Mutex<String>>,
}

impl Logged {
    pub fn spawn(mut c: Command, pid_file: PathBuf) -> Logged {
        let mut child: Child = c
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stderr = child.stderr.take().unwrap();
        let err = Arc::new(Mutex::new(String::new()));
        let e2 = Arc::clone(&err);
        std::thread::spawn(move || {
            let mut buf = [0u8; 4096];
            loop {
                match stderr.read(&mut buf) {
                    Ok(0) | Err(_) => return,
                    Ok(n) => e2
                        .lock()
                        .unwrap()
                        .push_str(&String::from_utf8_lossy(&buf[..n])),
                }
            }
        });
        Logged {
            _held: Supervisor::hold(child, pid_file),
            err,
        }
    }
    pub fn log(&self) -> String {
        self.err.lock().unwrap().clone()
    }
}

/// The probe's verdicts so far (`vol/probe.out`, appended as it goes).
pub fn verdicts(vol: &Path) -> Vec<(String, String)> {
    fs::read_to_string(vol.join("probe.out"))
        .unwrap_or_default()
        .lines()
        .filter_map(|l| {
            l.split_once(' ')
                .map(|(a, b)| (a.to_string(), b.to_string()))
        })
        .collect()
}

pub fn verdict(vol: &Path, name: &str) -> Option<String> {
    verdicts(vol)
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, v)| v)
}
