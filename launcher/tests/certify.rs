//! THE SEED (HOSTING-56, HOST-80, PROTOCOL-78; DESIGN-TRUST §4.4b): the writer's certify key is in
//! keybroker's key file, never in the writer, and it signs only heads the Lean decider's own fold of
//! the Store holds. A REAL World whose genesis authority is keybroker's certify key
//! (`keybroker --certify-pub` → `host genesis --certifier PUB --threshold 1`), its writer under
//! nd-supervise allowed to connect to `SOCKDIR/.writer/certify.sock` and nothing of KEYS:
//!
//! - the operator's `host seal STORE --certify SOCK` certifies the base it leaves: `base.cert`
//!   verifies, and keybroker made the head durable in `KEYS.certified` BEFORE it signed (the file
//!   holds exactly the certified bytes);
//! - a THIN JOINER adopts that base (`nd adopt`, the invitation's pin) and its `adopt` checks the
//!   writer's certificate under the World's authority; the same base with one signature byte
//!   changed in `base.cert` is refused `badCertifySignature` by name, nothing adopted;
//! - the decider refuses by name, over the writer's own socket: bytes that are no certified head
//!   (`badCertify`), a step count past its tip (`notYet`), a head at a step its fold holds with
//!   another chain (`notOnFold`), another head at the certified step or one below it (`regressed`);
//! - RESTART: keybroker (and its decider) start again over the same Store and KEYS; the decider
//!   anchors the last certified head to the World it opened from the Store's kept records (the
//!   writer has moved past it), signs the same head again (byte-identical signature) and still
//!   refuses another head at that step `regressed`: no restart resets what the key signed.
//!
//! - ROTATION (KERNEL-79, HOSTING-61): the genesis commits the digest of a successor seed that
//!   `keybroker --certify-keygen` wrote OUTSIDE KEYS. On the stopped writer's Store, `host
//!   rotate-certifier` with a seed no commitment opens is refused `notPreRotated` by name and writes
//!   nothing; with the committed successor it is admitted and a base sealed after it. KEYS takes the
//!   successor's line; `host serve --certify` certifies the rotated base at start (the old
//!   certificate does not certify it); the stranger with the genesis input alone takes the new
//!   certificate (the successor's key opens the committed digest) and still takes the old one for
//!   the head it signed; the founder writes and catches up past the rotation.
//!
//! CONTROL: the joiner's adoption of the true certificate succeeds (so the forged refusal is the
//! signature check, not a broken path), and the true head is granted after every refusal above.
//! The Lean exes and the client's `nd` / `nd-supervise` come from `nanodregg_devtools`.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use common::*;
use nanodregg_devtools::{
    Supervisor, lean_bin, nd, nd_supervise, supervise_host, supervise_host_connecting,
};
use nanodregg_launcher::broker_generated::wire::{BrokerRefusal, CertifyAnswer};
use nanodregg_launcher::broker_generated::{read_frame, write_frame};

fn err(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// One member's workspace and holding, `nd` run in it against the writer's socket.
struct Member {
    ws: PathBuf,
    holding: PathBuf,
    host_sock: PathBuf,
}

impl Member {
    fn new(root: &Path, name: &str, host_sock: &Path) -> Self {
        let holding = root.join(format!("{name}-holding"));
        nanodregg_devtools::mkdirs(&holding).unwrap();
        fs::set_permissions(&holding, fs::Permissions::from_mode(0o700)).unwrap();
        let m = Self {
            ws: root.join(name),
            holding,
            host_sock: host_sock.to_owned(),
        };
        assert!(m.nd(&["--init"]).status.success());
        m
    }
    fn nd(&self, args: &[&str]) -> Output {
        Command::new(nd())
            .env("ND_WORKSPACE", &self.ws)
            .env("ND_HOLDING", &self.holding)
            .env("ND_HOST_SOCK", &self.host_sock)
            .args(args)
            .output()
            .unwrap()
    }
    fn ok(&self, args: &[&str]) -> String {
        let o = self.nd(args);
        assert!(o.status.success(), "nd {args:?}: {}{}", text(&o), err(&o));
        text(&o)
    }
}

/// keybroker over `store`, its certify socket bound (bounded wait); its stderr piped. It runs as a
/// `Type=notify` unit would (OPS-22): its `READY=1` must reach the manager's socket, and only once the
/// writer's socket exists, since the writer's unit starts on it.
fn keybroker(d: &Scratch, keys: &Path, anchors: &Path, store: &Path, operator: &str) -> Child {
    let sock = certify_sock(d);
    let _ = fs::remove_file(&sock);
    let notify = d.join("notify");
    let _ = fs::remove_file(&notify);
    let manager = std::os::unix::net::UnixDatagram::bind(&notify).unwrap();
    let mut child = argv(
        keys,
        anchors,
        &d.socks,
        &d.join("pids"),
        "127.0.0.1:9",
        store,
        operator,
        &me(d).0.to_string(),
    )
    .env("NOTIFY_SOCKET", &notify)
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
    manager
        .set_read_timeout(Some(Duration::from_secs(30)))
        .unwrap();
    let mut said = [0u8; 64];
    let n = manager.recv(&mut said).unwrap_or(0);
    assert_eq!(&said[..n], b"READY=1", "keybroker tells the manager it is ready");
    assert!(
        fs::symlink_metadata(&sock).is_ok_and(|m| m.file_type().is_socket()),
        "READY before the writer's socket was bound"
    );
    let deadline = Instant::now() + Duration::from_secs(30);
    // bound, never probed by a connection (one connection at a time: a probe would make the
    // first ask `busy`)
    while !fs::symlink_metadata(&sock).is_ok_and(|m| m.file_type().is_socket()) {
        if child.try_wait().unwrap().is_some() || Instant::now() > deadline {
            let _ = child.kill();
            let out = child.wait_with_output().unwrap();
            panic!("keybroker bound no certify socket: {}", err(&out));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    child
}

fn certify_sock(d: &Scratch) -> PathBuf {
    d.socks.join(".writer").join("certify.sock")
}

/// The writer's socket, one connection for every ask of a keybroker life (keybroker serves one
/// connection at a time: a second, while one is open, is `busy`).
fn conn(d: &Scratch) -> UnixStream {
    let s = UnixStream::connect(certify_sock(d)).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    s
}

/// One certify ask on the writer's socket.
fn certify(s: &mut UnixStream, bytes: &[u8]) -> CertifyAnswer {
    write_frame(s, bytes).unwrap();
    CertifyAnswer::decode(&read_frame(s).unwrap()).unwrap()
}

fn refused(a: &CertifyAnswer, r: BrokerRefusal) -> bool {
    matches!(a, CertifyAnswer::Refused { broker_refusal } if *broker_refusal == r)
}

/// `u32le len ‖ bytes` at `at`: the bytes and the offset after them.
fn field(b: &[u8], at: usize) -> (&[u8], usize) {
    let n = u32::from_le_bytes(b[at..at + 4].try_into().unwrap()) as usize;
    (&b[at + 4..at + 4 + n], at + 4 + n)
}

/// The certified bytes a certificate carries (`certificateLayout`'s first field).
fn certified_of(cert: &[u8]) -> Vec<u8> {
    field(cert, 0).0.to_vec()
}

/// `certified` with its step count (`certifiedLayout`: origin, then the u64 steps) replaced.
fn with_steps(certified: &[u8], steps: u64) -> Vec<u8> {
    let (_, at) = field(certified, 0);
    let mut b = certified.to_vec();
    b[at..at + 8].copy_from_slice(&steps.to_le_bytes());
    b
}

fn steps_of(certified: &[u8]) -> u64 {
    let (_, at) = field(certified, 0);
    u64::from_le_bytes(certified[at..at + 8].try_into().unwrap())
}

/// `certified` with the last byte of its chain (the last field) changed.
fn with_other_chain(certified: &[u8]) -> Vec<u8> {
    let mut b = certified.to_vec();
    let last = b.len() - 1;
    b[last] ^= 1;
    b
}

/// `keybroker --certify-keygen OUT`: the public key it printed (`certify-next HEX`).
fn keygen(out: &Path) -> String {
    let o = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .arg("--certify-keygen")
        .arg(out)
        .output()
        .unwrap();
    assert!(o.status.success(), "--certify-keygen: {}", err(&o));
    line(&text(&o), "certify-next ").to_owned()
}

/// `host rotate-certifier STORE SEED NEXT` once the stopped writer has let go of the Store's lock.
fn rotate(store: &Path, seed: &Path, next: &str) -> Output {
    for _ in 0..200 {
        let o = Command::new(lean_bin("host"))
            .arg("rotate-certifier")
            .arg(store)
            .arg(seed)
            .arg(next)
            .output()
            .unwrap();
        if !err(&o).contains("locked") {
            return o;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    panic!("plant: neverUnlocked: {}", store.display())
}

/// `host seal STORE --certify SOCK` once the stopped writer has let go of the Store's lock.
fn seal_certify(store: &Path, sock: &Path) -> (String, String) {
    for _ in 0..200 {
        let o = Command::new(lean_bin("host"))
            .arg("seal")
            .arg(store)
            .arg("--certify")
            .arg(sock)
            .output()
            .unwrap();
        if o.status.success() {
            return (text(&o), err(&o));
        }
        assert!(err(&o).contains("locked"), "host seal: {}", err(&o));
        std::thread::sleep(Duration::from_millis(100));
    }
    panic!("plant: neverUnlocked: {}", store.display())
}

#[test]
fn the_certify_key_signs_only_heads_of_the_deciders_fold() {
    let d = dir("cert");
    let seed = "1d".repeat(32);
    let keys = d.join("keys");
    // The next seed never lives in KEYS (DESIGN-TRUST §4.4c): a file that carries one is refused.
    fs::write(
        &keys,
        format!(
            "7 provider-key\ncertify {seed}\ncertify.next {}\n",
            "2e".repeat(32)
        ),
    )
    .unwrap();
    fs::set_permissions(&keys, fs::Permissions::from_mode(0o600)).unwrap();
    let o = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .args(["--certify-pub", keys.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        !o.status.success() && err(&o).contains("keyFileFormat"),
        "a KEYS file holding the next seed: {}",
        err(&o)
    );
    fs::write(&keys, format!("7 provider-key\ncertify {seed}\n")).unwrap();
    let anchors = Pki::new().anchors(&d, 0o644);
    let o = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .args(["--certify-pub", keys.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(o.status.success(), "--certify-pub: {}", err(&o));
    let pubs = text(&o);
    let certifier = line(&pubs, "certify ").to_owned();
    // The successor seed: written outside KEYS, its public key's digest committed at genesis.
    let next_seed = d.join("certify-next.seed");
    let next_pub = keygen(&next_seed);
    assert_eq!(
        fs::metadata(&next_seed).unwrap().permissions().mode() & 0o777,
        0o600,
        "the successor seed is the operator's alone"
    );
    let o = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .arg("--certify-keygen")
        .arg(&next_seed)
        .output()
        .unwrap();
    assert!(
        !o.status.success() && err(&o).contains("keygenExists"),
        "keygen never overwrites a seed: {}",
        err(&o)
    );

    // A World whose authority is the certify key, its writer and the founder's follower.
    let root = nanodregg_devtools::scratch(&format!("kbz{}", std::process::id()));
    for s in ["stores/W", "stores/F", "stores/D", "keys"] {
        nanodregg_devtools::mkdirs(&root.join(s)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let host_sock = root.join("w.sock");
    let a = Member::new(&root, "a", &host_sock);
    let ks = a.ok(&["--keys"]);
    let (key, nextk) = (line(&ks, "key ").to_owned(), line(&ks, "next ").to_owned());
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut c = Command::new(lean_bin("host"));
        c.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            c.args(["--nonce", n]);
        }
        let o = c
            .args([
                "--certifier",
                &certifier,
                "--certifier-next",
                &next_pub,
                "--threshold",
                "1",
                &key,
                &nextk,
            ])
            .output()
            .unwrap();
        assert!(o.status.success(), "genesis: {}", err(&o));
        text(&o)
    };
    let g = genesis(&w, None);
    genesis(&f, Some(line(&g, "nonce ")));
    assert_eq!(line(&g, "authority "), "1 1", "{g}");
    a.ok(&["--input", line(&g, "input ")]);
    let (member, grant) = line(&g, "founder 0 member ").split_once(" grant ").unwrap();
    let kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let csock = certify_sock(&d);
    let serve = |a: &Member| {
        supervise_host_connecting(
            &nd_supervise(),
            &host_sock,
            &a.ws,
            &w,
            &[&csock],
            &[
                "serve",
                w.to_str().unwrap(),
                "--certify",
                csock.to_str().unwrap(),
            ],
        )
    };
    let writer = serve(&a);
    let _fa = supervise_host(
        &nd_supervise(),
        &a.ws.join("follow.sock"),
        &a.ws,
        &f,
        &["follow", f.to_str().unwrap(), member, grant],
    );
    let obj = line(&a.ok(&["create"]), "id ").to_owned();
    a.ok(&["write", &obj, "1", "hello"]);

    // The operator's seal certifies the base it leaves; the head was durable before it was signed.
    drop(writer);
    let (sealed, said) = seal_certify(&w, &csock);
    assert!(
        said.contains("STATUS certify") && said.contains(" certified"),
        "seal: {said}"
    );
    let cert = fs::read(w.join("base.cert")).unwrap();
    let certified = certified_of(&cert);
    let state = fs::read(d.join("keys.certified")).unwrap();
    assert_eq!(
        state, certified,
        "KEYS.certified is the head keybroker signed"
    );
    let writer = serve(&a);
    a.ok(&["write", &obj, "2", "after the seal"]);
    a.ok(&["write", &obj, "3", "and again"]);

    // A thin joiner adopts the certified base; a forged signature in base.cert is refused by name.
    let key_file = root.join("keys/sponsor.pub");
    fs::write(&key_file, format!("{key}\n")).unwrap();
    fs::set_permissions(&key_file, fs::Permissions::from_mode(0o644)).unwrap();
    let pinned = line(&a.ok(&["invite"]), "invite ").to_owned();
    let dm = Member::new(&root, "d", &host_sock);
    let store_d = root.join("stores/D");
    let joined = dm.nd(&[
        "--join",
        key_file.to_str().unwrap(),
        &pinned,
        store_d.to_str().unwrap(),
        lean_bin("host").to_str().unwrap(),
    ]);
    assert!(joined.status.success(), "{}", err(&joined));
    let id = line(&a.ok(&["enroll", line(&text(&joined), "join ")]), "id ").to_owned();
    let observe = a.ok(&["grant", "world", &id, "observe", "--via", grant]);
    let follow_d = [
        "follow",
        store_d.to_str().unwrap(),
        &id,
        line(&observe, "id "),
    ];
    let _fd: Supervisor = supervise_host(
        &nd_supervise(),
        &dm.ws.join("follow.sock"),
        &dm.ws,
        &store_d,
        &follow_d,
    );
    let mut forged = cert.clone();
    let last = forged.len() - 1;
    forged[last] ^= 1;
    fs::write(w.join("base.cert"), &forged).unwrap();
    let o = dm.nd(&["adopt", key_file.to_str().unwrap()]);
    assert_eq!(
        err(&o),
        "refused badCertifySignature\n",
        "a forged certificate"
    );
    fs::write(w.join("base.cert"), &cert).unwrap();
    let adopted = dm.ok(&["adopt", key_file.to_str().unwrap()]);
    let steps = sealed
        .split_whitespace()
        .find_map(|x| x.strip_prefix("steps="))
        .unwrap();
    assert!(
        line(&adopted, "adopted ").starts_with(&format!("{steps} ")),
        "the thin joiner adopts the certified base: {adopted} / {sealed}"
    );

    // The stranger's check (PROTOCOL-78): the genesis input and the certificate alone.
    let input = line(&g, "input ").to_owned();
    let stranger = |cert: &Path| {
        Command::new(lean_bin("host"))
            .arg("certified")
            .arg(&input)
            .arg(cert)
            .output()
            .unwrap()
    };
    let true_cert = root.join("true.cert");
    fs::write(&true_cert, &cert).unwrap();
    let o = stranger(&true_cert);
    assert!(o.status.success(), "the stranger: {}", err(&o));
    assert!(
        text(&o).starts_with(&format!(
            "certified origin={} steps={steps} ",
            line(&g, "origin ")
        )),
        "the stranger takes the certified head: {}",
        text(&o)
    );
    let forged_cert = root.join("forged.cert");
    fs::write(&forged_cert, &forged).unwrap();
    let o = stranger(&forged_cert);
    assert_eq!(
        err(&o),
        "refused notCertified badCertifySignature
",
        "the stranger, forged"
    );
    let other = root.join("stores/X");
    nanodregg_devtools::mkdirs(&other).unwrap();
    let gx = genesis(&other, None);
    let o = Command::new(lean_bin("host"))
        .arg("certified")
        .arg(line(&gx, "input "))
        .arg(&true_cert)
        .output()
        .unwrap();
    assert_eq!(
        err(&o),
        "refused notCertified otherWorld
",
        "another World's input"
    );

    // The decider's refusals, by name, over the writer's socket; the true head after each.
    let mut c = conn(&d);
    let s = steps_of(&certified);
    assert!(refused(
        &certify(&mut c, b"no head"),
        BrokerRefusal::BadCertify
    ));
    assert!(refused(
        &certify(&mut c, &with_steps(&certified, s + 1000)),
        BrokerRefusal::NotYet
    ));
    assert!(refused(
        &certify(&mut c, &with_other_chain(&with_steps(&certified, s + 1))),
        BrokerRefusal::NotOnFold
    ));
    assert!(refused(
        &certify(&mut c, &with_other_chain(&certified)),
        BrokerRefusal::Regressed
    ));
    assert!(refused(
        &certify(&mut c, &with_steps(&certified, s - 1)),
        BrokerRefusal::Regressed
    ));
    let CertifyAnswer::Signed {
        key: k1,
        signature: sig1,
    } = certify(&mut c, &certified)
    else {
        panic!("control: the certified head is granted again")
    };
    assert_eq!(hex(&k1), certifier, "signed by the certify key");
    assert_eq!(
        sig1,
        cert[cert.len() - 64..],
        "one head, one signature (base.cert's)"
    );

    // Restart: the restarted decider anchors the last certified head to the Store it opens (the
    // writer is past it: the kept records' pairs advance its chain to the opened World's). It
    // refuses another head at that step `regressed` (not `unanchored`: it anchored), no longer
    // holds that step in its fold (`notOnFold`), and certifies the next seal's base.
    drop(kb);
    let kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let mut c = conn(&d);
    let r = certify(&mut c, &with_other_chain(&certified));
    assert!(
        refused(&r, BrokerRefusal::Regressed),
        "after a restart: {r:?}"
    );
    let r = certify(&mut c, &certified);
    assert!(
        refused(&r, BrokerRefusal::NotOnFold),
        "after a restart: {r:?}"
    );
    drop(c);
    drop(writer);
    let (_, said) = seal_certify(&w, &csock);
    assert!(
        said.contains(" certified"),
        "the next seal, after a restart: {said}"
    );
    let cert2 = fs::read(w.join("base.cert")).unwrap();
    let certified2 = certified_of(&cert2);
    assert!(steps_of(&certified2) > s, "the next base is past the first");
    assert_eq!(fs::read(d.join("keys.certified")).unwrap(), certified2);

    // ROTATION (KERNEL-79): the writer and keybroker are stopped; the operator rotates.
    drop(kb);
    let after = d.join("certify-after.seed");
    let after_pub = keygen(&after);
    let o = rotate(&w, &after, &after_pub);
    assert_eq!(
        err(&o),
        "refused notPreRotated\n",
        "a seed the genesis did not commit"
    );
    let o = rotate(&w, &next_seed, &after_pub);
    assert!(o.status.success(), "rotate-certifier: {}", err(&o));
    assert!(
        text(&o).starts_with(&format!("rotated certifier=0 key={next_pub} ")),
        "{}",
        text(&o)
    );
    let next_line = fs::read_to_string(&next_seed).unwrap();
    fs::write(&keys, format!("7 provider-key\n{next_line}")).unwrap();
    let kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let writer = serve(&a);
    // serve certifies the rotated base at start: the old certificate does not certify it
    let deadline = Instant::now() + Duration::from_secs(60);
    let cert3 = loop {
        let c3 = fs::read(w.join("base.cert")).unwrap();
        if steps_of(&certified_of(&c3)) > steps_of(&certified2) {
            break c3;
        }
        assert!(Instant::now() < deadline, "serve never certified the rotated base");
        std::thread::sleep(Duration::from_millis(100));
    };
    let rotated_cert = root.join("rotated.cert");
    fs::write(&rotated_cert, &cert3).unwrap();
    let o = stranger(&rotated_cert);
    assert!(
        o.status.success(),
        "the stranger takes the successor's certificate: {}",
        err(&o)
    );
    let old_cert = root.join("old.cert");
    fs::write(&old_cert, &cert2).unwrap();
    let o = stranger(&old_cert);
    assert!(
        o.status.success(),
        "an old certificate stays valid for the head it signed: {}",
        err(&o)
    );
    a.ok(&["write", &obj, "4", "after the rotation"]);
    a.ok(&["sync"]);
    drop(writer);
    drop(kb);
    fs::remove_dir_all(&root).unwrap();
}

/// Copy a directory tree's directories and regular files (sockets and other special files are not
/// state), keeping each mode: a member's workspace and holding are custody, checked by mode.
fn copy_tree(src: &Path, dst: &Path) {
    nanodregg_devtools::mkdirs(dst).unwrap();
    fs::set_permissions(dst, fs::metadata(src).unwrap().permissions()).unwrap();
    for e in fs::read_dir(src).unwrap() {
        let e = e.unwrap();
        let t = e.file_type().unwrap();
        if t.is_dir() {
            copy_tree(&e.path(), &dst.join(e.file_name()));
        } else if t.is_file() {
            fs::copy(e.path(), dst.join(e.file_name())).unwrap();
        }
    }
}

/// Empty `dir` and copy `from`'s files into it (a restore into the same path, by hand).
fn restore_into(from: &Path, dir: &Path) {
    fs::remove_dir_all(dir).unwrap();
    copy_tree(from, dir);
}

/// A backup of a certifying writer's Store in RUNBOOK §4's order: keybroker's `KEYS.certified`
/// FIRST, then the Store's files in `Host.Store.backupOrder` (`key`, `base.world`, `base.cert`,
/// the index file, the segment files oldest first).
fn backup(certified: &Path, store: &Path, to: &Path) {
    nanodregg_devtools::mkdirs(&to.join("store")).unwrap();
    fs::copy(certified, to.join("keys.certified")).unwrap();
    let names: Vec<String> = fs::read_dir(store)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    let family = |p: &str, s: &str| {
        let mut v: Vec<&String> = names
            .iter()
            .filter(|n| n.starts_with(p) && n.ends_with(s))
            .collect();
        v.sort_by_key(|n| n[p.len()..n.len() - s.len()].parse::<u128>().unwrap_or(0));
        v
    };
    let order: Vec<&String> = names
        .iter()
        .filter(|n| *n == "key")
        .chain(names.iter().filter(|n| *n == "base.world"))
        .chain(names.iter().filter(|n| *n == "base.cert"))
        .chain(family("index.", ".log"))
        .chain(family("seg.", ".log"))
        .collect();
    for n in order {
        fs::copy(store.join(n), to.join("store").join(n)).unwrap();
    }
}

/// RUNBOOK §4–5 for a certifying writer: `KEYS.certified` never moves back, and the Store beside
/// it must extend it. A REAL World certified by keybroker's certify key is backed up in §4's order
/// (B1 at the first certificate, B2 after the second), advanced, and restored:
///
/// - B1's Store (OLDER than the live record) beside the live `KEYS.certified`: the decider answers
///   `unanchored`, the seal's `STATUS certify` line says `refused=unanchored`, and a direct ask of
///   B1's own head is refused `unanchored`: the key signs nothing for a rolled-back Store;
/// - B2's Store (it extends the live record) beside it: the restarted decider anchors it from the
///   Store's kept records and the next seal is certified;
/// - the box lost (B1's record, Store, follower and workspace restored together): the pair
///   anchors, and the key certifies ANOTHER head at the step count of the second certificate, which
///   it signed after B1: both pass the stranger's `host certified`, an equivocation. This is why a
///   restore never moves the record back and RUNBOOK §5 says not to certify again after a box loss.
///
/// CONTROL: B2's restore is certified, so B1's `unanchored` is the record's age, not a broken path.
#[test]
fn a_restore_meets_the_certified_head() {
    let d = dir("rcert");
    let keys = d.join("keys");
    fs::write(&keys, format!("7 provider-key\ncertify {}\n", "3c".repeat(32))).unwrap();
    fs::set_permissions(&keys, fs::Permissions::from_mode(0o600)).unwrap();
    let record = d.join("keys.certified");
    let anchors = Pki::new().anchors(&d, 0o644);
    let o = Command::new(env!("CARGO_BIN_EXE_keybroker"))
        .args(["--certify-pub", keys.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(o.status.success(), "--certify-pub: {}", err(&o));
    let certifier = line(&text(&o), "certify ").to_owned();
    // the successor the genesis commits (KERNEL-79), outside KEYS
    let successor = keygen(&d.join("certify-next.seed"));

    let root = nanodregg_devtools::scratch(&format!("kbr{}", std::process::id()));
    for s in ["stores/W", "stores/F", "b1", "b2"] {
        nanodregg_devtools::mkdirs(&root.join(s)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let host_sock = root.join("w.sock");
    let a = Member::new(&root, "a", &host_sock);
    let ks = a.ok(&["--keys"]);
    let (key, nextk) = (line(&ks, "key ").to_owned(), line(&ks, "next ").to_owned());
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut c = Command::new(lean_bin("host"));
        c.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            c.args(["--nonce", n]);
        }
        let o = c
            .args(["--certifier", &certifier, "--certifier-next", &successor, "--threshold", "1", &key, &nextk])
            .output()
            .unwrap();
        assert!(o.status.success(), "genesis: {}", err(&o));
        text(&o)
    };
    let g = genesis(&w, None);
    genesis(&f, Some(line(&g, "nonce ")));
    a.ok(&["--input", line(&g, "input ")]);
    let (member, grant) = line(&g, "founder 0 member ").split_once(" grant ").unwrap();
    let csock = certify_sock(&d);
    let serve = || {
        supervise_host_connecting(
            &nd_supervise(),
            &host_sock,
            &a.ws,
            &w,
            &[&csock],
            &["serve", w.to_str().unwrap(), "--certify", csock.to_str().unwrap()],
        )
    };
    let follow = || {
        supervise_host(
            &nd_supervise(),
            &a.ws.join("follow.sock"),
            &a.ws,
            &f,
            &["follow", f.to_str().unwrap(), member, grant],
        )
    };
    let cert_now = || certified_of(&fs::read(w.join("base.cert")).unwrap());
    let mut kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let mut fa = follow();
    let writer = serve();
    // the fresh Store's base is certified at the writer's start (PROTOCOL-84), by its worker: a page
    // served before that is refused `uncertifiedPage`, so the first command waits for it
    let deadline = Instant::now() + Duration::from_secs(60);
    while !w.join("base.cert").exists() {
        assert!(Instant::now() < deadline, "the start's certificate never came");
        std::thread::sleep(Duration::from_millis(50));
    }
    let obj = line(&a.ok(&["create"]), "id ").to_owned();
    a.ok(&["write", &obj, "1", "hello"]);
    drop(writer);
    let (_, said) = seal_certify(&w, &csock);
    assert!(said.contains(" certified"), "the first seal: {said}");
    let c1 = cert_now();

    // B1: the whole box at the first certificate (the member too, for the box-loss case).
    drop(fa);
    let b1 = root.join("b1");
    backup(&record, &w, &b1);
    copy_tree(&f, &b1.join("follow"));
    copy_tree(&a.ws, &b1.join("ws"));
    copy_tree(&a.holding, &b1.join("holding"));
    fa = follow();

    let writer = serve();
    a.ok(&["write", &obj, "2", "two"]);
    a.ok(&["write", &obj, "3", "three"]);
    drop(writer);
    let (_, said) = seal_certify(&w, &csock);
    assert!(said.contains(" certified"), "the second seal: {said}");
    let cert2 = fs::read(w.join("base.cert")).unwrap();
    let c2 = certified_of(&cert2);
    assert!(steps_of(&c2) > steps_of(&c1));
    assert_eq!(fs::read(&record).unwrap(), c2, "the live record is the second head");

    // B2: a LIVE backup past the second certificate.
    let writer = serve();
    a.ok(&["write", &obj, "4", "four"]);
    backup(&record, &w, &root.join("b2"));
    drop(writer);

    // 1a. B1's Store beside the live record (older than it): nothing is certified, by name.
    drop(kb);
    restore_into(&b1.join("store"), &w);
    kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let (_, said) = seal_certify(&w, &csock);
    assert!(
        said.contains("refused=unanchored"),
        "an older Store beside the live record: {said}"
    );
    // one connection at a time: the seal's may still be closing (`busy`), so ask until it is not
    let mut r = certify(&mut conn(&d), &c1);
    for _ in 0..50 {
        if !refused(&r, BrokerRefusal::Busy) {
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
        r = certify(&mut conn(&d), &c1);
    }
    assert!(
        refused(&r, BrokerRefusal::Unanchored),
        "the older Store's own head: {r:?}"
    );
    assert_eq!(fs::read(&record).unwrap(), c2, "the record did not move");

    // 1b. CONTROL: B2's Store extends the live record: anchored at the restart, the next seal certified.
    drop(kb);
    restore_into(&root.join("b2/store"), &w);
    kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let (_, said) = seal_certify(&w, &csock);
    assert!(
        said.contains(" certified"),
        "a Store that extends the live record: {said}"
    );
    let c3 = cert_now();
    assert!(steps_of(&c3) > steps_of(&c2));
    assert_eq!(fs::read(&record).unwrap(), c3);

    // 2. The box lost: B1's record, Store and member together. The pair anchors, and the same
    // writes with other values reach the second certificate's step count with another head.
    drop(kb);
    drop(fa);
    fs::copy(b1.join("keys.certified"), &record).unwrap();
    restore_into(&b1.join("store"), &w);
    restore_into(&b1.join("follow"), &f);
    restore_into(&b1.join("ws"), &a.ws);
    restore_into(&b1.join("holding"), &a.holding);
    kb = Kill(keybroker(&d, &keys, &anchors, &w, member));
    let fa = follow();
    let writer = serve();
    a.ok(&["write", &obj, "2", "other two"]);
    a.ok(&["write", &obj, "3", "other three"]);
    drop(writer);
    let (_, said) = seal_certify(&w, &csock);
    assert!(
        said.contains(" certified"),
        "the restored pair certifies: {said}"
    );
    let cert2x = fs::read(w.join("base.cert")).unwrap();
    let c2x = certified_of(&cert2x);
    assert_eq!(steps_of(&c2x), steps_of(&c2), "one step count");
    assert_ne!(c2x, c2, "two heads at it");
    // Both certificates pass the stranger's check (PROTOCOL-78) under the one genesis input.
    let input = line(&g, "input ").to_owned();
    let mut said = Vec::new();
    for (n, c) in [("c2.cert", &cert2), ("c2x.cert", &cert2x)] {
        let p = root.join(n);
        fs::write(&p, c).unwrap();
        let o = Command::new(lean_bin("host"))
            .arg("certified")
            .arg(&input)
            .arg(&p)
            .output()
            .unwrap();
        assert!(o.status.success(), "the stranger, {n}: {}", err(&o));
        said.push(text(&o));
    }
    let at = |t: &str| t.split_whitespace().find(|x| x.starts_with("steps=")).unwrap().to_owned();
    assert_eq!(at(&said[0]), at(&said[1]), "{said:?}");
    assert_ne!(said[0], said[1], "an equivocation: {said:?}");
    drop(fa);
    drop(kb);
    fs::remove_dir_all(&root).unwrap();
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The keybroker child stops with the test (the scratch removes its sockets).
struct Kill(Child);

impl Drop for Kill {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
