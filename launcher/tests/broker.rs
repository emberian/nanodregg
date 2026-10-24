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
//! - identity is the socket: the second resident grain's socket, with no allowance, is `noAllowance`;
//! - HOSTING-26: the sockets are the World's resident grains, never an operator list: a resident grain
//!   born while keybroker runs gets its socket, an app grain none; a removed one's socket and
//!   directory go, and an ask on a connection still open to it is refused `notResident`;
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
//!   uid (PEER), or whose SOCKDIR's group is not the peer's gid, answers `peerRefused`; a broker
//!   serving its own uid binds 0600 instead (the one-uid shape, HOSTING-21). A restarted
//!   broker meets the last life's socket and binds again. A peer of the right gid and another uid
//!   needs a second uid: unrun on one-uid boxes, and the PEER plant tests the same comparison.
//!
//! CONTROL: the canary key is present in what the fake upstream received over real TLS (so its
//! absence from the resident's bytes is not vacuous, and the TLS refusals are not a broken client). The Lean exes (`hosting-broker`, `host`) and the client's
//! `nd` / `nd-supervise` come from `nanodregg_devtools`; a missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::{Duration, Instant};

use common::*;
use nanodregg_devtools::{lean_bin, repo};
use nanodregg_launcher::broker_generated::read_frame;
use nanodregg_launcher::broker_generated::wire::{Answer, BrokerRefusal};
use rcgen::KeyPair;

/// keybroker over the World `w` (whose resident grains are `w.r1` and `w.r2`), trusting `anchors`,
/// serving this uid.
fn start(d: &Scratch, keys: &Path, anchors: &Path, up: &str, w: &World) -> Broker {
    start_peer(d, keys, anchors, up, w, me(d).0)
}

/// `start`, serving the uid `peer`.
fn start_peer(d: &Scratch, keys: &Path, anchors: &Path, up: &str, w: &World, peer: u32) -> Broker {
    start_residents(
        &d.socks,
        &d.join("pids"),
        keys,
        anchors,
        up,
        w,
        &[&w.r1, &w.r2],
        peer,
    )
}

#[test]
fn refusals_by_name_and_no_key_reaches_the_resident() {
    let d = dir("main");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let server = pki.server(HOST, false);
    pki.pin(&d, &[&server]);
    let (up, seen) = upstream(Mode::Ok, &server);
    // resident 01: model m (slot 7), n (slot 9: no key), and a twice (ambiguous)
    let w = World::genesis("main");
    let m = w.allowance(&w.r1, "claude-m", 7, 100_000);
    w.allowance(&w.r1, "claude-n", 9, 100_000);
    w.allowance(&w.r1, "claude-a", 7, 100_000);
    let a2 = w.allowance(&w.r1, "claude-a", 7, 100_000);
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
    // identity is the socket: r2 has a socket but no allowance, so it is refused whatever it asks
    let mut other = Resident::connect_as(&b, &w.r2);
    assert!(is_refused(
        &other.ask(&ask(b"claude-m", 10, b"hello")),
        BrokerRefusal::NoAllowance
    ));
    let a = r.ask(&ask(b"claude-m", 10, b"hello"));
    match &a {
        // the reply TEXT Lean read from the provider's JSON, never the provider's body
        Answer::Reply { text } => assert_eq!(text.as_slice(), REPLY),
        other => panic!("expected a grant, got {other:?}"),
    }
    assert!(
        !contains(&r.got, b"\"stop_reason\""),
        "a byte of the provider's JSON reached the resident"
    );
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
    let m2 = w.allowance(&w.r1, "claude-m", 7, 5);
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
        Answer::Reply { text } => assert_eq!(text.as_slice(), REPLY),
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
    let server = pki.server(HOST, false);
    pki.pin(&d, &[&server]);
    let (up, seen) = upstream(Mode::Echo, &server);
    let w = World::genesis("echo");
    w.allowance(&w.r1, "claude-m", 7, 100_000);
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
    ends_serving(d, keys, anchors, store, me(d).0)
}

/// `ends_over`, serving the uid `peer`.
fn ends_serving(
    d: &Path,
    keys: &Path,
    anchors: &Path,
    store: &Path,
    peer: u32,
) -> (String, Option<i32>) {
    ends_with(d, keys, anchors, store, peer, &lean_bin("hosting-broker"))
}

/// `ends_serving`, with `decider` for DECIDER.
fn ends_with(
    d: &Path,
    keys: &Path,
    anchors: &Path,
    store: &Path,
    peer: u32,
    decider: &Path,
) -> (String, Option<i32>) {
    let mut kb = argv_with(
        keys,
        anchors,
        &fs::read_link(d.join("socks")).unwrap(),
        &d.join("pids"),
        "127.0.0.1:9",
        store,
        "00",
        &peer.to_string(),
        decider,
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
    // file), the decider ends `store` (HOST's `missing key`, named, never an IO exception; DeciderExit,
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
    w.allowance(&w.r1, "claude-m", 7, 100_000);
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
        // pinned, so the Truncate case meets the TLS close, never the pin
        pki.pin(&d, &[&cert]);
        let (up, seen) = upstream(mode, &cert);
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
                !contains(&r.got, REPLY),
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
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let k = nanodregg_launcher::broker_generated::keybroker_exit::SOCK_DIR;
    let socks = d.socks.clone();
    // the resident directories are checked when the World's resident grains are served (HOSTING-26)
    let w = World::genesis("sockdir");
    let r = socks.join(&w.r1);
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
        let (err, got) = ends_over(&d, &keys, &anchors, &w.store);
        assert!(err.contains("keybroker: sockDir "), "{what}: stderr: {err}");
        assert_eq!(got, Some(i32::from(k)), "{what}: exit code");
        let s = r.join("broker.sock");
        assert!(
            !fs::symlink_metadata(&s).is_ok_and(|m| m.file_type().is_socket()),
            "{what}: a socket was opened"
        );
    }
    // CONTROL: the same SOCKDIR made right passes the socket checks: keybroker serves the World's
    // resident grain and binds its socket
    reset();
    let up = "127.0.0.1:9";
    let b = start_residents(
        &socks,
        &d.join("pids"),
        &keys,
        &anchors,
        up,
        &w,
        &[&w.r1],
        me(&d).0,
    );
    let m = fs::symlink_metadata(r.join("broker.sock")).unwrap();
    // serving its own uid (one uid: no group is needed), the socket is its owner's alone
    assert_eq!(
        m.permissions().mode() & 0o7777,
        0o600,
        "control: socket mode serving this uid"
    );
    assert_eq!(m.gid(), me(&socks).1, "control: socket group");
    assert_eq!(
        fs::symlink_metadata(&r).unwrap().permissions().mode() & 0o7777,
        0o2710,
        "control: resident directory mode"
    );
    drop(b);
    // CONTROL: the next life meets the last life's socket, unlinks it and binds again; serving another
    // uid (the deployment: nd serves nd-hosted), it is opened to SOCKDIR's group
    let other = me(&socks).0.wrapping_add(1);
    let b = start_residents(
        &socks,
        &d.join("pids"),
        &keys,
        &anchors,
        up,
        &w,
        &[&w.r1],
        other,
    );
    let m = fs::symlink_metadata(r.join("broker.sock")).unwrap();
    assert!(m.file_type().is_socket(), "another uid: no socket bound");
    assert_eq!(
        m.permissions().mode() & 0o7777,
        0o660,
        "another uid: socket mode"
    );
    assert_eq!(m.gid(), me(&socks).1, "another uid: socket group");
    drop(b);
}

/// HOSTING-26: keybroker serves exactly the World's resident grains, learned from its decider. At
/// start: one socket per resident grain (`r1`, `r2`), none for an app grain. A resident grain born
/// while keybroker runs gets its socket (no restart, no operator list). The operator's `remove` of a
/// resident grain closes its socket and removes its directory, and an ask on a connection that was
/// open to it is refused `notResident` (the decider no longer holds it). SOCKDIR lists exactly the
/// served residents throughout.
#[test]
fn sockets_follow_the_worlds_resident_grains() {
    let d = dir("follow");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let w = World::genesis("follow");
    let app = line(
        &w.run(&[
            "create",
            "--pkg",
            &w.lifecycle,
            "(record (entry \"app\") (kind app) (phase installed))",
        ]),
        "id ",
    )
    .to_owned();
    let b = start(&d, &keys, &anchors, "127.0.0.1:9", &w);
    let listing = || {
        let mut v: Vec<String> = fs::read_dir(&d.socks)
            .unwrap()
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect();
        v.sort();
        v
    };
    let mut want = vec![w.r1.clone(), w.r2.clone()];
    want.sort();
    assert_eq!(
        listing(),
        want,
        "start: SOCKDIR is not exactly the resident grains"
    );
    assert!(!d.socks.join(&app).exists(), "an app grain got a socket");
    // a birth while keybroker runs
    let r3 = w.resident("r3");
    let s3 = d.socks.join(&r3).join("broker.sock");
    until(
        "the born resident's socket",
        20,
        || UnixStream::connect(&s3).is_ok(),
        &|| format!("{:?}", listing()),
    );
    // a connection open to r2, then the operator removes r2 (lifecycle method 0, remove)
    let mut open2 = Resident::connect_as(&b, &w.r2);
    w.run(&["invoke", &w.r2, "0", "(record)"]);
    until(
        "the removed resident's socket to go",
        20,
        || !d.socks.join(&w.r2).exists(),
        &|| format!("{:?}", listing()),
    );
    let mut want = vec![w.r1.clone(), r3.clone()];
    want.sort();
    assert_eq!(
        listing(),
        want,
        "after the removal: SOCKDIR is not exactly the resident grains"
    );
    let a = open2.ask(&ask(b"claude-m", 10, b"hello"));
    assert!(
        is_refused(&a, BrokerRefusal::NotResident),
        "an ask on the removed resident's open connection: {a:?}"
    );
    // CONTROL: r1, still a resident, is decided (no allowance here: noAllowance, not notResident)
    let mut r1 = Resident::connect_as(&b, &w.r1);
    let a = r1.ask(&ask(b"claude-m", 10, b"hello"));
    assert!(
        is_refused(&a, BrokerRefusal::NoAllowance),
        "control: a resident's ask: {a:?}"
    );
    drop(b);
}

#[test]
fn a_peer_of_another_uid_or_group_is_refused_by_name() {
    let d = dir("peer");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let (up, seen) = upstream(Mode::Ok, &pki.server(HOST, false));
    let w = World::genesis("peer");
    w.allowance(&w.r1, "claude-m", 7, 100_000);
    let (uid, gid) = me(&d);
    let first = |b: &Broker| {
        let mut r = Resident::connect(b);
        r.ask(&ask(b"claude-m", 10, b"hi"))
    };
    // CONTROL: this uid with SOCKDIR's group is served (a decision, not peerRefused). It asks
    // through an upstream of its own: whether that ask is the start window's overSpend or, if a
    // window boundary passed, a grant that calls upstream, is timing, and must not reach `seen`,
    // the refused peers' upstream (HOST-11 saw it red once).
    let (up_control, _) = upstream(Mode::Ok, &pki.server(HOST, false));
    let b = start(&d, &keys, &anchors, &up_control, &w);
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

/// HOSTING-23 (burst5: a unit without AF_NETLINK made bwrap fail before the decider ran, and the
/// unnamed exit 1 was restarted to the start limit): a decider process that ends with a code Lean's
/// `DeciderExit` does not name ends keybroker `deciderMechanism` (fatal) with the raw code on
/// stderr, never a pass-through. The "decider" is `/usr/bin/false`, run under the real nd-bwrap
/// path, as the unit runs it. CONTROL: the real decider's own `store` end (an empty STORE) is passed
/// through with its own code (exposed_or_malformed_custody_files_stop_keybroker_by_name).
#[test]
fn a_decider_that_never_ran_its_own_end_stops_keybroker_by_name() {
    use nanodregg_launcher::broker_generated::{decider_exit, keybroker_exit};
    let d = dir("mech");
    let keys = key_file(&d, 0o600);
    let anchors = Pki::new().anchors(&d, 0o644);
    let empty = d.join("empty-store");
    nanodregg_devtools::mkdirs(&empty).unwrap();
    assert!(
        !decider_exit::ALL.contains(&1),
        "control: 1 is not a DeciderExit code"
    );
    let (err, got) = ends_with(
        &d,
        &keys,
        &anchors,
        &empty,
        me(&d).0,
        Path::new("/usr/bin/false"),
    );
    assert!(
        err.contains("keybroker: deciderMechanism 1"),
        "stderr: {err}"
    );
    assert_eq!(
        got,
        Some(i32::from(keybroker_exit::DECIDER_MECHANISM)),
        "exit code"
    );
}

/// The other half of HOSTING-23 (VACUITY-READER-H4): a decider KILLED by a signal makes bwrap exit
/// 128 + n, and that is `deciderSignaled` (102, restart: the OOM killer), never the mechanism's
/// fatal 79. The "decider" is a script that SIGKILLs itself, under the real nd-bwrap path.
#[test]
fn a_decider_killed_by_a_signal_is_restarted_not_stopped() {
    use nanodregg_launcher::broker_generated::keybroker_exit;
    let d = dir("sig");
    let keys = key_file(&d, 0o600);
    let anchors = Pki::new().anchors(&d, 0o644);
    let empty = d.join("empty-store");
    nanodregg_devtools::mkdirs(&empty).unwrap();
    let src = d.join("killself.src");
    fs::write(&src, b"#!/bin/sh\nkill -9 $$\n").unwrap();
    fs::set_permissions(&src, fs::Permissions::from_mode(0o700)).unwrap();
    let decider = d.join("killself");
    place_exe(&src, &decider);
    let (err, got) = ends_with(&d, &keys, &anchors, &empty, me(&d).0, &decider);
    assert!(err.contains("keybroker: deciderSignaled"), "stderr: {err}");
    assert_eq!(
        got,
        Some(i32::from(keybroker_exit::DECIDER_SIGNALED)),
        "exit code"
    );
}

/// One grant through keybroker over an upstream answering as `mode`, its leaf pinned: the
/// resident's answer, every byte it received, and what the upstream received.
fn one_grant(d: &Scratch, pki: &Pki, w: &World, mode: Mode) -> (Answer, Vec<u8>, usize) {
    let keys = key_file(d, 0o600);
    let anchors = pki.anchors(d, 0o644);
    let server = pki.server(HOST, false);
    pki.pin(d, &[&server]);
    sockdir(&d.socks);
    let (up, seen) = upstream(mode, &server);
    let t0 = now_ms();
    let b = start(d, &keys, &anchors, &up, w);
    next_window(t0);
    let mut r = Resident::connect(&b);
    let a = r.ask(&ask(b"claude-m", 10, b"hello"));
    let n = seen.lock().unwrap().len();
    (a, r.got, n)
}

/// HOSTING-29: the resident receives the reply TEXT the Lean decider read out of the provider's
/// JSON, never the body. Another status is passed on as the status, its body withheld; a 200 body
/// with no reply text is `replyMalformed`; a reply text that spells the key through JSON escapes
/// (the raw body never holds the key's bytes) is `keyEchoed`; escapes reach the resident decoded.
#[test]
fn the_resident_receives_the_text_lean_read_never_the_body() {
    let d = dir("reply");
    let pki = Pki::new();
    let w = World::genesis("reply");
    w.allowance(&w.r1, "claude-m", 7, 100_000);
    const LIMITED: &[u8] =
        b"{\"type\":\"error\",\"error\":{\"type\":\"rate_limit_error\",\"message\":\"slow down\"}}";
    let (a, got, n) = one_grant(&d, &pki, &w, Mode::Says(429, LIMITED));
    assert!(matches!(a, Answer::Status { status: 429 }), "a 429: {a:?}");
    assert!(
        n == 1 && !contains(&got, b"slow down"),
        "a 429's body reached the resident"
    );
    let (a, _, n) = one_grant(&d, &pki, &w, Mode::Says(200, b"{\"ok\":true}"));
    assert!(
        is_refused(&a, BrokerRefusal::ReplyMalformed) && n == 1,
        "a body with no content: {a:?}"
    );
    const SPELLED: &[u8] =
        b"{\"content\":[{\"type\":\"text\",\"text\":\"\\u0043ANARY-sk-0123456789abcdef\"}]}";
    assert!(
        !contains(SPELLED, KEY),
        "control: the raw body holds no key bytes"
    );
    let (a, got, n) = one_grant(&d, &pki, &w, Mode::Says(200, SPELLED));
    assert!(
        is_refused(&a, BrokerRefusal::KeyEchoed) && n == 1,
        "a reply spelling the key: {a:?}"
    );
    assert!(!contains(&got, KEY), "the spelled key reached the resident");
    const ESCAPED: &[u8] =
        b"{\"content\":[{\"type\":\"text\",\"text\":\"a\\nb \\u00e9 \\\"q\\\"\"}]}";
    let (a, _, _) = one_grant(&d, &pki, &w, Mode::Says(200, ESCAPED));
    match a {
        Answer::Reply { text } => assert_eq!(text, "a\nb é \"q\"".as_bytes()),
        other => panic!("escapes: {other:?}"),
    }
}

/// HOSTING-28: after rustls has verified the chain, the leaf's key must be one the operator's PINS
/// file names for Lean's host, or the call is refused `pinMismatch` before a request byte is
/// written. Two upstreams with certificates from the same CA for the same name: the pinned one is
/// answered, the other refused. A pin for another host, and the shipped production file (no pin),
/// refuse the pinned one too.
#[test]
fn a_leaf_key_the_operator_did_not_pin_is_refused_before_a_byte() {
    let d = dir("pin");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let w = World::genesis("pin");
    w.allowance(&w.r1, "claude-m", 7, 100_000);
    let pinned = pki.server(HOST, false);
    let other = pki.server(HOST, false);
    assert_ne!(pinned.pin, other.pin, "control: two leaf keys");
    let prod = fs::read(repo().join("deploy/tls/pins")).unwrap();
    let cases: [(&str, &Server, Vec<u8>, bool); 4] = [
        (
            "the pinned leaf",
            &pinned,
            format!("{HOST} {}\n", pinned.pin).into_bytes(),
            true,
        ),
        (
            "another leaf, same CA and name",
            &other,
            format!("{HOST} {}\n", pinned.pin).into_bytes(),
            false,
        ),
        (
            "the leaf pinned for another host",
            &pinned,
            format!("other.example {}\n", pinned.pin).into_bytes(),
            false,
        ),
        ("the shipped production pins", &pinned, prod, false),
    ];
    for (what, server, pins, ok) in cases {
        sockdir(&d.socks);
        pins_file(&d, &pins);
        let (up, seen) = upstream(Mode::Ok, server);
        let t0 = now_ms();
        let b = start(&d, &keys, &anchors, &up, &w);
        next_window(t0);
        let mut r = Resident::connect(&b);
        let a = r.ask(&ask(b"claude-m", 10, b"hello"));
        let n = seen.lock().unwrap().len();
        if ok {
            assert!(
                matches!(&a, Answer::Reply { text } if text == REPLY),
                "{what}: {a:?}"
            );
            assert_eq!(n, 1, "{what}: the upstream was not called");
        } else {
            assert!(is_refused(&a, BrokerRefusal::PinMismatch), "{what}: {a:?}");
            assert_eq!(n, 0, "{what}: the upstream received a request");
        }
        assert!(
            !contains(&r.got, KEY),
            "{what}: the key reached the resident"
        );
        drop(r);
        drop(b);
    }
}

/// HOSTING-28: the PINS file is read once at start under `custody::read_public`, strictly; each
/// refusal ends keybroker by name with Lean's code, before any socket opens. CONTROL: an empty file
/// and the shipped production file pass (keybroker goes on to its decider).
#[test]
fn a_bad_pins_file_stops_keybroker_by_name() {
    use nanodregg_launcher::broker_generated::keybroker_exit as k;
    let d = dir("pins");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let pin = pki.server(HOST, false).pin;
    let pins = d.join("pins");
    let good = format!("{HOST} {pin}\n");
    let write = |b: &[u8], mode: u32| {
        let _ = fs::remove_file(&pins);
        fs::write(&pins, b).unwrap();
        fs::set_permissions(&pins, fs::Permissions::from_mode(mode)).unwrap();
    };
    let malformed: Vec<(&str, String)> = vec![
        ("uppercase hex", format!("{HOST} {}\n", pin.to_uppercase())),
        ("63 digits", format!("{HOST} {}\n", &pin[1..])),
        ("no final line feed", format!("{HOST} {pin}")),
        ("a pin given twice", format!("{good}{good}")),
        ("two spaces", format!("{HOST}  {pin}\n")),
        ("an empty line", format!("{good}\n")),
        ("a comment", format!("# pins\n{good}")),
    ];
    for (what, text) in &malformed {
        write(text.as_bytes(), 0o644);
        let (err, got) = ends(&d, &keys, &anchors);
        assert!(
            err.contains("keybroker: pinsMalformed\n"),
            "{what}: stderr: {err}"
        );
        assert_eq!(got, Some(i32::from(k::PINS_MALFORMED)), "{what}: exit code");
    }
    write(good.as_bytes(), 0o666);
    let (err, got) = ends(&d, &keys, &anchors);
    assert!(
        err.contains("keybroker: pinsMode\n") && got == Some(i32::from(k::PINS_MODE)),
        "0666: {err}"
    );
    let _ = fs::remove_file(&pins);
    std::os::unix::fs::symlink(&anchors, &pins).unwrap();
    let (err, got) = ends(&d, &keys, &anchors);
    assert!(
        err.contains("keybroker: pinsLink\n") && got == Some(i32::from(k::PINS_LINK)),
        "link: {err}"
    );
    let _ = fs::remove_file(&pins);
    let (err, got) = ends(&d, &keys, &anchors);
    assert!(
        err.contains("keybroker: pinsMissing\n") && got == Some(i32::from(k::PINS_MISSING)),
        "missing: {err}"
    );
    assert!(!d.join("socks").join("01").exists(), "a socket was opened");
    for (what, text) in [
        ("empty", Vec::new()),
        ("good", good.into_bytes()),
        (
            "production",
            fs::read(repo().join("deploy/tls/pins")).unwrap(),
        ),
    ] {
        write(&text, 0o644);
        let (err, got) = ends(&d, &keys, &anchors);
        assert!(
            err.contains("keybroker: deciderRefused"),
            "control {what}: stderr: {err}"
        );
        assert_eq!(
            got,
            Some(i32::from(k::DECIDER_REFUSED)),
            "control {what}: exit code"
        );
    }
}

/// CLIENT-39 (A18): a decider that is alive and silent, or that writes half a verdict and stalls, is
/// LOST within the answer bound, by name, never a hang (keybroker held its decider lock across the
/// read with no deadline: every resident's ask behind it waited for good). Lost is for good: the next
/// question is not asked. CONTROL: a decider that answers is read.
#[test]
fn a_silent_or_stalled_decider_is_lost_within_the_answer_bound() {
    use nanodregg_launcher::broker_generated::wire::Verdict;
    use nanodregg_launcher::broker_generated::write_frame;
    use nanodregg_launcher::residents::{Decider, ask};
    use std::process::Command;
    let d = dir("lost");
    let mut answer = Vec::new();
    let names = vec![b"ab".to_vec()];
    write_frame(
        &mut answer,
        &Verdict::Residents {
            names: names.clone(),
        }
        .encode()
        .unwrap(),
    )
    .unwrap();
    fs::write(d.join("answer"), &answer).unwrap();
    let half = d.join("half");
    fs::write(&half, &answer[..answer.len() - 1]).unwrap();
    let silent = "sleep 30".to_string();
    let stalled = format!("cat {}; sleep 30", half.display());
    let answers = format!("cat {}; sleep 30", d.join("answer").display());
    for (what, script, want) in [
        ("silent", silent, None),
        ("stalled", stalled, None),
        ("answers", answers, Some(names.clone())),
    ] {
        let mut c = Command::new("/bin/sh")
            .args(["-c", &script])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut dec = Decider::new(
            c.stdin.take().unwrap(),
            c.stdout.take().unwrap(),
            Duration::from_millis(300),
        );
        let (tx, rx) = std::sync::mpsc::channel();
        let started = Instant::now();
        std::thread::spawn(move || {
            let first = ask(&mut dec, 0);
            let lost = dec.lost();
            let again = Instant::now();
            let second = ask(&mut dec, 0);
            let _ = tx.send((first, lost, second, again.elapsed()));
        });
        let got = rx.recv_timeout(Duration::from_secs(5));
        let _ = c.kill();
        let _ = c.wait();
        let (first, lost, second, quick) = got.unwrap_or_else(|_| panic!("{what}: HANG past 5 s"));
        assert_eq!(first, want, "{what}");
        assert!(
            started.elapsed() < Duration::from_secs(3),
            "{what}: {:?}",
            started.elapsed()
        );
        if want.is_none() {
            assert!(lost && second.is_none(), "{what}: lost for good");
            assert!(
                quick < Duration::from_millis(100),
                "{what}: a lost decider is not asked again"
            );
        }
    }
}
