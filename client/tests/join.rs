//! `nd --join` over a signed invitation (CLIENT-26, PROTOCOL-42), through the real `host` over
//! sockets: the founder keeps its genesis inputs and invites; a second workspace joins from the
//! invitation and its sponsor's key file, makes its join token, is enrolled, and a write it signs is
//! served. Refused before anything is written: a forged invitation (`pinMismatch`), a key other than
//! the sponsor's (`notSponsor`), a key file under a group-writable directory (the chain rule). The
//! kept files are re-read under the chain rule (`nd invite`, `nd adopt KEY_FILE`). Every accept and
//! refuse is Lean's.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use nanodregg_client::generated::command_exit;
use nanodregg_devtools::{Supervisor, mkdirs};

fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

fn text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn err(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// The value of `key` (`steps=`, `digest=`) on `host seal`'s `sealed` line.
fn field<'a>(sealed: &'a str, key: &str) -> &'a str {
    sealed
        .split_whitespace()
        .find_map(|w| w.strip_prefix(key))
        .unwrap_or_else(|| panic!("no `{key}` in {sealed}"))
}

/// `host seal STORE` once the stopped writer has let go of the Store's lock: `locked` is retried
/// (the killed supervisor's child exits on its stdin's end), any other refusal FAILS by name, and
/// still `locked` after 20 s FAILS (`neverUnlocked`): a liveness deadline, not a measurement.
fn seal_stopped(host: &Path, store: &Path) -> String {
    for _ in 0..200 {
        let o = Command::new(host).arg("seal").arg(store).output().unwrap();
        if o.status.success() {
            return line(&text(&o), "sealed ").to_owned();
        }
        assert!(err(&o).contains("locked"), "host seal: {}", err(&o));
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    panic!("plant: neverUnlocked: {}", store.display())
}

fn supervise(sock: &Path, ws: &Path, store: &Path, args: &[&str]) -> Supervisor {
    let sup = Path::new(env!("CARGO_BIN_EXE_nd-supervise"));
    nanodregg_devtools::supervise_host(sup, sock, ws, store, args)
}

/// One member's workspace and holding, and `nd` run in it against a writer's `host.sock`.
struct Member {
    ws: PathBuf,
    holding: PathBuf,
    host_sock: PathBuf,
}

impl Member {
    fn new(root: &Path, name: &str, host_sock: &Path) -> Self {
        let holding = root.join(format!("{name}-holding"));
        mkdirs(&holding).unwrap();
        let m = Self {
            ws: root.join(name),
            holding,
            host_sock: host_sock.to_owned(),
        };
        assert!(m.nd(&["--init"]).status.success());
        m
    }
    fn nd(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_nd"))
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
    fn join(&self, key: &Path, invitation: &str, store: &Path) -> Output {
        let host = nanodregg_devtools::lean_bin("host");
        let (k, s, h) = (
            key.to_str().unwrap(),
            store.to_str().unwrap(),
            host.to_str().unwrap(),
        );
        self.nd(&["--join", k, invitation, s, h])
    }
    /// Nothing kept, nothing in the Store: a refused join wrote nothing.
    fn unwritten(&self, store: &Path) {
        assert!(!self.ws.join("invitation").exists() && !self.ws.join("input").exists());
        assert_eq!(
            std::fs::read_dir(store).unwrap().count(),
            0,
            "the Store stayed empty"
        );
    }
}

#[test]
fn join_from_a_signed_invitation_refuses_forgeries_and_serves_a_write() {
    let host = nanodregg_devtools::lean_bin("host");
    let root = nanodregg_devtools::scratch(&format!("ndjoin-{}", std::process::id()));
    for d in ["stores/B", "stores/C", "stores/D", "keys", "loose"] {
        mkdirs(&root.join(d)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let host_sock = root.join("a.host.sock");
    let a = Member::new(&root, "a", &host_sock);
    let keys = a.ok(&["--keys"]);
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut cmd = Command::new(&host);
        cmd.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            cmd.args(["--nonce", n]);
        }
        let o = cmd.args([&key, &next]).output().unwrap();
        assert!(o.status.success(), "genesis: {}", err(&o));
        text(&o)
    };
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
    let g = genesis(&w, None);
    genesis(&f, Some(line(&g, "nonce ")));
    // A founder keeps its own genesis inputs (`nd --input`); bare `nd invite` reads them back.
    a.ok(&["--input", line(&g, "input ")]);
    let (member, grant) = line(&g, "founder 0 member ").split_once(" grant ").unwrap();
    let writer = supervise(&host_sock, &a.ws, &w, &["serve", w.to_str().unwrap()]);
    let _fa = supervise(
        &a.ws.join("follow.sock"),
        &a.ws,
        &f,
        &["follow", f.to_str().unwrap(), member, grant],
    );
    let obj = line(&a.ok(&["create"]), "id ").to_owned();
    a.ok(&["write", &obj, "1", "hello"]);
    let invitation = line(&a.ok(&["invite"]), "invite ").to_owned();
    // The sponsor's key reaches the joiner by its own channel: a file, read under the chain rule.
    let key_file = root.join("keys/sponsor.pub");
    std::fs::write(&key_file, format!("{key}\n")).unwrap();
    std::fs::set_permissions(&key_file, PermissionsExt::from_mode(0o644)).unwrap();

    let b = Member::new(&root, "b", &host_sock);
    let store_b = root.join("stores/B");
    // A forged invitation (one signature byte changed) is Lean's `pinMismatch`: nothing written.
    let mut forged = invitation.clone();
    let last = if forged.ends_with('0') { "1" } else { "0" };
    forged.replace_range(forged.len() - 1.., last);
    let o = b.join(&key_file, &forged, &store_b);
    assert_eq!(
        o.status.code(),
        Some(i32::from(command_exit::REFUSED)),
        "{}",
        err(&o)
    );
    assert_eq!(err(&o), "refused inviteRefused pinMismatch\n");
    b.unwritten(&store_b);
    // A key other than the sponsor's: `notSponsor`, nothing written.
    let b_key = line(&b.ok(&["--keys"]), "key ").to_owned();
    let other = root.join("keys/other.pub");
    std::fs::write(&other, &b_key).unwrap();
    std::fs::set_permissions(&other, PermissionsExt::from_mode(0o644)).unwrap();
    let o = b.join(&other, &invitation, &store_b);
    assert_eq!(
        o.status.code(),
        Some(i32::from(command_exit::REFUSED)),
        "{}",
        err(&o)
    );
    assert_eq!(err(&o), "refused inviteRefused notSponsor\n");
    b.unwritten(&store_b);
    // The trust root under a group-writable directory is refused by the chain rule, by name.
    let loose = root.join("loose");
    std::fs::copy(&key_file, loose.join("sponsor.pub")).unwrap();
    std::fs::set_permissions(&loose, PermissionsExt::from_mode(0o770)).unwrap();
    let o = b.join(&loose.join("sponsor.pub"), &invitation, &store_b);
    assert_eq!(o.status.code(), Some(i32::from(command_exit::CLIENT)));
    assert!(err(&o).contains("key file: Dir("), "{}", err(&o));
    b.unwritten(&store_b);

    // The honest join: B's World is the one the signed inputs make; it keeps the invitation and
    // the inputs, and prints its join token.
    let joined = b.join(&key_file, &invitation, &store_b);
    assert!(joined.status.success(), "{}", err(&joined));
    let joined = text(&joined);
    assert_eq!(
        line(&joined, "origin "),
        line(&g, "origin "),
        "the sponsor's World"
    );
    assert_eq!(line(&joined, "sponsor "), member);
    assert_eq!(line(&joined, "input "), line(&g, "input "));
    for (kept, want) in [
        ("invitation", invitation.as_str()),
        ("input", line(&g, "input ")),
    ] {
        let p = b.ws.join(kept);
        assert_eq!(std::fs::read_to_string(&p).unwrap(), want);
        let mode = std::fs::metadata(&p).unwrap().permissions().mode() & 0o7777;
        assert_eq!(mode, 0o600, "{kept} is kept owner-only");
    }
    let again = b.join(&key_file, &invitation, &store_b);
    assert!(
        err(&again).contains("invitation: exists"),
        "{}",
        err(&again)
    );
    let id = line(&a.ok(&["enroll", line(&joined, "join ")]), "id ").to_owned();
    let observe = a.ok(&["grant", "world", &id, "observe", "--via", grant]);
    let observe = line(&observe, "id ").to_owned();
    let mutate = line(&a.ok(&["grant", &obj, &id, "observe,mutate"]), "id ").to_owned();
    let follow_b = ["follow", store_b.to_str().unwrap(), &id, &observe];
    let _fb = supervise(&b.ws.join("follow.sock"), &b.ws, &store_b, &follow_b);
    b.ok(&["write", &obj, "2", "joined", "--via", &mutate]);
    assert_eq!(
        a.ok(&["read", &obj]),
        "1=hello\n2=joined\n",
        "the joiner's write served"
    );
    // A joiner invites from the inputs it kept.
    assert!(b.ok(&["invite"]).starts_with("invite "));
    // The kept files are re-read under the chain rule: a widened one is refused by name.
    let inv = b.ws.join("invitation");
    std::fs::set_permissions(&inv, PermissionsExt::from_mode(0o640)).unwrap();
    let o = b.nd(&["adopt", key_file.to_str().unwrap()]);
    assert_eq!(o.status.code(), Some(i32::from(command_exit::CLIENT)));
    assert!(err(&o).contains("invitation: Mode("), "{}", err(&o));
    std::fs::set_permissions(&inv, PermissionsExt::from_mode(0o600)).unwrap();
    std::fs::set_permissions(&b.ws, PermissionsExt::from_mode(0o770)).unwrap();
    let o = b.nd(&["invite"]);
    assert!(
        !o.status.success() && err(&o).contains("Dir("),
        "{}",
        err(&o)
    );
    std::fs::set_permissions(&b.ws, PermissionsExt::from_mode(0o700)).unwrap();

    // A thin joiner adopts from the invitation it kept, under the sponsor key file: Lean accepts
    // the kept bytes under the key (a wrong key is `notSponsor`). The sponsor's first invitation
    // pinned the base its own follow verified then, the genesis base, which a thin joiner already
    // holds: `notBehind`. The operator seals the stopped writer (`host seal STORE`, HOST-43), starts
    // it again, and the sponsor's next `nd invite` pins that base, its own follow's digest of its
    // own World there (PROTOCOL-47): the thin joiner adopts exactly the printed base.
    let c = Member::new(&root, "c", &host_sock);
    let store_c = root.join("stores/C");
    let joined = c.join(&key_file, &invitation, &store_c);
    assert!(joined.status.success(), "{}", err(&joined));
    let id = line(&a.ok(&["enroll", line(&text(&joined), "join ")]), "id ").to_owned();
    let observe = a.ok(&["grant", "world", &id, "observe", "--via", grant]);
    let follow_c = [
        "follow",
        store_c.to_str().unwrap(),
        &id,
        line(&observe, "id "),
    ];
    let fc = supervise(&c.ws.join("follow.sock"), &c.ws, &store_c, &follow_c);
    let o = c.nd(&["adopt", other.to_str().unwrap()]);
    assert_eq!(
        err(&o),
        "refused notSponsor
"
    );
    let o = c.nd(&["adopt", key_file.to_str().unwrap()]);
    assert_eq!(
        err(&o),
        "refused notBehind
"
    );
    drop(fc);
    drop(writer);
    let sealed = seal_stopped(&host, &w);
    let writer = supervise(&host_sock, &a.ws, &w, &["serve", w.to_str().unwrap()]);
    let pinned = line(&a.ok(&["invite"]), "invite ").to_owned();
    let d = Member::new(&root, "d", &host_sock);
    let store_d = root.join("stores/D");
    let joined = d.join(&key_file, &pinned, &store_d);
    assert!(joined.status.success(), "{}", err(&joined));
    let id = line(&a.ok(&["enroll", line(&text(&joined), "join ")]), "id ").to_owned();
    let observe = a.ok(&["grant", "world", &id, "observe", "--via", grant]);
    let follow_d = [
        "follow",
        store_d.to_str().unwrap(),
        &id,
        line(&observe, "id "),
    ];
    let _fd = supervise(&d.ws.join("follow.sock"), &d.ws, &store_d, &follow_d);
    let adopted = d.ok(&["adopt", key_file.to_str().unwrap()]);
    let (steps, digest) = (field(&sealed, "steps="), field(&sealed, "digest="));
    assert_eq!(
        line(&adopted, "adopted "),
        format!("{steps} {digest}"),
        "the thin joiner adopts the base the operator sealed: {sealed}"
    );
    // PROTOCOL-74 (DESIGN-TRUST T1): members compare heads. The founder attests its head at the
    // tip; the thin joiner, behind it, catches up THROUGH that position and finds the chain on its
    // own fold (`shared STEPS MEMBER`); a position stated with another chain is refused
    // `forkedWorld` by name on the way; a member already past a position is refused `ahead`; bytes that are
    // no attestation are `badAttestation`. Every verdict is Lean's (`Protocol.Head`).
    a.ok(&["write", &obj, "3", "attested"]);
    let attest = line(&a.ok(&["sync", "--attest"]), "attest ").to_owned();
    let checked = d.ok(&["sync", "--check", &attest]);
    let shared = line(&checked, "shared ").to_owned();
    let steps = shared.split_whitespace().next().unwrap().to_owned();
    assert_eq!(shared.split_whitespace().nth(1), Some(member), "{checked}");
    // B's follow last caught up before the seal: behind, it passes the founder's position on the
    // way and refuses a chain no fold has there (the page refused, B still behind); the honest
    // check then passes it (`shared`), and a position B is past is refused `ahead`.
    let forged = format!("{steps}:00");
    let o = b.nd(&["sync", "--to", &forged]);
    assert_eq!(o.status.code(), Some(i32::from(command_exit::REFUSED)));
    assert_eq!(err(&o), "refused forkedWorld\n");
    assert!(b.ok(&["sync", "--check", &attest]).starts_with("shared "));
    let o = b.nd(&["sync", "--to", &forged]);
    assert_eq!(err(&o), "refused ahead\n");
    let o = a.nd(&["sync", "--check", "00"]);
    assert_eq!(err(&o), "refused badAttestation\n");
    drop(writer);
    std::fs::remove_dir_all(&root).unwrap();
}
