//! E5 (PROGRAM §2(a), PROTOCOL-<E5>): receipts between Worlds, over TWO real Stores through the
//! real `host`. World A and World B are two geneses, each with its own writer. A member of B who
//! follows A (here `ba`, a workspace joined to A) holds A's receipts; B holds A's HEAD in an object of
//! `Std.headPackage` (`world/head/Head`) that B's members post to, and an acceptor
//! (`fixtures/foreign/Accept`) accepts a call A committed, once, on its receipt checked by Lean
//! (`Protocol.Foreign.check`) against that head. Every accept and refuse is Lean's.
//! * X1: an offer written in A, accepted in B on A's receipt: admitted, the acceptance row shows A's
//!   transaction id; X1b: the same acceptance again: refused `keyTaken` (one receipt, one
//!   acceptance), and so is a later receipt of the same call once B's head has advanced to it.
//! * X2: the receipt with its stated commit height changed (the roots still open the held head):
//!   refused `pathMismatch`; X2r: a receipt of another call of A with its cells root changed:
//!   refused `headMismatch` (never accepted, so a check without the roots comparison admits it);
//!   X2h: a receipt built at a later head of A than B holds: refused `headMismatch`.
//! * X3: a second poster's head at the SAME step count with other roots: refused `lawDenied`
//!   (`head: forkedHead`); X3b: the poster records the fork (`fork`): admitted, and every later receipt
//!   against that head object refuses `forkedHead`, and so does a post.
//! * X5: the owner withdraws the trust anchor (`distrust`): a valid receipt refuses `untrusted`.
//!
//! The control "A's call at B's writer refuses `wrongWorld`" is the `wrongWorld` row
//! (`Protocol.Rows.wrongWorld`). `headDead` (a retired head object) and `notCommitted` have no row
//! here (`nd` has no verb that retires an object or signs a call it does not send); they are the
//! Lang journey's rows RC1 (`headDead`), RC2 (`notCommitted`, an absent receipt) and RC3
//! (`notCommitted`, a refused one), in `Lang/Journey/Head.lean`.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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

fn both(o: &Output) -> String {
    format!("{}{}", text(o), err(o))
}

fn supervise(sock: &Path, ws: &Path, store: &Path, args: &[&str]) -> Supervisor {
    let sup = Path::new(env!("CARGO_BIN_EXE_nd-supervise"));
    nanodregg_devtools::supervise_host(sup, sock, ws, store, args)
}

fn repo_text(rel: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)).unwrap()
}

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
        assert!(
            o.status.success(),
            "nd {:?}: {}",
            &args[..args.len().min(3)],
            both(&o)
        );
        text(&o)
    }
    /// `nd` refused: its whole output, for the caller's assertion of the name.
    fn refused(&self, args: &[&str]) -> String {
        let o = self.nd(args);
        assert!(
            !o.status.success(),
            "nd {:?} admitted: {}",
            &args[..args.len().min(3)],
            both(&o)
        );
        both(&o)
    }
    /// The bytes of the member's newest frozen call (the attempt store's `call`), as hex.
    fn last_call(&self) -> String {
        let dir = self.ws.join("attempts");
        let n = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(|e| e.ok()?.file_name().to_str()?.parse::<u64>().ok())
            .max()
            .unwrap();
        let b = std::fs::read(dir.join(n.to_string()).join("call")).unwrap();
        b.iter().map(|x| format!("{x:02x}")).collect()
    }
    fn join(&self, key: &Path, invitation: &str, store: &Path) -> Output {
        let host = nanodregg_devtools::lean_bin("host");
        self.nd(&[
            "--join",
            key.to_str().unwrap(),
            invitation,
            store.to_str().unwrap(),
            host.to_str().unwrap(),
        ])
    }
}

/// One World: its founder's workspace, writer and follower, and its genesis lines.
struct World {
    founder: Member,
    genesis: String,
    grant: String,
    _writer: Supervisor,
    _follow: Supervisor,
}

fn world(root: &Path, name: &str) -> World {
    let host = nanodregg_devtools::lean_bin("host");
    let sock = root.join(format!("{name}.host.sock"));
    let a = Member::new(root, name, &sock);
    let keys = a.ok(&["--keys"]);
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );
    let (w, f) = (
        root.join(format!("stores/{name}W")),
        root.join(format!("stores/{name}F")),
    );
    let g = Command::new(&host)
        .arg("genesis")
        .arg(&w)
        .arg(name)
        .args([&key, &next])
        .output()
        .unwrap();
    assert!(g.status.success(), "genesis: {}", err(&g));
    let g = text(&g);
    let f_out = Command::new(&host)
        .arg("genesis")
        .arg(&f)
        .arg(name)
        .args(["--nonce", line(&g, "nonce ")])
        .args([&key, &next])
        .output()
        .unwrap();
    assert!(f_out.status.success(), "genesis F: {}", err(&f_out));
    a.ok(&["--input", line(&g, "input ")]);
    let (member, grant) = line(&g, "founder 0 member ").split_once(" grant ").unwrap();
    let (member, grant) = (member.to_owned(), grant.to_owned());
    let writer = supervise(&sock, &a.ws, &w, &["serve", w.to_str().unwrap()]);
    let follow = supervise(
        &a.ws.join("follow.sock"),
        &a.ws,
        &f,
        &["follow", f.to_str().unwrap(), &member, &grant],
    );
    World {
        founder: a,
        genesis: g,
        grant,
        _writer: writer,
        _follow: follow,
    }
}

/// A member of `w` joined from the founder's invitation, enrolled and following; returns it and its
/// member id.
fn joiner(root: &Path, w: &World, name: &str, sock: &Path) -> (Member, String, Supervisor) {
    let a = &w.founder;
    let key = line(&a.ok(&["--keys"]), "key ").to_owned();
    let key_file = root.join(format!("keys/{name}-sponsor.pub"));
    std::fs::write(&key_file, format!("{key}\n")).unwrap();
    std::fs::set_permissions(&key_file, PermissionsExt::from_mode(0o644)).unwrap();
    let invitation = line(&a.ok(&["invite"]), "invite ").to_owned();
    let m = Member::new(root, name, sock);
    let store = root.join(format!("stores/{name}"));
    mkdirs(&store).unwrap();
    let joined = m.join(&key_file, &invitation, &store);
    assert!(joined.status.success(), "{}", err(&joined));
    let id = line(&a.ok(&["enroll", line(&text(&joined), "join ")]), "id ").to_owned();
    let observe = line(
        &a.ok(&["grant", "world", &id, "observe", "--via", &w.grant]),
        "id ",
    )
    .to_owned();
    let follow = supervise(
        &m.ws.join("follow.sock"),
        &m.ws,
        &store,
        &["follow", store.to_str().unwrap(), &id, &observe],
    );
    (m, id, follow)
}

/// `receipt CALL` on a follower of A: the receipt and the head it was built at.
fn receipt(m: &Member, call: &str) -> (String, String, String, String) {
    let out = m.ok(&["receipt", call]);
    let head: Vec<&str> = line(&out, "head ").split_whitespace().collect();
    (
        line(&out, "receipt ").to_owned(),
        head[0].to_owned(),
        head[1].to_owned(),
        head[2].to_owned(),
    )
}

fn head_text(steps: &str, height: &str, roots: &str) -> String {
    format!("(record (height {height}) (roots #{roots}) (steps {steps}))")
}

/// Where the receipt's cells-root bytes start, in hex digits: the answer byte, two u64s, then the
/// `turn` and `txId` fields (u32 length and 32 bytes each), then `root`'s u32 length
/// (`Protocol.Receipt.layout`).
const ROOT_HEX: usize = 2 * (1 + 8 + 8 + (4 + 32) + (4 + 32) + 4);

/// One hex digit of the receipt changed: at 2, the low byte of the stated commit height (the frame:
/// the answer byte, then the height as u64 LE, `Protocol.Receipt.layout`).
fn forge(r: &str, at: usize) -> String {
    let mut b: Vec<u8> = r.as_bytes().to_vec();
    b[at] = if b[at] == b'0' { b'1' } else { b'0' };
    String::from_utf8(b).unwrap()
}

#[test]
fn a_receipt_from_another_world_is_accepted_once_and_forgeries_and_forks_refuse() {
    let root = nanodregg_devtools::scratch(&format!("ndforeign-{}", std::process::id()));
    for d in ["stores", "keys"] {
        mkdirs(&root.join(d)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let a = world(&root, "A");
    let b = world(&root, "B");
    assert_ne!(
        line(&a.genesis, "origin "),
        line(&b.genesis, "origin "),
        "two Worlds"
    );
    let a_origin = line(&a.genesis, "origin ").to_owned();
    // `ba` follows A: B's poster of A's head (a member of A, a workspace of the same person as B's
    // founder); `cb` is a second member of B who also follows A (`ca`).
    let (ba, _, _fba) = joiner(&root, &a, "ba", &root.join("A.host.sock"));
    let (ca, _, _fca) = joiner(&root, &a, "ca", &root.join("A.host.sock"));
    let (cb, cb_id, _fcb) = joiner(&root, &b, "cb", &root.join("B.host.sock"));

    // In A: an offer.
    let offer = line(&a.founder.ok(&["create"]), "id ").to_owned();
    a.founder.ok(&["write", &offer, "1", "five-for-a-bell"]);
    let call = a.founder.last_call();
    // A second call of A, never accepted in B: X2r's forged-roots receipt is about it.
    a.founder.ok(&["write", &offer, "3", "a-second-offer"]);
    let call2 = a.founder.last_call();
    let (r, steps, height, roots) = receipt(&ba, &call);
    let (r2, steps2, ..) = receipt(&ba, &call2);
    assert_eq!(steps, steps2, "both receipts at one head of A");

    // In B: the head object, holding A's head as `ba` folded it, and the acceptor trusting it.
    let bf = &b.founder;
    let head_pkg = line(&bf.ok(&["install", &repo_text("world/head/Head")]), "id ").to_owned();
    let acc_pkg = line(
        &bf.ok(&[
            "install",
            &repo_text("client/tests/fixtures/foreign/Accept"),
        ]),
        "id ",
    )
    .to_owned();
    let seed = format!(
        "(record (head (at {})) (world #{a_origin}))",
        head_text(&steps, &height, &roots)
    );
    let h = line(&bf.ok(&["create", "--pkg", &head_pkg, &seed]), "id ").to_owned();
    let acc = line(&bf.ok(&["create", "--pkg", &acc_pkg, "(record)"]), "id ").to_owned();
    bf.ok(&["invoke", &acc, "2", &format!("(record (cell #{h}))")]);
    let anchor = format!("(record (cell #{h}))");
    let accept = |m: &Member, rr: &str| -> Output {
        m.nd(&[
            "invoke",
            &acc,
            "0",
            &format!("(record (receipt #{rr}))"),
            "--range",
            "heads",
            "1",
            &anchor,
        ])
    };

    // X2: the stated commit height changed: `pathMismatch` (the roots still open the head's).
    let forged = forge(&r, 3);
    let o = accept(bf, &forged);
    assert!(
        !o.status.success() && both(&o).contains("pathMismatch"),
        "X2: {}",
        both(&o)
    );
    // X1: the receipt itself: admitted, and the acceptance row names A's transaction.
    bf.ok(&[
        "invoke",
        &acc,
        "0",
        &format!("(record (receipt #{r}))"),
        "--range",
        "heads",
        "1",
        &anchor,
    ]);
    let rows = bf.ok(&["read", &acc, "accepted", "4"]);
    assert_eq!(rows.lines().count(), 1, "X1: one acceptance: {rows}");
    // X2r: the second call's receipt with its CELLS root changed (so its roots no longer open the
    // held head, while its journal path and root still verify by themselves): `headMismatch`. This
    // transaction was never accepted, so a check that skipped the roots would ADMIT it here.
    let forged_roots = forge(&r2, ROOT_HEX + 1);
    let o = accept(bf, &forged_roots);
    assert!(
        !o.status.success() && both(&o).contains("headMismatch"),
        "X2r: {}",
        both(&o)
    );
    // X1b: the same acceptance again is refused (one receipt, one acceptance): the receipt checks,
    // and the acceptance row's key is taken.
    let o = accept(bf, &r);
    assert!(
        !o.status.success() && both(&o).contains("keyTaken"),
        "X1b: {}",
        both(&o)
    );
    // X2h: A moves on; a receipt built at A's NEW head does not open B's held one.
    a.founder.ok(&["write", &offer, "2", "later"]);
    let (r_later, s2, h2, roots2) = receipt(&ba, &call);
    let o = accept(bf, &r_later);
    assert!(
        !o.status.success() && both(&o).contains("headMismatch"),
        "X2h: {}",
        both(&o)
    );
    // ... and once B's head advances to it, it checks: the first acceptance already stands, so it is
    // refused as a second acceptance (`keyTaken`), not as a receipt (`headMismatch`).
    bf.ok(&["invoke", &h, "1", &head_text(&s2, &h2, &roots2)]);
    let o = accept(bf, &r_later);
    assert!(
        !o.status.success() && both(&o).contains("keyTaken") && !both(&o).contains("headMismatch"),
        "X2h: at the advanced head: {}",
        both(&o)
    );

    // X3: `cb` (granted post and fork) posts a head at the SAME step count with other roots.
    let g = line(&bf.ok(&["grant", &h, &cb_id, "invoke:0,invoke:1"]), "id ").to_owned();
    let fake = "00".repeat(roots2.len() / 2);
    let o = cb.refused(&["invoke", &h, "1", &head_text(&s2, &h2, &fake), "--via", &g]);
    assert!(
        o.contains("lawDenied") && o.contains("forkedHead"),
        "X3: {o}"
    );
    // X3b: `cb` records the fork; then no receipt checks against this head object, and no post lands.
    cb.ok(&[
        "invoke",
        &h,
        "0",
        &format!("(record (other #{fake}) (steps {s2}))"),
        "--via",
        &g,
    ]);
    let (r_now, ..) = receipt(&ca, &call);
    let o = accept(bf, &r_now);
    assert!(
        !o.status.success() && both(&o).contains("forkedHead"),
        "X3b accept: {}",
        both(&o)
    );
    let o = bf.refused(&["invoke", &h, "1", &head_text(&s2, &h2, &roots2)]);
    assert!(o.contains("forkedHead"), "X3b post: {o}");

    // X5: a second head object for A, trusted; the owner withdraws the anchor: `untrusted`.
    let (r5, s5, h5, roots5) = receipt(&ba, &call);
    let seed5 = format!(
        "(record (head (at {})) (world #{a_origin}))",
        head_text(&s5, &h5, &roots5)
    );
    let h5id = line(&bf.ok(&["create", "--pkg", &head_pkg, &seed5]), "id ").to_owned();
    let anchor5 = format!("(record (cell #{h5id}))");
    bf.ok(&["invoke", &acc, "2", &anchor5]);
    bf.ok(&["invoke", &acc, "1", &anchor5]);
    let o = bf.nd(&[
        "invoke",
        &acc,
        "0",
        &format!("(record (receipt #{r5}))"),
        "--range",
        "heads",
        "1",
        &anchor5,
    ]);
    assert!(
        !o.status.success() && both(&o).contains("untrusted"),
        "X5: {}",
        both(&o)
    );
    std::fs::remove_dir_all(&root).unwrap();
}
