//! A POINT read pinned from the deployed client (CLIENT-33, cv 01a166e9): `nd invoke … --pin REL KEY`
//! pins one row of a relation at follow's World, so a method's `(live)` point read (E1, LANG-75.1)
//! is drivable by a real member, not only by the Sims. Over `host serve` and `host follow` on two
//! real Stores (as `real.rs`), a package whose `use` reads its cell-keyed `facts` live is invoked:
//! without `--pin` the point slot is empty and the method refuses `unread`; with `--pin` it commits
//! while the fact's cell (a grant) is live; after `revoke` the same command is refused
//! `grantDead` by the method's own name, in the Turn that reads it (P8.2's revoked-grant tooth,
//! from nd). A KEY that does not read at the key type is `badKey`; an unknown relation is
//! `unknownRelation`. Every verdict here is Lean's; nd only moves bytes and signs.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::path::Path;
use std::process::{Command, Output};

use nanodregg_devtools::Supervisor;

fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

fn supervise(sock: &Path, ws: &Path, store: &Path, args: &[&str]) -> Supervisor {
    let sup = Path::new(env!("CARGO_BIN_EXE_nd-supervise"));
    nanodregg_devtools::supervise_host(sup, sock, ws, store, args)
}

/// The fixture's core text (`fixtures/pin/Live`, what `nd install` reads): `facts` is keyed by one
/// digest, so a method may read it `(live)`. Method 0 `post {cell}` inserts the row of a cell;
/// method 1 `use` reads ONE point of `facts` with its cell's liveness and refuses by name when the
/// point is not pinned (`unread`), holds no row (`unposted`) or names a cell that is not live
/// (`grantDead`). It was printed by LANG's printer from the surface text
/// `(method use (reads (facts (points 1) (live))) (case rows.facts.p0 (none _ (refuse "unread"))
/// (some p (case p.val (none _ (refuse "unposted")) (some _ (if p.live (done state)
/// (refuse "grantDead")))))))`; the core text is the one copy.
fn fixture() -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pin/Live"))
        .unwrap()
}

#[test]
fn pinned_live_point_read_refuses_a_revoked_grant() {
    let host = nanodregg_devtools::lean_bin("host");
    let root = nanodregg_devtools::scratch(&format!("ndpin-{}", std::process::id()));
    for d in ["holding", "stores"] {
        nanodregg_devtools::mkdirs(&root.join(d)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let (ws, holding) = (root.join("ws"), root.join("holding"));
    std::fs::set_permissions(
        &holding,
        std::os::unix::fs::PermissionsExt::from_mode(0o700),
    )
    .unwrap();
    let nd = |args: &[&str]| -> Output {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &ws)
            .env("ND_HOLDING", &holding)
            .args(args)
            .output()
            .unwrap()
    };
    let text = |o: &Output| String::from_utf8_lossy(&o.stdout).into_owned();
    let err = |o: &Output| String::from_utf8_lossy(&o.stderr).into_owned();
    assert!(nd(&["--init"]).status.success());
    let keys = text(&nd(&["--keys"]));
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
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
    let g = genesis(&w, None);
    assert_eq!(genesis(&f, Some(line(&g, "nonce "))), g);
    let founder = line(&g, "founder 0 member ");
    let (member, grant) = founder.split_once(" grant ").unwrap();
    let _h = supervise(
        &ws.join("host.sock"),
        &ws,
        &w,
        &["serve", w.to_str().unwrap()],
    );
    let _f = supervise(
        &ws.join("follow.sock"),
        &ws,
        &f,
        &["follow", f.to_str().unwrap(), member, grant],
    );
    let ok = |args: &[&str]| {
        let o = nd(args);
        assert!(o.status.success(), "nd {args:?}: {}{}", text(&o), err(&o));
        text(&o)
    };
    // (exit, stderr, stdout) of a refused command
    let refused = |args: &[&str]| {
        let o = nd(args);
        assert_eq!(
            o.status.code(),
            Some(i32::from(
                nanodregg_client::generated::command_exit::REFUSED
            )),
            "nd {args:?}: {}{}",
            text(&o),
            err(&o)
        );
        (err(&o), text(&o))
    };

    let pkg = line(&ok(&["install", &fixture()]), "id ").to_owned();
    let obj = line(&ok(&["create", "--pkg", &pkg, "(record)"]), "id ").to_owned();
    let desc = ok(&["read", &obj, "?"]);
    assert!(
        desc.contains("method 0 post") && desc.contains("method 1 use"),
        "{desc}"
    );
    // The fact's cell: a grant the member holds over the object, revocable by the member.
    let gr = line(&ok(&["grant", &obj, member, "observe"]), "id ").to_owned();
    let cell = format!("(record (cell #{gr}))");
    ok(&["invoke", &obj, "0", &cell]);
    assert_eq!(
        ok(&["read", &obj, "facts", "8"]).lines().count(),
        1,
        "one fact posted"
    );

    // No `--pin`: the plan pins no point, so the method's one point slot is empty.
    let (e, o) = refused(&["invoke", &obj, "1", "(record)"]);
    assert_eq!(e, "refused program\n");
    assert!(o.contains("unread"), "{o}");
    // Pinned while the grant is live: the live read sees it live, and the call commits.
    ok(&["invoke", &obj, "1", "(record)", "--pin", "facts", &cell]);
    // The grant revoked (its cell a tombstone): the SAME command, re-planned at follow's World,
    // pins the row and the method's live read sees the cell dead and refuses by its own name.
    ok(&["revoke", &gr]);
    let (e, o) = refused(&["invoke", &obj, "1", "(record)", "--pin", "facts", &cell]);
    assert_eq!(e, "refused program\n");
    assert!(o.contains("grantDead"), "{o}");
    // A pinned key that is not of the relation's key type, and a relation the package lacks.
    let (e, _) = refused(&[
        "invoke",
        &obj,
        "1",
        "(record)",
        "--pin",
        "facts",
        "(record (cell 7))",
    ]);
    assert_eq!(e, "refused badKey\n");
    let (e, _) = refused(&["invoke", &obj, "1", "(record)", "--pin", "nope", &cell]);
    assert_eq!(e, "refused unknownRelation\n");
    // A dangling `--pin` is the parser's usage refusal.
    let (e, _) = refused(&["invoke", &obj, "1", "(record)", "--pin", "facts"]);
    assert!(e.starts_with("refused usage"), "{e}");
    drop((_h, _f));
    std::fs::remove_dir_all(&root).unwrap();
}
