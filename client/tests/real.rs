//! THE REAL ROUND TRIP: `nd` ⇄ `nd-supervise` ⇄ HOST's `host serve` (the writer) and `host follow`
//! (the member's own fold), both confined (CLIENT-9), on two Stores made by `host genesis` from
//! custody's own public keys. create → write → read → a failing expectation → rotate → write under
//! the rotated key → read. Every accept and refuse here is Lean's (Ed25519 verify, the receivers,
//! follow's audit and rendering); the client only signs and moves bytes.
//!
//! It needs the Lean binary (`devtools::lean_bin("host")`: `$ND_LEAN_BIN/host`, else this tree's
//! `.lake/build/bin/host`); missing, the test FAILS by name, it never skips.
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

#[test]
fn real_host_create_write_read_rotate_write_read() {
    let host = nanodregg_devtools::lean_bin("host");
    // A short root: a Unix socket path must fit SUN_LEN (104 bytes on macOS).
    let root = nanodregg_devtools::scratch(&format!("ndreal-{}", std::process::id()));
    // `ws` is made by `nd --init` (0700 whatever the umask); the rest by the test.
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
        let mut c = Command::new(env!("CARGO_BIN_EXE_nd"));
        c.env("ND_WORKSPACE", &ws)
            .env("ND_HOLDING", &holding)
            .args(args);
        c.output().unwrap()
    };
    let text = |o: &Output| String::from_utf8_lossy(&o.stdout).into_owned();
    assert!(nd(&["--init"]).status.success());
    assert_eq!(
        std::os::unix::fs::PermissionsExt::mode(&std::fs::metadata(&ws).unwrap().permissions())
            & 0o7777,
        0o700,
        "nd --init makes the workspace the member's alone"
    );
    let keys = text(&nd(&["--keys"]));
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );

    // Two Stores from the same genesis: the writer's, and the member's own for `host follow`.
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
    // KERNEL-24: the member's Store reproduces the writer's genesis with the writer's nonce.
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut cmd = Command::new(&host);
        cmd.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            cmd.args(["--nonce", n]);
        }
        let o = cmd.args([&key, &next]).output();
        let o = o.unwrap();
        assert!(
            o.status.success(),
            "genesis: {}",
            String::from_utf8_lossy(&o.stderr)
        );
        text(&o)
    };
    let g = genesis(&w, None);
    assert_eq!(
        genesis(&f, Some(line(&g, "nonce "))),
        g,
        "one genesis, two Stores"
    );
    let founder = line(&g, "founder 0 member ");
    let (member, grant) = founder.split_once(" grant ").unwrap();
    let _h = supervise(
        &ws.join("host.sock"),
        &ws,
        &w,
        &["serve", w.to_str().unwrap()],
    );
    let follow_args = ["follow", f.to_str().unwrap(), member, grant];
    let _f = supervise(&ws.join("follow.sock"), &ws, &f, &follow_args);

    let ok = |args: &[&str]| {
        let o = nd(args);
        assert!(
            o.status.success(),
            "nd {args:?}: {}{}",
            text(&o),
            String::from_utf8_lossy(&o.stderr)
        );
        text(&o)
    };
    let obj = line(&ok(&["create"]), "id ").to_owned();
    ok(&["write", &obj, "1", "hello"]);
    assert_eq!(ok(&["read", &obj]), "1=hello\n");
    let refused = nd(&["read", &obj, "1=nope"]);
    assert_eq!(refused.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&refused.stderr), "refused expect\n");

    ok(&["rotate"]);
    let rotated = text(&nd(&["--keys"]));
    assert_eq!(
        line(&rotated, "key "),
        next,
        "custody's current key is the old next key"
    );
    assert_ne!(line(&rotated, "next "), next);
    // The writer accepts the rotated key (Lean's verify against the member's new key).
    ok(&["write", &obj, "2", "after"]);
    assert_eq!(ok(&["read", &obj]), "1=hello\n2=after\n");

    // HOSTING-17 §7: ND_FOLLOW_SOCK / ND_HOST_SOCK name the sockets when they are not the
    // workspace's. Pointed elsewhere, nd fails naming the socket; pointed at them, it reads.
    let over = |follow: &Path, host: &Path| {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &ws)
            .env("ND_HOLDING", &holding)
            .env("ND_FOLLOW_SOCK", follow)
            .env("ND_HOST_SOCK", host)
            .args(["read", &obj])
            .output()
            .unwrap()
    };
    let nowhere = root.join("nowhere.sock");
    let o = over(&nowhere, &ws.join("host.sock"));
    assert_eq!(
        o.status.code(),
        Some(i32::from(nanodregg_client::generated::command_exit::CLIENT)),
        "nd's own failure is CommandExit.client, never follow's uncertain"
    );
    assert!(!o.status.success() && String::from_utf8_lossy(&o.stderr).contains("follow.sock"));
    let o = over(&ws.join("follow.sock"), &nowhere);
    assert!(!o.status.success() && String::from_utf8_lossy(&o.stderr).contains("host.sock"));
    let o = over(&ws.join("follow.sock"), &ws.join("host.sock"));
    assert_eq!(text(&o), "1=hello\n2=after\n");
    drop((_h, _f));
    std::fs::remove_dir_all(&root).unwrap();
}
