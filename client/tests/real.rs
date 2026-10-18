//! THE REAL ROUND TRIP: `nd` ⇄ `nd-supervise` ⇄ HOST's `host serve` (the writer) and `host follow`
//! (the member's own fold), both confined (CLIENT-9), on two Stores made by `host genesis` from
//! custody's own public keys. create → write → read → a failing expectation → rotate → write under
//! the rotated key → read. Every accept and refuse here is Lean's (Ed25519 verify, the receivers,
//! follow's audit and rendering); the client only signs and moves bytes. The rotate is confirmed
//! by the member's follow reading through the incoming key, and a Host that answers `refused` for
//! a write that committed is overruled by the member's own receipt (PROTOCOL-46).
//!
//! It needs the Lean binary (`devtools::lean_bin("host")`: `$ND_LEAN_BIN/host`, else this tree's
//! `.lake/build/bin/host`); missing, the test FAILS by name, it never skips.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
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

/// A Host that lies: every `submit` the writer answers `ok` reaches nd as `refused`. Everything
/// else (lookups, the log pages follow reads) passes through unchanged.
fn lying_host(listen: &Path, upstream: PathBuf) {
    use nanodregg_client::{frame, generated as g, table::LIMITS};
    let l = UnixListener::bind(listen).unwrap();
    std::thread::spawn(move || {
        for nd in l.incoming() {
            let (Ok(mut nd), Ok(mut up)) = (nd, UnixStream::connect(&upstream)) else {
                return;
            };
            while let Ok(req) = frame::read(&mut nd, LIMITS) {
                if frame::write(&mut up, LIMITS, req.op, &req.payload).is_err() {
                    break;
                }
                let Ok(mut reply) = frame::read(&mut up, LIMITS) else {
                    break;
                };
                if req.op == g::host_op::SUBMIT && reply.op == g::status::OK {
                    reply.op = g::status::REFUSED;
                }
                if frame::write(&mut nd, LIMITS, reply.op, &reply.payload).is_err() {
                    break;
                }
            }
        }
    });
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

    // CLIENT-22, ROOT's ruling (A): an observer joins like any member (a one-record custody signs
    // its join token), is granted `observe` on the World, then is sealed (`nd --seal-observer`).
    // Sealed, its follower syncs and reads (envelope signatures only), and a write is refused
    // `envelopeOnly` by custody: no call is signed, nothing commits.
    let obs = root.join("obs");
    nanodregg_devtools::mkdirs(&obs).unwrap();
    let as_obs = |follow: &Path, args: &[&str]| -> Output {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &obs)
            .env("ND_FOLLOW_SOCK", follow)
            .env("ND_HOST_SOCK", ws.join("host.sock"))
            .args(args)
            .output()
            .unwrap()
    };
    assert!(
        as_obs(&obs.join("follow.sock"), &["--init-hosted"])
            .status
            .success()
    );
    let join = text(&as_obs(&ws.join("follow.sock"), &["init", member]));
    let token = line(&join, "join ").to_owned();
    let newcomer = line(&ok(&["enroll", &token]), "id ").to_owned();
    let observe = ok(&["grant", "world", &newcomer, "observe", "--via", grant]);
    let observe = line(&observe, "id ").to_owned();
    let o_store = root.join("stores/O");
    genesis(&o_store, Some(line(&g, "nonce ")));
    let o_args = ["follow", o_store.to_str().unwrap(), &newcomer, &observe];
    let _o = supervise(&obs.join("follow.sock"), &obs, &o_store, &o_args);
    let sealed = as_obs(&obs.join("follow.sock"), &["--seal-observer"]);
    assert!(
        sealed.status.success(),
        "{}",
        String::from_utf8_lossy(&sealed.stderr)
    );
    assert!(obs.join("observer").exists() && !obs.join("keys").exists());
    let sync = as_obs(&obs.join("follow.sock"), &["sync"]);
    assert!(
        sync.status.success() && text(&sync).starts_with("height "),
        "observer sync: {}{}",
        text(&sync),
        String::from_utf8_lossy(&sync.stderr)
    );
    let read = as_obs(&obs.join("follow.sock"), &["read", &obj]);
    assert_eq!(
        text(&read),
        "1=hello\n2=after\n",
        "{}",
        String::from_utf8_lossy(&read.stderr)
    );
    // The first fence is the kernel's: observe-only, the write is refused `noGrant` in Lean
    // before custody is asked. The second is custody's: with a grant that WOULD admit the write
    // (the owner grants mutate on the object), the sealed record still refuses to sign it.
    let write = as_obs(&obs.join("follow.sock"), &["write", &obj, "3", "observer"]);
    assert_eq!(String::from_utf8_lossy(&write.stderr), "refused noGrant\n");
    let mutate = ok(&["grant", &obj, &newcomer, "observe,mutate"]);
    let mutate = line(&mutate, "id ").to_owned();
    let synced = as_obs(&obs.join("follow.sock"), &["sync"]);
    assert!(
        synced.status.success(),
        "{}",
        String::from_utf8_lossy(&synced.stderr)
    );
    let write = as_obs(
        &obs.join("follow.sock"),
        &["write", &obj, "3", "observer", "--via", &mutate],
    );
    assert!(
        !write.status.success() && String::from_utf8_lossy(&write.stderr).contains("envelopeOnly"),
        "observer write: {:?} {}",
        write.status.code(),
        String::from_utf8_lossy(&write.stderr)
    );
    assert_eq!(
        ok(&["read", &obj]),
        "1=hello\n2=after\n",
        "the refused write left nothing"
    );

    // PROTOCOL-46: a write that commits, through a Host that answers its submit `refused`. The
    // member's own follow builds and checks the receipt; the write settles committed, and the
    // settlement on disk is follow's receipt, head and verdict, never the Host's reply.
    let lie = root.join("lie.sock");
    lying_host(&lie, ws.join("host.sock"));
    let lied = Command::new(env!("CARGO_BIN_EXE_nd"))
        .env("ND_WORKSPACE", &ws)
        .env("ND_HOLDING", &holding)
        .env("ND_HOST_SOCK", &lie)
        .args(["write", &obj, "3", "lied"])
        .output()
        .unwrap();
    assert!(
        lied.status.success(),
        "{}",
        String::from_utf8_lossy(&lied.stderr)
    );
    assert_eq!(ok(&["read", &obj]), "1=hello\n2=after\n3=lied\n");
    let last = std::fs::read_dir(ws.join("attempts"))
        .unwrap()
        .filter_map(|e| e.unwrap().file_name().to_str()?.parse::<u64>().ok())
        .max()
        .unwrap();
    let settled = std::fs::read_to_string(ws.join(format!("attempts/{last}/settled"))).unwrap();
    let lines: Vec<&str> = settled.lines().collect();
    assert!(
        lines.len() == 3
            && lines[0].starts_with("receipt ")
            && lines[1].starts_with("head ")
            && lines[2].starts_with("settle committed "),
        "{settled}"
    );
    drop(_o);
    drop((_h, _f));
    std::fs::remove_dir_all(&root).unwrap();
}
