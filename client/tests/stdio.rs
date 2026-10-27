//! `nd --stdio` through the real Host (HOSTING-20, CLIENT-24): a resident enrolled by the operator
//! reaches its own nd only through nd-supervise's socket, and that nd runs confined (write = the
//! resident's workspace, connect = [host.sock, the resident's follow socket]). Served: a read and a
//! granted write. Refused by name before follow sees them: every verb off STDIO_VERBS (flags,
//! custody words, an environment word), an undecodable request. A word naming a file is text: the
//! file's bytes never reach the reply.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

use nanodregg_client::frame;
use nanodregg_client::generated::layout::{Command as Cmd, CommandReply};
use nanodregg_client::generated::{command_exit, follow_op, status};
use nanodregg_client::table;
use nanodregg_devtools::{Supervisor, lean_bin, mkdirs, scratch, supervise_host};

fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

fn text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn ask(s: &mut UnixStream, op: u8, payload: &[u8]) -> CommandReply {
    frame::request(s, table::LIMITS, op, payload).unwrap();
    let f = frame::read(s, table::LIMITS).unwrap();
    assert_eq!(f.op, status::OK, "a stdio reply is always a done step");
    CommandReply::decode(&f.payload).unwrap()
}

fn cmd(s: &mut UnixStream, argv: &[&str]) -> CommandReply {
    let c = Cmd {
        argv: argv.iter().map(|a| a.as_bytes().to_vec()).collect(),
    };
    ask(s, follow_op::COMMAND, &c.encode().unwrap())
}

fn err(r: &CommandReply) -> String {
    String::from_utf8_lossy(&r.stderr).into_owned()
}

#[test]
fn a_resident_runs_world_verbs_through_nd_stdio_and_nothing_else() {
    let host = lean_bin("host");
    let sup = Path::new(env!("CARGO_BIN_EXE_nd-supervise"));
    let nd_exe = Path::new(env!("CARGO_BIN_EXE_nd")).canonicalize().unwrap();
    let root = scratch(&format!("ndst-{}", std::process::id()));
    for d in ["a", "ah", "run", "rf", "r", "ns", "stores"] {
        mkdirs(&root.join(d)).unwrap();
    }
    let (a, ah, run, rf, r, ns) = (
        root.join("a"),
        root.join("ah"),
        root.join("run"),
        root.join("rf"),
        root.join("r"),
        root.join("ns"),
    );
    let host_sock = run.join("host.sock");
    // The operator member A: its own nd, with the writer's socket outside its workspace.
    let nd = |ws: &Path, follow: &Path, args: &[&str]| -> Output {
        Command::new(&nd_exe)
            .env("ND_WORKSPACE", ws)
            .env("ND_HOLDING", &ah)
            .env("ND_FOLLOW_SOCK", follow)
            .env("ND_HOST_SOCK", &host_sock)
            .args(args)
            .output()
            .unwrap()
    };
    let a_follow = a.join("follow.sock");
    let ok = |args: &[&str]| {
        let o = nd(&a, &a_follow, args);
        assert!(
            o.status.success(),
            "A {args:?}: {}{}",
            text(&o),
            String::from_utf8_lossy(&o.stderr)
        );
        text(&o)
    };
    assert!(nd(&a, &a_follow, &["--init"]).status.success());
    let keys = text(&nd(&a, &a_follow, &["--keys"]));
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut c = Command::new(&host);
        c.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            c.args(["--nonce", n]);
        }
        let o = c.args([&key, &next]).output().unwrap();
        assert!(
            o.status.success(),
            "genesis: {}",
            String::from_utf8_lossy(&o.stderr)
        );
        text(&o)
    };
    let (w, fa, fr) = (
        root.join("stores/W"),
        root.join("stores/FA"),
        root.join("stores/FR"),
    );
    let g = genesis(&w, None);
    genesis(&fa, Some(line(&g, "nonce ")));
    let founder = line(&g, "founder 0 member ");
    let (member, grant) = founder.split_once(" grant ").unwrap();
    let _w = supervise_host(sup, &host_sock, &a, &w, &["serve", w.to_str().unwrap()]);
    let _fa = supervise_host(
        sup,
        &a_follow,
        &a,
        &fa,
        &["follow", fa.to_str().unwrap(), member, grant],
    );
    let obj = line(&ok(&["create"]), "id ").to_owned();
    ok(&["write", &obj, "1", "hello"]);
    // The resident R: a one-record custody that joins like any member, observe on the World and
    // mutate on A's object.
    let r_init = nd(&r, &a_follow, &["--init-hosted"]);
    assert!(
        r_init.status.success(),
        "{}",
        String::from_utf8_lossy(&r_init.stderr)
    );
    let token = line(&text(&nd(&r, &a_follow, &["init", member])), "join ").to_owned();
    let rid = line(&ok(&["enroll", &token]), "id ").to_owned();
    let rg = line(
        &ok(&["grant", "world", &rid, "observe", "--via", grant]),
        "id ",
    )
    .to_owned();
    let rm = line(&ok(&["grant", &obj, &rid, "observe,mutate"]), "id ").to_owned();
    genesis(&fr, Some(line(&g, "nonce ")));
    let r_follow = rf.join("follow.sock");
    let _fr = supervise_host(
        sup,
        &r_follow,
        &r,
        &fr,
        &["follow", fr.to_str().unwrap(), &rid, &rg],
    );
    // nd --stdio, confined, behind a group socket admitting only this uid in this gid.
    fs_mode(&ns, 0o2710);
    let me = std::fs::metadata(&ns).unwrap();
    let nd_sock = ns.join("nd.sock");
    let stdio = Command::new(sup)
        .arg(&nd_sock)
        .args([
            "--group",
            &me.gid().to_string(),
            "--peer",
            &me.uid().to_string(),
        ])
        .arg("--hide")
        .arg(&a)
        .arg("--write")
        .arg(&r)
        .arg("--exec")
        .arg(&nd_exe)
        .arg("--connect")
        .arg(&host_sock)
        .arg("--connect")
        .arg(&r_follow)
        .arg("--")
        .arg(&nd_exe)
        .arg("--stdio")
        .args([&r, &r_follow, &host_sock])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let _s = Supervisor::hold(stdio, root.join("stdio.pid"));
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut s = loop {
        if let Ok(s) = UnixStream::connect(&nd_sock) {
            break s;
        }
        assert!(
            Instant::now() < deadline,
            "neverBound: {}",
            nd_sock.display()
        );
        std::thread::sleep(Duration::from_millis(50));
    };
    s.set_read_timeout(Some(table::REPLY)).unwrap();
    // Served: a read and a granted write.
    let read = cmd(&mut s, &["read", &obj]);
    assert_eq!(
        (read.exit, read.stdout.as_slice()),
        (command_exit::OK, &b"1=hello\n"[..]),
        "{}",
        err(&read)
    );
    let write = cmd(&mut s, &["write", &obj, "2", "resident", "--via", &rm]);
    assert_eq!(write.exit, command_exit::OK, "{}", err(&write));
    assert_eq!(ok(&["read", &obj]), "1=hello\n2=resident\n");
    // Refused before follow sees it: off the surface.
    for argv in [
        &["--keys"][..],
        &["--init"],
        &["rotate"],
        &["init", member],
        &["adopt", "00", "00"],
        &["ND_WORKSPACE=/tmp", "read", &obj],
        &[],
    ] {
        let rep = cmd(&mut s, argv);
        let verb = argv.first().copied().unwrap_or("");
        let want = if verb.is_empty() {
            "refused notOnSurface\n".to_owned()
        } else {
            format!("refused notOnSurface {verb}\n")
        };
        assert_eq!(
            (rep.exit, err(&rep)),
            (command_exit::REFUSED, want),
            "{argv:?}"
        );
    }
    // Undecodable: another op, or bytes that are not a Command.
    let read_cmd = Cmd {
        argv: vec![b"read".to_vec(), obj.as_bytes().to_vec()],
    }
    .encode()
    .unwrap();
    for (op, payload) in [
        (follow_op::COMMAND, &[0xffu8, 0xff, 0xff][..]),
        (9, &read_cmd[..]),
    ] {
        let rep = ask(&mut s, op, payload);
        assert_eq!(
            (rep.exit, err(&rep)),
            (command_exit::REFUSED, "refused undecodable\n".to_owned())
        );
    }
    // Another wire (PROTOCOL-87): the version is read before the op and the payload, and refused by name.
    let mut other = nanodregg_client::generated::WIRE_VERSION;
    other[0] ^= 0xff;
    let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    frame::write(&mut s, table::LIMITS, follow_op::COMMAND, &[&other[..], &read_cmd[..]].concat()).unwrap();
    let f = frame::read(&mut s, table::LIMITS).unwrap();
    assert_eq!(f.op, status::OK, "a stdio reply is always a done step");
    let rep = CommandReply::decode(&f.payload).unwrap();
    assert_eq!(
        (rep.exit, err(&rep)),
        (
            command_exit::REFUSED,
            format!(
                "refused wireVersion {} expected {}\n",
                hex(&other),
                hex(&nanodregg_client::generated::WIRE_VERSION)
            )
        ),
        "a member at another wire"
    );
    // A word naming a file is text: nd never opens it.
    let canary = root.join("canary");
    std::fs::write(&canary, b"CANARY-BYTES-7f3a").unwrap();
    let rep = cmd(&mut s, &["install", canary.to_str().unwrap()]);
    assert_ne!(rep.exit, command_exit::OK);
    let all = [rep.stdout.as_slice(), rep.stderr.as_slice()].concat();
    assert!(
        !String::from_utf8_lossy(&all).contains("CANARY-BYTES"),
        "the canary was read"
    );
    // The second fence: with the surface widened to `rotate` (in process, the same `answer` and
    // the same custody `nd --stdio` opens), the rotation is refused `noRotation` by custody.
    drop(s);
    drop(_s);
    let at = nanodregg_client::stdio::Place {
        follow: &r_follow,
        host: &host_sock,
        attempts: &r.join("attempts"),
    };
    let c = nanodregg_client::stdio::custody(&r).unwrap();
    let rotate = Cmd {
        argv: vec![b"rotate".to_vec()],
    }
    .encode()
    .unwrap();
    let rep = nanodregg_client::stdio::answer(follow_op::COMMAND, &rotate, &at, &c, &["rotate"]);
    assert!(
        err(&rep).contains("noRotation"),
        "{:?} {}",
        rep.exit,
        err(&rep)
    );
    assert_eq!(
        std::fs::metadata(r.join("keys")).unwrap().len(),
        64,
        "no pending key minted"
    );
    let _ = std::fs::remove_dir_all(&root);
}

fn fs_mode(p: &Path, m: u32) {
    std::fs::set_permissions(p, std::fs::Permissions::from_mode(m)).unwrap();
}
