//! The resident row (`cargo:launcher:resident`, PROTOCOL-7's agreed need, HOSTING-17, HOSTING-21,
//! HOSTING-25): a hosted resident, confined under grain-launch with a Lean plan, reaches ONLY its own
//! broker socket, where it is granted, and its own member socket, through which it writes the World.
//!
//! Everything is the deployed path. A real Store (`host genesis`, `host serve`, and the operator's
//! `host follow` Store under the hosting root, the one the controller tails). The operator installs
//! `world/grain/Lifecycle` and `world/hosting/Allowance`, creates a resident grain, gives it an
//! allowance, and starts it. keybroker runs with the emitted unit's argv, serving the grain's
//! `dirOf` and a second resident. grain-launch runs with ITS emitted unit's argv
//! (deploy/units/linux/nd-grain-launch@.service) over the real `hosting-controller`, which plans
//! the launch in Lean. The resident is the probe (launcher/src/bin/probe.rs). It is sequenced by
//! files the test writes into its volume (`wait`), never by time.
//!
//! - R1: the launch's connect entries are read from grain-launch's report of the plan (one line per
//!   socket, `grain-launch: <g> connect <path>`), and must be exactly BROKER/<dirOf>/broker.sock then
//!   MEMBER/<dirOf>/nd.sock (HOSTING-25: the typed member root).
//! - W (HOSTING-25): the resident's member (enrolled by the operator, its custody in the hidden
//!   member workspace `worlds/w/members/<dirOf>`) is served by `nd --stdio` on MEMBER/<dirOf>/nd.sock.
//!   Inside, the resident `write`s the operator's data object it holds a mutate grant on, and the
//!   operator `read`s the value over its own sockets. Its write to an object it holds no grant on is
//!   refused, and the operator reads that object unchanged. An off-surface verb (`rotate`) is refused
//!   `notOnSurface`. The other resident's member socket is ENOENT, and the member directory lists
//!   exactly `nd.sock`. The member's key never enters the sandbox (the workspace is hidden: W-key).
//! - R2: grain-launch resolves it through `Policy.connect` (one uid here: the socket is this uid's,
//!   exactly 0600, because keybroker binds 0600 when PEER is its own uid, HOSTING-21). The
//!   refusals at resolve are `refusals_at_resolve_by_name`.
//! - R3: inside, the resident asks keybroker and is granted (the fake TLS upstream's 200).
//! - R4: inside, the key file is ENOENT.
//! - R5: inside, the second resident's socket is ENOENT, and SOCKDIR lists at most this resident's
//!   own directory (bwrap makes the bound directory's parents as empty mount scaffolding:
//!   isolation.rs measured it, so SOCKDIR either refuses the listing or shows `<dirOf>` alone,
//!   never the other resident).
//! - R5b: inside, the bound directory lists exactly `broker.sock`.
//! - restart (PROTOCOL-7's (d)): keybroker is stopped (its process, by the handle whose pid is its
//!   PID file) and started again. The resident, never relaunched, asks again and is granted. That
//!   works because the sandbox binds the DIRECTORY, so the new socket inode is in its view.
//! - R6 CONTROL: the canary key is in what the upstream received, and absent from every byte the
//!   resident received. The resident did receive bytes, so the absence is not vacuous.
//! - the operator's stop (`invoke 2`) ends the child, and grain-launch reports its exit.
//!
//! Declared UNRUN (one uid on hbox): Policy.connect's other-uid branch (`ConnectOwner`, and the
//! 0660 group socket it would accept) and keybroker's `peerRefused` for a real second uid. Both need
//! a second uid. The broker test's PEER plant runs the same comparison.
//!
//! Needs the built Lean exes (`hosting-controller`, `hosting-broker`, `host`, and `hosting-drive` for
//! the refusals) and the client's `nd`/`nd-supervise`. A missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::Path;
use std::process::{Command, Stdio};

use common::*;
use nanodregg_devtools::lean_bin;

/// The Store label of the World the grain lives in.
const LABEL: &str = "w";

#[test]
fn a_resident_is_granted_through_its_own_socket_and_reaches_nothing_else() {
    let d = dir("res");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let (up, seen) = upstream(Mode::Ok, pki.server(HOST, false));
    let sock = Short::new("r");
    sockdir(&sock.0);
    let sock = &sock.0;
    // The hosting root: the World's follower Store is the controller's (HOSTING-17 §7)
    let hosting = Gone(nanodregg_devtools::scratch(&format!(
        "kbh{}",
        std::process::id()
    )));
    let hosting = &hosting.0;
    let world = hosting.join("worlds").join(LABEL);
    // the member workspaces' directory: every plan hides it, and the sandbox refuses a missing path
    nanodregg_devtools::mkdirs(&world.join("members")).unwrap();
    // the member root (HOSTING-25): a short scratch of its own, disjoint from the other two roots
    let mroot = Short::new("m");
    let mroot = &mroot.0;
    let w = World::genesis_following("res", Some(world.join("store")));
    let lifecycle = w.lifecycle.clone();
    // the other resident: a resident grain of the World (born at genesis, never started), so
    // keybroker serves its socket on the host (HOSTING-26)
    let other = w.r1.clone();
    let other = other.as_str();
    let g = line(
        &w.run(&[
            "create",
            "--pkg",
            &lifecycle,
            "(record (entry \"probe\") (kind resident) (phase installed))",
        ]),
        "id ",
    )
    .to_owned();
    assert!(
        g.len() == 64
            && g.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "plant: a grain id is not 64 lowercase hex digits: {g}"
    );
    w.allowance(&g, "claude-m", 7, 100_000);
    // the resident's member, served on MEMBER/<g>/nd.sock (it must exist before the launch resolves
    // it), and a second resident's member socket on the host, for no grain here
    for r in [g.as_str(), other] {
        nanodregg_devtools::mkdirs(&mroot.join(r)).unwrap();
        fs::set_permissions(mroot.join(r), fs::Permissions::from_mode(0o700)).unwrap();
    }
    let other_m = mroot.join(other).join("nd.sock");
    let _other_m = UnixListener::bind(&other_m).unwrap();
    fs::set_permissions(&other_m, fs::Permissions::from_mode(0o600)).unwrap();
    let mfollow = Short::new("f");
    let member = w.member(
        &world.join("members").join(&g),
        &mfollow.0.join("follow.sock"),
        &w.root.join("stores/R"),
        &mroot.join(&g).join("nd.sock"),
        &d.join("pids"),
    );
    // the operator's objects: one the resident may mutate, one it holds no grant on
    let obj = line(&w.run(&["create"]), "id ").to_owned();
    let rm = line(
        &w.run(&["grant", &obj, &member.id, "observe,mutate"]),
        "id ",
    )
    .to_owned();
    let bare = line(&w.run(&["create"]), "id ").to_owned();
    w.run(&["write", &bare, "1", "operator"]);
    // the grain's package: the probe and its targets (the paths it tries are the host's)
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &pkg.join("probe"));
    let own = sock.join(&g).join("broker.sock");
    let ms = member.sock.display().to_string();
    let targets = [
        ("go1", "wait", vol.join("go1")),
        ("ask1", "ask", own.clone()),
        ("key-read", "read", keys.clone()),
        (
            "other-connect",
            "connect",
            sock.join(other).join("broker.sock"),
        ),
        ("sockdir-list", "list", sock.to_path_buf()),
        ("own-list", "list", sock.join(&g)),
        (
            "member-write",
            "nd",
            format!("{ms} write {obj} 1 resident --via {rm}").into(),
        ),
        ("member-read", "nd", format!("{ms} read {obj}").into()),
        (
            "member-nogrant",
            "nd",
            format!("{ms} write {bare} 1 resident").into(),
        ),
        ("member-rotate", "nd", format!("{ms} rotate").into()),
        ("member-other", "connect", other_m.clone()),
        ("member-list", "list", mroot.join(&g)),
        ("member-key", "list", member.ws.clone()),
        ("go2", "wait", vol.join("go2")),
        ("ask2", "ask", own.clone()),
        ("own-list2", "list", sock.join(&g)),
        ("hold", "wait", vol.join("never")),
    ];
    let text: String = targets
        .iter()
        .map(|(n, o, p)| format!("{n} {o} {}\n", p.display()))
        .collect();
    fs::write(pkg.join("probe.targets"), text).unwrap();
    // CONTROL for R4/R5: the paths the resident must not reach exist on the host
    assert!(keys.is_file() && fs::metadata(&own).is_err());

    let (uid, _) = me(sock);
    let residents = [g.as_str(), other];
    let kb = start_residents(
        sock,
        &d.join("pids"),
        &keys,
        &anchors,
        &up,
        &w,
        &residents,
        uid,
    );
    let t1 = now_ms();
    assert!(
        fs::symlink_metadata(sock.join(other).join("broker.sock")).is_ok(),
        "control: the other resident's socket exists on the host"
    );

    let gl_pids = d.join("gl-pids");
    nanodregg_devtools::mkdirs(&gl_pids).unwrap();
    let store = world.join("store");
    let controller = lean_bin("hosting-controller");
    let gl = Logged::spawn(
        grain_launch_rendered(&[
            ("/srv/nd-hosted", hosting.as_os_str()),
            ("/run/nd-broker", sock.as_os_str()),
            ("/run/nd-member", mroot.as_os_str()),
            ("%i", LABEL.as_ref()),
            ("/run/nd-grain-launch/%i", gl_pids.as_os_str()),
            ("/opt/nd/bin/hosting-controller", controller.as_os_str()),
            ("/srv/nd-hosted/worlds/%i/store", store.as_os_str()),
        ]),
        d.join("grain-launch.pid"),
    );
    let wstore = w.store.clone();
    let fstore2 = w.fstore.clone();
    let log = || {
        let ls = |p: &Path| {
            let mut v: Vec<String> = fs::read_dir(p)
                .map(|r| {
                    r.filter_map(|e| e.ok())
                        .map(|e| {
                            format!(
                                "{:?}={}",
                                e.file_name(),
                                e.metadata().map(|m| m.len()).unwrap_or(0)
                            )
                        })
                        .collect()
                })
                .unwrap_or_default();
            v.sort();
            v.join(" ")
        };
        format!(
            "{}\nwriter Store: {}\nfollower Store: {}",
            gl.log(),
            ls(&wstore),
            ls(&fstore2)
        )
    };
    // the operator starts the grain and syncs the follower Store (the operator's nd drives the
    // hosted follower, HOSTING-17 §7 ruling (B)); the controller, tailing it, launches the grain
    w.run(&["invoke", &g, "1", "(record)"]);
    w.run(&["sync"]);
    until(
        "the launch",
        60,
        || log().contains(&format!("grain-launch: {g} started")),
        &log,
    );
    // R1: Lean's plan, as grain-launch joined it onto BROKER
    let connects: Vec<String> = log()
        .lines()
        .filter_map(|l| l.strip_prefix(&format!("grain-launch: {g} connect ")))
        .map(str::to_owned)
        .collect();
    assert_eq!(
        connects,
        vec![own.display().to_string(), ms.clone()],
        "R1: the plan's connect entries are not exactly BROKER/<dirOf>/broker.sock, MEMBER/<dirOf>/nd.sock:\n{}",
        log()
    );

    // past keybroker's start window (forfeit, HOSTING-12), the resident asks
    next_window(t1);
    fs::write(vol.join("go1"), b"").unwrap();
    until(
        "the first round",
        60,
        || verdict(&vol, "member-key").is_some(),
        &|| format!("{:?}\n{}", verdicts(&vol), log()),
    );
    let v = |n: &str| verdict(&vol, n).unwrap_or_else(|| "absent".into());
    assert_eq!(
        v("ask1"),
        "ok answer 200",
        "R3: the resident was not granted"
    );
    assert_eq!(
        v("key-read"),
        "denied ENOENT",
        "R4: the key file inside the sandbox"
    );
    assert_eq!(
        v("other-connect"),
        "denied ENOENT",
        "R5: another resident's socket"
    );
    let sl = v("sockdir-list");
    assert!(
        sl.starts_with("denied") || sl == format!("ok {g}"),
        "R5: SOCKDIR shows more than this resident's own directory: {sl}"
    );
    assert_eq!(
        v("own-list"),
        "ok broker.sock",
        "R5b: the bound directory holds more than broker.sock"
    );
    // W: the resident reaches the World through its member socket, and only as its grants say
    assert!(
        v("member-write").starts_with("ok 0"),
        "W: the resident's granted write: {}",
        v("member-write")
    );
    assert_eq!(
        v("member-read"),
        "ok 0 1=resident",
        "W: the resident reads its write back"
    );
    assert_eq!(
        w.run(&["read", &obj]),
        "1=resident\n",
        "W: the operator reads the resident's write over its own sockets"
    );
    assert_eq!(
        v("member-nogrant"),
        "ok 1 refused noGrant",
        "W: a write with no grant was not refused by name"
    );
    assert_eq!(
        w.run(&["read", &bare]),
        "1=operator\n",
        "W: the ungranted object moved"
    );
    assert_eq!(
        v("member-rotate"),
        "ok 1 refused notOnSurface rotate",
        "W: an off-surface verb"
    );
    assert_eq!(
        v("member-other"),
        "denied ENOENT",
        "W: another resident's member socket"
    );
    assert_eq!(
        v("member-list"),
        "ok nd.sock",
        "W: the member directory holds more than nd.sock"
    );
    assert_eq!(
        v("member-key"),
        "denied ENOENT",
        "W-key: the member workspace (its custody) inside the sandbox"
    );
    assert!(
        member.ws.join("keys").exists() || fs::read_dir(&member.ws).unwrap().next().is_some(),
        "control: the member workspace holds its custody on the host"
    );

    // restart: keybroker stops (its own process) and a new life binds a new socket in the same
    // directory; the resident is never relaunched
    let pid_file = d.join("keybroker.pid");
    fs::write(&pid_file, format!("{}\n", kb.child.id())).unwrap();
    drop(kb);
    let _ = fs::remove_file(&pid_file);
    // THE RACE (HOSTING-26), planted: a resident grain born and started while keybroker has not
    // learned its birth (here: keybroker is down) is launched before its broker socket exists. Its
    // package, volume and member socket exist, so the launch is refused `pathMissing` for the broker
    // socket alone, by name, and the controller counts it as an exit. When keybroker comes back it
    // learns the birth and binds the socket.
    let c = w.resident("probe");
    let cdir = world.join("grains").join(&c);
    for p in ["pkg", "vol"] {
        nanodregg_devtools::mkdirs(&cdir.join(p)).unwrap();
    }
    place_exe(
        Path::new(env!("CARGO_BIN_EXE_probe")),
        &cdir.join("pkg/probe"),
    );
    fs::write(cdir.join("pkg/probe.targets"), b"").unwrap();
    nanodregg_devtools::mkdirs(&mroot.join(&c)).unwrap();
    fs::set_permissions(mroot.join(&c), fs::Permissions::from_mode(0o700)).unwrap();
    let cm = mroot.join(&c).join("nd.sock");
    let _cm = UnixListener::bind(&cm).unwrap();
    fs::set_permissions(&cm, fs::Permissions::from_mode(0o600)).unwrap();
    w.run(&["invoke", &c, "1", "(record)"]);
    w.run(&["sync"]);
    until(
        "the race's refusal",
        60,
        || log().contains(&format!("grain-launch: {c} failed pathMissing")),
        &log,
    );
    assert!(
        !log().contains(&format!("grain-launch: {c} started")),
        "the race: a resident started with no broker socket:\n{}",
        log()
    );
    let kb = start_residents(
        sock,
        &d.join("pids"),
        &keys,
        &anchors,
        &up,
        &w,
        &[g.as_str(), other, c.as_str()],
        uid,
    );
    let t2 = now_ms();
    next_window(t2);
    fs::write(vol.join("go2"), b"").unwrap();
    until(
        "the second round",
        60,
        || verdict(&vol, "own-list2").is_some(),
        &|| format!("{:?}\n{}", verdicts(&vol), log()),
    );
    assert_eq!(
        v("ask2"),
        "ok answer 200",
        "restart: the resident was not granted by keybroker's next life"
    );
    assert_eq!(v("own-list2"), "ok broker.sock", "R5b after the restart");
    assert_eq!(
        log().matches(&format!("grain-launch: {g} started")).count(),
        1,
        "the resident was relaunched:\n{}",
        log()
    );

    eprintln!("resident verdicts: {:?}", verdicts(&vol));
    // R6 CONTROL: the key went upstream, never to the resident (which did receive answers)
    let reqs = seen.lock().unwrap().clone();
    assert_eq!(reqs.len(), 2, "R6: exactly the two grants called upstream");
    assert!(
        reqs.iter()
            .all(|r| contains(r, &[b"x-api-key: ".as_slice(), KEY].concat())),
        "R6 control: the key was not sent upstream"
    );
    let got = fs::read(vol.join("probe.recv")).unwrap();
    assert!(!got.is_empty(), "R6 control: the resident received nothing");
    assert!(!contains(&got, KEY), "R6: the key reached the resident");

    // the operator's stop ends the child (the controller kills it; grain-launch reports the exit)
    w.run(&["invoke", &g, "2", "(record)"]);
    w.run(&["sync"]);
    until(
        "the stop",
        60,
        || log().contains(&format!("grain-launch: {g} exited")),
        &log,
    );
    assert!(
        fs::read_dir(&gl_pids).unwrap().next().is_none(),
        "a PID file outlived its child"
    );
    drop(gl);
    drop(kb);
    drop(w);
}

/// R2's refusals, at resolve, before any process: grain-launch launches a Lean-planned resident
/// (`hosting-drive --resident`) whose broker socket is wrong in one way each time, and the launch
/// is reported `failed` by the sandbox's name. CONTROL: the right socket (this uid's, 0600, in a
/// 0700 directory) launches.
/// One resolve case: what it is, the refusal it must meet, and its setup (a listener it holds).
type Case<'a> = (&'a str, &'a str, &'a dyn Fn() -> Option<UnixListener>);

#[test]
fn refusals_at_resolve_by_name() {
    use std::os::unix::fs::symlink;
    const A: &str = "a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1";
    let root = Gone(nanodregg_devtools::scratch(&format!(
        "kbr{}",
        std::process::id()
    )));
    let root = &root.0;
    for p in ["worlds/w1/store", "worlds/w1/members"] {
        nanodregg_devtools::mkdirs(&root.join(p)).unwrap();
    }
    let gdir = root.join("worlds/w1/grains").join(A);
    let (pkg, pids) = (gdir.join("pkg"), root.join("pids"));
    for p in [&pkg, &pids, &gdir.join("vol")] {
        nanodregg_devtools::mkdirs(p).unwrap();
    }
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &pkg.join("probe"));
    fs::write(pkg.join("probe.targets"), b"").unwrap();
    let broker = Short::new("q");
    let (broker, rd) = (&broker.0, broker.0.join(A));
    let s = rd.join("broker.sock");
    let elsewhere = broker.join("elsewhere");
    // the member root holds the resident's right member socket throughout, so each refusal below
    // is the broker socket's
    let mroot = Short::new("p");
    nanodregg_devtools::mkdirs(&mroot.0.join(A)).unwrap();
    fs::set_permissions(mroot.0.join(A), fs::Permissions::from_mode(0o700)).unwrap();
    let ms = mroot.0.join(A).join("nd.sock");
    let _member = UnixListener::bind(&ms).unwrap();
    fs::set_permissions(&ms, fs::Permissions::from_mode(0o600)).unwrap();
    let reset = || {
        let _ = fs::remove_dir_all(&rd);
        let _ = fs::remove_dir_all(&elsewhere);
        nanodregg_devtools::mkdirs(&rd).unwrap();
        nanodregg_devtools::mkdirs(&elsewhere).unwrap();
    };
    let listen = |p: &Path, mode: u32| {
        let l = UnixListener::bind(p).unwrap();
        fs::set_permissions(p, fs::Permissions::from_mode(mode)).unwrap();
        l
    };
    let launch = || {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(root)
            .arg(broker)
            .arg(&mroot.0)
            .arg("w1")
            .arg(&pids)
            .arg(lean_bin("hosting-drive"))
            .args(["--resident", "w1", A, "probe"])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        String::from_utf8_lossy(&out.stderr).into_owned()
    };
    let cases: [Case<'_>; 5] = [
        ("a regular file", "connectNotSocket", &|| {
            fs::write(&s, b"x").unwrap();
            None
        }),
        ("a symlink to a socket", "connectLink", &|| {
            let l = listen(&elsewhere.join("real.sock"), 0o600);
            symlink(elsewhere.join("real.sock"), &s).unwrap();
            Some(l)
        }),
        ("a 0666 socket", "connectMode", &|| Some(listen(&s, 0o666))),
        ("a 0660 socket of this uid", "connectMode", &|| {
            Some(listen(&s, 0o660))
        }),
        ("a group-writable directory above it", "connectDir", &|| {
            let l = listen(&s, 0o600);
            fs::set_permissions(&rd, fs::Permissions::from_mode(0o770)).unwrap();
            Some(l)
        }),
    ];
    for (what, name, plant) in cases {
        reset();
        let held = plant();
        let err = launch();
        assert!(
            err.contains(&format!("report failed {name}")),
            "{what}: not refused {name}:\n{err}"
        );
        assert!(!err.contains("report started"), "{what}: launched:\n{err}");
        drop(held);
    }
    // CONTROL: the right socket launches (so each refusal above is the case's, not the setup's)
    reset();
    let held = listen(&s, 0o600);
    let err = launch();
    assert!(
        err.contains("report started"),
        "control: the right socket did not launch:\n{err}"
    );
    drop(held);
}
