//! nd-members (HOSTING-30, CLIENT-29): each resident grain the World holds gets its member socket
//! `MEMBER/<dirOf>/nd.sock`, served by `nd --stdio` over its own member workspace and its OWN
//! follower (`host follow MEMBERS/<name>/store MEMBER GRANT`, from the provisioning step's
//! `MEMBERS/<name>/follow`), from the decider's `residents` frames: at birth, gone at removal.
//!
//! Every plant runs the real binaries: a real writer and Store (`World`), the real decider
//! (`hosting-broker`, which answers `residents` as `hosting-residents` will), nd-supervise, nd and
//! host. Each nd-members child has a PID file in PIDS; `Members` stops nd-members by its handle and
//! then each child by its PID file, never by a pattern.
//!
//! Declared UNRUN (one uid on hbox): a peer of a second real uid. The stranger plant configures
//! PEER as another uid, which nd-supervise's peer check refuses exactly as it would a stranger.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use common::*;
use nanodregg_client::generated::layout::{Command as NdCommand, CommandReply};
use nanodregg_client::generated::{command_exit, follow_op, status};
use nanodregg_client::{frame, table};
use nanodregg_devtools::{lean_bin, nd, nd_supervise};
use nanodregg_launcher::broker_generated::wire::Verdict;
use nanodregg_launcher::broker_generated::{decider_exit, members_exit, write_frame};

/// The roots one nd-members runs over, removed on drop.
struct Roots {
    member: Short,
    follow: Short,
    base: Gone,
}

impl Roots {
    /// MEMBER (02710, this uid's) and FOLLOW (0700) short enough for a socket path under a 64-digit
    /// name; MEMBERS and PIDS in a scratch tree of their own.
    fn new(tag: char) -> Roots {
        let member = Short::new(&format!("M{tag}"));
        sockdir(&member.0);
        let follow = Short::new(&format!("F{tag}"));
        fs::set_permissions(&follow.0, fs::Permissions::from_mode(0o700)).unwrap();
        let base = Gone(nanodregg_devtools::scratch(&format!(
            "ndm{}{tag}",
            std::process::id()
        )));
        for d in ["members", "pids"] {
            nanodregg_devtools::mkdirs(&base.0.join(d)).unwrap();
        }
        Roots {
            member,
            follow,
            base,
        }
    }
    fn members(&self) -> PathBuf {
        self.base.0.join("members")
    }
    fn pids(&self) -> PathBuf {
        self.base.0.join("pids")
    }
    fn sock(&self, name: &str) -> PathBuf {
        self.member.0.join(name).join("nd.sock")
    }
    fn follow_sock(&self, name: &str) -> PathBuf {
        self.follow.0.join(name).join("follow.sock")
    }
}

/// Provision resident `name`'s member as the operator's provisioning step does: `nd
/// --init-hosted` in `MEMBERS/<name>`, `init`, the operator's `enroll` and `grant world … observe`,
/// its follower Store `MEMBERS/<name>/store` from the World's genesis, and `MEMBERS/<name>/follow`
/// (`MEMBER GRANT`, 0600). The member's id.
fn provision(w: &World, r: &Roots, name: &str) -> String {
    let ws = r.members().join(name);
    nanodregg_devtools::mkdirs(&ws).unwrap();
    let holding = r.base.0.join(format!("{}.holding", &name[..8]));
    nanodregg_devtools::mkdirs(&holding).unwrap();
    let (op_follow, host) = (w.ws.join("follow.sock"), w.host_sock.clone());
    let o = member_nd(&ws, &holding, &op_follow, &host, &["--init-hosted"]);
    assert!(o.status.success(), "nd --init-hosted: {}", both(&o));
    let o = member_nd(&ws, &holding, &op_follow, &host, &["init", &w.operator]);
    assert!(o.status.success(), "nd init: {}", both(&o));
    let token = line(&text(&o), "join ").to_owned();
    let id = line(&w.run(&["enroll", &token]), "id ").to_owned();
    let observe = line(
        &w.run(&["grant", "world", &id, "observe", "--via", &w.grant]),
        "id ",
    )
    .to_owned();
    let o = Command::new(lean_bin("host"))
        .arg("genesis")
        .arg(ws.join("store"))
        .args(&w.genesis_args)
        .output()
        .unwrap();
    assert_eq!(text(&o), w.genesis_out, "one genesis, another Store");
    let f = ws.join("follow");
    fs::write(&f, format!("{id} {observe}\n")).unwrap();
    fs::set_permissions(&f, fs::Permissions::from_mode(0o600)).unwrap();
    id
}

/// nd-members' argv over `w` and `r`, serving uid `peer`, with `decider` and its arguments.
fn argv(w: &World, r: &Roots, peer: u32, decider: &Path, dargs: &[&std::ffi::OsStr]) -> Command {
    argv_over(w, r, peer, &w.store, decider, dargs)
}

/// nd-members' argv with STORE (the decider's only readable path) given.
fn argv_over(
    w: &World,
    r: &Roots,
    peer: u32,
    store: &Path,
    decider: &Path,
    dargs: &[&std::ffi::OsStr],
) -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_nd-members"));
    c.arg(&r.member.0)
        .arg(r.members())
        .arg(&r.follow.0)
        .arg(r.pids())
        .arg(&w.host_sock)
        .arg(peer.to_string())
        .arg(nd_supervise())
        .arg(nd())
        .arg(lean_bin("host"))
        .arg(store)
        .arg("--hide")
        .arg(&w.ws)
        .arg("--")
        .arg(decider)
        .args(dargs);
    c
}

/// The real decider's argv after DECIDER: `T0 SLOTS STORE OPERATOR`.
fn broker_args(w: &World) -> Vec<std::ffi::OsString> {
    vec![
        now_ms().to_string().into(),
        "1".into(),
        w.store.clone().into(),
        w.operator.clone().into(),
    ]
}

/// A running nd-members. Dropped: nd-members stopped by its handle, then each child it left by
/// the pid in its PID file (a SIGKILLed nd-members cleans nothing up).
struct Members {
    run: Option<Logged>,
    pids: PathBuf,
}

impl Members {
    fn start(w: &World, r: &Roots, peer: u32) -> Members {
        let args = broker_args(w);
        let args: Vec<&std::ffi::OsStr> = args.iter().map(|a| a.as_os_str()).collect();
        let c = argv(w, r, peer, &lean_bin("hosting-broker"), &args);
        Members {
            run: Some(Logged::spawn(c, r.base.0.join("nd-members.pid"))),
            pids: r.pids(),
        }
    }
    fn log(&self) -> String {
        self.run.as_ref().map(Logged::log).unwrap_or_default()
    }
    fn pid(&self, file: &str) -> Option<i32> {
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

/// One nd command through a member socket: the reply's exit and its stdout (OK) or stderr.
fn nd_via(sock: &Path, argv: &[&str]) -> Result<(u8, String), String> {
    let mut s = UnixStream::connect(sock).map_err(|e| format!("connect {e}"))?;
    s.set_read_timeout(Some(table::REPLY)).unwrap();
    let c = NdCommand {
        argv: argv.iter().map(|a| a.as_bytes().to_vec()).collect(),
    }
    .encode()
    .unwrap();
    frame::write(&mut s, table::LIMITS, follow_op::COMMAND, &c).map_err(|e| e.to_string())?;
    let f = frame::read(&mut s, table::LIMITS).map_err(|e| format!("read {e}"))?;
    if f.op != status::OK {
        return Err(format!(
            "op {} {}",
            f.op,
            String::from_utf8_lossy(&f.payload)
        ));
    }
    let r = CommandReply::decode(&f.payload).unwrap();
    let t = if r.exit == command_exit::OK {
        r.stdout
    } else {
        r.stderr
    };
    Ok((r.exit, String::from_utf8_lossy(&t).into_owned()))
}

fn uid(p: &Path) -> u32 {
    fs::metadata(p).unwrap().uid()
}

/// The fds nd-members holds at rest (`/proc/<pid>/fd`, the least of five looks: a spawn or a PID
/// file write holds one for an instant).
fn fds(pid: u32) -> usize {
    (0..5)
        .map(|_| {
            std::thread::sleep(std::time::Duration::from_millis(50));
            fs::read_dir(format!("/proc/{pid}/fd")).unwrap().count()
        })
        .min()
        .unwrap()
}

/// Send `sig` to the process whose pid is in `file`.
fn signal(file: &Path, sig: rustix::process::Signal) -> i32 {
    let pid: i32 = fs::read_to_string(file).unwrap().trim().parse().unwrap();
    rustix::process::kill_process(rustix::process::Pid::from_raw(pid).unwrap(), sig).unwrap();
    pid
}

/// Born → bound and served; born while running (provisioned after the birth) → bound within the
/// tick loop; removed → both sockets, directories and PID files gone, a connect refused ENOENT;
/// an app grain → nothing. nd-members' own fds do not grow with the residents it serves.
#[test]
fn each_resident_grain_gets_its_member_socket_and_a_removed_one_loses_it() {
    let w = World::genesis("ndm");
    let r = Roots::new('a');
    let ids: Vec<String> = [&w.r1, &w.r2]
        .iter()
        .map(|g| provision(&w, &r, g))
        .collect();
    let obj = line(&w.run(&["create"]), "id ").to_owned();
    w.run(&["write", &obj, "1", "operator"]);
    for id in &ids {
        w.run(&["grant", &obj, id, "observe"]);
    }
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
    let m = Members::start(&w, &r, uid(&r.member.0));
    for g in [&w.r1, &w.r2] {
        until(
            "a born resident's member socket",
            30,
            || r.sock(g).exists(),
            &|| m.log(),
        );
        let got = std::cell::RefCell::new(Err::<(u8, String), String>(String::new()));
        until(
            "a read through the member socket",
            30,
            || {
                *got.borrow_mut() = nd_via(&r.sock(g), &["read", &obj]);
                got.borrow()
                    .as_ref()
                    .is_ok_and(|(e, t)| *e == command_exit::OK && t.contains("1=operator"))
            },
            &|| format!("{:?}\n{}", got.borrow(), m.log()),
        );
        let mode = fs::metadata(r.sock(g)).unwrap().permissions().mode() & 0o7777;
        assert_eq!(
            mode, 0o600,
            "one uid: the member socket is 0600 (HOSTING-21)"
        );
        let listed: Vec<_> = fs::read_dir(r.member.0.join(g))
            .unwrap()
            .flatten()
            .map(|e| e.file_name())
            .collect();
        assert_eq!(
            listed,
            ["nd.sock"],
            "the member directory holds only its socket"
        );
    }
    assert!(
        !r.member.0.join(&app).exists(),
        "an app grain got a member socket"
    );
    let pid: u32 = fs::read_to_string(r.base.0.join("nd-members.pid"))
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    let before = fds(pid);
    // a birth while it runs, provisioned only after the birth (the grain's name is its id)
    let r3 = w.resident("r3");
    let id3 = provision(&w, &r, &r3);
    w.run(&["grant", &obj, &id3, "observe"]);
    until(
        "the born resident's member socket",
        30,
        || r.sock(&r3).exists(),
        &|| m.log(),
    );
    let got = std::cell::RefCell::new(Err::<(u8, String), String>(String::new()));
    until(
        "a read through the born resident's socket",
        30,
        || {
            *got.borrow_mut() = nd_via(&r.sock(&r3), &["read", &obj]);
            got.borrow()
                .as_ref()
                .is_ok_and(|(e, _)| *e == command_exit::OK)
        },
        &|| format!("{:?}\n{}", got.borrow(), m.log()),
    );
    assert_eq!(
        fds(pid),
        before,
        "nd-members' own fds grew with a resident:\n{}",
        m.log()
    );
    // the operator removes r2 (lifecycle method 0)
    w.run(&["invoke", &w.r2, "0", "(record)"]);
    until(
        "the removed resident's member socket to go",
        30,
        || !r.member.0.join(&w.r2).exists() && !r.follow.0.join(&w.r2).exists(),
        &|| m.log(),
    );
    let e = UnixStream::connect(r.sock(&w.r2)).unwrap_err();
    assert_eq!(
        e.kind(),
        std::io::ErrorKind::NotFound,
        "a connect to the removed resident's socket"
    );
    for role in ["follow", "stdio"] {
        assert!(
            m.pid(&format!("{}.{role}.pid", w.r2)).is_none(),
            "the removed resident's {role} PID file stayed"
        );
    }
    // each child started once: the stdio child waits for its follow socket (its connect grant
    // resolves it at launch), so no start was spent on a refusal
    for g in [&w.r1, &r3] {
        for role in ["follow", "stdio"] {
            assert_eq!(starts(&m.log(), g, role), 1, "{role} of {g}:\n{}", m.log());
        }
    }
    assert!(!m.log().contains(" ended "), "a child ended:\n{}", m.log());
    // CONTROL: r1 is still served
    let (e, t) = nd_via(&r.sock(&w.r1), &["read", &obj]).unwrap();
    assert_eq!(
        (e, t.contains("1=operator")),
        (command_exit::OK, true),
        "control: r1 after r2's removal: {t}"
    );
}

/// A peer that is not PEER in MEMBER's group is closed `peerRefused` by the member socket (here
/// PEER is another uid: nd-supervise's `--group --peer` check, the socket 0660).
#[test]
fn a_stranger_on_the_member_socket_is_refused_by_name() {
    let w = World::genesis("ndp");
    let r = Roots::new('p');
    provision(&w, &r, &w.r1);
    let m = Members::start(&w, &r, uid(&r.member.0) + 1);
    let sock = r.sock(&w.r1);
    until(
        "the member socket",
        30,
        || UnixStream::connect(&sock).is_ok(),
        &|| m.log(),
    );
    let mode = fs::metadata(&sock).unwrap().permissions().mode() & 0o7777;
    assert_eq!(mode, 0o660, "a group socket for another uid");
    let mut s = UnixStream::connect(&sock).unwrap();
    s.set_read_timeout(Some(table::REPLY)).unwrap();
    let _ = frame::write(&mut s, table::LIMITS, follow_op::COMMAND, b"x");
    let f = frame::read(&mut s, table::LIMITS).unwrap();
    assert_eq!((f.op, f.payload), (status::CLOSED, b"peerRefused".to_vec()));
}

/// A resident not provisioned is named `memberMissing` and left unbound while the others are
/// served; a socket directory holding anything but its socket is named `socketDirShared`, unbound.
#[test]
fn an_unprovisioned_member_or_a_shared_socket_directory_is_named_and_the_others_served() {
    let w = World::genesis("ndq");
    let r = Roots::new('q');
    provision(&w, &r, &w.r1);
    provision(&w, &r, &w.r2);
    // r2's follow directory holds a stray file: a connect grant would show it to nd --stdio
    nanodregg_devtools::mkdirs(&r.follow.0.join(&w.r2)).unwrap();
    fs::write(r.follow.0.join(&w.r2).join("stray"), b"x").unwrap();
    let r3 = w.resident("r3");
    let m = Members::start(&w, &r, uid(&r.member.0));
    until(
        "r1's member socket",
        30,
        || UnixStream::connect(r.sock(&w.r1)).is_ok(),
        &|| m.log(),
    );
    until(
        "both names",
        30,
        || {
            let l = m.log();
            l.contains(&format!("memberMissing {r3}"))
                && l.contains(&format!("socketDirShared {}", w.r2))
        },
        &|| m.log(),
    );
    assert!(
        !r.sock(&r3).exists() && !r.sock(&w.r2).exists(),
        "an unprovisioned or shared resident was bound"
    );
    assert_eq!(
        m.log().matches(&format!("memberMissing {r3}")).count(),
        1,
        "memberMissing is named once"
    );
    // the stray goes: r2 is bound on a later tick (retried, not only on an answer change)
    fs::remove_file(r.follow.0.join(&w.r2).join("stray")).unwrap();
    until(
        "r2 bound once its directory is alone",
        30,
        || r.sock(&w.r2).exists(),
        &|| m.log(),
    );
}

/// The follower dying: a command then gets a named reply from nd (`follow.sock: …`), never a bare
/// EOF; nd-members starts the follower again and the next command is served. nd-members is held
/// stopped (SIGSTOP) across the kill, so the window in which the follower is dead is the test's,
/// not a race with the tick.
#[test]
fn a_dead_follower_is_named_to_its_resident_and_started_again() {
    use rustix::process::Signal;
    let w = World::genesis("ndf");
    let r = Roots::new('f');
    provision(&w, &r, &w.r1);
    let m = Members::start(&w, &r, uid(&r.member.0));
    let sock = r.sock(&w.r1);
    let got = std::cell::RefCell::new(Err::<(u8, String), String>(String::new()));
    until(
        "a served sync",
        30,
        || {
            *got.borrow_mut() = nd_via(&sock, &["sync"]);
            got.borrow()
                .as_ref()
                .is_ok_and(|(e, _)| *e == command_exit::OK)
        },
        &|| format!("{:?}\n{}", got.borrow(), m.log()),
    );
    let me = r.base.0.join("nd-members.pid");
    signal(&me, Signal::STOP);
    let pid = signal(&r.pids().join(format!("{}.follow.pid", w.r1)), Signal::KILL);
    std::thread::sleep(std::time::Duration::from_millis(300));
    let named = nd_via(&sock, &["sync"]);
    signal(&me, Signal::CONT);
    match &named {
        Ok((e, t)) => assert!(
            *e == command_exit::CLIENT && t.contains("follow.sock"),
            "not named: {e} {t}"
        ),
        Err(e) => panic!("no reply while the follower was dead: {e}\n{}", m.log()),
    }
    until(
        "a sync served by the restarted follower",
        30,
        || nd_via(&sock, &["sync"]).is_ok_and(|(e, _)| e == command_exit::OK),
        &|| m.log(),
    );
    assert!(
        m.log().contains(&format!("{} follow ended", w.r1)),
        "{}",
        m.log()
    );
    assert_ne!(
        m.pid(&format!("{}.follow.pid", w.r1)),
        Some(pid),
        "the follower was not started again"
    );
}

/// One follower per resident, because a follower is one member's command machine (it plans every
/// call and envelope in its own MEMBER's name). A resident's nd --stdio driven at ANOTHER
/// resident's follower signs an envelope naming that member with its own key; the writer refuses
/// it (Envelope.check: unknownKey), follow retries once by the incoming key (PROTOCOL-46), and
/// nd --stdio's custody refuses that by name (noRotation). CONTROL: its own follower serves the
/// same sync.
#[test]
fn another_residents_follower_is_refused_by_name() {
    let w = World::genesis("ndo");
    let r = Roots::new('o');
    provision(&w, &r, &w.r1);
    provision(&w, &r, &w.r2);
    let m = Members::start(&w, &r, uid(&r.member.0));
    for g in [&w.r1, &w.r2] {
        until(
            "the member socket",
            30,
            || UnixStream::connect(r.sock(g)).is_ok(),
            &|| m.log(),
        );
    }
    // r1's workspace driven at r2's follow socket, by hand (nd-members never builds this)
    let wrong = r.base.0.join("wrong.sock");
    let ws = r.members().join(&w.r1);
    let fsock = r.follow_sock(&w.r2);
    let child = Command::new(nd_supervise())
        .arg(&wrong)
        .arg("--hide")
        .arg(&w.ws)
        .arg("--write")
        .arg(&ws)
        .arg("--exec")
        .arg(nd())
        .arg("--connect")
        .arg(&w.host_sock)
        .arg("--connect")
        .arg(&fsock)
        .arg("--")
        .arg(nd())
        .arg("--stdio")
        .arg(&ws)
        .arg(&fsock)
        .arg(&w.host_sock)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .spawn()
        .unwrap();
    let _held = nanodregg_devtools::Supervisor::hold(child, r.base.0.join("wrong.pid"));
    until(
        "the hand-built socket",
        30,
        || UnixStream::connect(&wrong).is_ok(),
        &|| m.log(),
    );
    w.run(&["create"]); // a Turn to catch up on
    let (e, t) = nd_via(&wrong, &["sync"]).unwrap();
    assert_eq!(e, command_exit::REFUSED, "another resident's follower: {t}");
    assert!(t.contains("refused noRotation"), "not refused by name: {t}");
    let (e, t) = nd_via(&r.sock(&w.r1), &["sync"]).unwrap();
    assert_eq!(e, command_exit::OK, "control: its own follower: {t}");
}

/// How many times nd-members started `role` of `name` (its `NAME ROLE PID` lines).
fn starts(log: &str, name: &str, role: &str) -> usize {
    let head = format!("nd-members: {name} {role} ");
    log.lines()
        .filter_map(|l| l.strip_prefix(&head))
        .filter(|rest| rest.bytes().all(|b| b.is_ascii_digit()))
        .count()
}

/// A member whose follower can never run (its Store is an empty directory: `host follow` refuses
/// it) is started again at most every RESTART_AFTER, and past STARTS_MAX starts it is named
/// `memberCrashLoop` and left unbound with no socket directory.
#[test]
fn a_member_that_always_crashes_is_named_crash_loop_and_left_unbound() {
    let w = World::genesis("ndc");
    let r = Roots::new('c');
    provision(&w, &r, &w.r1);
    let store = r.members().join(&w.r1).join("store");
    fs::remove_dir_all(&store).unwrap();
    nanodregg_devtools::mkdirs(&store).unwrap();
    let m = Members::start(&w, &r, uid(&r.member.0));
    until(
        "the first start",
        30,
        || starts(&m.log(), &w.r1, "follow") >= 1,
        &|| m.log(),
    );
    std::thread::sleep(std::time::Duration::from_millis(1500));
    assert!(
        starts(&m.log(), &w.r1, "follow") <= 2,
        "restarted without waiting RESTART_AFTER:\n{}",
        m.log()
    );
    let named = format!("memberCrashLoop {} follow", w.r1);
    until(
        "the crash loop named",
        60,
        || m.log().contains(&named),
        &|| m.log(),
    );
    assert_eq!(
        starts(&m.log(), &w.r1, "follow"),
        5,
        "STARTS_MAX starts:\n{}",
        m.log()
    );
    // nd-supervise binds the follow socket once host follow is spawned, before host refuses its
    // Store, so a stdio start may fall in that instant; never more than one
    assert!(
        starts(&m.log(), &w.r1, "stdio") <= 1,
        "stdio children without a follower:\n{}",
        m.log()
    );
    assert!(
        !r.member.0.join(&w.r1).exists(),
        "a crash-looping member left a socket directory"
    );
    std::thread::sleep(std::time::Duration::from_secs(3));
    assert_eq!(
        starts(&m.log(), &w.r1, "follow"),
        5,
        "started after the crash loop"
    );
}

/// Run nd-members to its end: its stderr and exit code. Not ended within 30 s FAILS by name (a
/// liveness deadline: every end here comes at start or at the first answer).
fn ends(c: &mut Command) -> (String, Option<i32>) {
    let err = Gone(nanodregg_devtools::scratch(&format!(
        "ndx{}",
        std::process::id()
    )));
    let log = err.0.join("err");
    let mut child = c
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(fs::File::create(&log).unwrap())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    let st = loop {
        if let Some(st) = child.try_wait().unwrap() {
            break st;
        }
        if std::time::Instant::now() > deadline {
            let _ = (child.kill(), child.wait());
            panic!(
                "hang: nd-members did not end: {}",
                fs::read_to_string(&log).unwrap_or_default()
            );
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    };
    (fs::read_to_string(&log).unwrap(), st.code())
}

/// A decider that prints `frame` once (a stub: `cat`), then sleeps.
fn stub(r: &Roots, names: Vec<Vec<u8>>) -> (PathBuf, PathBuf) {
    let dir = r.base.0.join("stub");
    nanodregg_devtools::mkdirs(&dir).unwrap();
    let mut f = Vec::new();
    write_frame(&mut f, &Verdict::Residents { names }.encode().unwrap()).unwrap();
    fs::write(dir.join("frame"), f).unwrap();
    let sh = r.base.0.join("stub.sh");
    fs::write(
        &sh,
        "#!/bin/sh\n/usr/bin/cat \"$1/frame\"\nexec /usr/bin/sleep 30\n",
    )
    .unwrap();
    fs::set_permissions(&sh, fs::Permissions::from_mode(0o700)).unwrap();
    (sh, dir)
}

/// Every own end by name and code (`members_exit`, Lean's `Hosting.MembersExit`), and a World past
/// RESIDENTS_MAX ends it with the decider's own code for that fact (7).
#[test]
fn nd_members_ends_by_name() {
    let w = World::genesis("nde");
    let r = Roots::new('e');
    let me = uid(&r.member.0);
    let broker = lean_bin("hosting-broker");
    let bargs = broker_args(&w);
    let bargs: Vec<&std::ffi::OsStr> = bargs.iter().map(|a| a.as_os_str()).collect();
    let (l, c) = ends(Command::new(env!("CARGO_BIN_EXE_nd-members")).arg("x"));
    assert_eq!(c, Some(i32::from(members_exit::USAGE)), "usage: {l}");
    // RLIMIT_NOFILE below one child's fds_max
    let mut low = Command::new("/bin/sh");
    low.arg("-c")
        .arg("ulimit -n 40 && exec \"$0\" \"$@\"")
        .arg(env!("CARGO_BIN_EXE_nd-members"));
    let a = argv(&w, &r, me, &broker, &bargs);
    low.args(a.get_args());
    let (l, c) = ends(&mut low);
    assert_eq!(c, Some(i32::from(members_exit::FD_LIMIT)), "{l}");
    assert!(l.contains("fdLimit RLIMIT_NOFILE 40"), "{l}");
    // each root, refused by name before the decider starts
    for (root, code, name) in [
        (r.member.0.clone(), members_exit::MEMBER_ROOT, "memberRoot"),
        (r.members(), members_exit::MEMBERS_ROOT, "membersRoot"),
        (r.follow.0.clone(), members_exit::FOLLOW_ROOT, "followRoot"),
    ] {
        let was = fs::metadata(&root).unwrap().permissions().mode() & 0o7777;
        fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
        let (l, c) = ends(&mut argv(&w, &r, me, &broker, &bargs));
        fs::set_permissions(&root, fs::Permissions::from_mode(was)).unwrap();
        assert_eq!(c, Some(i32::from(code)), "{name}: {l}");
        assert!(l.contains(name), "{name}: {l}");
    }
    // a decider that never ran its own end
    let (l, c) = ends(&mut argv(&w, &r, me, Path::new("/usr/bin/false"), &[]));
    assert_eq!(c, Some(i32::from(members_exit::DECIDER_MECHANISM)), "{l}");
    // a name that is not a grain directory name, and a World past the bound
    let (sh, dir) = stub(&r, vec![b"../x".to_vec()]);
    let (l, c) = ends(&mut argv_over(&w, &r, me, &dir, &sh, &[dir.as_os_str()]));
    assert_eq!(
        c,
        Some(i32::from(members_exit::MEMBER_ROOT)),
        "a bad name: {l}"
    );
    let past: Vec<Vec<u8>> = (0..1025)
        .map(|i| format!("{i:064x}").into_bytes())
        .collect();
    let (sh, dir) = stub(&r, past);
    let (l, c) = ends(&mut argv_over(&w, &r, me, &dir, &sh, &[dir.as_os_str()]));
    assert_eq!(
        c,
        Some(i32::from(decider_exit::RESIDENTS_PAST_BOUND)),
        "past the bound: {l}"
    );
    assert!(l.contains("residentsPastBound 1025"), "{l}");
    // CONTROL: exactly the bound is served (no end within a few ticks)
    let at: Vec<Vec<u8>> = (0..1024)
        .map(|i| format!("{i:064x}").into_bytes())
        .collect();
    let (sh, dir) = stub(&r, at);
    let run = Logged::spawn(
        argv_over(&w, &r, me, &dir, &sh, &[dir.as_os_str()]),
        r.base.0.join("bound.pid"),
    );
    std::thread::sleep(std::time::Duration::from_secs(2));
    assert!(
        !run.log().contains("residentsPastBound"),
        "the bound itself refused: {}",
        run.log()
    );
    assert_eq!(
        run.log().matches("memberMissing").count(),
        1024,
        "control: 1024 names read:\n{}",
        run.log()
    );
}
