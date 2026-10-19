//! nd-members (HOSTING-30, CLIENT-29): each resident grain the World holds gets its member socket
//! `MEMBER/<dirOf>/nd.sock`, served by `nd --stdio` over its own member workspace and its OWN
//! follower (`host follow STATE/<name>/store MEMBER GRANT`, from the provisioning step's
//! `STATE/<name>/follow`), from the decider's `residents` frames: at birth, gone at removal. The
//! stdio child writes its workspace and nothing of STATE (HOSTING-32: the probe in nd's place).
//!
//! Every plant runs the real binaries: a real writer and Store (`World`), the real decider
//! (`hosting-residents STORE`, HOSTING-33, which answers only `residents`), nd-supervise, nd and
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
use nanodregg_launcher::broker_generated::{GRAIN_NAME_MAX, SOCK_PATH_MAX};
use nanodregg_launcher::broker_generated::{decider_exit, members_exit, write_frame};

/// nd-members' argv over `w` and `r`, serving uid `peer`, with `decider` and its arguments: the
/// plants' argv. With the real decider it is exactly the emitted unit's (`members_rendered`;
/// checked in `each_resident_grain_gets_its_member_socket_and_a_removed_one_loses_it`).
fn argv(w: &World, r: &Roots, peer: u32, decider: &Path, dargs: &[&std::ffi::OsStr]) -> Command {
    argv_over(w, r, peer, &w.store, &nd(), decider, dargs)
}

/// nd-members' argv with STORE (the decider's only readable path) and ND given.
fn argv_over(
    w: &World,
    r: &Roots,
    peer: u32,
    store: &Path,
    nd_exe: &Path,
    decider: &Path,
    dargs: &[&std::ffi::OsStr],
) -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_nd-members"));
    c.arg(&r.member.0)
        .arg(r.members())
        .arg(r.state())
        .arg(&r.follow.0)
        .arg(r.pids())
        .arg(&w.host_sock)
        .arg(peer.to_string())
        .arg(nd_supervise())
        .arg(nd_exe)
        .arg(lean_bin("host"))
        .arg(store)
        .arg("--hide")
        .arg(&w.ws)
        .arg("--hide")
        .arg(&w.holding)
        .arg("--")
        .arg(decider)
        .args(dargs);
    c
}

/// The real decider's argv after DECIDER (`hosting-residents STORE`, HOSTING-33): the Store alone.
fn broker_args(w: &World) -> Vec<std::ffi::OsString> {
    vec![w.store.clone().into()]
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
/// tick loop; removed → a peer waiting on each of its sockets reads `closed unreachable` (CLIENT-30),
/// both sockets, directories and PID files gone, a connect refused ENOENT;
/// an app grain → nothing. nd-members' own fds do not grow with the residents it serves.
#[test]
fn each_resident_grain_gets_its_member_socket_and_a_removed_one_loses_it() {
    let w = World::genesis("ndm");
    let r = Roots::new('a');
    let ids: Vec<String> = [&w.r1, &w.r2].iter().map(|g| w.provision(&r, g)).collect();
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
    // the plants' argv is the emitted unit's (the unit and the plants cannot drift)
    let bargs = broker_args(&w);
    let bargs: Vec<&std::ffi::OsStr> = bargs.iter().map(|a| a.as_os_str()).collect();
    let (unit, plant) = (
        members_rendered(&w, &r, uid(&r.member.0)),
        argv(
            &w,
            &r,
            uid(&r.member.0),
            &lean_bin("hosting-residents"),
            &bargs,
        ),
    );
    assert_eq!(
        (unit.get_program(), unit.get_args().collect::<Vec<_>>()),
        (plant.get_program(), plant.get_args().collect::<Vec<_>>()),
        "the plants' argv is not the emitted unit's"
    );
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
    let id3 = w.provision(&r, &r3);
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
    // a peer waits on each of r2's sockets (the member one served once) as r2 is removed (CLIENT-30)
    let waiting: Vec<UnixStream> = [r.sock(&w.r2), r.follow_sock(&w.r2)]
        .iter()
        .map(|p| {
            let s = UnixStream::connect(p).unwrap();
            s.set_read_timeout(Some(table::MUX.reply_write)).unwrap();
            s
        })
        .collect();
    let read = NdCommand {
        argv: vec![b"read".to_vec(), obj.as_bytes().to_vec()],
    };
    frame::write(
        &mut &waiting[0],
        table::LIMITS,
        follow_op::COMMAND,
        &read.encode().unwrap(),
    )
    .unwrap();
    assert_eq!(
        frame::read(&mut &waiting[0], table::LIMITS).unwrap().op,
        status::OK
    );
    // the operator removes r2 (lifecycle method 0)
    w.run(&["invoke", &w.r2, "0", "(record)"]);
    until(
        "the removed resident's member socket to go",
        30,
        || !r.member.0.join(&w.r2).exists() && !r.follow.0.join(&w.r2).exists(),
        &|| m.log(),
    );
    for mut s in waiting {
        let f = frame::read(&mut s, table::LIMITS);
        let f = f.unwrap_or_else(|e| panic!("a bare end ({e}) for r2's peer:\n{}", m.log()));
        assert_eq!(
            (f.op, f.payload.as_slice()),
            (status::CLOSED, &b"unreachable"[..]),
            "a peer of the removed resident"
        );
    }
    let e = UnixStream::connect(r.sock(&w.r2)).unwrap_err();
    assert_eq!(
        e.kind(),
        std::io::ErrorKind::NotFound,
        "a connect to the removed resident's socket"
    );
    // its supervisors are reaped on a later tick (CLIENT-30: the tick never waits on a stop)
    for role in ["follow", "stdio"] {
        let file = format!("{}.{role}.pid", w.r2);
        until(
            "the removed resident's PID file to go",
            10,
            || m.pid(&file).is_none(),
            &|| m.log(),
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
    w.provision(&r, &w.r1);
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
    w.provision(&r, &w.r1);
    w.provision(&r, &w.r2);
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
    w.provision(&r, &w.r1);
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
/// nd --stdio's custody refuses that (noRotation); the command ends by the WRITER's word,
/// `refused unknownKey` (PROTOCOL-56: custody's refusal of the incoming key never masks it).
/// CONTROL: its own follower serves the same sync.
#[test]
fn another_residents_follower_is_refused_by_name() {
    let w = World::genesis("ndo");
    let r = Roots::new('o');
    w.provision(&r, &w.r1);
    w.provision(&r, &w.r2);
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
    assert!(t.contains("refused unknownKey"), "not refused by name: {t}");
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
    w.provision(&r, &w.r1);
    let store = r.state().join(&w.r1).join("store");
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

/// A decider answering whatever `DIR/frame` holds at each ask (a stub: python, one frame per
/// request), so the test moves the World's answer between ticks by renaming one file.
fn steered(r: &Roots, names: &[&String]) -> (PathBuf, PathBuf) {
    let dir = r.base.0.join("steer");
    nanodregg_devtools::mkdirs(&dir).unwrap();
    steer(&dir, names);
    let sh = r.base.0.join("steer.sh");
    let py = "import struct,sys\ni,o=sys.stdin.buffer,sys.stdout.buffer\nwhile True:\n h=i.read(4)\n if len(h)<4: break\n i.read(struct.unpack('<I',h)[0])\n o.write(open(sys.argv[1]+'/frame','rb').read()); o.flush()\n";
    fs::write(
        &sh,
        format!("#!/bin/sh\nexec /usr/bin/python3 -I -c \"{py}\" \"$1\"\n"),
    )
    .unwrap();
    fs::set_permissions(&sh, fs::Permissions::from_mode(0o700)).unwrap();
    (sh, dir)
}

/// The steered decider's next answer: `names`.
fn steer(dir: &Path, names: &[&String]) {
    let names = names.iter().map(|n| n.as_bytes().to_vec()).collect();
    let mut f = Vec::new();
    write_frame(&mut f, &Verdict::Residents { names }.encode().unwrap()).unwrap();
    fs::write(dir.join("frame.new"), f).unwrap();
    fs::rename(dir.join("frame.new"), dir.join("frame")).unwrap();
}

/// CLIENT-30 (ROOT ruling): a removal never stalls the tick. r2's stdio supervisor is held (SIGSTOP:
/// a supervisor that cannot end, which no slow peer makes for long, since its writers give up within
/// `reply_write`) while r2 is removed and r3 born in one answer: r3 is bound and served at once.
/// r2 answered again while its supervisor stops is `memberStopping`, and gets no second supervisor;
/// at GRACE the held one is SIGKILLed (`memberStopForced`) and r2 is bound again. r1 is served
/// throughout.
#[test]
fn a_held_removal_stalls_no_birth_and_is_killed_at_its_grace() {
    use rustix::process::Signal;
    let w = World::genesis("ndg");
    let r = Roots::new('g');
    let r3 = w.resident("r3");
    for g in [&w.r1, &w.r2, &r3] {
        w.provision(&r, g);
    }
    let (sh, dir) = steered(&r, &[&w.r1, &w.r2]);
    let c = argv_over(
        &w,
        &r,
        uid(&r.member.0),
        &dir,
        &nd(),
        &sh,
        &[dir.as_os_str()],
    );
    let m = Members::spawn(c, &r);
    let served = |g: &str| nd_via(&r.sock(g), &["sync"]).is_ok_and(|(e, _)| e == command_exit::OK);
    for g in [&w.r1, &w.r2] {
        until("a born resident served", 30, || served(g), &|| m.log());
    }
    let held = r.pids().join(format!("{}.stdio.pid", w.r2));
    let pid = signal(&held, Signal::STOP);
    steer(&dir, &[&w.r1, &r3]);
    until(
        "r2 removed",
        10,
        || m.log().contains(&format!("removed {}", w.r2)),
        &|| m.log(),
    );
    let removed = std::time::Instant::now();
    until("r3 born while r2 is held", 10, || served(&r3), &|| m.log());
    assert!(
        removed.elapsed() < std::time::Duration::from_secs(10),
        "the birth waited on the held removal:\n{}",
        m.log()
    );
    steer(&dir, &[&w.r1, &w.r2, &r3]);
    let stopping = format!("memberStopping {}", w.r2);
    until(
        "r2's rebirth named waiting",
        10,
        || m.log().contains(&stopping),
        &|| m.log(),
    );
    assert_eq!(
        starts(&m.log(), &w.r2, "stdio"),
        1,
        "a second r2 supervisor:\n{}",
        m.log()
    );
    assert!(served(&w.r1), "control: r1 while r2 stops");
    let forced = format!("memberStopForced {}", w.r2);
    let grace = table::MUX.reply_write * 3;
    until(
        "the held supervisor killed at GRACE",
        grace.as_secs() + 30,
        || m.log().contains(&forced),
        &|| m.log(),
    );
    assert!(
        removed.elapsed() >= grace - std::time::Duration::from_secs(1),
        "killed before GRACE"
    );
    // killed is not yet reaped: until nd-members' next tick waits it, the killed supervisor is a
    // zombie whose /proc entry stands; it must be gone (killed AND reaped) within a few ticks
    until(
        "the held supervisor killed and reaped",
        10,
        || !Path::new(&format!("/proc/{pid}")).exists(),
        &|| m.log(),
    );
    until("r2 bound again", 30, || served(&w.r2), &|| m.log());
    assert_eq!(starts(&m.log(), &w.r2, "stdio"), 2, "{}", m.log());
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
    let broker = lean_bin("hosting-residents");
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
    // a socket root so long that ROOT/<64-byte name>/SOCK would pass sun_path is refused at start, by
    // name and length, never per resident (bind → refusedAtLaunch → memberCrashLoop); CONTROL: at
    // exactly SOCK_PATH_MAX the roots pass and the run ends at its decider (/usr/bin/false)
    for (short, code, name, sock) in [
        (
            r.member.0.clone(),
            members_exit::MEMBER_ROOT,
            "memberRoot",
            "nd.sock",
        ),
        (
            r.follow.0.clone(),
            members_exit::FOLLOW_ROOT,
            "followRoot",
            "follow.sock",
        ),
    ] {
        for over in [1, 0] {
            let want = SOCK_PATH_MAX as usize + over;
            // a sibling of the short root, named to make the root exactly want - 2 - name - sock
            let target = want - (GRAIN_NAME_MAX as usize + sock.len() + 2);
            let (parent, base) = (short.parent().unwrap(), short.file_name().unwrap());
            let n = target - parent.as_os_str().len() - 1;
            assert!(
                n >= base.len(),
                "plant: {} is past the root being planted",
                short.display()
            );
            let mut leaf = base.to_owned();
            leaf.push("l".repeat(n - base.len()));
            let long = parent.join(leaf);
            let made = long != short;
            if made {
                fs::create_dir(&long).unwrap();
                let mode = fs::metadata(&short).unwrap().permissions().mode() & 0o7777;
                fs::set_permissions(&long, fs::Permissions::from_mode(mode)).unwrap();
            }
            assert_eq!(long.as_os_str().len(), target);
            let a = argv(&w, &r, me, Path::new("/usr/bin/false"), &[]);
            let args: Vec<std::ffi::OsString> = a
                .get_args()
                .map(|x| {
                    if x == short.as_os_str() {
                        long.clone().into()
                    } else {
                        x.to_owned()
                    }
                })
                .collect();
            let (l, c) = ends(Command::new(a.get_program()).args(&args));
            if made {
                fs::remove_dir(&long).unwrap();
            }
            if over == 1 {
                assert_eq!(c, Some(i32::from(code)), "{name} too long: {l}");
                assert!(
                    l.contains(&format!("{name} "))
                        && l.contains(&format!("socket path {want} bytes")),
                    "{l}"
                );
            } else {
                assert_eq!(
                    c,
                    Some(i32::from(members_exit::DECIDER_MECHANISM)),
                    "{name} at the bound: {l}"
                );
            }
        }
    }
    // STATE inside MEMBERS: a follower Store would sit in a workspace the stdio child writes
    let inner = r.members().join("state");
    fs::create_dir(&inner).unwrap();
    fs::set_permissions(&inner, fs::Permissions::from_mode(0o700)).unwrap();
    let nested = argv(&w, &r, me, &broker, &bargs);
    let args: Vec<std::ffi::OsString> = nested
        .get_args()
        .map(|a| {
            if a == r.state().as_os_str() {
                inner.clone().into_os_string()
            } else {
                a.to_owned()
            }
        })
        .collect();
    let mut nested_c = Command::new(nested.get_program());
    nested_c.args(&args);
    let (l, c) = ends(&mut nested_c);
    assert_eq!(
        c,
        Some(i32::from(members_exit::ROOTS_OVERLAP)),
        "nested roots: {l}"
    );
    assert!(l.contains("rootsOverlap"), "nested roots: {l}");
    fs::remove_dir(&inner).unwrap();
    // a decider that never ran its own end
    let (l, c) = ends(&mut argv(&w, &r, me, Path::new("/usr/bin/false"), &[]));
    assert_eq!(c, Some(i32::from(members_exit::DECIDER_MECHANISM)), "{l}");
    // a name that is not a grain directory name, and a World past the bound
    let (sh, dir) = stub(&r, vec![b"../x".to_vec()]);
    let (l, c) = ends(&mut argv_over(
        &w,
        &r,
        me,
        &dir,
        &nd(),
        &sh,
        &[dir.as_os_str()],
    ));
    assert_eq!(
        c,
        Some(i32::from(members_exit::MEMBER_ROOT)),
        "a bad name: {l}"
    );
    let past: Vec<Vec<u8>> = (0..1025)
        .map(|i| format!("{i:064x}").into_bytes())
        .collect();
    let (sh, dir) = stub(&r, past);
    let (l, c) = ends(&mut argv_over(
        &w,
        &r,
        me,
        &dir,
        &nd(),
        &sh,
        &[dir.as_os_str()],
    ));
    assert_eq!(
        c,
        Some(i32::from(decider_exit::RESIDENTS_PAST_BOUND)),
        "past the bound: {l}"
    );
    assert!(l.contains("residentsPastBound 1025"), "{l}");
    // CONTROL: exactly the bound is served: all 1024 names are read (one `memberMissing` each) and
    // the bound is not refused. Waited for by its outcome with a liveness deadline, never a fixed
    // sleep: on a loaded box 2 s read 378 of the 1024 (KERNEL-25's judge).
    let at: Vec<Vec<u8>> = (0..1024)
        .map(|i| format!("{i:064x}").into_bytes())
        .collect();
    let (sh, dir) = stub(&r, at);
    let run = Logged::spawn(
        argv_over(&w, &r, me, &dir, &nd(), &sh, &[dir.as_os_str()]),
        r.base.0.join("bound.pid"),
    );
    until(
        "1024 names read, or the bound refused",
        120,
        || {
            let l = run.log();
            l.contains("residentsPastBound") || l.matches("memberMissing").count() >= 1024
        },
        &|| run.log(),
    );
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

/// HOSTING-32 (cv 01a1507c-7245): the stdio child's only write is its member workspace. With the
/// launcher's probe in nd's place (`probe --stdio WS …`, under exactly the policy nd-members gives
/// `nd --stdio`), a write into its own follower Store, a read of its `follow` file and a listing of
/// the Store are refused by the sandbox, while a write into the workspace lands. CONTROL: the same
/// probe unconfined reaches all four, so each refusal is the sandbox's.
#[test]
fn the_stdio_child_writes_its_workspace_and_no_follower_store() {
    let w = World::genesis("nds");
    let r = Roots::new('s');
    let g = w.r1.clone();
    w.provision(&r, &g);
    let ws = r.members().join(&g);
    let st = r.state().join(&g);
    let targets = |tag: &str| {
        format!(
            "ws write {}\nstore write {}\nfollow read {}\nlist list {}\n",
            ws.join(format!("probe.{tag}")).display(),
            st.join("store").join(format!("probe.{tag}")).display(),
            st.join("follow").display(),
            st.join("store").display(),
        )
    };
    let probe = Path::new(env!("CARGO_BIN_EXE_probe"));
    let out = ws.join("probe.out");
    // CONTROL: unconfined, the probe reaches every target
    fs::write(ws.join("probe.targets"), targets("c")).unwrap();
    let st_c = Command::new(probe)
        .arg("--stdio")
        .arg(&ws)
        .status()
        .unwrap();
    assert!(
        st_c.success(),
        "control: the probe failed unconfined: {st_c}"
    );
    let got = fs::read_to_string(&out).unwrap();
    assert_eq!(got.lines().count(), 4, "control: four targets tried: {got}");
    for l in got.lines() {
        assert!(
            l.split(' ').nth(1) == Some("ok"),
            "control: unconfined, {l}"
        );
    }
    fs::remove_file(&out).unwrap();
    fs::remove_file(st.join("store").join("probe.c")).unwrap();
    // the probe as nd: nd-members starts it under the stdio child's policy once the follow socket is
    // bound; it tries its targets and ends (nd-members restarts it, then names a crash loop)
    fs::write(ws.join("probe.targets"), targets("s")).unwrap();
    let args = broker_args(&w);
    let args: Vec<&std::ffi::OsStr> = args.iter().map(|a| a.as_os_str()).collect();
    let c = argv_over(
        &w,
        &r,
        uid(&r.member.0),
        &w.store,
        probe,
        &lean_bin("hosting-residents"),
        &args,
    );
    let m = Members::spawn(c, &r);
    until(
        "the probe's four lines",
        60,
        || fs::read_to_string(&out).is_ok_and(|t| t.lines().count() >= 4),
        &|| m.log(),
    );
    assert!(
        m.log().contains(&format!("{g} stdio ")),
        "the probe did not run as the stdio child:\n{}",
        m.log()
    );
    let got = fs::read_to_string(&out).unwrap();
    let verdict = |name: &str| {
        got.lines()
            .find_map(|l| l.strip_prefix(&format!("{name} ")))
            .unwrap_or("absent")
            .to_owned()
    };
    assert_eq!(
        verdict("ws"),
        "ok",
        "the stdio child cannot write its own workspace:\n{got}"
    );
    assert!(
        verdict("store").starts_with("denied"),
        "the stdio child wrote its follower Store:\n{got}"
    );
    assert!(
        verdict("follow").starts_with("denied"),
        "the stdio child read its follow file:\n{got}"
    );
    assert!(
        verdict("list").starts_with("denied"),
        "the stdio child listed its follower Store:\n{got}"
    );
    assert!(
        !st.join("store").join("probe.s").exists(),
        "a probe file landed in the follower Store"
    );
    drop(m);
}

/// HOSTING-33: nd-members' decider, `hosting-residents STORE`, answers `residents` with the World's
/// resident grains and nothing else: a `decide` frame (keybroker's question, never nd-members') ends
/// it `badRequest`, and any argv but one STORE ends it `usage`. It is given no clock, no key slots
/// and no operator (the unit's `membersUnit_decider_store`).
#[test]
fn the_residents_decider_answers_residents_and_refuses_a_decide() {
    use nanodregg_launcher::broker_generated::wire::Request;
    let w = World::genesis("ndh");
    let exe = lean_bin("hosting-residents");
    for args in [vec![], vec!["0", "1"]] {
        let o = Command::new(&exe).args(&args).output().unwrap();
        assert_eq!(
            o.status.code(),
            Some(i32::from(decider_exit::USAGE)),
            "argv {args:?}: {}",
            String::from_utf8_lossy(&o.stderr)
        );
    }
    let mut child = Command::new(&exe)
        .arg(&w.store)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut din = child.stdin.take().unwrap();
    let mut dout = child.stdout.take().unwrap();
    let mut names = nanodregg_launcher::residents::ask(&mut din, &mut dout, now_ms())
        .expect("a residents answer");
    names.sort();
    let mut want = vec![w.r1.clone().into_bytes(), w.r2.clone().into_bytes()];
    want.sort();
    assert_eq!(names, want, "the World's resident grains");
    let decide = Request::Decide {
        resident: w.r1.clone().into_bytes(),
        at_ms: now_ms(),
    }
    .encode()
    .unwrap();
    write_frame(&mut din, &decide).unwrap();
    drop(din);
    let o = child.wait_with_output().unwrap();
    assert_eq!(
        o.status.code(),
        Some(i32::from(decider_exit::BAD_REQUEST)),
        "a decide frame: {}",
        String::from_utf8_lossy(&o.stderr)
    );
    assert!(
        String::from_utf8_lossy(&o.stderr).contains("hosting-residents: badRequest"),
        "{}",
        String::from_utf8_lossy(&o.stderr)
    );
}
