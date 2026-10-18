//! THE BAR's hosted Hermes, end to end (`cargo:launcher:resident_bell`, HOSTING-27): the real
//! resident, the Lean exe `resident`, confined under grain-launch with its Lean plan, answers a
//! bell (`world/resident/Bell`, LANG-52) that the founder rings, with the reply keybroker got from
//! the FAKE provider. The founder reads the answer.
//!
//! Everything is the deployed path:
//! - a real Store, with the operator's follower Store under the hosting root;
//! - keybroker on the emitted unit's argv;
//! - grain-launch on ITS unit's argv over the real `hosting-controller`;
//! - the resident's member, served by `nd --stdio` under nd-supervise on MEMBER/<dirOf>/nd.sock;
//! - the operator's Bell object, `resident` = that member, with `observe,invoke:0` granted to it
//!   (the config names the grant; `invoke … --via` it).
//!
//! The resident reads `pkg/resident.conf` (one Lang value) and its plan from argv. It learns
//! `answer`'s index from the description. Sequencing waits on what the founder reads, never on time
//! alone.
//!
//! - B1: the founder rings `hi`. The founder reads exactly
//!   `(record (answer "hello back") (open true) (pending false) (resident #M) (ring "hi") (ringer #OP))`.
//! - B2, exactly one ask per ring: a second ring gets its own answer. After it, the fake provider
//!   has received exactly two requests, and still two after several more ticks with nothing
//!   pending. The key went upstream on both (CONTROL); the resident's volume never holds it.
//! - Refused, each by name. The member surface names a method's check `program`; the bell's own reason
//!   (`unrung`, `notResident`) does not cross it, and Lang's journey LB5/LB8 pin those reasons:
//!   - (unrung) the resident's member answers a bell that is not pending: `refused program`, and
//!     the state does not move.
//!   - (notResident) the operator answers: `refused program`. The resident exe, configured for a
//!     bell whose resident is the operator (granted invoke), asks ONCE. Its answer is refused, the
//!     bell still waits, so it ends `answerRefused program`. The controller restarts it; it answers
//!     again from its kept text and asks no more (the provider's count rises by exactly one).
//!   - (grantRight) the resident exe, configured for a bell whose grant to it carries `observe`
//!     but not `invoke:0`, ends `answerRefused grantRight`, again after exactly one ask.
//!   - (off its fence) the resident exe refuses an argv that is not its own plan before it reads
//!     anything: its broker and member sockets swapped (a reordering of grain-launch's fields), and
//!     another resident's broker socket, each end `argvNotPlan` (exit 10). CONTROL: its true argv,
//!     read back from grain-launch's report, passes `place` and reaches the config (exit 11, run
//!     with no config). Inside the sandbox that other socket does not even exist: the resident row's
//!     R5.
//!
//! Needs the built Lean exes (`resident`, `hosting-controller`, `hosting-broker`, `host`) and the
//! client's `nd`/`nd-supervise`. A missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::Command;

use common::*;
use nanodregg_client::generated::layout::{Command as NdCommand, CommandReply};
use nanodregg_client::generated::{follow_op, status};
use nanodregg_client::{frame, table};
use nanodregg_devtools::lean_bin;

const LABEL: &str = "w";

/// One command through a member socket (the client's own frame and layout code): exit, stdout,
/// stderr.
fn member_cmd(sock: &Path, argv: &[&str]) -> (u8, String, String) {
    let mut s = UnixStream::connect(sock).unwrap();
    s.set_read_timeout(Some(table::REPLY)).unwrap();
    let c = NdCommand {
        argv: argv.iter().map(|a| a.as_bytes().to_vec()).collect(),
    }
    .encode()
    .unwrap();
    frame::write(&mut s, table::LIMITS, follow_op::COMMAND, &c).unwrap();
    let f = frame::read(&mut s, table::LIMITS).unwrap();
    assert_eq!(f.op, status::OK, "the member socket's reply status");
    let r = CommandReply::decode(&f.payload).unwrap();
    (
        r.exit,
        String::from_utf8_lossy(&r.stdout).into_owned(),
        String::from_utf8_lossy(&r.stderr).into_owned(),
    )
}

/// The Bell's state text for a new bell whose resident is `resident`.
fn bell_state(resident: &str, ringer: &str) -> String {
    format!(
        "(record (answer \"\") (open true) (pending false) (resident #{resident}) (ring \"\") (ringer #{ringer}))"
    )
}

/// The resident's config for bell `bell`.
fn conf(bell: &str, grant: &str) -> String {
    format!(
        "(record (bell #{bell}) (grant #{grant}) (maxTokens 50) (model \"claude-m\") (system \"\"))"
    )
}

#[test]
fn the_resident_answers_the_bell_once_per_ring_and_nothing_else() {
    let d = dir("bel");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let server = pki.server(HOST, false);
    pki.pin(&d, &[&server]);
    let (up, seen) = upstream(Mode::Ok, &server);
    let asks = || seen.lock().unwrap().len();
    let sock = Short::new("b");
    sockdir(&sock.0);
    let sock = &sock.0;
    let hosting = Gone(nanodregg_devtools::scratch(&format!(
        "kbb{}",
        std::process::id()
    )));
    let hosting = &hosting.0;
    let world = hosting.join("worlds").join(LABEL);
    nanodregg_devtools::mkdirs(&world.join("members")).unwrap();
    let mroot = Short::new("n");
    let mroot = &mroot.0;
    let w = World::genesis_following("bel", Some(world.join("store")));
    let g = w.resident("resident");
    w.allowance(&g, "claude-m", 7, 100_000);
    nanodregg_devtools::mkdirs(&mroot.join(&g)).unwrap();
    fs::set_permissions(mroot.join(&g), fs::Permissions::from_mode(0o700)).unwrap();
    let mfollow = Short::new("e");
    let member = w.member(
        &world.join("members").join(&g),
        &mfollow.0.join("follow.sock"),
        &w.root.join("stores/R"),
        &mroot.join(&g).join("nd.sock"),
        &d.join("pids"),
    );
    let m = member.id.clone();
    let op = w.operator.clone();
    // the bells: B (the resident's, granted), NG (the resident's, no grant), NR (the operator's,
    // granted)
    let bell_pkg = w.install("world/resident/Bell");
    let create = |resident: &str| {
        line(
            &w.run(&["create", "--pkg", &bell_pkg, &bell_state(resident, &op)]),
            "id ",
        )
        .to_owned()
    };
    let (b, ng, nr) = (create(&m), create(&m), create(&op));
    let grant = |o: &str, rights: &str| line(&w.run(&["grant", o, &m, rights]), "id ").to_owned();
    let (gb, gnr, gng) = (
        grant(&b, "observe,invoke:0"),
        grant(&nr, "observe,invoke:0"),
        grant(&ng, "observe"),
    );
    // the grain's package: the resident and its config
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(&lean_bin("resident"), &pkg.join("resident"));
    fs::write(pkg.join("resident.conf"), conf(&b, &gb)).unwrap();

    let (uid, _) = me(sock);
    let kb = start_residents(
        sock,
        &d.join("pids"),
        &keys,
        &anchors,
        &up,
        &w,
        &[g.as_str(), w.r1.as_str()],
        uid,
    );
    let t1 = now_ms();
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
    let log = || gl.log();
    let read = |o: &str| w.run(&["read", o]).trim_end().to_owned();
    let start = || {
        w.run(&["invoke", &g, "1", "(record)"]);
        w.run(&["sync"]);
    };
    let stop = || {
        w.run(&["invoke", &g, "2", "(record)"]);
        w.run(&["sync"]);
    };
    next_window(t1);
    start();
    until(
        "the resident learns the bell",
        90,
        || log().contains("resident: bell answer method 0"),
        &log,
    );

    // B1: the founder rings; the resident answers; the founder reads it
    w.run(&["invoke", &b, "3", "(record (text \"hi\"))"]);
    let answered = |text: &str, ring: &str| {
        format!(
            "(record (answer \"{text}\") (open true) (pending false) (resident #{m}) (ring \"{ring}\") (ringer #{op}))"
        )
    };
    until(
        "the first answer",
        90,
        || read(&b) == answered("hello back", "hi"),
        &|| format!("{}\n{}", read(&b), log()),
    );
    assert_eq!(asks(), 1, "B1: one ring, one ask");

    // B2: a second ring, its own ask and answer; then nothing more
    w.run(&["invoke", &b, "3", "(record (text \"again\"))"]);
    until(
        "the second answer",
        90,
        || read(&b) == answered("hello back", "again"),
        &|| format!("{}\n{}", read(&b), log()),
    );
    // five ticks with nothing pending: an absence has only time to wait on
    std::thread::sleep(std::time::Duration::from_secs(5));
    assert_eq!(asks(), 2, "B2: two rings, exactly two asks:\n{}", log());
    let reqs = seen.lock().unwrap().clone();
    assert!(
        reqs.iter()
            .all(|r| contains(r, &[b"x-api-key: ".as_slice(), KEY].concat())),
        "control: the key went upstream"
    );
    for e in fs::read_dir(&vol).unwrap().filter_map(Result::ok) {
        assert!(
            !contains(&fs::read(e.path()).unwrap(), KEY),
            "the key reached the resident's volume"
        );
    }

    // unrung: the resident's member answers a bell with nothing pending
    let (exit, _, err) = member_cmd(
        &member.sock,
        &["invoke", &b, "0", "(record (text \"x\"))", "--via", &gb],
    );
    assert_eq!(
        (exit, err.trim_end()),
        (1, "refused program"),
        "unrung: an answer with nothing pending"
    );
    assert_eq!(
        read(&b),
        answered("hello back", "again"),
        "unrung: the bell moved"
    );
    // notResident (the operator answers)
    let o = w.nd(&["invoke", &b, "0", "(record (text \"x\"))"]);
    assert!(
        both(&o).contains("refused program"),
        "notResident: the operator answered: {}",
        both(&o)
    );

    // the resident exe on a bell whose resident is the operator: one ask, then notResident
    let mutation = |bell: &str, via: &str, ring: &str, name: &str| {
        stop();
        until(
            "no child of the grain",
            60,
            || fs::read_dir(&gl_pids).unwrap().next().is_none(),
            &log,
        );
        let before = asks();
        let refusals = log().matches(&format!("answerRefused {name}")).count();
        fs::write(pkg.join("resident.conf"), conf(bell, via)).unwrap();
        w.run(&["invoke", bell, "3", &format!("(record (text \"{ring}\"))")]);
        start();
        until(
            &format!("two {name} ends"),
            120,
            || log().matches(&format!("answerRefused {name}")).count() >= refusals + 2,
            &log,
        );
        assert_eq!(
            asks(),
            before + 1,
            "{name}: the resident asked more than once for one ring:\n{}",
            log()
        );
        assert!(
            read(bell).contains("(pending true)"),
            "{name}: the bell took an answer"
        );
    };
    mutation(&nr, &gnr, "nr", "program");
    mutation(&ng, &gng, "ng", "grantRight");

    // off its fence: argv that is not its plan. Its true argv, as grain-launch joined it:
    let connects: Vec<String> = log()
        .lines()
        .filter_map(|l| l.strip_prefix(&format!("grain-launch: {g} connect ")))
        .map(str::to_owned)
        .take(2)
        .collect();
    assert_eq!(connects.len(), 2, "grain-launch's connect report");
    let (bs, ms) = (connects[0].clone(), connects[1].clone());
    let prog = pkg.join("resident").display().to_string();
    let argv = |broker: &str, member: &str| {
        vec![
            prog.clone(),
            "1".into(),
            pkg.display().to_string(),
            "1".into(),
            vol.display().to_string(),
            "0".into(),
            "1".into(),
            broker.to_owned(),
            "1".into(),
            member.to_owned(),
        ]
    };
    let run = |args: Vec<String>, conf_dir_empty: bool| {
        let saved = pkg.join("resident.conf.saved");
        if conf_dir_empty {
            fs::rename(pkg.join("resident.conf"), &saved).unwrap();
        }
        let o = Command::new(lean_bin("resident"))
            .args(&args)
            .output()
            .unwrap();
        if conf_dir_empty {
            fs::rename(&saved, pkg.join("resident.conf")).unwrap();
        }
        (
            o.status.code(),
            String::from_utf8_lossy(&o.stderr).into_owned(),
        )
    };
    // CONTROL: the true argv is its plan (it gets as far as the config, which is moved away)
    stop();
    let (c, e) = run(argv(&bs, &ms), true);
    assert_eq!(c, Some(11), "control: the true argv: {e}");
    assert!(e.contains("resident: confMissing"), "control: {e}");
    let (c, e) = run(argv(&ms, &bs), false);
    assert_eq!(
        (c, e.trim_end()),
        (Some(10), "resident: argvNotPlan not this resident's plan"),
        "swapped sockets"
    );
    let other = sock.join(&w.r1).join("broker.sock").display().to_string();
    let (c, e) = run(argv(&other, &ms), false);
    assert_eq!(
        (c, e.trim_end()),
        (Some(10), "resident: argvNotPlan not this resident's plan"),
        "another resident's broker socket"
    );

    eprintln!("{}", log());
    drop(gl);
    drop(kb);
    drop(member);
    drop(w);
}
