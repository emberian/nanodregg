//! THE BAR's hosted Hermes, end to end (`cargo:launcher:resident_bell`, HOSTING-27, HOSTING-31):
//! the real resident, the Lean exe `resident`, confined under grain-launch with its Lean plan,
//! answers the rings of a bell (`world/resident/Bell`, LANG-58: a queue of rings) with the reply
//! keybroker got from the FAKE provider. The founders read the answers.
//!
//! Everything is the deployed path:
//! - a real Store, with the operator's follower Store under the hosting root;
//! - keybroker on the emitted unit's argv;
//! - grain-launch on ITS unit's argv over the real `hosting-controller`;
//! - the resident's member, served by `nd --stdio` under nd-supervise on MEMBER/<dirOf>/nd.sock;
//! - a second founder, C, a member with its own `nd --stdio`, granted `ring` on the bell;
//! - the operator's Bell object, `resident` = the resident's member, with `observe,invoke:0`
//!   granted to it (the config names the grant; `invoke … --via` it).
//!
//! The resident reads `pkg/resident.conf` (one Lang value) and its plan from argv. It learns
//! `answer`'s index and `pending`'s limit from the description, and each tick reads every pending
//! ring with ONE range read. Sequencing waits on what the founders read, never on time alone.
//!
//! - Q1, the row the queue was bought for: the operator and C ring at the same moment, before the
//!   resident runs. BOTH land (the old Bell refused the second `busy`); the two keys share a
//!   notBefore, so they were signed over one view.
//! - Q2, lowest first: the resident starts with both pending and answers them in key order (its
//!   log names each answer's key); both answers read back from `answers`, `pending` is empty, the
//!   provider saw exactly one request per ring, and no answer of the resident's was refused.
//! - Q3, exactly once: a second answer to an answered ring, through the resident's own member, is
//!   refused `missingRow` (the kernel: the pending row is gone), and nothing moves.
//! - Q4, a stranger's answer: the operator answers a pending ring: `refused program`, the ring
//!   still pending; the resident then answers it.
//! - Q5, retire: the owner retires the lowest answered ring: admitted; its `answers` and `rings`
//!   rows are gone.
//! - Q6, the intent: the resident is stopped after its ask reached the provider and before any
//!   reply (the provider holds it back). Restarted, it answers that ring `(unanswered restart)` from
//!   the intent it kept BEFORE the ask, and asks no more.
//! - Refused, each by name (HOSTING-27's, re-cut to the queue): the resident exe on a bell whose
//!   resident is the operator ends `answerRefused program` after exactly one ask, restarts, answers
//!   from its kept text and asks no more; on a bell whose grant lacks `invoke:0`, `answerRefused
//!   grantRight`; an argv that is not its plan, `argvNotPlan` (CONTROL: its true argv reaches the
//!   config).
//!
//! Plants (HOSTING-31, each run by hand, red by name): answering an answered ring (decideTick
//! without the pending check, with the kept answer not forgotten on delivery) → Q2 "an answer was
//! refused"; answering out of order (the highest pending) → Q2 "lowest first"; the intent dropped
//! (no keep before the ask) → Q6 "a restart asked again"; a stranger's answer (the Bell without its
//! resident check and guard) → Q4 "a stranger's answer landed".
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
use std::sync::atomic::Ordering;

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

/// The Bell's state for a new bell whose resident is `resident`.
fn bell_state(resident: &str) -> String {
    format!("(record (open true) (resident #{resident}))")
}

/// The resident's config for bell `bell`.
fn conf(bell: &str, grant: &str) -> String {
    format!(
        "(record (bell #{bell}) (grant #{grant}) (maxTokens 50) (model \"claude-m\") (system \"\"))"
    )
}

/// The text between `pre` and the next `end` in `l`.
fn between<'a>(l: &'a str, pre: &str, end: char) -> &'a str {
    let i = l.find(pre).unwrap_or_else(|| panic!("no `{pre}` in {l}")) + pre.len();
    let rest = &l[i..];
    &rest[..rest.find(end).unwrap()]
}

/// A row of one of the Bell's relations, as `read OBJ REL K` prints it:
/// `(record (key (record (notBefore N) (ringer #H))) (val (record (text "T"))))`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Row {
    not_before: u64,
    ringer: String,
    text: String,
}

fn rows(out: &str) -> Vec<Row> {
    out.lines()
        .filter(|l| !l.is_empty())
        .map(|l| Row {
            not_before: between(l, "(notBefore ", ')').parse().unwrap(),
            ringer: between(l, "(ringer #", ')').to_owned(),
            text: between(l, "(text \"", '"').to_owned(),
        })
        .collect()
}

/// `answer`'s argument for the ring keyed by `r`.
fn answer_arg(r: &Row, text: &str) -> String {
    format!(
        "(record (notBefore {}) (ringer #{}) (text \"{text}\"))",
        r.not_before, r.ringer
    )
}

/// The keys of the resident's `answered N HEX K bytes` lines, in the order it logged them.
fn answered_keys(log: &str) -> Vec<(u64, String)> {
    log.lines()
        .filter_map(|l| l.split_once("resident: answered ").map(|x| x.1))
        .map(|l| {
            let mut w = l.split(' ');
            (
                w.next().unwrap().parse().unwrap(),
                w.next().unwrap().to_owned(),
            )
        })
        .collect()
}

#[test]
fn the_resident_answers_every_ring_lowest_first_once_and_nothing_else() {
    let d = dir("bel");
    let keys = key_file(&d, 0o600);
    let pki = Pki::new();
    let anchors = pki.anchors(&d, 0o644);
    let server = pki.server(HOST, false);
    pki.pin(&d, &[&server]);
    let (up, seen, hold) = upstream_held(Mode::Ok, &server);
    let asks = || seen.lock().unwrap().len();
    let asked_about = |ring: &str| {
        let needle = format!("\"{ring}\"");
        seen.lock()
            .unwrap()
            .iter()
            .filter(|r| contains(r, needle.as_bytes()))
            .count()
    };
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
    // C, the second founder: a member of its own, with its own `nd --stdio`
    let (cfollow, csock) = (Short::new("f"), Short::new("c"));
    let cpids = d.join("cpids");
    nanodregg_devtools::mkdirs(&cpids).unwrap();
    let founder_c = w.member(
        &d.join("c-ws"),
        &cfollow.0.join("follow.sock"),
        &w.root.join("stores/C"),
        &csock.0.join("nd.sock"),
        &cpids,
    );
    let c = founder_c.id.clone();
    // the bells: B (the resident's, granted), NG (the resident's, no grant), NR (the operator's,
    // granted)
    let bell_pkg = w.install("world/resident/Bell");
    let create = |resident: &str| {
        line(
            &w.run(&["create", "--pkg", &bell_pkg, &bell_state(resident)]),
            "id ",
        )
        .to_owned()
    };
    let (b, ng, nr) = (create(&m), create(&m), create(&op));
    let grant =
        |o: &str, to: &str, rights: &str| line(&w.run(&["grant", o, to, rights]), "id ").to_owned();
    let (gb, gnr, gng) = (
        grant(&b, &m, "observe,invoke:0"),
        grant(&nr, &m, "observe,invoke:0"),
        grant(&ng, &m, "observe"),
    );
    let gc = grant(&b, &c, "observe,invoke:4");
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
    let rel = |o: &str, r: &str| rows(&w.run(&["read", o, r, "64"]));
    let start = || {
        w.run(&["invoke", &g, "1", "(record)"]);
        w.run(&["sync"]);
    };
    let stop = || {
        w.run(&["invoke", &g, "2", "(record)"]);
        w.run(&["sync"]);
    };
    let no_child = || {
        until(
            "no child of the grain",
            60,
            || fs::read_dir(&gl_pids).unwrap().next().is_none(),
            &log,
        );
    };
    let ring_op = |o: &str, text: &str| {
        w.run(&["invoke", o, "4", &format!("(record (text \"{text}\"))")]);
    };
    let state = |o: &str| {
        format!(
            "pending {:?}\nanswers {:?}\n{}",
            rel(o, "pending"),
            rel(o, "answers"),
            log()
        )
    };

    // Q1: two founders ring at one moment, before the resident runs: both land, over one view
    w.run(&["sync"]);
    member_cmd(&founder_c.sock, &["sync"]);
    std::thread::scope(|s| {
        s.spawn(|| ring_op(&b, "from-op"));
        s.spawn(|| {
            let (exit, out, err) = member_cmd(
                &founder_c.sock,
                &[
                    "invoke",
                    &b,
                    "4",
                    "(record (text \"from-c\"))",
                    "--via",
                    &gc,
                ],
            );
            assert_eq!(exit, 0, "C's ring: {out}{err}");
        });
    });
    w.run(&["sync"]);
    let pending = rel(&b, "pending");
    assert_eq!(
        pending
            .iter()
            .map(|r| r.text.as_str())
            .collect::<std::collections::BTreeSet<_>>(),
        ["from-c", "from-op"].into_iter().collect(),
        "Q1: both rings land: {pending:?}"
    );
    assert_eq!(
        pending[0].not_before, pending[1].not_before,
        "Q1: the two rings were signed over one view: {pending:?}"
    );
    assert!(
        pending[0] < pending[1],
        "Q1: the range read lists in key order: {pending:?}"
    );
    let ringers: std::collections::BTreeSet<_> = pending.iter().map(|r| r.ringer.clone()).collect();
    assert_eq!(
        ringers,
        [op.clone(), c.clone()].into_iter().collect(),
        "Q1: the ringers"
    );
    assert_eq!(
        rel(&b, "rings"),
        pending,
        "Q1: rings holds what pending holds"
    );

    // Q2: the resident answers both, lowest first
    next_window(t1);
    start();
    until(
        "the resident learns the bell",
        90,
        || log().contains("resident: bell answer method 0 pending limit 64"),
        &log,
    );
    until(
        "both answers",
        120,
        || rel(&b, "answers").len() == 2,
        &|| state(&b),
    );
    let answers = rel(&b, "answers");
    let expect: Vec<Row> = pending
        .iter()
        .map(|r| Row {
            text: String::from_utf8_lossy(REPLY).into_owned(),
            ..r.clone()
        })
        .collect();
    assert_eq!(answers, expect, "Q2: each ring's answer, at its key");
    assert_eq!(rel(&b, "pending"), vec![], "Q2: nothing pending");
    assert_eq!(
        answered_keys(&log()),
        pending
            .iter()
            .map(|r| (r.not_before, r.ringer.clone()))
            .collect::<Vec<_>>(),
        "Q2: lowest first: the resident answered out of order:\n{}",
        log()
    );
    assert_eq!(asks(), 2, "Q2: two rings, two asks:\n{}", log());
    assert_eq!(
        (asked_about("from-op"), asked_about("from-c")),
        (1, 1),
        "Q2: exactly one request per ring"
    );
    assert!(
        !log().contains("resident: answer refused"),
        "Q2: an answer was refused: the resident answered a ring that was not pending:\n{}",
        log()
    );
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

    // Q3: a second answer to an answered ring, through the resident's own member
    let (exit, _, err) = member_cmd(
        &member.sock,
        &[
            "invoke",
            &b,
            "0",
            &answer_arg(&pending[0], "x"),
            "--via",
            &gb,
        ],
    );
    assert_eq!(
        (exit, err.trim_end()),
        (1, "refused missingRow"),
        "Q3: a second answer to one ring"
    );
    assert_eq!(rel(&b, "answers"), answers, "Q3: the answers moved");

    // Q4: a stranger (the operator) answers a pending ring
    stop();
    no_child();
    ring_op(&b, "third");
    w.run(&["sync"]);
    let third = rel(&b, "pending");
    assert_eq!(third.len(), 1, "Q4: the third ring is pending: {third:?}");
    let o = w.nd(&["invoke", &b, "0", &answer_arg(&third[0], "x")]);
    assert!(
        both(&o).contains("refused program"),
        "Q4: a stranger's answer landed: {}",
        both(&o)
    );
    assert_eq!(
        rel(&b, "pending"),
        third,
        "Q4: a stranger's answer took the ring"
    );
    assert_eq!(
        rel(&b, "answers"),
        answers,
        "Q4: a stranger's answer landed"
    );
    start();
    until(
        "the third answer",
        120,
        || rel(&b, "answers").len() == 3,
        &|| state(&b),
    );
    assert_eq!(asks(), 3, "Q4: three rings, three asks:\n{}", log());

    // Q5: the owner retires the lowest answered ring
    w.run(&[
        "invoke",
        &b,
        "3",
        &format!(
            "(record (notBefore {}) (ringer #{}))",
            pending[0].not_before, pending[0].ringer
        ),
    ]);
    w.run(&["sync"]);
    let low = |r: &Row| r.not_before == pending[0].not_before && r.ringer == pending[0].ringer;
    assert!(
        !rel(&b, "answers").iter().any(low),
        "Q5: the retired answer stays"
    );
    assert!(
        !rel(&b, "rings").iter().any(low),
        "Q5: the retired ring stays"
    );
    assert_eq!(
        rel(&b, "answers").len(),
        2,
        "Q5: retire took more than its ring"
    );

    // Q6: stopped after its ask was spent, before any reply; restarted, it answers from the intent
    stop();
    no_child();
    ring_op(&b, "held");
    let before = asks();
    hold.store(true, Ordering::SeqCst);
    start();
    until(
        "the held ask reaches the provider",
        120,
        || asks() == before + 1,
        &log,
    );
    stop();
    no_child();
    hold.store(false, Ordering::SeqCst);
    start();
    until(
        "the held ring answered",
        120,
        || rel(&b, "pending").is_empty(),
        &|| state(&b),
    );
    assert_eq!(
        (asks(), asked_about("held")),
        (before + 1, 1),
        "Q6: the intent dropped: a restart asked again:\n{}",
        log()
    );
    assert!(
        rel(&b, "answers")
            .iter()
            .any(|r| r.text == "(unanswered restart)"),
        "Q6: the held ring's answer is not the intent's: {:?}",
        rel(&b, "answers")
    );

    // the resident exe on a bell whose resident is the operator: one ask, then notResident
    let mutation = |bell: &str, via: &str, ring: &str, name: &str| {
        stop();
        no_child();
        let before = asks();
        let refusals = log().matches(&format!("answerRefused {name}")).count();
        fs::write(pkg.join("resident.conf"), conf(bell, via)).unwrap();
        ring_op(bell, ring);
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
        let p = rel(bell, "pending");
        assert!(
            p.len() == 1 && p[0].text == ring && rel(bell, "answers").is_empty(),
            "{name}: the bell took an answer: {p:?}"
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
    drop(founder_c);
    drop(w);
}
