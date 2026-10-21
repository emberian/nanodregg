//! The grain row's physical half (`cargo:launcher:grain`, PROTOCOL-7's agreed need; it restates the
//! sandbox half of m6grain, whose Lean `grain` row names this test). An app grain, programmed by
//! the shipped lifecycle package, is started by its owner and runs under the controller's Lean
//! plan. A grantee whose grant is start-only (`invoke:1`) is refused stopping it (`grantRight`, the
//! World's verdict), and the process lives on. The owner's stop ends it, and grain-launch reports
//! its exit.
//!
//! Everything is the deployed path, as resident.rs. The real Store is the writer plus the operator's
//! follower Store at `<hosting root>/worlds/w/store`, which the controller tails. grain-launch runs
//! from its emitted unit's argv over the real `hosting-controller`. The grantee is a second member:
//! `nd --init` in its own workspace, `nd init` (its join token), the operator's `enroll` and
//! `grant world … observe`, then its own `host follow` Store, through which every command it makes
//! reads.
//!
//! - start: the owner's `invoke 1`, then `sync`. The grain is launched once, and inside it writes its
//!   volume and is denied the Store (the plan, confined).
//! - grantee stop: `invoke 2 --via <invoke:1 grant>` is refused `grantRight` by name. After the
//!   operator's `sync` (the follower holds everything the writer does), the grain's process is
//!   alive, its PID file names it, and no exit was reported.
//! - owner stop: `invoke 2`, then `sync`. grain-launch reports `exited 9` (killed by the controller's
//!   kill frame), and no PID file survives.
//!
//! Needs the built Lean exes (`hosting-controller`, `host`) and the client's `nd` / `nd-supervise`.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::path::Path;

use common::*;
use nanodregg_devtools::lean_bin;

const LABEL: &str = "w";

/// The logical end reported by the deployed reader, including its committed segment identity.
/// Physical header sizes and filenames are Host's format, never a second codec in this test.
fn seg_end(store: &Path) -> u64 {
    let out = std::process::Command::new(lean_bin("host"))
        .arg("check")
        .arg(store)
        .output()
        .unwrap();
    assert!(out.status.success(), "host check: {}", both(&out));
    text(&out)
        .split_whitespace()
        .find_map(|word| word.strip_prefix("seg_bytes="))
        .expect("host check reports seg_bytes")
        .parse()
        .unwrap()
}

#[test]
fn the_owner_stops_a_grain_and_a_start_only_grantee_cannot() {
    let hosting = Gone(nanodregg_devtools::scratch(&format!(
        "kbg{}",
        std::process::id()
    )));
    let hosting = &hosting.0;
    let world = hosting.join("worlds").join(LABEL);
    nanodregg_devtools::mkdirs(&world).unwrap();
    let w = World::genesis_following("grn", Some(world.join("store")));
    let lifecycle = w.lifecycle.clone();
    let g = line(
        &w.run(&[
            "create",
            "--pkg",
            &lifecycle,
            "(record (entry \"probe\") (kind app) (phase installed))",
        ]),
        "id ",
    )
    .to_owned();
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &pkg.join("probe"));
    let targets = [
        ("vol-write", "write", vol.join("own")),
        ("store-read", "read", world.join("store/key")),
        ("hold", "wait", vol.join("never")),
    ];
    let text_t: String = targets
        .iter()
        .map(|(n, o, p)| format!("{n} {o} {}\n", p.display()))
        .collect();
    fs::write(pkg.join("probe.targets"), text_t).unwrap();
    assert!(
        world.join("store/key").is_file(),
        "control: the Store's key exists on the host"
    );

    // the grantee, a second member with its own follower
    let (ws2, h2) = (w.root.join("ws2"), w.root.join("holding2"));
    for p in [&ws2, &h2] {
        nanodregg_devtools::mkdirs(p).unwrap();
    }
    let (op_follow, host) = (w.ws.join("follow.sock"), w.host_sock.clone());
    let o = member_nd(&ws2, &h2, &op_follow, &host, &["--init"]);
    assert!(o.status.success(), "grantee nd --init: {}", both(&o));
    let o = member_nd(&ws2, &h2, &op_follow, &host, &["init", &w.operator]);
    assert!(o.status.success(), "grantee nd init: {}", both(&o));
    let token = line(&text(&o), "join ").to_owned();
    let member = line(&w.run(&["enroll", &token]), "id ").to_owned();
    let observe = line(
        &w.run(&["grant", "world", &member, "observe", "--via", &w.grant]),
        "id ",
    )
    .to_owned();
    let follow2 = ws2.join("follow.sock");
    let _f2 = w.follower(&w.root.join("stores/G"), &follow2, &ws2, &member, &observe);
    let start_only = line(&w.run(&["grant", &g, &member, "invoke:1"]), "id ").to_owned();

    let gl_pids = w.root.join("gl-pids");
    nanodregg_devtools::mkdirs(&gl_pids).unwrap();
    let store = world.join("store");
    let controller = lean_bin("hosting-controller");
    // a broker root and a member root of its own (an app plans no socket; grain-launch requires
    // each root to exist and the three to be pairwise disjoint)
    let broker = Gone(nanodregg_devtools::scratch(&format!(
        "kbgb{}",
        std::process::id()
    )));
    let member = Gone(nanodregg_devtools::scratch(&format!(
        "kbgm{}",
        std::process::id()
    )));
    let gl = Logged::spawn(
        grain_launch_rendered(&[
            ("/srv/nd-hosted", hosting.as_os_str()),
            ("/run/nd-broker", broker.0.as_os_str()),
            ("/run/nd-member", member.0.as_os_str()),
            ("%i", LABEL.as_ref()),
            ("/run/nd-grain-launch/%i", gl_pids.as_os_str()),
            ("/opt/nd/bin/hosting-controller", controller.as_os_str()),
            ("/srv/nd-hosted/worlds/%i/store", store.as_os_str()),
        ]),
        w.root.join("grain-launch.pid"),
    );
    let log = || gl.log();
    let ctx = || format!("{:?}\n{}", verdicts(&vol), log());

    // start: the owner's invoke, the follower synced; the controller launches the plan
    w.run(&["invoke", &g, "1", "(record)"]);
    w.run(&["sync"]);
    until(
        "the launch",
        60,
        || log().contains(&format!("grain-launch: {g} started")),
        &log,
    );
    until(
        "the grain's first verdicts",
        60,
        || verdict(&vol, "store-read").is_some(),
        &ctx,
    );
    assert_eq!(
        verdict(&vol, "vol-write").as_deref(),
        Some("ok"),
        "start: the grain cannot write its volume:\n{}",
        ctx()
    );
    assert!(
        verdict(&vol, "store-read").is_some_and(|v| v.starts_with("denied")),
        "start: the grain read its Store (the plan is not in force):\n{}",
        ctx()
    );
    let pid_file = gl_pids.join(format!("{g}.pid"));
    let pid: u32 = fs::read_to_string(&pid_file)
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    let alive = || Path::new(&format!("/proc/{pid}")).exists();
    assert!(alive(), "start: the grain's process is not running");

    // grantee stop: refused by the World, so nothing reaches the box
    let o = member_nd(
        &ws2,
        &h2,
        &follow2,
        &host,
        &["invoke", &g, "2", "(record)", "--via", &start_only],
    );
    assert!(
        !o.status.success() && both(&o).contains("grantRight"),
        "grantee stop: not refused grantRight: {}",
        both(&o)
    );
    w.run(&["sync"]);
    assert_eq!(
        seg_end(&w.store),
        seg_end(&store),
        "the follower Store did not reach the writer's"
    );
    assert!(
        alive() && pid_file.is_file(),
        "grantee stop: the grain's process ended:\n{}",
        log()
    );
    assert!(
        !log().contains(&format!("grain-launch: {g} exited")),
        "grantee stop: an exit was reported:\n{}",
        log()
    );

    // owner stop: the controller kills it; grain-launch reports the exit (SIGKILL: status 9)
    w.run(&["invoke", &g, "2", "(record)"]);
    w.run(&["sync"]);
    until(
        "the stop",
        60,
        || log().contains(&format!("grain-launch: {g} exited")),
        &log,
    );
    assert!(
        log().contains(&format!("grain-launch: {g} exited 9")),
        "owner stop: the exit is not the controller's kill:\n{}",
        log()
    );
    assert!(!alive(), "owner stop: the grain's process lives on");
    assert!(
        fs::read_dir(&gl_pids).unwrap().next().is_none(),
        "a PID file outlived its child"
    );
    assert_eq!(
        log().matches(&format!("grain-launch: {g} started")).count(),
        1,
        "the grain was launched more than once:\n{}",
        log()
    );
    drop(gl);
    drop(w);
}
