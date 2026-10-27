//! The physical isolation test (HOSTING-6's tooth on a real box). A grain launched by `grain-launch`
//! from a LEAN plan (`hosting-drive`, which runs the deployed `plan` and `encodeAction`) writes its
//! own volume and is denied: writing and reading another world's volume, writing its package, and
//! reading its Store. The same probe run unconfined does all of those first, so the denials are not
//! vacuous. Plants: a plan with `worlds/` added to `read` is refused (`foreignPath`), and a symlinked
//! program pointing outside its package is refused (`programOutside`); each must show by name.
//!
//! On Linux the grain confines itself (Landlock and seccomp, CLIENT-48): what it may not open is
//! `EACCES` (its name still resolves), its package is read-only, and it executes only its program
//! and its `exec` entries. A connect grant is the socket alone, reached through the connector, never
//! a view of its directory. The verdicts below say "denied" with the errno the OS gave.
//!
//! Needs the built Lean exe `hosting-drive` (`nanodregg_devtools::lean_bin`; missing, it fails by name).
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use common::{Gone, place_exe};
use nanodregg_devtools::lean_bin;
use nanodregg_launcher::generated::{controller_exit, launch_exit};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const A: &str = "a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1";
const B: &str = "b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2";

struct Tree {
    root: PathBuf,
    /// the broker root, a sibling of `root` (HOSTING-17 §8)
    broker: PathBuf,
    /// the member root, a sibling of both (HOSTING-25)
    member: PathBuf,
    pkg: PathBuf,
    vol: PathBuf,
    pids: PathBuf,
}

/// A test owns its tree: the three roots are removed when it is dropped, also when the test
/// panics (unwinding drops it), so no judged run leaves a directory behind in the target dir
/// (GATES-6, cv 01a14ed7-79cf).
impl Drop for Tree {
    fn drop(&mut self) {
        for d in [&self.root, &self.broker, &self.member] {
            let _ = fs::remove_dir_all(d);
        }
    }
}

fn tree(name: &str) -> Tree {
    let root =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("iso-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    let root = root.canonicalize().unwrap();
    let broker =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("isob-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&broker);
    fs::create_dir_all(&broker).unwrap();
    let member =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("isom-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&member);
    fs::create_dir_all(&member).unwrap();
    let w1 = root.join("worlds/w1");
    let w2 = root.join("worlds/w2");
    let g = w1.join("grains").join(A);
    let t = Tree {
        pkg: g.join("pkg"),
        vol: g.join("vol"),
        pids: root.join("pids"),
        root: root.clone(),
        broker,
        member,
    };
    for d in [
        w1.join("store"),
        w2.join("store"),
        w2.join("grains").join(B).join("vol"),
        t.pkg.clone(),
        t.pids.clone(),
    ] {
        fs::create_dir_all(d).unwrap();
    }
    fs::write(w1.join("store/key"), b"STORE-KEY").unwrap();
    fs::write(w2.join("grains").join(B).join("vol/secret"), b"NEIGHBOUR").unwrap();
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &t.pkg.join("probe"));
    let nb = w2.join("grains").join(B).join("vol");
    let targets = [
        ("vol-write", "write", t.vol.join("own")),
        ("neighbour-write", "write", nb.join("planted")),
        ("neighbour-read", "read", nb.join("secret")),
        ("pkg-write", "write", t.pkg.join("x")),
        ("store-read", "read", w1.join("store/key")),
    ];
    let text: String = targets
        .iter()
        .map(|(n, o, p)| format!("{n} {o} {}\n", p.display()))
        .collect();
    fs::write(t.pkg.join("probe.targets"), text).unwrap();
    t
}

fn verdicts(t: &Tree) -> Vec<(String, String)> {
    let out = fs::read_to_string(t.vol.join("probe.out")).unwrap_or_default();
    out.lines()
        .filter_map(|l| {
            l.split_once(' ')
                .map(|(a, b)| (a.to_string(), b.to_string()))
        })
        .collect()
}

fn verdict(v: &[(String, String)], name: &str) -> String {
    v.iter()
        .find(|(n, _)| n == name)
        .map(|(_, r)| r.clone())
        .unwrap_or_else(|| "absent".into())
}

/// `grain-launch` over one `hosting-drive` launch; its stderr (the drive's report lines included).
fn launch(t: &Tree, plant: bool) -> String {
    launch_as(t, plant, false)
}

/// `launch`, of a resident grain when `resident`.
fn launch_as(t: &Tree, plant: bool, resident: bool) -> String {
    let drive = lean_bin("hosting-drive");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_grain-launch"));
    cmd.arg(&t.root)
        .arg(&t.broker)
        .arg(&t.member)
        .arg("w1")
        .arg(&t.pids)
        .arg(&drive);
    if plant {
        cmd.arg("--plant-read-worlds");
    }
    if resident {
        cmd.arg("--resident");
    }
    cmd.args(["w1", A, "probe"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped());
    let mut child = cmd.spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() > deadline {
            let _ = child.kill(); // our own child, by its handle
            let _ = child.wait();
            panic!("grain-launch did not end within 60 s");
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    let out = child.wait_with_output().unwrap();
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn a_grain_writes_its_volume_and_reaches_nothing_else() {
    let t = tree("confine");
    // CONTROL first: unconfined, the same probe reaches everything, the neighbour write included.
    fs::create_dir_all(&t.vol).unwrap();
    let st = Command::new(t.pkg.join("probe"))
        .env_clear()
        .status()
        .unwrap();
    assert!(st.success(), "unconfined probe failed: {st}");
    let c = verdicts(&t);
    for n in [
        "vol-write",
        "neighbour-write",
        "neighbour-read",
        "pkg-write",
        "store-read",
    ] {
        assert_eq!(
            verdict(&c, n),
            "ok",
            "control: unconfined {n} must succeed, or the denials below prove nothing"
        );
    }
    let nb = t.root.join("worlds/w2/grains").join(B).join("vol/planted");
    for p in [
        nb.clone(),
        t.pkg.join("x"),
        t.vol.join("probe.out"),
        t.vol.join("own"),
    ] {
        fs::remove_file(p).unwrap();
    }
    // CONFINED: the Lean plan, through the launcher, through the sandbox.
    let log = launch(&t, false);
    assert!(
        log.contains("report started") && log.contains("report exited 0"),
        "launch did not run the probe:\n{log}"
    );
    let v = verdicts(&t);
    assert_eq!(verdict(&v, "vol-write"), "ok", "own volume:\n{log}");
    for n in [
        "neighbour-write",
        "neighbour-read",
        "pkg-write",
        "store-read",
    ] {
        assert!(
            verdict(&v, n).starts_with("denied"),
            "{n} was {}:\n{log}",
            verdict(&v, n)
        );
    }
    assert!(!nb.exists(), "the neighbour's volume was written");
    eprintln!("confined verdicts: {v:?}");
    assert!(
        fs::read_dir(&t.pids).unwrap().next().is_none(),
        "a PID file outlived its child"
    );
}

#[test]
fn plant_a_plan_reading_worlds_is_refused_foreign_path() {
    let t = tree("plant-worlds");
    let log = launch(&t, true);
    // HOSTING-25: a read outside the grain's own directory is the frame's own defect, refused before
    // the sandbox resolves anything (the sandbox's `Exposed`, the next barrier, is its own test:
    // sandbox/tests/confine.rs)
    // one line: the refusal names the planted `worlds` path itself
    assert!(
        log.lines()
            .any(|l| l.starts_with("grain-launch: foreignPath ") && l.ends_with(" worlds")),
        "a plan reading worlds/ was not refused by name:\n{log}"
    );
    assert!(verdicts(&t).is_empty(), "the planted plan ran the probe");
}

#[test]
fn plant_a_symlinked_program_is_refused_program_outside() {
    let t = tree("plant-link");
    fs::remove_file(t.pkg.join("probe")).unwrap();
    std::os::unix::fs::symlink(env!("CARGO_BIN_EXE_probe"), t.pkg.join("probe")).unwrap();
    let log = launch(&t, false);
    assert!(
        log.contains("report failed programOutside"),
        "a program linked outside its package launched:\n{log}"
    );
    assert!(verdicts(&t).is_empty(), "the linked program ran");
}

/// HOSTING-17 §8, HOSTING-25: a socket root inside the hosting root (or around it) would put every
/// socket in it under a grain grant, and a member root inside the broker root (or around it) would
/// mix the two typed roots; grain-launch ends `rootsOverlap` before it starts the controller, for
/// every pair of its three roots.
#[test]
fn overlapping_roots_are_refused() {
    let t = tree("overlap");
    let inside = t.root.join("worlds/w1/grains").join(A).join("vol");
    fs::create_dir_all(&inside).unwrap();
    let in_broker = t.broker.join("m");
    fs::create_dir_all(&in_broker).unwrap();
    let up = t.root.parent().unwrap();
    let pairs: [(&Path, &Path); 5] = [
        (&inside, &t.member),
        (up, &t.member),
        (&t.broker, &inside),
        (&t.broker, up),
        (&t.broker, &in_broker),
    ];
    for (broker, member) in pairs {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(&t.root)
            .arg(broker)
            .arg(member)
            .arg("w1")
            .arg(&t.pids)
            .arg(lean_bin("hosting-drive"))
            .args(["w1", A, "probe"])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(
            err.contains("grain-launch: rootsOverlap"),
            "{} {}: stderr: {err}",
            broker.display(),
            member.display()
        );
        assert!(!err.contains("report"), "a launch happened: {err}");
        assert_eq!(
            out.status.code(),
            Some(i32::from(launch_exit::ROOTS_OVERLAP)),
            "rootsOverlap exit code"
        );
    }
}

/// HOSTING-19: grain-launch's exit is Lean's table, and a controller's end is passed through with
/// its own code (the real `hosting-controller`, confined): with no arguments it ends `usage`, with an
/// uppercase label `badLabel`, and grain-launch exits each one's code. A grain-launch of its own
/// with no arguments ends with its own `usage`.
#[test]
fn grain_launch_exits_by_lean_table_and_passes_the_controller_through() {
    let t = tree("exits");
    let store = t.root.join("worlds/w1/store");
    let cases: [(&[&std::ffi::OsStr], u8, &str); 2] = [
        (&[], controller_exit::USAGE, "usage"),
        (
            &[store.as_os_str(), "W1".as_ref()],
            controller_exit::BAD_LABEL,
            "badLabel",
        ),
    ];
    for (args, code, name) in cases {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(&t.root)
            .arg(&t.broker)
            .arg(&t.member)
            .arg("w1")
            .arg(&t.pids)
            .arg(lean_bin("hosting-controller"))
            .args(args)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(
            err.contains(&format!("hosting-controller: {name}")),
            "{name}: stderr: {err}"
        );
        assert!(
            err.contains(&format!("grain-launch: controllerEnded {code}")),
            "{name}: stderr: {err}"
        );
        assert_eq!(
            out.status.code(),
            Some(i32::from(code)),
            "{name}: exit code"
        );
    }
    let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(i32::from(launch_exit::USAGE)),
        "grain-launch usage"
    );
    // A controller that ends (a Store refusal's code) right after a launch: the launcher's report
    // of the child then meets a gone reader, and the run's exit is still the controller's code,
    // never a restartable reportPipe (VACUITY-READER-H4 on HOSTING-19).
    let t = tree("gone");
    fs::create_dir_all(&t.vol).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
        .arg(&t.root)
        .arg(&t.broker)
        .arg(&t.member)
        .arg("w1")
        .arg(&t.pids)
        .arg(lean_bin("hosting-drive"))
        .args(["--exit-after-launch", "w1", A, "probe"])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("hosting-drive: abandoned"),
        "gone: stderr: {err}"
    );
    assert_eq!(
        out.status.code(),
        Some(i32::from(controller_exit::STORE)),
        "gone: the controller's end was not passed through: {err}"
    );
}

/// HOSTING-17 hole 1 (VACUITY-READER-H4), HOSTING-25: identity is the socket, so a resident must
/// reach its OWN broker socket and its OWN member socket and nothing else in either root. Each root
/// holds two residents' listening sockets (BROKER/<A>/broker.sock, BROKER/<B>/broker.sock,
/// MEMBER/<A>/nd.sock, MEMBER/<B>/nd.sock; one uid here: 0600 in 0700 directories, CLIENT-20's
/// one-uid rule) and a file. Lean plans the resident (`hosting-drive --resident`): its socket entries
/// are `<A>/broker.sock`, joined onto BROKER, and `<A>/nd.sock`, joined onto MEMBER, by grain-launch.
#[test]
fn a_resident_reaches_its_own_sockets_and_nothing_else() {
    use std::os::unix::net::UnixListener;
    let mut t = tree("resident");
    // A socket path is at most 107 bytes (sun_path) and a resident's directory name is 64 hex
    // digits, so this test's broker root is a short scratch directory of its own (the pid in base
    // 36), not under the target dir; it is removed at the end.
    let mut n = std::process::id();
    let mut tag = String::new();
    while n > 0 {
        tag.insert(0, char::from_digit(n % 36, 36).unwrap());
        n /= 36;
    }
    // the tree's own socket roots go first: the tree removes whatever its fields name when dropped
    let _ = fs::remove_dir_all(&t.broker);
    let _ = fs::remove_dir_all(&t.member);
    t.broker = nanodregg_devtools::scratch(&format!("i{tag}"));
    t.member = nanodregg_devtools::scratch(&format!("j{tag}"));
    let mut held = Vec::new();
    for (root, sock) in [(&t.broker, "broker.sock"), (&t.member, "nd.sock")] {
        let _ = fs::remove_dir_all(root);
        nanodregg_devtools::mkdirs(root).unwrap();
        for g in [A, B] {
            let d = root.join(g);
            fs::create_dir_all(&d).unwrap();
            fs::set_permissions(&d, fs::Permissions::from_mode(0o700)).unwrap();
            let s = d.join(sock);
            held.push(UnixListener::bind(&s).unwrap());
            fs::set_permissions(&s, fs::Permissions::from_mode(0o600)).unwrap();
        }
        fs::write(root.join("secret"), b"ROOT-FILE").unwrap();
    }
    let own = t.broker.join(A).join("broker.sock");
    let other = t.broker.join(B).join("broker.sock");
    let own_m = t.member.join(A).join("nd.sock");
    let other_m = t.member.join(B).join("nd.sock");
    let text = format!(
        "own-connect connect {}\nother-connect connect {}\nown-list list {}\nbroker-read read {}\nbroker-list list {}\n\
         own-member connect {}\nother-member connect {}\nown-member-list list {}\nmember-read read {}\nmember-list list {}\n",
        own.display(),
        other.display(),
        t.broker.join(A).display(),
        t.broker.join("secret").display(),
        t.broker.display(),
        own_m.display(),
        other_m.display(),
        t.member.join(A).display(),
        t.member.join("secret").display(),
        t.member.display()
    );
    fs::write(t.pkg.join("probe.targets"), text).unwrap();
    // CONTROL first: unconfined, the same probe reaches both sockets and the broker root.
    fs::create_dir_all(&t.vol).unwrap();
    let st = Command::new(t.pkg.join("probe"))
        .env_clear()
        .status()
        .unwrap();
    assert!(st.success(), "control probe failed");
    let v = verdicts(&t);
    for n in [
        "own-connect",
        "other-connect",
        "broker-read",
        "own-member",
        "other-member",
        "member-read",
    ] {
        assert_eq!(
            verdict(&v, n),
            "ok",
            "control {n}: the denial below would be vacuous"
        );
    }
    fs::remove_file(t.vol.join("probe.out")).unwrap();
    // CONFINED, through grain-launch + the Lean plan + the self-confinement step
    let err = launch_as(&t, false, true);
    assert!(err.contains("report started"), "not launched: {err}");
    let v = verdicts(&t);
    assert_eq!(verdict(&v, "own-connect"), "ok", "own socket: {err}");
    // a connect grant is the socket, not its directory (CLIENT-48): the directory is not listed
    assert!(
        verdict(&v, "own-list").starts_with("denied"),
        "own directory: {}",
        verdict(&v, "own-list")
    );
    assert!(
        verdict(&v, "other-connect").starts_with("denied"),
        "another resident's socket: {}",
        verdict(&v, "other-connect")
    );
    assert!(
        verdict(&v, "broker-read").starts_with("denied"),
        "a file in the broker root: {}",
        verdict(&v, "broker-read")
    );
    let bl = verdict(&v, "broker-list");
    assert!(bl.starts_with("denied"), "the broker root is listed: {bl}");
    // the member root, the same way (HOSTING-25)
    assert_eq!(verdict(&v, "own-member"), "ok", "own member socket: {err}");
    assert!(
        verdict(&v, "own-member-list").starts_with("denied"),
        "own member directory: {}",
        verdict(&v, "own-member-list")
    );
    for n in ["other-member", "member-read"] {
        assert!(
            verdict(&v, n).starts_with("denied"),
            "{n} inside: {}",
            verdict(&v, n)
        );
    }
    let ml = verdict(&v, "member-list");
    assert!(ml.starts_with("denied"), "the member root is listed: {ml}");
    // R1's isolation half: the launch named exactly the two own sockets, each under its own root
    let connects: Vec<&str> = err
        .lines()
        .filter_map(|l| l.strip_prefix(&format!("grain-launch: {A} connect ")))
        .collect();
    assert_eq!(
        connects,
        vec![own.display().to_string(), own_m.display().to_string()],
        "the plan's sockets: {err}"
    );
    eprintln!(
        "resident: other-connect {}, broker-read {}, broker-list {}",
        verdict(&v, "other-connect"),
        verdict(&v, "broker-read"),
        verdict(&v, "broker-list")
    );
    drop(held);
}

/// HOSTING-25: a launch frame naming another grain's socket, under either socket root, ends
/// grain-launch `foreignPath` (fatal) before anything is resolved or launched. Lean's plans never
/// do (`plan_sockets_named`), so the frames come from `hosting-drive --plant-foreign`. CONTROL: the
/// same drive without the plant launches (`report started`), so the refusal is the frame's.
#[test]
fn a_launch_naming_another_grains_socket_is_refused_foreign_path() {
    let t = tree("foreign");
    let run = |plant: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(&t.root)
            .arg(&t.broker)
            .arg(&t.member)
            .arg("w1")
            .arg(&t.pids)
            .arg(lean_bin("hosting-drive"))
            .args(plant)
            .args(["w1", A, "probe"])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            String::from_utf8_lossy(&out.stderr).into_owned(),
            out.status.code(),
        )
    };
    for root in ["broker", "member"] {
        let (err, code) = run(&["--resident", "--plant-foreign", root, B]);
        // a whole line: grain-launch writes each line in one write, so the drive's own end
        // (`hosting-drive: launcherGone`) can never land inside it
        let refused = format!("grain-launch: foreignPath {A} {B}/");
        assert!(
            err.lines().any(|l| l.starts_with(&refused)),
            "{root}: stderr: {err}"
        );
        assert!(!err.contains("report started"), "{root}: launched: {err}");
        assert_eq!(
            code,
            Some(i32::from(launch_exit::FOREIGN_PATH)),
            "{root}: exit code"
        );
    }
    // CONTROL: an app (no socket entries) under the same drive launches
    fs::create_dir_all(&t.vol).unwrap();
    let (err, _) = run(&[]);
    assert!(err.contains("report started"), "control: {err}");
}

/// The ETXTBSY race (`place_exe`): while another thread spawns children as fast as it can (as
/// parallel tests do), place and run a fresh copy of the probe `ROUNDS` times. Not one exec may
/// be refused `ETXTBSY` (os error 26). The race is not deterministic. Planted with `fs::copy` in
/// `place_exe`, this test was red in each of three runs on hbox (23, 30 and 41
/// of 300 execs ETXTBSY).
#[test]
fn a_placed_executable_is_never_busy_under_concurrent_spawns() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    const ROUNDS: usize = 300;
    let d = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("iso-{}-busy", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    let _gone = Gone(d.clone());
    let stop = Arc::new(AtomicBool::new(false));
    let s2 = Arc::clone(&stop);
    let spawner = std::thread::spawn(move || {
        let mut n = 0u64;
        while !s2.load(Ordering::Relaxed) {
            if let Ok(mut c) = Command::new("true").stdin(Stdio::null()).spawn() {
                let _ = c.wait();
                n += 1;
            }
        }
        n
    });
    let mut busy = 0;
    for i in 0..ROUNDS {
        let p = d.join(format!("probe{i}"));
        place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &p);
        // the probe finds no targets beside it and ends 2: only the exec matters here
        match Command::new(&p).env_clear().stdin(Stdio::null()).status() {
            Ok(_) => {}
            Err(e) if e.raw_os_error() == Some(26) => busy += 1,
            Err(e) => panic!("exec {}: {e}", p.display()),
        }
    }
    stop.store(true, Ordering::Relaxed);
    let spawned = spawner.join().unwrap();
    let _ = fs::remove_dir_all(&d);
    assert!(spawned > 0, "control: the spawner thread spawned nothing");
    assert_eq!(
        busy, 0,
        "{busy} of {ROUNDS} execs were ETXTBSY ({spawned} concurrent spawns)"
    );
}

/// HOSTING-24: a directory Lean's plans hide (`LAYOUT_HIDDEN` under `worlds/<label>`) that is absent
/// would refuse every launch `pathMissing` and crash-loop each grain; grain-launch ends
/// `layoutMissing` (fatal), naming the directory, before it starts the controller. HOSTING-23: a
/// controller process that ends below 128 with a code Lean's `ControllerExit` does not name (here
/// `/usr/bin/false`, exit 1, under the real confinement) ends grain-launch `controllerMechanism`
/// (fatal), never a pass-through of an unnamed code.
#[test]
fn a_missing_layout_or_a_controller_that_never_ran_stops_grain_launch_by_name() {
    use nanodregg_launcher::generated::{LAYOUT_HIDDEN, controller_exit};
    let run = |t: &Tree, controller: &Path| {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(&t.root)
            .arg(&t.broker)
            .arg(&t.member)
            .arg("w1")
            .arg(&t.pids)
            .arg(controller)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        (
            String::from_utf8_lossy(&out.stderr).into_owned(),
            out.status.code(),
        )
    };
    // the member workspaces and follower Stores are outside the hosted tree (HOSTING-32), so the
    // layout a World needs under it is its Store alone
    assert_eq!(
        LAYOUT_HIDDEN,
        &["store"],
        "control: the layout grain-launch requires: {LAYOUT_HIDDEN:?}"
    );
    for name in LAYOUT_HIDDEN {
        let t = tree(&format!("layout-{name}"));
        let gone = t.root.join("worlds/w1").join(name);
        fs::remove_dir_all(&gone).unwrap();
        let (err, code) = run(&t, &lean_bin("hosting-controller"));
        assert!(
            err.contains(&format!("grain-launch: layoutMissing {}", gone.display())),
            "{name}: stderr: {err}"
        );
        assert!(
            !err.contains("hosting-controller"),
            "{name}: the controller started: {err}"
        );
        assert_eq!(
            code,
            Some(i32::from(launch_exit::LAYOUT_MISSING)),
            "{name}: exit code"
        );
    }
    // a controller KILLED by a signal is controllerSignaled, restartable
    let t = tree("killed");
    // the probe placed as `killself` SIGKILLs itself (no interpreter: a `#!` script would need its
    // shell granted exec, which the sandbox no longer infers)
    let killer = t.root.join("killself");
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &killer);
    let (err, code) = run(&t, &killer);
    assert!(
        err.contains("grain-launch: controllerSignaled"),
        "killed: stderr: {err}"
    );
    assert_eq!(
        code,
        Some(i32::from(launch_exit::CONTROLLER_SIGNALED)),
        "killed: exit code"
    );
    let t = tree("mechanism");
    assert!(
        !controller_exit::ALL.contains(&1),
        "control: 1 is not a ControllerExit code"
    );
    let (err, code) = run(&t, Path::new("/usr/bin/false"));
    assert!(
        err.contains("grain-launch: controllerMechanism 1"),
        "stderr: {err}"
    );
    assert_eq!(
        code,
        Some(i32::from(launch_exit::CONTROLLER_MECHANISM)),
        "exit code"
    );
}

/// GATES-6 (cv 01a14ed7-79cf): a test that panics still removes its tree, because unwinding drops
/// it. CONTROL: the three roots existed while the test ran.
#[test]
fn a_panicking_test_still_removes_its_tree() {
    let seen = std::sync::Mutex::new(Vec::new());
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let t = tree("panics");
        for d in [&t.root, &t.broker, &t.member] {
            seen.lock().unwrap().push((d.clone(), d.is_dir()));
        }
        panic!("planted: the test fails while it holds its tree");
    }));
    assert!(r.is_err(), "control: the planted test did not panic");
    let seen = seen.into_inner().unwrap();
    assert_eq!(seen.len(), 3);
    for (d, was) in seen {
        assert!(
            was,
            "control: {} did not exist while the test ran",
            d.display()
        );
        assert!(!d.exists(), "{} outlived its panicking test", d.display());
    }
}
