//! The physical isolation test (HOSTING-6's tooth on a real box). A grain launched by `grain-launch`
//! from a LEAN plan (`hosting-drive`, which runs the deployed `plan` and `encodeAction`) writes its
//! own volume and is denied: writing and reading another world's volume, writing its package, and
//! reading its Store. The same probe run unconfined does all of those first, so the denials are not
//! vacuous. Plants: a plan with `worlds/` added to `read` is refused (`exposed`), and a symlinked
//! program pointing outside its package is refused (`programOutside`); each must show by name.
//!
//! On Linux bwrap mounts and does not filter exec: what the grain cannot see is absent (`ENOENT`),
//! its package is read-only (`EROFS`), and everything under the read-only /usr floor is visible and
//! executable inside (`nanodregg_sandbox::EXEC_FILTERED` = false). The verdicts below say "denied"
//! with the errno the OS gave, never a bare EPERM it did not give.
//!
//! Needs the built Lean exe `hosting-drive` (`nanodregg_devtools::lean_bin`; missing, it fails by name).
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use common::place_exe;
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
    pkg: PathBuf,
    vol: PathBuf,
    pids: PathBuf,
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
    let w1 = root.join("worlds/w1");
    let w2 = root.join("worlds/w2");
    let g = w1.join("grains").join(A);
    let t = Tree {
        pkg: g.join("pkg"),
        vol: g.join("vol"),
        pids: root.join("pids"),
        root: root.clone(),
        broker,
    };
    for d in [
        w1.join("store"),
        w1.join("members"),
        w2.join("store"),
        w2.join("grains").join(B).join("vol"),
        t.pkg.clone(),
        t.pids.clone(),
    ] {
        fs::create_dir_all(d).unwrap();
    }
    fs::write(w1.join("store/key"), b"STORE-KEY").unwrap();
    fs::write(w1.join("members/seed"), b"SEED").unwrap();
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
fn plant_a_plan_reading_worlds_is_refused_exposed() {
    let t = tree("plant-worlds");
    let log = launch(&t, true);
    assert!(
        log.contains("report failed exposed"),
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

/// HOSTING-17 §8: a broker root inside the hosting root (or around it) would put every socket in it
/// under a grain grant; grain-launch ends `rootsOverlap` before it starts the controller.
#[test]
fn a_broker_root_overlapping_the_hosting_root_is_refused() {
    let t = tree("overlap");
    let inside = t.root.join("worlds/w1/grains").join(A).join("vol");
    fs::create_dir_all(&inside).unwrap();
    for broker in [inside.as_path(), t.root.parent().unwrap()] {
        let out = Command::new(env!("CARGO_BIN_EXE_grain-launch"))
            .arg(&t.root)
            .arg(broker)
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
            "{}: stderr: {err}",
            broker.display()
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

/// HOSTING-17 hole 1 (VACUITY-READER-H4): identity is the socket, so a resident must reach its OWN
/// broker socket and nothing else in the broker root. The broker root holds two residents' listening
/// sockets (BROKER/<A>/broker.sock, BROKER/<B>/broker.sock, one uid here: 0600 in 0700 directories,
/// CLIENT-20's one-uid rule) and a file. Lean plans the resident (`hosting-drive --resident`): its
/// connect entry is `<A>/broker.sock`, joined onto BROKER by grain-launch.
#[test]
fn a_resident_reaches_its_own_broker_socket_and_nothing_else() {
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
    t.broker = nanodregg_devtools::scratch(&format!("i{tag}"));
    let _ = fs::remove_dir_all(&t.broker);
    nanodregg_devtools::mkdirs(&t.broker).unwrap();
    let mut held = Vec::new();
    for g in [A, B] {
        let d = t.broker.join(g);
        fs::create_dir_all(&d).unwrap();
        fs::set_permissions(&d, fs::Permissions::from_mode(0o700)).unwrap();
        let s = d.join("broker.sock");
        held.push(UnixListener::bind(&s).unwrap());
        fs::set_permissions(&s, fs::Permissions::from_mode(0o600)).unwrap();
    }
    fs::write(t.broker.join("secret"), b"BROKER-ROOT").unwrap();
    let own = t.broker.join(A).join("broker.sock");
    let other = t.broker.join(B).join("broker.sock");
    let text = format!(
        "own-connect connect {}\nother-connect connect {}\nown-list list {}\nbroker-read read {}\nbroker-list list {}\n",
        own.display(),
        other.display(),
        t.broker.join(A).display(),
        t.broker.join("secret").display(),
        t.broker.display()
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
    for n in ["own-connect", "other-connect", "broker-read"] {
        assert_eq!(
            verdict(&v, n),
            "ok",
            "control {n}: the denial below would be vacuous"
        );
    }
    fs::remove_file(t.vol.join("probe.out")).unwrap();
    // CONFINED, through grain-launch + the Lean plan + nd-bwrap
    let err = launch_as(&t, false, true);
    assert!(err.contains("report started"), "not launched: {err}");
    let v = verdicts(&t);
    assert_eq!(verdict(&v, "own-connect"), "ok", "own socket: {err}");
    assert_eq!(verdict(&v, "own-list"), "ok broker.sock", "own directory");
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
    // bwrap makes the bound directory's parents as empty mount scaffolding, so the broker root may
    // list inside, but only as the resident's own directory: never another resident's, never its file
    let bl = verdict(&v, "broker-list");
    assert!(
        bl.starts_with("denied") || bl == format!("ok {A}"),
        "the broker root shows more than this resident's own directory: {bl}"
    );
    eprintln!(
        "resident: other-connect {}, broker-read {}, broker-list {}",
        verdict(&v, "other-connect"),
        verdict(&v, "broker-read"),
        verdict(&v, "broker-list")
    );
    drop(held);
    let _ = fs::remove_dir_all(&t.broker);
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
