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

use nanodregg_devtools::lean_bin;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const A: &str = "a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1";
const B: &str = "b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2";

struct Tree {
    root: PathBuf,
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
    let w1 = root.join("worlds/w1");
    let w2 = root.join("worlds/w2");
    let g = w1.join("grains").join(A);
    let t = Tree {
        pkg: g.join("pkg"),
        vol: g.join("vol"),
        pids: root.join("pids"),
        root: root.clone(),
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
    fs::copy(env!("CARGO_BIN_EXE_probe"), t.pkg.join("probe")).unwrap();
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
    let drive = lean_bin("hosting-drive");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_grain-launch"));
    cmd.arg(&t.root).arg("w1").arg(&t.pids).arg(&drive);
    if plant {
        cmd.arg("--plant-read-worlds");
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
