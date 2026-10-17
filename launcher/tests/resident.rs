//! The resident row (`cargo:launcher:resident`, PROTOCOL-7's agreed need, HOSTING-17, HOSTING-21):
//! a hosted resident, confined under grain-launch with a Lean plan, reaches ONLY its own broker
//! socket and is granted through it.
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
//! - R1: the launch's connect entry is read from grain-launch's report of the plan (one line per
//!   socket, `grain-launch: <g> connect <path>`), and must be exactly BROKER/<dirOf>/broker.sock.
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
use std::io::Read;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use common::*;
use nanodregg_devtools::{Supervisor, lean_bin, repo};

/// The second resident keybroker serves (a socket that exists on the host, for no grain here).
const OTHER: &str = "b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2";
/// The Store label of the World the grain lives in.
const LABEL: &str = "w";

/// A short scratch directory (`<prefix><pid in base 36>`): a socket path is at most 107 bytes and a
/// resident's directory name is 64 hex digits, so SOCKDIR must stay within 30 bytes. Removed on drop.
struct Short(PathBuf);

impl Short {
    fn new(prefix: &str) -> Short {
        let mut n = std::process::id();
        let mut tag = String::new();
        while n > 0 {
            tag.insert(0, char::from_digit(n % 36, 36).unwrap());
            n /= 36;
        }
        let p = nanodregg_devtools::scratch(&format!("{prefix}{tag}"));
        assert!(
            p.as_os_str().len() + 1 + 64 + "/broker.sock".len() <= 107,
            "plant: {} is too long for a socket path",
            p.display()
        );
        Short(p)
    }
}

impl Drop for Short {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A scratch tree removed on drop (also when an assertion fails).
struct Gone(PathBuf);

impl Drop for Gone {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Wait (bounded: a liveness deadline, a miss renders `hang`, never a verdict) until `ok()`.
fn until(what: &str, secs: u64, mut ok: impl FnMut() -> bool, log: &dyn Fn() -> String) {
    let deadline = Instant::now() + Duration::from_secs(secs);
    while !ok() {
        assert!(
            Instant::now() < deadline,
            "hang: {what} not within {secs} s:\n{}",
            log()
        );
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// grain-launch's argv as its emitted unit renders it, each rendered word replaced by this test's
/// value (a word with no value, or a value no word asks for, is red: the unit and the launcher's
/// parser cannot drift, as broker.rs does for keybroker).
fn grain_launch_rendered(values: &[(&str, &std::ffi::OsStr)]) -> Command {
    let unit =
        fs::read_to_string(repo().join("deploy/units/linux/nd-grain-launch@.service")).unwrap();
    let line = unit
        .lines()
        .find_map(|l| l.strip_prefix("ExecStart="))
        .expect("the unit has an ExecStart");
    let mut words = line.split(' ');
    assert_eq!(
        words.next(),
        Some("/opt/nd/bin/grain-launch"),
        "the unit runs grain-launch"
    );
    let mut c = Command::new(env!("CARGO_BIN_EXE_grain-launch"));
    let mut used = std::collections::BTreeSet::new();
    for w in words {
        let (k, v) = values
            .iter()
            .find(|(k, _)| *k == w)
            .unwrap_or_else(|| panic!("the unit's word {w} has no test value"));
        c.arg(v);
        used.insert(*k);
    }
    assert_eq!(
        used.len(),
        values.len(),
        "a test value the unit never asks for"
    );
    c
}

/// A child whose stderr is collected as it arrives (grain-launch's: its launch and report lines).
struct Logged {
    /// stopped by its handle (the pid in its PID file) when dropped
    _held: Supervisor,
    err: Arc<Mutex<String>>,
}

impl Logged {
    fn spawn(mut c: Command, pid_file: PathBuf) -> Logged {
        let mut child: Child = c
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stderr = child.stderr.take().unwrap();
        let err = Arc::new(Mutex::new(String::new()));
        let e2 = Arc::clone(&err);
        std::thread::spawn(move || {
            let mut buf = [0u8; 4096];
            loop {
                match stderr.read(&mut buf) {
                    Ok(0) | Err(_) => return,
                    Ok(n) => e2
                        .lock()
                        .unwrap()
                        .push_str(&String::from_utf8_lossy(&buf[..n])),
                }
            }
        });
        Logged {
            _held: Supervisor::hold(child, pid_file),
            err,
        }
    }
    fn log(&self) -> String {
        self.err.lock().unwrap().clone()
    }
}

/// The probe's verdicts so far (`vol/probe.out`, appended as it goes).
fn verdicts(vol: &Path) -> Vec<(String, String)> {
    fs::read_to_string(vol.join("probe.out"))
        .unwrap_or_default()
        .lines()
        .filter_map(|l| {
            l.split_once(' ')
                .map(|(a, b)| (a.to_string(), b.to_string()))
        })
        .collect()
}

fn verdict(vol: &Path, name: &str) -> Option<String> {
    verdicts(vol)
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, v)| v)
}

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
    let w = World::genesis_following("res", Some(world.join("store")));
    let lifecycle = w.install("world/grain/Lifecycle");
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
    // the grain's package: the probe and its targets (the paths it tries are the host's)
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(Path::new(env!("CARGO_BIN_EXE_probe")), &pkg.join("probe"));
    let own = sock.join(&g).join("broker.sock");
    let targets = [
        ("go1", "wait", vol.join("go1")),
        ("ask1", "ask", own.clone()),
        ("key-read", "read", keys.clone()),
        (
            "other-connect",
            "connect",
            sock.join(OTHER).join("broker.sock"),
        ),
        ("sockdir-list", "list", sock.to_path_buf()),
        ("own-list", "list", sock.join(&g)),
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
    let residents = [g.as_str(), OTHER];
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
        fs::symlink_metadata(sock.join(OTHER).join("broker.sock")).is_ok(),
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
        vec![own.display().to_string()],
        "R1: the plan's connect entries are not exactly BROKER/<dirOf>/broker.sock:\n{}",
        log()
    );

    // past keybroker's start window (forfeit, HOSTING-12), the resident asks
    next_window(t1);
    fs::write(vol.join("go1"), b"").unwrap();
    until(
        "the first round",
        60,
        || verdict(&vol, "own-list").is_some(),
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

    // restart: keybroker stops (its own process) and a new life binds a new socket in the same
    // directory; the resident is never relaunched
    let pid_file = d.join("keybroker.pid");
    fs::write(&pid_file, format!("{}\n", kb.child.id())).unwrap();
    drop(kb);
    let _ = fs::remove_file(&pid_file);
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
