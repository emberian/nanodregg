//! The connect plants (HOSTING-17 §5, CLIENT-20): what `Policy::connect` lets a confined child
//! reach, what it refuses before launch, and the platform fact that a file grant is a connect grant
//! where the mechanism does not filter connect (Linux).
#![allow(clippy::unwrap_used, clippy::expect_used)] // a plant that cannot set up is a failed plant
use std::ffi::OsStr;
use std::fs;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use nanodregg_devtools::{mkdirs, scratch};
use nanodregg_sandbox::{CONNECT_FILTERED, CONNECT_MAX, ConfineError, Policy, command};

/// Connects to each argument path (waiting up to 5 s for it to appear) and prints one line each.
const PROBE: &str = r#"
import socket, sys, os, time
for p in sys.argv[1:]:
    t = time.time()
    while not os.path.exists(p) and time.time() - t < 5:
        time.sleep(0.05)
    s = socket.socket(socket.AF_UNIX)
    try:
        s.connect(p)
        print("CONNECTED")
    except FileNotFoundError:
        print("ENOENT")
    except Exception as e:
        print("ERR", type(e).__name__)
"#;

fn python() -> (PathBuf, PathBuf) {
    let o = Command::new("python3")
        .args([
            "-I",
            "-c",
            "import os,sys;print(os.path.realpath(sys.executable));print(os.path.realpath(sys.prefix))",
        ])
        .output()
        .unwrap();
    let t = String::from_utf8(o.stdout).unwrap();
    let mut l = t.lines().map(PathBuf::from);
    (l.next().unwrap(), l.next().unwrap())
}

struct T {
    root: PathBuf,
    ws: PathBuf,
}

impl Drop for T {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn tree(name: &str) -> T {
    let root = scratch(&format!("cn-{}-{name}", std::process::id()));
    let ws = root.join("ws");
    mkdirs(&ws).unwrap();
    T { root, ws }
}

/// A listening socket at `dir/s.sock`, mode `mode`.
fn sock(dir: &Path, mode: u32) -> (UnixListener, PathBuf) {
    mkdirs(dir).unwrap();
    let p = dir.join("s.sock");
    let l = UnixListener::bind(&p).unwrap();
    fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
    (l, p)
}

fn policy(t: &T, read: Vec<PathBuf>, connect: Vec<PathBuf>) -> Policy {
    let (_, prefix) = python();
    Policy {
        read,
        exec: vec![prefix],
        hidden: vec![t.ws.clone()],
        connect,
        ..Policy::default()
    }
}

fn run(p: &Policy, targets: &[&Path]) -> Output {
    let (py, _) = python();
    let mut args: Vec<&OsStr> = vec![OsStr::new("-I"), OsStr::new("-c"), OsStr::new(PROBE)];
    args.extend(targets.iter().map(|t| t.as_os_str()));
    command(p, py.as_os_str(), &args).unwrap().output().unwrap()
}

fn lines(o: &Output) -> Vec<String> {
    String::from_utf8_lossy(&o.stdout)
        .lines()
        .map(str::to_owned)
        .collect()
}

fn refused(p: &Policy) -> ConfineError {
    let (py, _) = python();
    command(p, py.as_os_str(), &[]).expect_err("plant: the policy launched")
}

#[test]
fn the_connect_socket_is_reached_and_a_sibling_socket_is_not() {
    let t = tree("reach");
    let (_a, a) = sock(&t.root.join("a"), 0o600);
    let (_b, b) = sock(&t.root.join("b"), 0o600);
    let o = run(&policy(&t, vec![], vec![a.clone()]), &[&a, &b]);
    assert_eq!(
        lines(&o),
        ["CONNECTED", "ENOENT"],
        "{}",
        String::from_utf8_lossy(&o.stderr)
    );
}

#[test]
fn more_than_connect_max_entries_is_refused_by_name() {
    let t = tree("many");
    let socks: Vec<_> = (0..=CONNECT_MAX)
        .map(|i| sock(&t.root.join(format!("s{i}")), 0o600))
        .collect();
    let paths: Vec<PathBuf> = socks.iter().map(|(_, p)| p.clone()).collect();
    assert!(matches!(
        refused(&policy(&t, vec![], paths.clone())),
        ConfineError::ConnectTooMany(n) if n == CONNECT_MAX + 1
    ));
    // The bound itself launches.
    let _ok = command(
        &policy(&t, vec![], paths[..CONNECT_MAX].to_vec()),
        python().0.as_os_str(),
        &[OsStr::new("-c"), OsStr::new("pass")],
    )
    .unwrap();
}

#[test]
fn each_connect_entry_is_checked_before_launch() {
    let t = tree("checks");
    let (_m, wide) = sock(&t.root.join("wide"), 0o666);
    assert!(matches!(
        refused(&policy(&t, vec![], vec![wide])),
        ConfineError::ConnectMode { mode: 0o666, .. }
    ));
    let (_g, grp) = sock(&t.root.join("grp"), 0o660);
    assert!(matches!(
        refused(&policy(&t, vec![], vec![grp])),
        ConfineError::ConnectMode { mode: 0o660, .. }
    ));
    let file = t.root.join("file");
    fs::write(&file, b"x").unwrap();
    fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
    assert!(matches!(
        refused(&policy(&t, vec![], vec![file])),
        ConfineError::ConnectNotSocket(_)
    ));
    let (_l, real) = sock(&t.root.join("real"), 0o600);
    let link = t.root.join("link.sock");
    std::os::unix::fs::symlink(&real, &link).unwrap();
    assert!(matches!(
        refused(&policy(&t, vec![], vec![link])),
        ConfineError::ConnectLink(_)
    ));
    let open = t.root.join("open");
    let (_o, inner) = sock(&open.join("d"), 0o600);
    fs::set_permissions(&open, fs::Permissions::from_mode(0o770)).unwrap();
    assert!(
        matches!(refused(&policy(&t, vec![], vec![inner])), ConfineError::ConnectDir(d) if d == open)
    );
}

/// A socket of another uid, outside the egid: found on this box (hbox: root:docker
/// /run/docker.sock), none found FAILS the plant. The accepting branch (another uid, group = egid,
/// 0660) needs a second uid and is DECLARED UNRUN (one uid on hbox).
#[test]
fn a_socket_of_another_user_outside_our_group_is_refused_owner() {
    let t = tree("owner");
    let me = fs::metadata(&t.ws).unwrap();
    let theirs = ["/run", "/var/run", "/private/var/run"]
        .iter()
        .filter_map(|r| fs::read_dir(r).ok())
        .flatten()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .find(|p| {
            fs::symlink_metadata(p).is_ok_and(|m| {
                m.file_type().is_socket()
                    && m.uid() != me.uid()
                    && m.gid() != me.gid()
                    && m.permissions().mode() & 0o007 == 0
            })
        })
        .expect("plant: no socket of another user outside our group on this box");
    assert!(
        matches!(
            refused(&policy(&t, vec![], vec![theirs.clone()])),
            ConfineError::ConnectOwner { .. }
        ),
        "{}",
        theirs.display()
    );
}

#[test]
fn a_connect_directory_overlapping_a_grant_is_refused_overlap() {
    let t = tree("overlap");
    let d = t.root.join("d");
    let (_s, s) = sock(&d, 0o600);
    for read in [d.clone(), t.root.join("d")] {
        assert!(matches!(
            refused(&policy(&t, vec![read], vec![s.clone()])),
            ConfineError::ConnectOverlap { .. }
        ));
    }
    let inner = d.join("sub");
    mkdirs(&inner).unwrap();
    // A grant inside the connect directory is an overlap too (and the socket is under no grant).
    assert!(matches!(
        refused(&policy(&t, vec![inner], vec![s])),
        ConfineError::ConnectOverlap { .. }
    ));
}

#[test]
fn a_grant_holding_a_socket_at_launch_is_refused_socket_in_grant() {
    let t = tree("ingrant");
    let g = t.root.join("g");
    let (_s, s) = sock(&g.join("deep"), 0o600);
    assert!(
        matches!(refused(&policy(&t, vec![g.clone()], vec![])), ConfineError::SocketInGrant(p) if p == s)
    );
    let mut w = policy(&t, vec![], vec![]);
    w.write = vec![g];
    assert!(matches!(refused(&w), ConfineError::SocketInGrant(p) if p == s));
}

/// The platform fact: a socket bound under a READ grant after launch (which `SocketInGrant` cannot
/// see) is reachable exactly where the mechanism does not filter connect. Linux: reached (measured
/// on hbox). macOS: refused (DECLARED UNRUN since the hbox move).
#[test]
fn connect_is_filtered_exactly_where_the_platform_says() {
    let t = tree("filtered");
    let r = t.root.join("r");
    mkdirs(&r).unwrap();
    let late = r.join("late.sock");
    let (py, _) = python();
    let p = policy(&t, vec![r.clone()], vec![]);
    let child = command(
        &p,
        py.as_os_str(),
        &[
            OsStr::new("-I"),
            OsStr::new("-c"),
            OsStr::new(PROBE),
            late.as_os_str(),
        ],
    )
    .unwrap()
    .stdout(Stdio::piped())
    .spawn()
    .unwrap();
    let _l = UnixListener::bind(&late).unwrap();
    fs::set_permissions(&late, fs::Permissions::from_mode(0o600)).unwrap();
    let o = child.wait_with_output().unwrap();
    let reached = lines(&o) == ["CONNECTED"];
    assert_eq!(reached, !CONNECT_FILTERED, "{:?}", lines(&o));
}
