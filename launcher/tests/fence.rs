//! The two-uid custody fence run as the deployed uids (HOSTING-17, HOSTING-40): the row
//! `cargo-untraced:launcher:fence` (run without strace: a traced process cannot gain sudo's setuid).
//!
//! Every other launcher row runs as ONE uid (keybroker binds 0600 when PEER is its own uid), so
//! keybroker's peer check and `Policy.connect`'s group branch had never met a second uid. Here
//! the operator's side is uid `nd` and the hosted side is uid `nd-hosted`, the deployed users
//! (deploy/units/linux/sysusers/nd.conf). The World (`host serve` and `host follow` under
//! nd-supervise, the operator's `nd`) and keybroker run as `nd` in a run tree under
//! `ND_TREE`. SOCKDIR is a directory of the deployed `/run/nd-broker` (tmpfiles nd-broker.conf:
//! 02710 nd:nd-hosted). Each connector is this test binary re-run as a uid
//! (`fence_helper`, ignored, its operation passed by `env`).
//!
//! - `keybroker_serves_the_hosted_uid_alone`: the hosted uid is decided (`noAllowance`, a
//!   decision); the owner `nd` (gid nd), a third uid holding the group (this uid, gid nd-hosted)
//!   and the hosted uid with another gid are each answered `peerRefused`; this uid without the
//!   group cannot reach the socket at all (EACCES at SOCKDIR's 02710).
//! - `the_hosted_uid_alone_resolves_the_group_socket`: `Policy.connect` as the hosted uid accepts
//!   the 0660 nd:nd-hosted socket, and the child it confines (under nd-bwrap, as the hosted uid)
//!   reaches keybroker and is decided; as the hosted uid with gid nd it is `ConnectOwner`; as the
//!   owner `nd` it is `ConnectMode` (an own socket must be 0600); as this uid it is
//!   `PathMissing` (EACCES: the directory refuses before the policy reads the socket).
//! - `a_home_grant_is_refused_and_home_is_absent_for_both_uids`: the units' `--hide /home`, below.
//!
//! Plants (run by hand, hbox logs/hosting15-plants.out, logs/hosting16-plants.out), each RED:
//! keybroker's peer check made `true` (the first test); `Policy.connect`'s other-gid refusal made a
//! 0660 accept (the second); `make_dir` back to mkdir-then-chmod, and keybroker under UMask 0077
//! (both: `sockDir … Mode(456)`, `Mode(1472)`); the sandbox's `Exposed` check disabled, and its grant
//! scan made to skip an unlistable directory (the third).
//!
//! When the fence is absent (no `nd`/`nd-hosted` uid, no `sudo -n` to them, no run roots, no
//! SOCKDIR at its deployed shape, nd-bwrap not executable by both uids) each test prints
//! `skipped: no nd-hosted uid (<test>: <what is absent>; restore: <the operator's command>)` on
//! stderr, uncaptured, and returns: the gates row reads such a run INCOMPLETE in a landing and RED in
//! the standing run (ROOT, 10-21), never ok. sudo is used only to run a process as
//! `nd`, `nd-hosted` or this uid with group `nd-hosted`; each such process runs under `timeout
//! --kill-after` and is stopped by SIGTERM to its own sudo (whose real uid is this one), never by
//! sudo kill. Each run tree is removed by the helper running as the uid that made it, which
//! refuses a path outside its root, a symlink, or a name the test did not make (ROOT, 10-21).
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use common::*;
use nanodregg_devtools::{lean_bin, nd, nd_supervise, repo};
use nanodregg_launcher::broker_generated::wire::Answer;
use nanodregg_launcher::broker_generated::{read_frame, write_frame};

/// The deployed users.
const ND: &str = "nd";
const HOSTED: &str = "nd-hosted";
/// nd's run roots on hbox (0700 nd), made by the operator (HOSTING-40); runs go in `<root>/<run>`.
const ND_TREE: &str = "/tank/hosting15-nd";
/// The deployed SOCKDIR (tmpfiles nd-broker.conf); each run serves a directory `t<pid><tag>` of it.
const BROKER: &str = "/run/nd-broker";
const MECHANISM: &str = "/usr/local/libexec/nd-bwrap";
/// The longest any process run as another uid lives.
const LIFE_S: &str = "600";

/// One user's (uid, primary gid) from /etc/passwd.
fn user(name: &str) -> Option<(u32, u32)> {
    let pw = fs::read_to_string("/etc/passwd").ok()?;
    pw.lines().find_map(|l| {
        let f: Vec<&str> = l.split(':').collect();
        if f.len() > 3 && f[0] == name {
            Some((f[2].parse().ok()?, f[3].parse().ok()?))
        } else {
            None
        }
    })
}

fn sudo_ok(u: &str, args: &[&str]) -> bool {
    Command::new("sudo")
        .args(["-n", "-u", u, "--"])
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

/// The fence as deployed, or `None` after printing what is absent (uncaptured, by name).
struct Fence {
    nd: (u32, u32),
    hosted: (u32, u32),
}

fn fence(test: &str) -> Option<Fence> {
    let absent = || -> Option<String> {
        let units = repo().join("deploy/units/linux");
        let (Some(n), Some(h)) = (user(ND), user(HOSTED)) else {
            let conf = units.join("sysusers/nd.conf");
            return Some(format!(
                "no nd or nd-hosted in /etc/passwd; restore: sudo systemd-sysusers {}",
                conf.display()
            ));
        };
        for u in [ND, HOSTED] {
            if !sudo_ok(u, &["/usr/bin/test", "-x", MECHANISM]) {
                return Some(format!(
                    "sudo -n -u {u}, or {MECHANISM} not executable by it; restore: sudo setfacl -m \
                     u:{ND}:rx,u:{HOSTED}:rx {MECHANISM}"
                ));
            }
        }
        let t = fs::symlink_metadata(ND_TREE).ok();
        if !t.is_some_and(|m| m.is_dir() && m.uid() == n.0 && m.mode() & 0o7777 == 0o700) {
            return Some(format!(
                "{ND_TREE} is not nd's 0700 directory; restore: sudo install -d -o {ND} -g {ND} \
                 -m 0700 {ND_TREE}"
            ));
        }
        let b = fs::symlink_metadata(BROKER).ok();
        if !b.is_some_and(|m| {
            m.is_dir() && m.uid() == n.0 && m.gid() == h.1 && m.mode() & 0o7777 == 0o2710
        }) {
            // the four run directories of the deployed units (a reboot clears /run)
            let confs: Vec<String> = ["nd-broker", "nd-follow", "nd-member", "nd-member-follow"]
                .iter()
                .map(|c| {
                    units
                        .join(format!("tmpfiles/{c}.conf"))
                        .display()
                        .to_string()
                })
                .collect();
            return Some(format!(
                "{BROKER} is not 02710 nd:nd-hosted; restore: sudo systemd-tmpfiles --create {}",
                confs.join(" ")
            ));
        }
        None
    };
    match absent() {
        None => Some(Fence {
            nd: user(ND).unwrap(),
            hosted: user(HOSTED).unwrap(),
        }),
        Some(why) => {
            let _ = std::io::stderr()
                .write_all(format!("skipped: no nd-hosted uid ({test}: {why})\n").as_bytes());
            None
        }
    }
}

/// `prog args` as `u` (optionally with primary group `g`), its environment `envs` passed through
/// `env` (sudo resets the caller's), bounded by `timeout --kill-after`.
fn as_user(
    u: &str,
    g: Option<&str>,
    envs: &[(&str, &OsStr)],
    prog: &OsStr,
    args: &[&OsStr],
) -> Command {
    let mut c = Command::new("sudo");
    c.args(["-n", "-u", u]);
    if let Some(g) = g {
        c.args(["-g", g]);
    }
    c.args([
        "--",
        "/usr/bin/timeout",
        "--kill-after=5",
        LIFE_S,
        "/usr/bin/env",
    ]);
    for (k, v) in envs {
        let mut kv = OsString::from(*k);
        kv.push("=");
        kv.push(v);
        c.arg(kv);
    }
    c.arg(prog).args(args);
    c
}

/// A process run as another uid: stopped by SIGTERM to its own sudo (sudo relays it), waited for.
struct AsChild(Child);

impl Drop for AsChild {
    fn drop(&mut self) {
        if let Some(pid) = rustix::process::Pid::from_raw(self.0.id() as i32) {
            let _ = rustix::process::kill_process(pid, rustix::process::Signal::TERM);
        }
        let deadline = Instant::now() + Duration::from_secs(15);
        while Instant::now() < deadline {
            if let Ok(Some(_)) = self.0.try_wait() {
                return;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        // past the deadline: sudo goes; `timeout --kill-after` still bounds its child
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// This test binary re-run as `u` (group `g`) for one helper operation; its `fence: ` lines.
fn helper(u: &str, g: Option<&str>, op: &str, args: &[&OsStr]) -> Vec<String> {
    let me = std::env::current_exe().unwrap();
    let mut envs: Vec<(String, OsString)> = vec![("FENCE_OP".into(), op.into())];
    for (i, a) in args.iter().enumerate() {
        envs.push((format!("FENCE_ARG{i}"), a.to_os_string()));
    }
    let envs: Vec<(&str, &OsStr)> = envs
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_os_str()))
        .collect();
    let rest: Vec<&OsStr> = [
        "--ignored",
        "--exact",
        "fence_helper",
        "--nocapture",
        "--test-threads",
        "1",
    ]
    .iter()
    .map(OsStr::new)
    .collect();
    let o = as_user(u, g, &envs, me.as_os_str(), &rest)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&o.stdout).into_owned();
    let lines: Vec<String> = out
        .lines()
        .filter_map(after_tag)
        .map(str::to_owned)
        .collect();
    assert!(
        o.status.success() && !lines.is_empty(),
        "plant: helper {op} as {u}/{g:?}: {}\n{out}{}",
        o.status,
        String::from_utf8_lossy(&o.stderr)
    );
    lines
}

fn one(u: &str, g: Option<&str>, op: &str, args: &[&OsStr]) -> String {
    let l = helper(u, g, op, args);
    assert_eq!(l.len(), 1, "plant: helper {op}: {l:?}");
    l[0].clone()
}

/// The helper's line: what follows `fence: ` (libtest prints `test fence_helper ... ` before it).
fn after_tag(l: &str) -> Option<&str> {
    l.find("fence: ").map(|i| &l[i + "fence: ".len()..])
}

/// The name of a confine refusal (`ConnectOwner { … }` → `ConnectOwner`).
fn name_of(e: &impl std::fmt::Debug) -> String {
    let d = format!("{e:?}");
    d.split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("")
        .to_owned()
}

/// One broker answer, rendered `decided <Answer>` / `refused <name>`, or the IO error's kind.
fn ask_once(sock: &Path) -> String {
    let mut s = match UnixStream::connect(sock) {
        Ok(s) => s,
        Err(e) => return format!("connect {:?}", e.kind()),
    };
    s.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    let _ = write_frame(&mut s, &ask(b"claude-m", 10, b"hello"));
    match read_frame(&mut s).map(|f| Answer::decode(&f)) {
        Ok(Ok(Answer::Refused { broker_refusal })) => format!("refused {broker_refusal:?}"),
        Ok(Ok(a)) => format!("decided {a:?}"),
        other => format!("unreadable {other:?}"),
    }
}

/// The helper, run only as another uid by `helper` (FENCE_OP and FENCE_ARGn from `env`).
#[test]
#[ignore = "run by the fence tests as another uid"]
fn fence_helper() {
    let op = std::env::var("FENCE_OP").expect("plant: no FENCE_OP");
    let arg = |i: usize| PathBuf::from(std::env::var_os(format!("FENCE_ARG{i}")).unwrap());
    let say = |s: String| println!("fence: {s}");
    match op.as_str() {
        // a directory of `mode`. A setgid mode is never set by chmod: a chmod by a uid outside the
        // directory's group clears S_ISGID (Linux), so it must come from a setgid parent at mkdir
        "mkdir" => {
            let mode = u32::from_str_radix(&arg(1).to_string_lossy(), 8).unwrap();
            fs::DirBuilder::new()
                .mode(mode & 0o777)
                .create(arg(0))
                .unwrap();
            if mode & 0o2000 == 0 {
                fs::set_permissions(arg(0), fs::Permissions::from_mode(mode)).unwrap();
            }
            let got = fs::metadata(arg(0)).unwrap().mode() & 0o7777;
            assert_eq!(got, mode, "plant: mkdir {} is {got:o}", arg(0).display());
            say("made".into());
        }
        // FENCE_ARG1's bytes (hex) written to a new file of mode FENCE_ARG2
        "write" => {
            let hex = arg(1).to_string_lossy().into_owned();
            let bytes: Vec<u8> = (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                .collect();
            fs::write(arg(0), bytes).unwrap();
            let mode = u32::from_str_radix(&arg(2).to_string_lossy(), 8).unwrap();
            fs::set_permissions(arg(0), fs::Permissions::from_mode(mode)).unwrap();
            say("written".into());
        }
        // until a connect to the socket succeeds (bounded)
        "bound" => {
            let deadline = Instant::now() + Duration::from_secs(30);
            while UnixStream::connect(arg(0)).is_err() {
                assert!(
                    Instant::now() < deadline,
                    "hang: {} never bound",
                    arg(0).display()
                );
                std::thread::sleep(Duration::from_millis(50));
            }
            say("bound".into());
        }
        // until the path is a socket of mode FENCE_ARG1 (bounded), without connecting
        "sock" => {
            let mode = u32::from_str_radix(&arg(1).to_string_lossy(), 8).unwrap();
            let deadline = Instant::now() + Duration::from_secs(30);
            while !fs::symlink_metadata(arg(0)).is_ok_and(|m| m.mode() & 0o7777 == mode) {
                assert!(
                    Instant::now() < deadline,
                    "hang: no socket {}",
                    arg(0).display()
                );
                std::thread::sleep(Duration::from_millis(50));
            }
            say("sock".into());
        }
        "ask" => say(ask_once(&arg(0))),
        // Policy.connect for the socket; resolved, the confined child (this binary, `ask`) runs
        "resolve" => {
            let me = arg(1);
            let policy = nanodregg_sandbox::Policy {
                exec: vec![me.clone(), PathBuf::from("/usr/bin/env")],
                connect: vec![arg(0)],
                ..nanodregg_sandbox::Policy::default()
            };
            let env = Path::new("/usr/bin/env");
            let op = "FENCE_OP=ask";
            let a0 = {
                let mut s = OsString::from("FENCE_ARG0=");
                s.push(arg(0));
                s
            };
            let words: Vec<&OsStr> = [
                OsStr::new(&op),
                a0.as_os_str(),
                me.as_os_str(),
                OsStr::new("--ignored"),
                OsStr::new("--exact"),
                OsStr::new("fence_helper"),
                OsStr::new("--nocapture"),
                OsStr::new("--test-threads"),
                OsStr::new("1"),
            ]
            .to_vec();
            match nanodregg_sandbox::command(&policy, env.as_os_str(), &words) {
                Err(e) => say(format!("refused {}", name_of(&e))),
                Ok(mut c) => {
                    let o = c.stdin(Stdio::null()).output().unwrap();
                    let out = String::from_utf8_lossy(&o.stdout);
                    let inner: Vec<&str> = out.lines().filter_map(after_tag).collect();
                    say(format!("resolved; confined {}", inner.join(" / ")));
                }
            }
        }
        // remove ROOT/RUN, made by this uid, holding only the MANIFEST's names (ROOT, 10-21)
        "remove" => {
            let (root, run) = (arg(0), arg(1));
            let manifest: Vec<String> = arg(2)
                .to_string_lossy()
                .split(',')
                .filter(|s| !s.is_empty())
                .map(str::to_owned)
                .collect();
            let euid = rustix::process::geteuid().as_raw();
            let p = root.join(&run);
            let ok_root = [ND_TREE, BROKER].iter().any(|r| Path::new(r) == root);
            let one_name = run.components().count() == 1 && !run.as_os_str().is_empty();
            let m = fs::symlink_metadata(&p);
            let refuse = |why: &str| say(format!("refused {why} {}", p.display()));
            if !ok_root || !one_name {
                return refuse("outside its root");
            }
            let Ok(m) = m else { return refuse("absent") };
            if m.file_type().is_symlink() || !m.is_dir() || m.uid() != euid {
                return refuse("not this uid's directory");
            }
            for e in fs::read_dir(&p).unwrap() {
                let n = e.unwrap().file_name().to_string_lossy().into_owned();
                if !manifest.contains(&n) {
                    return refuse(&format!("holds {n}, not the test's"));
                }
            }
            fs::remove_dir_all(&p).unwrap();
            say(format!("removed {}", p.display()));
        }
        other => panic!("plant: no helper {other}"),
    }
}

/// A run directory as `u` under `root`; removed on drop by the helper as `u`.
struct Run {
    u: &'static str,
    root: &'static str,
    name: String,
    manifest: Vec<String>,
}

impl Run {
    fn new(u: &'static str, root: &'static str, name: String, mode: &str) -> Run {
        let p = Path::new(root).join(&name);
        one(u, None, "mkdir", &[p.as_os_str(), OsStr::new(mode)]);
        Run {
            u,
            root,
            name,
            manifest: Vec::new(),
        }
    }
    fn path(&self) -> PathBuf {
        Path::new(self.root).join(&self.name)
    }
    /// A directory `name` in it, of `mode`.
    fn dir(&mut self, name: &str, mode: &str) -> PathBuf {
        let p = self.path().join(name);
        one(self.u, None, "mkdir", &[p.as_os_str(), OsStr::new(mode)]);
        self.manifest.push(name.to_owned());
        p
    }
    fn file(&mut self, name: &str, bytes: &[u8], mode: &str) -> PathBuf {
        let p = self.path().join(name);
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        one(
            self.u,
            None,
            "write",
            &[p.as_os_str(), OsStr::new(&hex), OsStr::new(mode)],
        );
        self.manifest.push(name.to_owned());
        p
    }
}

impl Drop for Run {
    fn drop(&mut self) {
        let out = helper(
            self.u,
            None,
            "remove",
            &[
                OsStr::new(self.root),
                OsStr::new(&self.name),
                OsStr::new(&self.manifest.join(",")),
            ],
        );
        eprintln!("fence: {}", out.join(" / "));
    }
}

/// A World served as `nd`: `host serve` and `host follow` under nd-supervise, the operator's `nd`
/// as nd; one resident grain born (installed, never started), the name keybroker serves.
struct NdWorld {
    ws: PathBuf,
    holding: PathBuf,
    host_sock: PathBuf,
    store: PathBuf,
    operator: String,
    resident: String,
    _serve: AsChild,
    _follow: AsChild,
}

impl NdWorld {
    fn nd(&self, args: &[&str]) -> String {
        nd_as(&self.ws, &self.holding, Some(&self.host_sock), args)
    }

    fn genesis(run: &mut Run) -> NdWorld {
        let (ws, holding) = (run.dir("ws", "700"), run.dir("holding", "700"));
        let stores = run.dir("stores", "700");
        let rdir = run.dir("run", "700");
        let (store, fstore) = (stores.join("W"), stores.join("F"));
        nd_as(&ws, &holding, None, &["--init"]);
        let keys = nd_as(&ws, &holding, None, &["--keys"]);
        let host = lean_bin("host");
        let genesis = |s: &Path, nonce: Option<&str>| {
            let mut a: Vec<&OsStr> = vec![OsStr::new("genesis"), s.as_os_str(), OsStr::new("nano")];
            if let Some(n) = nonce {
                a.extend([OsStr::new("--nonce"), OsStr::new(n)]);
            }
            a.extend([
                OsStr::new(line(&keys, "key ")),
                OsStr::new(line(&keys, "next ")),
            ]);
            let o = as_user(ND, None, &[], host.as_os_str(), &a)
                .output()
                .unwrap();
            assert!(o.status.success(), "genesis as nd: {}", both(&o));
            text(&o)
        };
        let g = genesis(&store, None);
        assert_eq!(
            genesis(&fstore, Some(line(&g, "nonce "))),
            g,
            "one genesis, two Stores"
        );
        let founder = line(&g, "founder 0 member ");
        let (operator, grant) = founder.split_once(" grant ").unwrap();
        let host_sock = rdir.join("host.sock");
        let serve = supervise_as(
            &host_sock,
            &ws,
            &store,
            &[OsStr::new("serve"), store.as_os_str()],
        );
        let follow_sock = ws.join("follow.sock");
        let follow = supervise_as(
            &follow_sock,
            &ws,
            &fstore,
            &[
                OsStr::new("follow"),
                fstore.as_os_str(),
                OsStr::new(operator),
                OsStr::new(grant),
            ],
        );
        let mut w = NdWorld {
            ws,
            holding,
            host_sock,
            store,
            operator: operator.to_owned(),
            resident: String::new(),
            _serve: serve,
            _follow: follow,
        };
        let text = fs::read_to_string(repo().join("world/grain/Lifecycle")).unwrap();
        let lifecycle = line(&w.nd(&["install", &text]), "id ").to_owned();
        w.resident = line(
            &w.nd(&[
                "create",
                "--pkg",
                &lifecycle,
                "(record (entry \"r1\") (kind resident) (phase installed))",
            ]),
            "id ",
        )
        .to_owned();
        w
    }
}

/// The operator's `nd` as nd; it must succeed.
fn nd_as(ws: &Path, holding: &Path, host: Option<&Path>, args: &[&str]) -> String {
    let mut envs: Vec<(&str, &OsStr)> = vec![
        ("ND_WORKSPACE", ws.as_os_str()),
        ("ND_HOLDING", holding.as_os_str()),
    ];
    if let Some(h) = host {
        envs.push(("ND_HOST_SOCK", h.as_os_str()));
    }
    let a: Vec<&OsStr> = args.iter().map(OsStr::new).collect();
    let o = as_user(ND, None, &envs, nd().as_os_str(), &a)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(o.status.success(), "nd {args:?} as nd: {}", both(&o));
    text(&o)
}

/// `host ARGS` under nd-supervise as nd (`devtools::supervise_host`'s argv), bound before it returns.
fn supervise_as(sock: &Path, hide: &Path, store: &Path, args: &[&OsStr]) -> AsChild {
    let host = lean_bin("host");
    let mut a: Vec<&OsStr> = vec![
        sock.as_os_str(),
        OsStr::new("--hide"),
        hide.as_os_str(),
        OsStr::new("--write"),
        store.as_os_str(),
        OsStr::new("--exec"),
        host.as_os_str(),
        OsStr::new("--"),
        host.as_os_str(),
    ];
    a.extend_from_slice(args);
    let child = as_user(ND, None, &[], nd_supervise().as_os_str(), &a)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let c = AsChild(child);
    one(ND, None, "bound", &[sock.as_os_str()]);
    c
}

/// The `UMask=` of the emitted unit `deploy/units/linux/<unit>` (systemd's default 0022 when absent).
fn unit_umask(unit: &str) -> String {
    let text = fs::read_to_string(repo().join("deploy/units/linux").join(unit)).unwrap();
    let u = text
        .lines()
        .find_map(|l| l.strip_prefix("UMask="))
        .unwrap_or("0022")
        .to_owned();
    assert!(
        u.len() == 4 && u.bytes().all(|b| (b'0'..=b'7').contains(&b)),
        "plant: {unit}'s UMask {u}"
    );
    u
}

/// The run's tag: this process's pid in base 36 and a letter per test (SOCKDIR + 64 + /broker.sock
/// must fit sun_path).
fn tag(letter: char) -> String {
    let mut n = std::process::id();
    let mut t = String::new();
    while n > 0 {
        t.insert(0, char::from_digit(n % 36, 36).unwrap());
        n /= 36;
    }
    format!("t{t}{letter}")
}

/// keybroker as nd on its rendered unit's argv over `w`, PEER = the hosted uid, SOCKDIR a fresh
/// directory of the deployed /run/nd-broker; returns once the resident's socket is bound 0660.
struct Served {
    sock: PathBuf,
    _kb: AsChild,
    _sockdir: Run,
    _world: NdWorld,
    _run: Run,
}

fn served(f: &Fence, letter: char) -> Served {
    let mut run = Run::new(ND, ND_TREE, tag(letter), "700");
    let w = NdWorld::genesis(&mut run);
    let pki = Pki::new();
    let keys = run.file("keys", &[b"7 ".as_slice(), KEY, b"\n"].concat(), "600");
    let anchors = run.file("anchors.pem", pki.ca_pem.as_bytes(), "644");
    run.file("pins", b"", "644");
    let pids = run.dir("pids", "700");
    let mut sockdir = Run::new(ND, BROKER, tag(letter), "2710");
    sockdir.manifest.push(w.resident.clone());
    let socks = sockdir.path();
    let c = argv(
        &keys,
        &anchors,
        &socks,
        &pids,
        "127.0.0.1:9",
        &w.store,
        &w.operator,
        &f.hosted.0.to_string(),
    );
    let args: Vec<&OsStr> = c.get_args().collect();
    let err = nanodregg_devtools::scratch(&format!("fence-{}", tag(letter))).join("keybroker.err");
    eprintln!("fence: keybroker's stderr: {}", err.display());
    // under the unit's own UMask (systemd sets it before exec): R4, a 0077 makes 02700
    let umask = unit_umask("nd-keybroker.service");
    let script = format!("umask {umask}; exec \"$0\" \"$@\"");
    let words: Vec<&OsStr> = [OsStr::new("-c"), OsStr::new(&script), c.get_program()]
        .into_iter()
        .chain(args.iter().copied())
        .collect();
    let kb = AsChild(
        as_user(ND, None, &[], OsStr::new("/bin/sh"), &words)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(fs::File::create(&err).unwrap())
            .spawn()
            .unwrap(),
    );
    let sock = socks.join(&w.resident).join("broker.sock");
    // the hosted uid may look the name up (02710: group traverse) without connecting
    one(HOSTED, None, "sock", &[sock.as_os_str(), OsStr::new("660")]);
    Served {
        sock,
        _kb: kb,
        _sockdir: sockdir,
        _world: w,
        _run: run,
    }
}

#[test]
fn keybroker_serves_the_hosted_uid_alone() {
    let Some(f) = fence("keybroker_serves_the_hosted_uid_alone") else {
        return;
    };
    assert_ne!(
        f.nd.1, f.hosted.1,
        "the fence: nd and nd-hosted share a primary group"
    );
    let s = served(&f, 'k');
    let sock = s.sock.as_os_str();
    // CONTROL: the hosted uid is decided (no allowance: noAllowance, a decision past the peer check)
    let v = one(HOSTED, None, "ask", &[sock]);
    eprintln!("fence verdict: as nd-hosted: {v}");
    assert_eq!(
        v, "refused NoAllowance",
        "control: the hosted uid was not decided"
    );
    let me = rustix::process::getuid().as_raw();
    let me_name = fs::read_to_string("/etc/passwd")
        .unwrap()
        .lines()
        .find_map(|l| {
            let f: Vec<&str> = l.split(':').collect();
            (f.len() > 2 && f[2] == me.to_string()).then(|| f[0].to_owned())
        })
        .unwrap();
    for (who, u, g) in [
        ("the owner nd (gid nd)", ND, None),
        (
            "a third uid holding the group",
            me_name.as_str(),
            Some(HOSTED),
        ),
        ("the hosted uid with gid nd", HOSTED, Some(ND)),
    ] {
        let v = one(u, g, "ask", &[sock]);
        eprintln!("fence verdict: as {who}: {v}");
        assert_eq!(
            v, "refused PeerRefused",
            "{who} was not refused peerRefused"
        );
    }
    // this uid without the group: SOCKDIR (02710) refuses the lookup itself
    let v = ask_once(&s.sock);
    eprintln!("fence verdict: as this uid, no group: {v}");
    assert_eq!(v, "connect PermissionDenied", "this uid reached the socket");
}

#[test]
fn the_hosted_uid_alone_resolves_the_group_socket() {
    let Some(f) = fence("the_hosted_uid_alone_resolves_the_group_socket") else {
        return;
    };
    let s = served(&f, 'c');
    let sock = s.sock.as_os_str();
    let me = std::env::current_exe().unwrap();
    let me = me.as_os_str();
    // the deployed branch: another uid's socket, group = egid, 0660; the confined child reaches it
    let v = one(HOSTED, None, "resolve", &[sock, me]);
    eprintln!("fence verdict: Policy.connect as nd-hosted: {v}");
    assert_eq!(
        v, "resolved; confined refused NoAllowance",
        "the hosted uid's confined child was not decided"
    );
    for (who, u, g, want) in [
        (
            "the hosted uid with gid nd",
            HOSTED,
            Some(ND),
            "refused ConnectOwner",
        ),
        ("the owner nd", ND, None, "refused ConnectMode"),
    ] {
        let v = one(u, g, "resolve", &[sock, me]);
        eprintln!("fence verdict: Policy.connect as {who}: {v}");
        assert_eq!(v, want, "Policy.connect as {who}");
    }
    let policy = nanodregg_sandbox::Policy {
        connect: vec![s.sock.clone()],
        ..nanodregg_sandbox::Policy::default()
    };
    let v = match nanodregg_sandbox::command(&policy, OsStr::new("/usr/bin/true"), &[]) {
        Err(e) => format!("refused {}", name_of(&e)),
        Ok(_) => "resolved".into(),
    };
    eprintln!("fence verdict: Policy.connect as this uid: {v}");
    assert_eq!(
        v, "refused PathMissing",
        "this uid resolved the hosted socket"
    );
}

/// nd-supervise as `u` (None: this uid) at `sock`, granting `grant` (`--read`), hiding `hide`, its
/// program `/usr/bin/test ARGS`; its stderr's last line (the refusal, or the child's exit status).
fn supervise_test(
    u: Option<&str>,
    sock: &Path,
    grant: &Path,
    hide: &[&Path],
    args: &[&str],
) -> String {
    let mut a: Vec<&OsStr> = vec![
        sock.as_os_str(),
        OsStr::new("--read"),
        grant.as_os_str(),
        OsStr::new("--exec"),
        OsStr::new("/usr/bin/test"),
    ];
    for h in hide {
        a.extend([OsStr::new("--hide"), h.as_os_str()]);
    }
    a.extend([OsStr::new("--"), OsStr::new("/usr/bin/test")]);
    a.extend(args.iter().map(OsStr::new));
    let sup = nd_supervise();
    let mut c = match u {
        Some(u) => as_user(u, None, &[], sup.as_os_str(), &a),
        None => {
            let mut c = Command::new("/usr/bin/timeout");
            c.args(["--kill-after=5", LIFE_S]).arg(&sup).args(&a);
            c
        }
    };
    let o = c.stdin(Stdio::null()).output().unwrap();
    let err = String::from_utf8_lossy(&o.stderr).into_owned();
    err.lines().last().unwrap_or("").to_owned()
}

/// Check 3, the units' `--hide /home` (nd-host-serve, nd-hosted-follow@, nd-members@), for real.
///
/// On Linux a confined child is built from an empty root, so `/home` is absent from it whether or
/// not anything hides it; the hide is a refusal before launch of a grant overlapping `/home`
/// (`Exposed`). Measured here (HOSTING-16, logs/hosting16-home*.out):
/// - as nd and as nd-hosted, a grant naming `/home` is refused by name (`cannot list grant
///   /home/<user>`, `GrantUnlisted`), and so is a grant of a user's directory under it: the socket
///   scan of every grant (which runs before the hide check) cannot list another user's 0750 home.
///   With the `/home` hide removed the refusal is IDENTICAL: on this box the hide is never reached
///   for the deployed uids. It would be on a box whose `/home` holds a path they can list.
/// - as nd, a child granted only its run tree tests `-e /home`: absent (exit 1); unconfined, nd
///   sees it (exit 0).
/// - as this uid, which can list a directory under /home (cargo's), the hide is reached and refuses
///   (`exposed: … reaches hidden /home`); CONTROL, the hide removed: the child launches and reads
///   that directory (exit 0). So the check bites where it is reached.
#[test]
fn a_home_grant_is_refused_and_home_is_absent_for_both_uids() {
    let Some(_f) = fence("a_home_grant_is_refused_and_home_is_absent_for_both_uids") else {
        return;
    };
    let home = Path::new("/home");
    let mut run = Run::new(ND, ND_TREE, tag('h'), "700");
    let rdir = run.dir("h", "700");
    let tree = run.path();
    // never bound: each launch below is refused before nd-supervise binds; both uids traverse
    // SOCKDIR (02710 nd:nd-hosted) and the directory named does not exist
    let nowhere = Path::new(BROKER)
        .join(format!("{}-absent", tag('h')))
        .join("s.sock");
    let users: Vec<PathBuf> = fs::read_dir(home)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    for u in [ND, HOSTED] {
        for g in std::iter::once(home.to_path_buf()).chain(users.iter().cloned()) {
            for (word, hide) in [
                ("hidden", vec![tree.as_path(), home]),
                ("hide removed", vec![tree.as_path()]),
            ] {
                let v = supervise_test(Some(u), &nowhere, &g, &hide, &["-r", &g.to_string_lossy()]);
                eprintln!(
                    "fence verdict: as {u}, grant {} (/home {word}): {v}",
                    g.display()
                );
                assert!(
                    v.contains("cannot list grant /home/"),
                    "as {u}, a grant of {} ({word}) was not refused by name: {v}",
                    g.display()
                );
            }
        }
    }
    // /home is absent from a confined child as nd; nd itself sees it
    let v = supervise_test(
        Some(ND),
        &rdir.join("s.sock"),
        &rdir,
        &[home],
        &["-e", "/home"],
    );
    eprintln!("fence verdict: as nd, confined, test -e /home: {v}");
    assert!(
        v.ends_with("child exit status: 1"),
        "a confined child as nd saw /home: {v}"
    );
    let seen = Command::new("sudo")
        .args(["-n", "-u", ND, "--", "/usr/bin/test", "-e", "/home"])
        .status()
        .unwrap();
    assert!(
        seen.success(),
        "control: nd does not see /home unconfined: {seen}"
    );
    // where the hide IS reached: this uid lists cargo's directory under /home
    let cargo = Path::new(env!("CARGO"))
        .canonicalize()
        .ok()
        .and_then(|p| p.parent().map(Path::to_path_buf))
        .filter(|d| d.starts_with(home));
    let Some(dir) = cargo else {
        let _ = std::io::stderr().write_all(
            b"skipped: no listable directory under /home for this uid \
              (a_home_grant_is_refused_and_home_is_absent_for_both_uids: the hide's own bite)\n",
        );
        return;
    };
    let scratch = nanodregg_devtools::scratch(&format!("fence-{}", tag('h')));
    let d = dir.to_string_lossy();
    let v = supervise_test(
        None,
        &scratch.join("on.sock"),
        &dir,
        &[&scratch, home],
        &["-r", &d],
    );
    eprintln!("fence verdict: as this uid, grant {d} (/home hidden): {v}");
    assert!(
        v.contains("reaches hidden /home"),
        "the hide did not refuse {d}: {v}"
    );
    let v = supervise_test(
        None,
        &scratch.join("off.sock"),
        &dir,
        &[&scratch],
        &["-r", &d],
    );
    eprintln!("fence verdict: as this uid, grant {d} (hide removed): {v}");
    assert!(
        v.ends_with("child exit status: 0"),
        "control: with the hide removed the child did not read {d}: {v}"
    );
    let _ = fs::remove_dir_all(&scratch);
}
