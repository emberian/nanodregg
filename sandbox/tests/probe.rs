//! The probe (CLIENT-52, CRIT-SANDBOX): the sandbox's own negative test. A confined child
//! (`sandbox-probe`, a compiled plant) ATTEMPTS each operation the policy must refuse, and each is
//! refused with the errno named here; the same operation run unconfined by the same uid is NOT
//! refused that way, so every refusal below is the sandbox's, never the file system's or the
//! kernel's defaults. Every target is the test's own: files in its scratch tree, sockets it binds,
//! and the probe's parent (this test process), signalled with signal 0 (nothing is delivered).
//!
//! What it does not reach: the connector's peer-credential refusal and `Privileged` need a second
//! uid or root (the fence, `launcher/tests/fence.rs`, holds the second uid), and ABI 6's signal
//! scoping needs a 6.12 kernel (this test asserts the refusal of a launch that requires it on a
//! lower one). The production unit run is `deploy/live/confined-unit.sh … probe`.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

use std::ffi::OsStr;
use std::fs;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::process::Command;

use nanodregg_devtools::{mkdirs, scratch};
use nanodregg_sandbox::{ConfineError, Policy, command};

const PROBE: &str = env!("CARGO_BIN_EXE_sandbox-probe");

struct T {
    root: PathBuf,
    /// the write grant, holding `own`
    w: PathBuf,
    /// a sibling directory outside every grant, holding `f`
    sib: PathBuf,
    /// the hidden workspace
    ws: PathBuf,
}

fn tree(name: &str) -> T {
    // the scratch root (0700 directories under the user's own: a socket directory's ancestors
    // must not be writable by another, `Policy.connect`)
    let root = scratch(&format!("probe-{}-{name}", std::process::id()));
    let root = root.canonicalize().unwrap();
    let t = T {
        w: root.join("w"),
        sib: root.join("sib"),
        ws: root.join("ws"),
        root,
    };
    for (d, f) in [(&t.w, "own"), (&t.sib, "f"), (&t.ws, "seed")] {
        mkdirs(d).unwrap();
        fs::write(d.join(f), b"x").unwrap();
    }
    t
}

fn policy(t: &T) -> Policy {
    Policy {
        write: vec![t.w.clone()],
        exec: vec![PROBE.into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    }
}

fn out(c: &mut Command) -> String {
    let o = c.output().unwrap();
    let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
    assert!(
        o.status.success(),
        "plant: the probe ended {}: {s} {}",
        o.status,
        String::from_utf8_lossy(&o.stderr)
    );
    s
}

fn os<'a>(a: &[&'a str]) -> Vec<&'a OsStr> {
    a.iter().map(|s| OsStr::new(*s)).collect()
}

fn confined(p: &Policy, a: &[&str]) -> String {
    out(&mut command(p, OsStr::new(PROBE), &os(a)).unwrap())
}

fn unconfined(a: &[&str]) -> String {
    out(Command::new(PROBE).args(a))
}

/// Each operation the policy refuses: its name, the probe's op and argument, and the refusal.
#[test]
fn each_operation_the_policy_must_refuse_is_refused_by_the_sandbox() {
    let t = tree("ops");
    let sib = t.sib.join("f").to_str().unwrap().to_owned();
    let own = t.w.join("own").to_str().unwrap().to_owned();
    let fifo = t.w.join("fifo").to_str().unwrap().to_owned();
    let w = t.w.to_str().unwrap().to_owned();
    let mut cases: Vec<(&str, &str, &str, &str)> = vec![
        // the metadata calls Landlock does not mediate, on a same-uid file outside the grant
        (
            "chmod a sibling file",
            "fchmodat",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "chmod a sibling file (fchmodat2)",
            "fchmodat2",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "set a sibling file's times",
            "utimensat",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "chown a sibling file to its owner",
            "chown",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "set an xattr on a sibling file",
            "setxattr",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "fchmod a file in the write grant",
            "fchmod",
            own.as_str(),
            "refused EPERM",
        ),
        // the file rules themselves
        (
            "read a sibling file",
            "open",
            sib.as_str(),
            "refused EACCES",
        ),
        (
            "make a fifo in the write grant",
            "mkfifo",
            fifo.as_str(),
            "refused EPERM",
        ),
        // signals to a process not itself: its parent (this test), or everyone
        ("signal the parent", "kill-parent", "", "refused EPERM"),
        ("signal every process", "kill-all", "", "refused EPERM"),
        ("tgkill the parent", "tgkill-parent", "", "refused EPERM"),
        (
            "queue a signal to the parent",
            "sigqueue-parent",
            "",
            "refused EPERM",
        ),
        (
            "open a pidfd of the parent",
            "pidfd-parent",
            "",
            "refused EPERM",
        ),
        // kernel-sent signals arranged through fcntl (no kill call at all)
        (
            "F_SETOWN to the parent",
            "setown-parent",
            "",
            "refused EPERM",
        ),
        (
            "F_SETOWN_EX to the parent",
            "setown-ex-parent",
            "",
            "refused EPERM",
        ),
        ("F_SETSIG", "setsig", "", "refused EPERM"),
        ("O_ASYNC", "async", "", "refused EPERM"),
        // the parent-death signal the launcher set
        (
            "clear the parent-death signal",
            "pdeathsig-clear",
            "",
            "refused EPERM",
        ),
        // what a child may not create
        ("make a socket", "socket", "", "refused EPERM"),
        ("make a socket pair", "socketpair", "", "refused EPERM"),
        ("make a memfd", "memfd", "", "refused EPERM"),
        ("clone a process", "clone-process", "", "refused EPERM"),
        ("set up io_uring", "io-uring", "", "refused ENOSYS"),
        // a file it wrote, run directly
        (
            "exec a file it wrote",
            "exec-written",
            w.as_str(),
            "refused EACCES",
        ),
    ];
    #[cfg(target_arch = "x86_64")]
    cases.extend([
        (
            "chmod a sibling file (chmod)",
            "chmod",
            sib.as_str(),
            "refused EPERM",
        ),
        (
            "set a sibling file's times (utimes)",
            "utimes",
            sib.as_str(),
            "refused EPERM",
        ),
    ]);
    let p = policy(&t);
    let mut wrong = Vec::new();
    for (name, op, arg, want) in &cases {
        let a: Vec<&str> = std::iter::once(*op)
            .chain((!arg.is_empty()).then_some(*arg))
            .collect();
        let got = confined(&p, &a);
        let control = unconfined(&a);
        let _ = fs::remove_file(t.w.join("probe-copy"));
        let _ = fs::remove_file(&fifo);
        eprintln!("probe: {name}: confined `{got}`, unconfined `{control}`");
        // refused as named confined, and not so refused unconfined: the refusal is the sandbox's
        if got != *want || control == *want {
            wrong.push(format!(
                "{name}: confined `{got}` (want `{want}`), unconfined `{control}`"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "not refused by the sandbox:\n{}",
        wrong.join("\n")
    );
    fs::remove_dir_all(&t.root).unwrap();
}

/// A descriptor the launcher holds open WITHOUT close-on-exec does not reach the child: the step
/// marks every descriptor above stdio close-on-exec. CONTROL: unconfined, the same number is open.
#[test]
fn a_leaked_descriptor_is_closed_at_exec() {
    let t = tree("fd");
    let f = fs::File::open(t.sib.join("f")).unwrap();
    // a dup is not close-on-exec: inherited by every child this process starts while it lives
    let leaked = rustix::io::dup(&f).unwrap();
    let n = leaked.as_raw_fd().to_string();
    assert_eq!(
        unconfined(&["fd", &n]),
        "ok",
        "control: unconfined, fd {n} is inherited"
    );
    assert_eq!(
        confined(&policy(&t), &["fd", &n]),
        "refused EBADF",
        "confined: fd {n} reached the child"
    );
    drop(leaked);
    fs::remove_dir_all(&t.root).unwrap();
}

/// A socket of ours as `Policy.connect` accepts one: mode 0600 in a 0700 directory.
fn bind(p: &Path) -> UnixListener {
    mkdirs(p.parent().unwrap()).unwrap();
    let l = UnixListener::bind(p).unwrap();
    fs::set_permissions(p, fs::Permissions::from_mode(0o600)).unwrap();
    l
}

/// A listener at `p` that writes `tag` and a newline to each connection.
fn serve(p: &Path, tag: &'static str) -> UnixListener {
    let l = bind(p);
    let c = l.try_clone().unwrap();
    std::thread::spawn(move || {
        for s in c.incoming().flatten() {
            let mut s = s;
            let _ = writeln!(s, "{tag}");
        }
    });
    l
}

/// The connector dials through the socket directory it opened at launch: an ancestor renamed away
/// and replaced with another directory holding another server does not redirect it (the child
/// reaches the original server), and the granted name replaced with a link to another socket of
/// ours is refused (`ECONNREFUSED`). CONTROL: an unconfined connect to the same path reaches the
/// replacement, so each swap was real.
#[test]
fn a_swapped_socket_name_or_ancestor_does_not_redirect_the_connector() {
    let t = tree("swap");
    let up = t.root.join("up");
    let sd = up.join("sd");
    mkdirs(&up).unwrap();
    let sock = sd.join("s.sock");
    let sock_s = sock.to_str().unwrap().to_owned();
    let _a = serve(&sock, "A");
    let p = Policy {
        connect: vec![sock.clone()],
        ..policy(&t)
    };
    // the ancestor: `up/sd` renamed away, a new `up/sd/s.sock` served by B
    let mut c = command(&p, OsStr::new(PROBE), &os(&["connect", &sock_s])).unwrap();
    fs::rename(&sd, up.join("sd-old")).unwrap();
    let _b = serve(&sock, "B");
    assert_eq!(
        out(&mut c),
        "ok A",
        "confined: the swapped ancestor redirected the connector"
    );
    assert_eq!(
        unconfined(&["connect", &sock_s]),
        "ok B",
        "control: the swap was real"
    );
    // the name: `up/sd/s.sock` replaced by a link to another socket of ours
    let other = t.root.join("other");
    let _c = serve(&other.join("c.sock"), "C");
    let mut c = command(&p, OsStr::new(PROBE), &os(&["connect", &sock_s])).unwrap();
    fs::remove_file(&sock).unwrap();
    std::os::unix::fs::symlink(other.join("c.sock"), &sock).unwrap();
    assert_eq!(
        out(&mut c),
        "refused ECONNREFUSED",
        "confined: the link redirected the connector"
    );
    assert_eq!(
        unconfined(&["connect", &sock_s]),
        "ok C",
        "control: the link was real"
    );
    fs::remove_dir_all(&t.root).unwrap();
}

/// The policies refused before anything runs: a `/` grant beside a hidden tree (`Exposed`, the
/// root is no exception on Linux), a socket name with a quote (`UnnameablePath`), a socket
/// directory under a write grant (`ConnectOverlap`), and a Landlock ABI above the kernel's
/// (`LandlockAbi`).
#[test]
fn a_root_grant_a_quoted_socket_an_overlap_and_a_missing_abi_are_refused_at_launch() {
    let t = tree("refuse");
    let probe = OsStr::new(PROBE);
    let root = Policy {
        read: vec!["/".into()],
        ..policy(&t)
    };
    assert!(
        matches!(
            command(&root, probe, &[]),
            Err(ConfineError::Exposed { .. })
        ),
        "a `/` read grant beside hidden {} launched",
        t.ws.display()
    );
    let q = t.root.join("q");
    let quoted = q.join("a\"b.sock");
    let _l = bind(&quoted);
    let p = Policy {
        connect: vec![quoted],
        ..policy(&t)
    };
    assert!(
        matches!(
            command(&p, probe, &[]),
            Err(ConfineError::UnnameablePath(_))
        ),
        "a quoted socket name launched"
    );
    let sd = t.w.join("sd");
    let _s = bind(&sd.join("s.sock"));
    let p = Policy {
        connect: vec![sd.join("s.sock")],
        ..policy(&t)
    };
    assert!(
        matches!(
            command(&p, probe, &[]),
            Err(ConfineError::ConnectOverlap { .. })
        ),
        "a socket directory under the write grant launched"
    );
    let p = Policy {
        landlock_abi: 99,
        ..policy(&t)
    };
    assert!(
        matches!(
            command(&p, probe, &[]),
            Err(ConfineError::LandlockAbi { need: 99, .. })
        ),
        "a launch requiring Landlock ABI 99 ran"
    );
    // CONTROL: the base policy launches
    assert_eq!(confined(&policy(&t), &["noop"]), "ok exec");
    fs::remove_dir_all(&t.root).unwrap();
}

/// The one residual this test names rather than refuses: the ELF loader, executable by the runtime
/// manifest, maps a file the child wrote as its argument (Landlock does not mediate `mmap`). A
/// unit's `NoExecPaths` over the write grant refuses it (`deploy/live/confined-unit.sh … probe`);
/// the sandbox alone does not. If this starts failing, the residual closed: move the case above.
#[test]
fn the_loader_still_maps_a_written_file_standalone() {
    let t = tree("loader");
    let w = t.w.to_str().unwrap().to_owned();
    assert_eq!(confined(&policy(&t), &["loader-written", &w]), "ok exec");
    fs::remove_dir_all(&t.root).unwrap();
}
