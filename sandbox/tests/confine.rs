//! The isolation plants (CLIENT-8, CLIENT-9). A confined child reads what its policy allows and
//! nothing else: not the seed under the hidden workspace, and not a file nobody mentioned (the
//! allow-list property a deny-list fails). The same commands unconfined succeed, and an allowed
//! file is read confined, so neither plant is vacuous. A policy that reaches the workspace is
//! refused before anything runs.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::ffi::OsStr;
use std::fs;
use std::path::PathBuf;
use std::process::Output;

use nanodregg_sandbox::{ConfineError, EXEC_FILTERED, Policy, command};

const CAT: &str = "/bin/cat";

struct Tree {
    root: PathBuf,
    ws: PathBuf,
    allowed: PathBuf,
    other: PathBuf,
}

fn tree(name: &str) -> Tree {
    let root = std::env::temp_dir().join(format!("nd-confine-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    // The child is given real paths: the profile allows `/private/var/…`, not the `/var` link.
    let root = root.canonicalize().unwrap();
    let t = Tree {
        ws: root.join("ws"),
        allowed: root.join("allowed"),
        other: root.join("other"),
        root,
    };
    for (d, f, b) in [
        (&t.ws, "seed", "SEED-BYTES"),
        (&t.allowed, "f", "ALLOWED"),
        (&t.other, "g", "OTHER"),
    ] {
        fs::create_dir_all(d).unwrap();
        fs::write(d.join(f), b).unwrap();
    }
    t
}

fn confined(policy: &Policy, file: &std::path::Path) -> Output {
    command(policy, OsStr::new(CAT), &[file.as_os_str()])
        .unwrap()
        .output()
        .unwrap()
}

#[test]
fn confined_child_reads_what_is_allowed_and_nothing_else() {
    let t = tree("read");
    let (seed, f, g) = (t.ws.join("seed"), t.allowed.join("f"), t.other.join("g"));
    for (p, b) in [(&seed, &b"SEED-BYTES"[..]), (&g, b"OTHER")] {
        let control = std::process::Command::new(CAT).arg(p).output().unwrap();
        assert_eq!(
            control.stdout,
            b,
            "control: unconfined, {} is readable",
            p.display()
        );
    }
    let policy = Policy {
        read: vec![t.allowed.clone()],
        exec: vec![CAT.into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let ok = confined(&policy, &f);
    assert_eq!(
        ok.stdout,
        b"ALLOWED",
        "confined: the allowed file is read: {}",
        String::from_utf8_lossy(&ok.stderr)
    );
    let out = confined(&policy, &seed);
    assert!(
        !out.status.success() && out.stdout.is_empty(),
        "isolation: child read the seed"
    );
    let out = confined(&policy, &g);
    assert!(
        !out.status.success() && out.stdout.is_empty(),
        "allow-list: child read an unmentioned file"
    );
    fs::remove_dir_all(&t.root).unwrap();
}

#[test]
fn a_policy_that_reaches_the_workspace_is_refused() {
    let t = tree("exposed");
    let wider = Policy {
        read: vec![t.root.clone()],
        exec: vec![CAT.into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let inside = Policy {
        write: vec![t.ws.clone()],
        exec: vec![CAT.into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    for p in [wider, inside] {
        assert!(matches!(
            command(&p, OsStr::new(CAT), &[]),
            Err(ConfineError::Exposed { .. })
        ));
    }
    fs::remove_dir_all(&t.root).unwrap();
}

#[test]
fn a_missing_path_or_a_relative_program_refuses_to_launch() {
    let missing = Policy {
        exec: vec![CAT.into()],
        hidden: vec!["/nonexistent/nd-confine".into()],
        ..Policy::default()
    };
    assert!(matches!(
        command(&missing, OsStr::new(CAT), &[]),
        Err(ConfineError::PathMissing(..))
    ));
    assert!(matches!(
        command(&Policy::default(), OsStr::new("true"), &[]),
        Err(ConfineError::ProgramNotAbsolute(_))
    ));
}

#[test]
fn a_symlinked_program_does_not_widen_the_policy_to_its_target() {
    let t = tree("link");
    // `allowed/prog` is a link to /bin/cat: the policy names allowed/, not /bin.
    std::os::unix::fs::symlink(CAT, t.allowed.join("prog")).unwrap();
    let policy = Policy {
        read: vec![t.allowed.clone()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let prog = t.allowed.join("prog");
    assert!(matches!(
        command(&policy, prog.as_os_str(), &[]),
        Err(ConfineError::ProgramOutside { .. })
    ));
    // Named for what it is, it launches.
    let named = Policy {
        exec: vec![CAT.into()],
        ..policy
    };
    assert!(command(&named, prog.as_os_str(), &[]).is_ok());
    fs::remove_dir_all(&t.root).unwrap();
}

/// The EXEC_FILTERED row, measured: a shell allowed to run only itself starts /usr/bin/true, which
/// no `exec` entry names. Where the platform filters exec it is refused; where it does not
/// (Linux bwrap) it runs. Either way the row must say what happened.
#[test]
fn exec_is_filtered_exactly_where_the_platform_says() {
    let t = tree("exec");
    let sh = "/bin/sh";
    let policy = Policy {
        exec: vec![sh.into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let out = command(
        &policy,
        std::ffi::OsStr::new(sh),
        &[
            std::ffi::OsStr::new("-c"),
            std::ffi::OsStr::new("/usr/bin/true && echo RAN"),
        ],
    )
    .unwrap()
    .output()
    .unwrap();
    let ran = out.stdout == b"RAN\n";
    assert_eq!(
        ran,
        !EXEC_FILTERED,
        "EXEC_FILTERED = {EXEC_FILTERED}, but an unlisted /usr/bin/true ran = {ran} ({})",
        String::from_utf8_lossy(&out.stderr)
    );
    fs::remove_dir_all(&t.root).unwrap();
}
