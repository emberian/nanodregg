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

use nanodregg_sandbox::{ConfineError, Policy, command};

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

fn sh(policy: &Policy, line: &str) -> Output {
    command(
        policy,
        OsStr::new("/bin/sh"),
        &[OsStr::new("-c"), OsStr::new(line)],
    )
    .unwrap()
    .output()
    .unwrap()
}

/// Exec is filtered on both platforms (CLIENT-9, CLIENT-48): a shell allowed to run only itself
/// may exec itself again, and is refused an exec of /usr/bin/true, which no `exec` entry names
/// (Linux: Landlock's execute right, EACCES; macOS: `process-exec`). The same line runs unconfined.
#[test]
fn exec_is_filtered_to_the_program_and_its_exec_entries() {
    let t = tree("exec");
    let policy = Policy {
        exec: vec!["/bin/sh".into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let control = std::process::Command::new("/bin/sh")
        .args(["-c", "exec /usr/bin/true"])
        .status()
        .unwrap();
    assert!(control.success(), "control: unconfined, the exec runs");
    let own = sh(&policy, "exec /bin/sh -c 'echo RAN'");
    assert_eq!(
        own.stdout,
        b"RAN\n",
        "its own program re-execs: {}",
        String::from_utf8_lossy(&own.stderr)
    );
    let other = sh(&policy, "exec /usr/bin/true");
    assert!(
        !other.status.success(),
        "an unlisted program ran: {}",
        String::from_utf8_lossy(&other.stderr)
    );
    #[cfg(target_os = "linux")]
    assert!(
        String::from_utf8_lossy(&other.stderr).contains("Permission denied"),
        "refused by name: {}",
        String::from_utf8_lossy(&other.stderr)
    );
    fs::remove_dir_all(&t.root).unwrap();
}

/// No confined child makes a process (Linux: `clone` without `CLONE_THREAD` is EPERM; macOS:
/// `process-fork` is never allowed): a shell that must fork to run a command cannot, while the
/// same shell's builtins still run.
#[test]
fn a_confined_child_cannot_fork() {
    let t = tree("fork");
    let policy = Policy {
        exec: vec!["/bin/sh".into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let out = sh(&policy, "echo BUILTIN; /bin/sh -c 'echo FORKED'");
    let said = String::from_utf8_lossy(&out.stdout);
    assert!(said.contains("BUILTIN"), "the shell ran: {said}");
    assert!(!said.contains("FORKED"), "a child process ran: {said}");
    fs::remove_dir_all(&t.root).unwrap();
}

/// Linux names the refusal: an open outside the ruleset is EACCES, and a file the child wrote in
/// its write grant cannot be executed (write grants carry no execute right).
#[cfg(target_os = "linux")]
#[test]
fn an_open_outside_the_ruleset_is_refused_by_name_and_written_files_do_not_run() {
    let t = tree("named");
    let w = t.root.join("w");
    fs::create_dir_all(&w).unwrap();
    fs::copy("/usr/bin/true", w.join("true")).unwrap();
    let policy = Policy {
        write: vec![w.clone()],
        exec: vec!["/bin/sh".into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let seed = t.ws.join("seed");
    let out = sh(
        &policy,
        &format!("read x < {}; echo \"$x\"", seed.display()),
    );
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(out.stdout.iter().all(|b| *b == b'\n'), "read the seed");
    assert!(err.contains("Permission denied"), "refused by name: {err}");
    let ok = sh(
        &policy,
        &format!("echo HI > {0}/f && read x < {0}/f && echo $x", w.display()),
    );
    assert_eq!(
        ok.stdout,
        b"HI\n",
        "the write grant: {}",
        String::from_utf8_lossy(&ok.stderr)
    );
    let run = sh(&policy, &format!("exec {}/true", w.display()));
    assert!(!run.status.success(), "a written file ran");
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("Permission denied"),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    fs::remove_dir_all(&t.root).unwrap();
}

/// A confined child signals itself and nothing else: its own `kill -0 $$` succeeds, the same check
/// of a process outside it (an unconfined sleeper the plant owns) is refused.
#[cfg(target_os = "linux")]
#[test]
fn a_confined_child_signals_only_itself() {
    let t = tree("signal");
    let mut other = std::process::Command::new("/bin/sleep")
        .arg("30")
        .spawn()
        .unwrap();
    let policy = Policy {
        exec: vec!["/bin/sh".into()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let out = sh(
        &policy,
        &format!(
            "kill -0 $$ && echo SELF; kill -0 {} && echo OTHER",
            other.id()
        ),
    );
    let _ = other.kill();
    let _ = other.wait();
    let said = String::from_utf8_lossy(&out.stdout);
    assert!(
        said.contains("SELF"),
        "{said} {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(!said.contains("OTHER"), "signalled another process: {said}");
    fs::remove_dir_all(&t.root).unwrap();
}

/// Where a program lives is not what it is granted (TESTGROUND-4): a runnable file inside a hidden
/// tree is granted as that one file, so it launches with the tree hidden, and still cannot read a
/// sibling in that tree. A read grant inside the hidden tree, or a non-executable file named as the
/// program there, is still `Exposed`.
#[test]
fn a_program_inside_a_hidden_tree_runs_and_exposes_only_itself() {
    use std::os::unix::fs::PermissionsExt;
    let t = tree("inside");
    let prog = t.ws.join("cat");
    fs::copy(CAT, &prog).unwrap();
    fs::set_permissions(&prog, fs::Permissions::from_mode(0o755)).unwrap();
    let policy = Policy {
        read: vec![t.allowed.clone()],
        exec: vec![prog.clone()],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    let run = |f: &std::path::Path| {
        command(&policy, prog.as_os_str(), &[f.as_os_str()])
            .unwrap()
            .output()
            .unwrap()
    };
    let ok = run(&t.allowed.join("f"));
    assert_eq!(
        ok.stdout,
        b"ALLOWED",
        "{}",
        String::from_utf8_lossy(&ok.stderr)
    );
    let seed = run(&t.ws.join("seed"));
    assert!(
        !seed.status.success() && seed.stdout.is_empty(),
        "the sibling seed was read"
    );
    let wider = Policy {
        read: vec![t.ws.join("seed")],
        ..policy.clone()
    };
    assert!(matches!(
        command(&wider, prog.as_os_str(), &[]),
        Err(ConfineError::Exposed { .. })
    ));
    let seed_as_program = Policy {
        exec: vec![t.ws.join("seed")],
        hidden: vec![t.ws.clone()],
        ..Policy::default()
    };
    assert!(matches!(
        command(&seed_as_program, t.ws.join("seed").as_os_str(), &[]),
        Err(ConfineError::Exposed { .. })
    ));
    fs::remove_dir_all(&t.root).unwrap();
}
