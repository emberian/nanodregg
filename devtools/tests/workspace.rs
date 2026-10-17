//! The workspace plants: every crate directory of the repository is a workspace member (so the
//! workspace judgement builds it), no deployed crate depends on devtools, and a missing Lean exe
//! fails the calling test by name.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::fs;
use std::path::Path;

use nanodregg_devtools::{lean_bin, lean_bin_in, nd, nd_supervise, repo, supervise_host};

/// The `members = [...]` list of the root Cargo.toml.
fn members(root: &Path) -> Vec<String> {
    let text = fs::read_to_string(root.join("Cargo.toml")).unwrap();
    let line = text.lines().find(|l| l.starts_with("members")).unwrap();
    let inner = &line[line.find('[').unwrap() + 1..line.rfind(']').unwrap()];
    let mut m: Vec<String> = inner
        .split(',')
        .map(|s| s.trim().trim_matches('"').to_owned())
        .filter(|s| !s.is_empty())
        .collect();
    m.sort();
    m
}

/// Every directory under the root holding a Cargo.toml (the root itself, build output, Lean's
/// `.lake` and dot-directories excluded), as a path relative to the root.
fn crates(root: &Path) -> Vec<String> {
    let mut c = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            let name = p.file_name().unwrap().to_string_lossy().into_owned();
            if !p.is_dir() || name.starts_with('.') || name == "target" {
                continue;
            }
            if p.join("Cargo.toml").is_file() {
                c.push(p.strip_prefix(root).unwrap().to_string_lossy().into_owned());
            }
            stack.push(p);
        }
    }
    c.sort();
    c
}

#[test]
fn every_crate_directory_is_a_workspace_member_and_holds_no_lock_of_its_own() {
    let root = repo();
    let crates = crates(&root);
    assert!(crates.len() >= 5, "plant: found only {crates:?}");
    assert_eq!(
        members(&root),
        crates,
        "notAMember: a crate outside the workspace is never judged"
    );
    for c in &crates {
        assert!(
            !root.join(c).join("Cargo.lock").exists(),
            "ownLock: {c}/Cargo.lock beside the workspace's one lock"
        );
        let manifest = fs::read_to_string(root.join(c).join("Cargo.toml")).unwrap();
        assert!(
            !manifest.lines().any(|l| l.trim() == "[workspace]"),
            "ownWorkspace: {c}/Cargo.toml declares its own workspace"
        );
    }
    assert!(
        root.join("Cargo.lock").is_file(),
        "noLock: the workspace has no Cargo.lock"
    );
}

#[test]
fn no_crate_depends_on_devtools_outside_its_dev_dependencies() {
    let root = repo();
    for c in crates(&root) {
        let manifest = fs::read_to_string(root.join(&c).join("Cargo.toml")).unwrap();
        let mut section = String::new();
        for l in manifest.lines().map(str::trim) {
            if l.starts_with('[') {
                section = l.to_owned();
            } else if l.starts_with("nanodregg-devtools") {
                assert_eq!(
                    section, "[dev-dependencies]",
                    "devtoolsDeployed: {c} depends on devtools in {section}"
                );
            }
        }
    }
}

#[test]
fn a_missing_lean_exe_fails_by_name() {
    let empty = std::env::temp_dir().join(format!("nd-devtools-{}", std::process::id()));
    fs::create_dir_all(&empty).unwrap();
    let err = std::panic::catch_unwind(|| lean_bin_in(&empty, "host"));
    let _ = fs::remove_dir_all(&empty);
    let msg = err.err().unwrap();
    let msg = msg
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| msg.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap();
    assert!(
        msg.contains("plant: no lake-built host at") && msg.contains("lake build host"),
        "{msg}"
    );
    // The same discovery finds this tree's host once it is built (`lake build host`).
    assert!(lean_bin("host").is_absolute());
}

/// What another crate's test does: this tree's `nd-supervise` (built by devtools) runs this tree's
/// `host serve` on a fresh Store and binds; dropping the holder stops it and removes its pid file.
#[test]
fn the_built_supervisor_runs_the_built_host() {
    assert!(nd().is_file() && nd().is_absolute());
    let root = std::env::temp_dir().join(format!("nd-dt-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("ws")).unwrap();
    let root = root.canonicalize().unwrap();
    let store = root.join("store");
    let g = std::process::Command::new(lean_bin("host"))
        .arg("genesis")
        .arg(&store)
        .arg("devtools")
        .output()
        .unwrap();
    assert!(g.status.success(), "plant: genesis: {g:?}");
    let sock = root.join("h.sock");
    let held = supervise_host(
        &nd_supervise(),
        &sock,
        &root.join("ws"),
        &store,
        &["serve", store.to_str().unwrap()],
    );
    let pid = root.join("h.sock.pid");
    assert!(
        fs::read_to_string(&pid)
            .unwrap()
            .trim()
            .parse::<u32>()
            .is_ok()
    );
    drop(held);
    assert!(!pid.exists(), "the holder removes its pid file");
    let _ = fs::remove_dir_all(&root);
}
