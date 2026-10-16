//! The isolation plant (DECISIONS CLIENT-8): a confined child cannot read a seed under a hidden
//! directory, while the same command unconfined can (so the plant is not vacuous).
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::ffi::OsStr;
use std::fs;

use nanodregg_sandbox::{Policy, command};

#[test]
fn confined_child_cannot_read_the_seed() {
    let ws = std::env::temp_dir().join(format!("nd-confine-{}", std::process::id()));
    let _ = fs::remove_dir_all(&ws);
    fs::create_dir(&ws).unwrap();
    let seed = ws.join("seed");
    fs::write(&seed, b"SEED-BYTES").unwrap();
    let cat = OsStr::new("/bin/cat");

    let control = std::process::Command::new(cat).arg(&seed).output().unwrap();
    assert_eq!(control.stdout, b"SEED-BYTES", "control: unconfined, the seed is readable");

    let policy = Policy { hidden: vec![ws.clone()] };
    let out = command(&policy, cat, &[seed.as_os_str()]).unwrap().output().unwrap();
    assert!(!out.status.success(), "isolation: child read the seed");
    assert!(out.stdout.is_empty(), "isolation: child read the seed");
    fs::remove_dir_all(&ws).unwrap();
}

#[test]
fn a_missing_hidden_path_refuses_to_launch() {
    let policy = Policy { hidden: vec!["/nonexistent/nd-confine".into()] };
    assert!(command(&policy, OsStr::new("/bin/true"), &[]).is_err());
}
