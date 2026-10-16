//! Custody plants: a seed that is not owner-only, not exactly 32 bytes, or a link is refused.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::fs;
use std::os::unix::fs::PermissionsExt;

use nanodregg_client::custody::{Custody, CustodyError};

fn scratch(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("nd-custody-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir(&d).unwrap();
    d
}

#[test]
fn create_open_sign() {
    let d = scratch("ok");
    Custody::create(&d, "seed").unwrap();
    assert!(matches!(
        Custody::create(&d, "seed"),
        Err(CustodyError::Exists)
    ));
    let c = Custody::open(&d.join("seed")).unwrap();
    let sig = c.sign(b"header");
    let vk = ed25519_dalek::VerifyingKey::from_bytes(&c.public_key()).unwrap();
    vk.verify_strict(b"header", &ed25519_dalek::Signature::from_bytes(&sig))
        .unwrap();
    fs::remove_dir_all(&d).unwrap();
}

#[test]
fn group_readable_is_refused() {
    let d = scratch("mode");
    Custody::create(&d, "seed").unwrap();
    fs::set_permissions(d.join("seed"), fs::Permissions::from_mode(0o640)).unwrap();
    assert!(matches!(
        Custody::open(&d.join("seed")),
        Err(CustodyError::Permissions { mode: 0o640 })
    ));
    fs::remove_dir_all(&d).unwrap();
}

#[test]
fn wrong_length_is_refused() {
    let d = scratch("len");
    fs::write(d.join("seed"), [0u8; 33]).unwrap();
    fs::set_permissions(d.join("seed"), fs::Permissions::from_mode(0o600)).unwrap();
    assert!(matches!(
        Custody::open(&d.join("seed")),
        Err(CustodyError::WrongLength { len: 33 })
    ));
    fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_link_is_refused() {
    let d = scratch("link");
    Custody::create(&d, "seed").unwrap();
    std::os::unix::fs::symlink(d.join("seed"), d.join("alias")).unwrap();
    assert!(matches!(
        Custody::open(&d.join("alias")),
        Err(CustodyError::NotRegularFile)
    ));
    fs::remove_dir_all(&d).unwrap();
}
