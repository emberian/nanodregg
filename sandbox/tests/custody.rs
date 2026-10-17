//! The custody-read plants: one per refusal. Each refused file differs from an accepted one in
//! exactly the property its refusal names, and the accepted one is read in every scratch, so no
//! plant is vacuous.
#![allow(clippy::unwrap_used, clippy::expect_used)] // a plant that cannot set up is a failed plant
use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

use nanodregg_sandbox::custody::{PRIVATE, Refused, check_private_dir, read_private, read_public};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A scratch directory holding `ok`: 32 bytes, mode 0600, ours, read back exactly.
fn scratch(name: &str) -> Scratch {
    let d = nanodregg_devtools::scratch(&format!("nd-custody-{}-{name}", std::process::id()));
    nanodregg_devtools::mkdirs(&d).unwrap();
    put(&d.join("ok"), &[7u8; 32], PRIVATE);
    assert_eq!(*read_private(&d.join("ok"), 32..=32).unwrap(), [7u8; 32]);
    Scratch(d)
}

fn put(path: &Path, bytes: &[u8], mode: u32) {
    fs::write(path, bytes).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
}

#[test]
fn a_link_to_an_accepted_file_is_refused_link() {
    let s = scratch("link");
    std::os::unix::fs::symlink(s.0.join("ok"), s.0.join("l")).unwrap();
    assert!(matches!(
        read_private(&s.0.join("l"), 32..=32),
        Err(Refused::Link)
    ));
}

#[test]
fn a_group_or_other_bit_and_a_read_only_file_are_refused_mode() {
    let s = scratch("mode");
    for m in [0o640, 0o604, 0o400, 0o700] {
        let f = s.0.join(format!("m{m:o}"));
        put(&f, &[7u8; 32], m);
        assert!(
            matches!(read_private(&f, 32..=32), Err(Refused::Mode(x)) if x == m),
            "mode {m:o}"
        );
    }
}

/// Another user's 0600 file cannot be opened by us at all, so the plant is a file we can open that
/// is not ours: `/etc/passwd` (root's). Owner is checked before mode, so it is `Owner`, not `Mode`.
#[test]
fn a_file_of_another_user_is_refused_owner() {
    let s = scratch("owner");
    let me = fs::metadata(&s.0).unwrap().uid();
    assert_ne!(me, 0, "the owner plant needs a non-root runner");
    let theirs = Path::new("/etc/passwd");
    assert_eq!(fs::metadata(theirs).unwrap().uid(), 0);
    assert!(matches!(
        read_private(theirs, 1..=1 << 20),
        Err(Refused::Owner(0))
    ));
}

#[test]
fn a_length_outside_the_range_is_refused_length() {
    let s = scratch("length");
    put(&s.0.join("long"), &[7u8; 33], PRIVATE);
    assert!(matches!(
        read_private(&s.0.join("long"), 32..=32),
        Err(Refused::Length(33))
    ));
    put(&s.0.join("empty"), &[], PRIVATE);
    assert!(matches!(
        read_private(&s.0.join("empty"), 1..=64),
        Err(Refused::Length(0))
    ));
    assert_eq!(read_private(&s.0.join("long"), 1..=64).unwrap().len(), 33);
}

#[test]
fn a_directory_and_a_fifo_are_refused_not_regular() {
    let s = scratch("kind");
    nanodregg_devtools::mkdirs(&s.0.join("d")).unwrap();
    fs::set_permissions(s.0.join("d"), fs::Permissions::from_mode(PRIVATE)).unwrap();
    assert!(matches!(
        read_private(&s.0.join("d"), 0..=64),
        Err(Refused::NotRegular)
    ));
    // A FIFO is refused at once: the open does not wait for a writer.
    let fifo = s.0.join("f");
    assert!(
        Command::new("mkfifo")
            .arg("-m")
            .arg("600")
            .arg(&fifo)
            .status()
            .unwrap()
            .success()
    );
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        tx.send(matches!(
            read_private(&fifo, 0..=64),
            Err(Refused::NotRegular)
        ))
    });
    let r = rx.recv_timeout(std::time::Duration::from_secs(5));
    assert!(r.is_ok(), "fifoWaited: the custody read blocked on a FIFO");
    assert!(r.unwrap(), "a FIFO read is not refused NotRegular");
}

#[test]
fn a_holding_directory_is_refused_unless_ours_0700_and_not_a_link() {
    let s = scratch("dir");
    let h = s.0.join("h");
    nanodregg_devtools::mkdirs(&h).unwrap();
    fs::set_permissions(&h, fs::Permissions::from_mode(0o700)).unwrap();
    check_private_dir(&h).unwrap();
    std::os::unix::fs::symlink(&h, s.0.join("hl")).unwrap();
    assert!(matches!(
        check_private_dir(&s.0.join("hl")),
        Err(Refused::Link)
    ));
    assert!(matches!(
        check_private_dir(&s.0.join("ok")),
        Err(Refused::NotRegular)
    ));
    fs::set_permissions(&h, fs::Permissions::from_mode(0o755)).unwrap();
    assert!(matches!(check_private_dir(&h), Err(Refused::Mode(0o755))));
}

/// The public read (trust anchors): an owner-only, a world-readable and a read-only file pass; a
/// group- or world-writable one, or one with a setuid/setgid/sticky bit, is `Mode`; and the
/// shared checks (link, kind, owner, length) are the private read's.
#[test]
fn a_public_file_is_refused_writable_by_others_and_by_the_shared_checks() {
    let s = scratch("public");
    for m in [0o600, 0o644, 0o444] {
        let f = s.0.join(format!("ok{m:o}"));
        put(&f, b"ANCHOR", m);
        assert_eq!(read_public(&f, 1..=64).unwrap(), b"ANCHOR", "mode {m:o}");
    }
    for m in [0o664, 0o646, 0o4644, 0o2644, 0o1644] {
        let f = s.0.join(format!("m{m:o}"));
        put(&f, b"ANCHOR", m);
        assert!(
            matches!(read_public(&f, 1..=64), Err(Refused::Mode(x)) if x == m),
            "mode {m:o}"
        );
    }
    std::os::unix::fs::symlink(s.0.join("ok644"), s.0.join("l")).unwrap();
    assert!(matches!(
        read_public(&s.0.join("l"), 1..=64),
        Err(Refused::Link)
    ));
    assert!(matches!(
        read_public(&s.0, 0..=1 << 20),
        Err(Refused::NotRegular)
    ));
    assert!(matches!(
        read_public(Path::new("/etc/passwd"), 1..=1 << 20),
        Err(Refused::Owner(0))
    ));
    assert!(matches!(
        read_public(&s.0.join("ok644"), 7..=64),
        Err(Refused::Length(6))
    ));
    // The private read still refuses what the public one accepts.
    assert!(matches!(
        read_private(&s.0.join("ok644"), 1..=64),
        Err(Refused::Mode(0o644))
    ));
}

/// A directory above a custody file that another can write, or that another user owns, lets them
/// swap the file: refused `Dir`, naming that directory, for both reads (sshd's StrictModes). The
/// file itself is accepted in an accepted directory (the scratch's `ok`), so the plant is not
/// vacuous.
#[test]
fn a_parent_writable_by_others_or_owned_by_another_user_is_refused_dir() {
    let s = scratch("dir-chain");
    let g = s.0.join("g");
    nanodregg_devtools::mkdirs(&g).unwrap();
    put(&g.join("k"), &[7u8; 32], PRIVATE);
    for m in [0o770, 0o707, 0o1777] {
        fs::set_permissions(&g, fs::Permissions::from_mode(m)).unwrap();
        assert!(
            matches!(read_private(&g.join("k"), 32..=32), Err(Refused::Dir(d)) if d == g),
            "parent mode {m:o}"
        );
        assert!(
            matches!(read_public(&g.join("k"), 32..=32), Err(Refused::Dir(d)) if d == g),
            "parent mode {m:o}"
        );
    }
    fs::set_permissions(&g, fs::Permissions::from_mode(0o700)).unwrap();
    assert!(read_private(&g.join("k"), 32..=32).is_ok());
    // /tmp: root's, sticky, world-writable. Refused before any open (the file need not exist).
    let tmp = Path::new("/tmp").canonicalize().unwrap();
    assert!(
        matches!(read_private(&tmp.join("nd-absent"), 1..=8), Err(Refused::Dir(d)) if d == tmp)
    );
    // A directory of another (non-root) user, found on this box; none found FAILS the plant.
    let euid = fs::metadata(&s.0).unwrap().uid();
    let theirs = [
        "/var/lib",
        "/var/spool",
        "/var/cache",
        "/home",
        "/var/db",
        "/private/var/db",
    ]
    .iter()
    .filter_map(|r| fs::read_dir(r).ok())
    .flatten()
    .filter_map(|e| e.ok().map(|e| e.path()))
    .find(|p| {
        fs::symlink_metadata(p).is_ok_and(|m| {
            m.is_dir() && m.uid() != 0 && m.uid() != euid && m.permissions().mode() & 0o022 == 0
        })
    })
    .expect("plant: no directory of another non-root user on this box");
    let theirs = theirs.canonicalize().unwrap();
    assert!(
        matches!(read_private(&theirs.join("k"), 1..=8), Err(Refused::Dir(d)) if d == theirs),
        "{}",
        theirs.display()
    );
    assert!(matches!(check_private_dir(&theirs.join("h")), Err(Refused::Dir(d)) if d == theirs));
}
