//! Durable files. Every workspace write goes through here, and a crash leaves each file either
//! absent or complete-and-durable: its bytes are written whole and synced in `.NAME.tmp` (mode 0600,
//! `O_EXCL`), and only then given its name, by a hard link for `create_once` (which, unlike a
//! rename, refuses an existing name) or a rename for `replace`; the directory is synced. A `.NAME.tmp`
//! is fsx's own residue of a crash, incomplete by construction: the next write of NAME removes it,
//! and a reader of the directory passes over it ([`is_residue`]). Custody files are read by
//! `nanodregg_sandbox::custody`, the one read every key holder shares.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;

pub(crate) use nanodregg_sandbox::custody::PRIVATE;

/// Create `dir/name` holding exactly `bytes`, or nothing: `AlreadyExists` if it is there, and a
/// crash at any instant leaves it absent or complete (CLIENT-39, A18: written in place, a crash right
/// after the create left an empty `rotation` that refused every later command).
pub(crate) fn create_once(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let tmp = staged(dir, name, bytes)?;
    let linked = fs::hard_link(&tmp, dir.join(name));
    fs::remove_file(&tmp)?;
    linked?;
    sync_dir(dir)
}

/// Replace `dir/name` by a file holding exactly `bytes`, atomically: a reader (or a crash) sees
/// the old file or the new one, never a mix.
pub(crate) fn replace(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let tmp = staged(dir, name, bytes)?;
    fs::rename(&tmp, dir.join(name))?;
    sync_dir(dir)
}

/// `dir/.name.tmp` holding exactly `bytes`, synced; a leftover from a crash is removed first.
fn staged(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<std::path::PathBuf> {
    let tmp = dir.join(format!(".{name}.tmp"));
    match fs::remove_file(&tmp) {
        Err(e) if e.kind() != io::ErrorKind::NotFound => return Err(e),
        _ => {}
    }
    write_new(&tmp, bytes)?;
    Ok(tmp)
}

/// Whether a directory entry is fsx's crash residue (`.NAME.tmp`), never a file of any layout.
pub(crate) fn is_residue(name: &str) -> bool {
    name.starts_with('.') && name.ends_with(".tmp")
}

/// Rename `dir/from` over `dir/to`, durably.
pub(crate) fn rename(dir: &Path, from: &str, to: &str) -> io::Result<()> {
    fs::rename(dir.join(from), dir.join(to))?;
    sync_dir(dir)
}

/// Remove `dir/name`, durably; absent is fine.
pub(crate) fn remove(dir: &Path, name: &str) -> io::Result<()> {
    match fs::remove_file(dir.join(name)) {
        Err(e) if e.kind() != io::ErrorKind::NotFound => Err(e),
        _ => sync_dir(dir),
    }
}

fn write_new(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(PRIVATE)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()
}

/// Make the directory entries of `dir` durable.
pub(crate) fn sync_dir(dir: &Path) -> io::Result<()> {
    File::open(dir)?.sync_all()
}
