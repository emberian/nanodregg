//! Durable files. Every workspace write goes through here: a file is created with `O_EXCL` and mode
//! 0600, written whole, synced, and its directory synced, so a crash leaves it either absent or
//! complete-and-durable. `replace` is the one overwrite: a complete new file renamed over the old.
//! Custody files are read by `nanodregg_sandbox::custody`, the one read every key holder shares.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;

pub(crate) use nanodregg_sandbox::custody::PRIVATE;

/// Create `dir/name` holding exactly `bytes`; `AlreadyExists` if it is there.
pub(crate) fn create_once(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    write_new(&dir.join(name), bytes)?;
    sync_dir(dir)
}

/// Replace `dir/name` by a file holding exactly `bytes`, atomically: a reader (or a crash) sees
/// the old file or the new one, never a mix.
pub(crate) fn replace(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let tmp = dir.join(format!(".{name}.tmp"));
    // A leftover from a crash mid-replace is ours and incomplete by construction.
    match fs::remove_file(&tmp) {
        Err(e) if e.kind() != io::ErrorKind::NotFound => return Err(e),
        _ => {}
    }
    write_new(&tmp, bytes)?;
    fs::rename(&tmp, dir.join(name))?;
    sync_dir(dir)
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
