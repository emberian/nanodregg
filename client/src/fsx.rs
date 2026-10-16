//! Durable, create-once files. Every workspace write goes through here: the file is created with
//! `O_EXCL` and mode 0600, written whole, synced, and its directory synced, so a crash leaves the
//! file either absent or complete-and-durable, and an existing file is never overwritten.

use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;

/// Owner read/write only.
pub(crate) const PRIVATE: u32 = 0o600;

/// Create `dir/name` holding exactly `bytes`; `AlreadyExists` if it is there.
pub(crate) fn create_once(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).mode(PRIVATE).open(dir.join(name))?;
    file.write_all(bytes)?;
    file.sync_all()?;
    sync_dir(dir)
}

/// Make the directory entries of `dir` durable.
pub(crate) fn sync_dir(dir: &Path) -> io::Result<()> {
    File::open(dir)?.sync_all()
}
