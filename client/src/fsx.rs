//! Durable files. Every workspace write goes through here: a file is created with `O_EXCL` and mode
//! 0600, written whole, synced, and its directory synced, so a crash leaves it either absent or
//! complete-and-durable. `replace` is the one overwrite: a complete new file renamed over the old.
//! `read_private` is the one read of a custody file, under the custody checks.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::Path;

use rustix::fs::{Mode, OFlags};
use zeroize::Zeroizing;

/// Owner read/write only.
pub(crate) const PRIVATE: u32 = 0o600;

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

/// Why a custody file (or the holding directory) was refused.
#[derive(Debug)]
pub enum Refused {
    /// A link, or not the kind of file asked for.
    NotRegular,
    /// Its mode is not owner-only.
    Mode(u32),
    /// It belongs to another user.
    Owner(u32),
    /// Its length is none of the allowed ones.
    Length(u64),
    /// The file system failed (`NotFound` included).
    Io(io::Error),
}

/// Owner-only (`mode`) and owned by the effective user.
fn private(meta: &fs::Metadata, mode: u32) -> Result<(), Refused> {
    match (meta.permissions().mode() & 0o7777, meta.uid()) {
        (m, _) if m != mode => Err(Refused::Mode(m)),
        (_, u) if u != rustix::process::geteuid().as_raw() => Err(Refused::Owner(u)),
        _ => Ok(()),
    }
}

/// Read `path` without following a link, refused unless it is a regular file, mode 0600, owned by
/// the effective user, and exactly one of `lens` bytes long. The bytes are zeroized on drop.
pub(crate) fn read_private(path: &Path, lens: &[usize]) -> Result<Zeroizing<Vec<u8>>, Refused> {
    let fd = rustix::fs::open(
        path,
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|e| match e {
        rustix::io::Errno::LOOP => Refused::NotRegular,
        e => Refused::Io(e.into()),
    })?;
    let mut file = File::from(fd);
    let meta = file.metadata().map_err(Refused::Io)?;
    if !meta.file_type().is_file() {
        return Err(Refused::NotRegular);
    }
    private(&meta, PRIVATE)?;
    if !lens.iter().any(|&n| n as u64 == meta.len()) {
        return Err(Refused::Length(meta.len()));
    }
    let mut bytes = Zeroizing::new(vec![0u8; meta.len() as usize]);
    file.read_exact(&mut bytes).map_err(Refused::Io)?;
    if file.read(&mut [0u8; 1]).map_err(Refused::Io)? != 0 {
        return Err(Refused::Length(meta.len() + 1));
    }
    Ok(bytes)
}

/// Refused unless `dir` is a real directory (not a link), mode 0700, owned by the effective user.
pub(crate) fn check_private_dir(dir: &Path) -> Result<(), Refused> {
    let meta = fs::symlink_metadata(dir).map_err(Refused::Io)?;
    if !meta.file_type().is_dir() {
        return Err(Refused::NotRegular);
    }
    private(&meta, 0o700)
}
