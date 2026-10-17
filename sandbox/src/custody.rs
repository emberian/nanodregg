//! The one read of a custody file, shared by every process that holds a key: the member client's
//! seed and holding (CLIENT-13) and the operator's provider-key broker (HOSTING-12). A custody file
//! is read without following a link and refused unless it is a regular file owned by the effective
//! user, mode exactly 0600, and of a length the caller allows. The bytes are zeroized on drop.
//! `read_public` is the same read for a public file custody's integrity depends on (trust
//! anchors): the same checks, but any mode without a group or other write bit.
//! Each refusal is a name (`Refused`); the caller renders it, nothing here decides what the bytes
//! mean.

use std::fs::{self, File};
use std::io::{self, Read};
use std::ops::RangeInclusive;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;

use rustix::fs::{Mode, OFlags};
use zeroize::Zeroizing;

/// Owner read/write only: the mode a custody file is created with and the only one it is read at.
pub const PRIVATE: u32 = 0o600;

/// Owner-only directory mode (a member's separate holding).
pub const PRIVATE_DIR: u32 = 0o700;

/// Why a custody file (or a holding directory) was refused.
#[derive(Debug)]
pub enum Refused {
    /// The path is a symbolic link.
    Link,
    /// Not the kind of file asked for (a directory, a device, a socket).
    NotRegular,
    /// It belongs to another user (this uid).
    Owner(u32),
    /// Its mode is not the owner-only one.
    Mode(u32),
    /// Its length is outside the allowed range.
    Length(u64),
    /// The file system failed (`NotFound` included).
    Io(io::Error),
}

/// Owned by the effective user, then a mode `ok` accepts.
fn owned(meta: &fs::Metadata, ok: impl Fn(u32) -> bool) -> Result<(), Refused> {
    match (meta.uid(), meta.permissions().mode() & 0o7777) {
        (u, _) if u != rustix::process::geteuid().as_raw() => Err(Refused::Owner(u)),
        (_, m) if !ok(m) => Err(Refused::Mode(m)),
        _ => Ok(()),
    }
}

/// Read `path` under the checks every custody read shares: not a link, a regular file, owned by
/// the effective user, a mode `ok` accepts, a length `lens` holds. A FIFO is refused, never
/// waited on (`O_NONBLOCK`); a file that grows while read is refused `Length`. The bytes are read
/// into `bytes`, which the caller allocates (zeroizing for a secret).
fn read_checked<B: AsMut<Vec<u8>>>(
    path: &Path,
    lens: RangeInclusive<usize>,
    ok: impl Fn(u32) -> bool,
    mut bytes: B,
) -> Result<B, Refused> {
    let fd = rustix::fs::open(
        path,
        OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .map_err(|e| match e {
        rustix::io::Errno::LOOP => Refused::Link,
        e => Refused::Io(e.into()),
    })?;
    let mut file = File::from(fd);
    let meta = file.metadata().map_err(Refused::Io)?;
    if !meta.file_type().is_file() {
        return Err(Refused::NotRegular);
    }
    owned(&meta, ok)?;
    let len = meta.len();
    if !usize::try_from(len).is_ok_and(|n| lens.contains(&n)) {
        return Err(Refused::Length(len));
    }
    let v = bytes.as_mut();
    v.resize(len as usize, 0);
    file.read_exact(v).map_err(Refused::Io)?;
    if file.read(&mut [0u8; 1]).map_err(Refused::Io)? != 0 {
        return Err(Refused::Length(len + 1));
    }
    Ok(bytes)
}

/// Read the custody file `path` (a secret): the shared checks, mode exactly 0600, zeroized.
pub fn read_private(
    path: &Path,
    lens: RangeInclusive<usize>,
) -> Result<Zeroizing<Vec<u8>>, Refused> {
    read_checked(path, lens, |m| m == PRIVATE, Zeroizing::new(Vec::new()))
}

/// Read a PUBLIC file whose integrity custody depends on (keybroker's TLS trust anchors,
/// HOSTING-15): the shared checks, and a mode with no group or other WRITE bit and no
/// setuid/setgid/sticky bit (`0644`, `0444` and `0600` pass; `0664`, `0646` do not). Its bytes
/// are not secret, so they are not zeroized.
pub fn read_public(path: &Path, lens: RangeInclusive<usize>) -> Result<Vec<u8>, Refused> {
    read_checked(path, lens, |m| m & PUBLIC_REFUSED == 0, Vec::new())
}

/// The mode bits `read_public` refuses: group/other write, setuid, setgid, sticky.
pub const PUBLIC_REFUSED: u32 = 0o7022;

/// Refused unless `dir` is a directory (not a link), owned by the effective user, mode 0700.
pub fn check_private_dir(dir: &Path) -> Result<(), Refused> {
    let meta = fs::symlink_metadata(dir).map_err(Refused::Io)?;
    if meta.file_type().is_symlink() {
        return Err(Refused::Link);
    }
    if !meta.file_type().is_dir() {
        return Err(Refused::NotRegular);
    }
    owned(&meta, |m| m == PRIVATE_DIR)
}
