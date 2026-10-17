//! The one read of a custody file, shared by every process that holds a key: the member client's
//! seed and holding (CLIENT-13) and the operator's provider-key broker (HOSTING-12). A custody file
//! is read without following a link and refused unless every directory above it is the euid's or
//! root's and writable by no one else, and it is a regular file owned by the effective
//! user, mode exactly 0600, and of a length the caller allows. The bytes are zeroized on drop.
//! `read_public` is the same read for a public file custody's integrity depends on (trust
//! anchors): the same checks, but any mode without a group or other write bit.
//! Each refusal is a name (`Refused`); the caller renders it, nothing here decides what the bytes
//! mean.

use std::fs::{self, File};
use std::io::{self, Read};
use std::ops::RangeInclusive;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

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
    /// A directory on its canonical path (this one) is neither the euid's nor root's, or has a
    /// group or other write bit: whoever can write it can swap the file (sshd's StrictModes).
    Dir(PathBuf),
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

/// Every directory from `dir` (canonical) up to `/` is owned by the euid or root and has no group
/// or other write bit. A sticky world-writable directory (`/tmp`) is refused too, as sshd does.
fn check_chain(dir: &Path) -> Result<(), Refused> {
    chain(dir, None).map_err(|e| match e {
        Ok(d) => Refused::Dir(d),
        Err(e) => Refused::Io(e),
    })
}

/// The one directory-chain walk (sshd's StrictModes): every directory from `dir` (canonical) up to
/// `/` is owned by root, the euid or `also` (a connect socket's owner, HOSTING-17), with no group or
/// other write bit. `Err(Ok(d))` names the first directory that fails; `Err(Err(e))` is the IO.
pub(crate) fn chain(dir: &Path, also: Option<u32>) -> Result<(), Result<PathBuf, io::Error>> {
    let euid = rustix::process::geteuid().as_raw();
    for d in dir.ancestors() {
        let m = fs::metadata(d).map_err(Err)?;
        let owner = m.uid() == 0 || m.uid() == euid || Some(m.uid()) == also;
        if !owner || m.permissions().mode() & 0o022 != 0 {
            return Err(Ok(d.to_path_buf()));
        }
    }
    Ok(())
}

/// `path` with its parent canonicalized, once the parent chain passes `check_chain`: the file is
/// then opened through directories that were checked, so a symlinked component swapped after the
/// check cannot redirect the open.
fn trusted(path: &Path) -> Result<PathBuf, Refused> {
    let Some(name) = path.file_name() else {
        return Err(Refused::NotRegular);
    };
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let parent = parent.canonicalize().map_err(Refused::Io)?;
    check_chain(&parent)?;
    Ok(parent.join(name))
}

/// Read `path` under the checks every custody read shares: its parent chain (`check_chain`), not a link, a regular file, owned by
/// the effective user, a mode `ok` accepts, a length `lens` holds. A FIFO is refused, never
/// waited on (`O_NONBLOCK`); a file that grows while read is refused `Length`. The bytes are read
/// into `bytes`, which the caller allocates (zeroizing for a secret).
fn read_checked<B: AsMut<Vec<u8>>>(
    path: &Path,
    lens: RangeInclusive<usize>,
    ok: impl Fn(u32) -> bool,
    mut bytes: B,
) -> Result<B, Refused> {
    let path = trusted(path)?;
    let fd = rustix::fs::open(
        &path,
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

/// Refused unless `dir`'s parent chain passes, and it is a directory (not a link), owned by the
/// effective user, mode 0700.
pub fn check_private_dir(dir: &Path) -> Result<(), Refused> {
    let dir = trusted(dir)?;
    let meta = fs::symlink_metadata(&dir).map_err(Refused::Io)?;
    if meta.file_type().is_symlink() {
        return Err(Refused::Link);
    }
    if !meta.file_type().is_dir() {
        return Err(Refused::NotRegular);
    }
    owned(&meta, |m| m == PRIVATE_DIR)
}

/// The mode of a directory shared with one group (HOSTING-17's SOCKDIR and each per-resident
/// directory under it): owner rwx, group search only, setgid so what is made inside keeps the group.
pub const SHARED_DIR: u32 = 0o2710;

/// Refused unless `dir`'s parent chain passes, and it is a directory (not a link), owned by the
/// effective user, mode exactly [`SHARED_DIR`]. Returns its group, which the caller requires of
/// every directory it makes inside (HOSTING-17).
pub fn check_shared_dir(dir: &Path) -> Result<u32, Refused> {
    let dir = trusted(dir)?;
    let meta = fs::symlink_metadata(&dir).map_err(Refused::Io)?;
    if meta.file_type().is_symlink() {
        return Err(Refused::Link);
    }
    if !meta.file_type().is_dir() {
        return Err(Refused::NotRegular);
    }
    owned(&meta, |m| m == SHARED_DIR)?;
    Ok(meta.gid())
}

/// The connected peer's `(uid, gid)` as the kernel recorded them at connect (`SO_PEERCRED`), for a
/// server that admits one uid and one group (keybroker, HOSTING-17). macOS (`getpeereid`) is not
/// reached through rustix here: it is `Unsupported`, declared, never guessed.
#[cfg(target_os = "linux")]
pub fn peer_cred(s: &std::os::unix::net::UnixStream) -> io::Result<(u32, u32)> {
    let c = rustix::net::sockopt::socket_peercred(s)?;
    Ok((c.uid.as_raw(), c.gid.as_raw()))
}

/// See the Linux row.
#[cfg(not(target_os = "linux"))]
pub fn peer_cred(_: &std::os::unix::net::UnixStream) -> io::Result<(u32, u32)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "peer_cred: no SO_PEERCRED on this platform",
    ))
}
