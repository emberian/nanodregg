//! `Policy::connect` (HOSTING-17 §5, CLIENT-20): the unix sockets a confined child may connect to,
//! checked before any process exists. Both mechanisms filter the connect itself (macOS
//! `network-outbound` to exactly these paths; Linux the connector, CLIENT-48), so a file grant is
//! never a connect grant and a socket's directory needs no isolation from the other grants.

use std::fs;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

use crate::ConfineError;

/// At most this many connect entries (HOSTING-17 §5: the model driver reaches its broker socket and
/// its own `nd`; the resident's `nd` the host socket and its follow socket). A third is
/// `ConnectTooMany`.
pub const CONNECT_MAX: usize = 2;

/// Checks one connect entry and returns its canonical path and directory:
/// a socket (`ConnectLink` for a link, `ConnectNotSocket` otherwise), no other bits, and EITHER the
/// euid's at exactly 0600 OR another uid's with group = egid at exactly 0660 (`ConnectOwner`,
/// `ConnectMode`); every ancestor owned by root, the euid or the socket's owner, with no group or
/// other write bit (`ConnectDir`).
pub(crate) fn entry(p: &Path) -> Result<PathBuf, ConfineError> {
    let missing = |e| ConfineError::PathMissing(p.to_path_buf(), e);
    let (Some(name), Some(parent)) = (p.file_name(), p.parent()) else {
        return Err(ConfineError::ConnectNotSocket(p.to_path_buf()));
    };
    let dir = crate::canonical(parent)?;
    let sock = dir.join(name);
    let m = fs::symlink_metadata(&sock).map_err(missing)?;
    if m.file_type().is_symlink() {
        return Err(ConfineError::ConnectLink(sock));
    }
    if !m.file_type().is_socket() {
        return Err(ConfineError::ConnectNotSocket(sock));
    }
    let mode = m.permissions().mode() & 0o7777;
    let (euid, egid) = (
        rustix::process::geteuid().as_raw(),
        rustix::process::getegid().as_raw(),
    );
    let want = if m.uid() == euid {
        0o600
    } else if m.gid() == egid {
        0o660
    } else {
        return Err(ConfineError::ConnectOwner {
            path: sock,
            uid: m.uid(),
            gid: m.gid(),
        });
    };
    if mode != want {
        return Err(ConfineError::ConnectMode { path: sock, mode });
    }
    crate::custody::chain(&dir, Some(m.uid())).map_err(|e| match e {
        Ok(d) => ConfineError::ConnectDir(d),
        Err(e) => ConfineError::PathMissing(dir.clone(), e),
    })?;
    Ok(sock)
}
