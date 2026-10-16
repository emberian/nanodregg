//! Custody of one member key: a 32-byte seed in a file only its owner can read.
//!
//! The seed file is opened without following links and refused unless it is a regular file of
//! exactly 32 bytes, mode 0600, owned by the effective user. The seed lives in zeroizing memory.
//! Custody signs the bytes it is handed and adds nothing: what may be signed is decided by the
//! consent provider (Lean), which re-derives every header before custody sees it.

use std::fs::File;
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;

use ed25519_dalek::{Signer as _, SigningKey};
use rustix::fs::{Mode, OFlags};
use zeroize::Zeroizing;

use crate::fsx;

/// Seed length in bytes.
pub const SEED_BYTES: usize = 32;

/// Why custody refused.
#[derive(Debug)]
pub enum CustodyError {
    /// The seed file is a link, a directory or another non-regular file.
    NotRegularFile,
    /// The seed file is not exactly [`SEED_BYTES`] long.
    WrongLength {
        /// Its length.
        len: u64,
    },
    /// The seed file is readable or writable by someone other than its owner.
    Permissions {
        /// Its permission bits.
        mode: u32,
    },
    /// The seed file belongs to another user.
    Owner {
        /// Its owner.
        uid: u32,
        /// The effective user of this process.
        euid: u32,
    },
    /// A seed file already exists where a new one was asked for.
    Exists,
    /// The file system failed.
    Io(io::Error),
}

impl std::fmt::Display for CustodyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotRegularFile => write!(f, "custody: seed is not a regular file"),
            Self::WrongLength { len } => write!(f, "custody: seed is {len} bytes, not {SEED_BYTES}"),
            Self::Permissions { mode } => write!(f, "custody: seed mode {mode:o}, not 600"),
            Self::Owner { uid, euid } => write!(f, "custody: seed owned by uid {uid}, not {euid}"),
            Self::Exists => write!(f, "custody: a seed already exists"),
            Self::Io(e) => write!(f, "custody: {e}"),
        }
    }
}

impl std::error::Error for CustodyError {}

impl From<io::Error> for CustodyError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

/// A loaded member key. Dropping it zeroizes the seed.
pub struct Custody {
    key: SigningKey,
}

impl Custody {
    /// Create a fresh seed at `dir/name` from the operating system's random source.
    pub fn create(dir: &Path, name: &str) -> Result<(), CustodyError> {
        let mut seed = Zeroizing::new([0u8; SEED_BYTES]);
        File::open("/dev/urandom")?.read_exact(seed.as_mut())?;
        fsx::create_once(dir, name, seed.as_ref()).map_err(|e| match e.kind() {
            io::ErrorKind::AlreadyExists => CustodyError::Exists,
            _ => CustodyError::Io(e),
        })
    }

    /// Open the seed at `path` under the custody checks.
    pub fn open(path: &Path) -> Result<Self, CustodyError> {
        let fd = rustix::fs::open(path, OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC, Mode::empty())
            .map_err(|e| match e {
                rustix::io::Errno::LOOP => CustodyError::NotRegularFile,
                e => CustodyError::Io(e.into()),
            })?;
        let mut file = File::from(fd);
        let meta = file.metadata()?;
        if !meta.file_type().is_file() {
            return Err(CustodyError::NotRegularFile);
        }
        let mode = meta.permissions().mode() & 0o7777;
        if mode != fsx::PRIVATE {
            return Err(CustodyError::Permissions { mode });
        }
        let euid = rustix::process::geteuid().as_raw();
        if meta.uid() != euid {
            return Err(CustodyError::Owner { uid: meta.uid(), euid });
        }
        if meta.len() != SEED_BYTES as u64 {
            return Err(CustodyError::WrongLength { len: meta.len() });
        }
        let mut seed = Zeroizing::new([0u8; SEED_BYTES]);
        file.read_exact(seed.as_mut())?;
        let mut extra = [0u8; 1];
        if file.read(&mut extra)? != 0 {
            return Err(CustodyError::WrongLength { len: SEED_BYTES as u64 + 1 });
        }
        Ok(Self { key: SigningKey::from_bytes(&seed) })
    }

    /// The public key consent and the Host know this member by.
    pub fn public_key(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    /// Sign `message` exactly as given.
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        self.key.sign(message).to_bytes()
    }
}
