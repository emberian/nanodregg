//! Custody of one member's keys (CLIENT-13, ruled by Ember 2026-10-16): the CURRENT key signs every
//! call; the precommitted NEXT key signs only the `rotate` that makes it current (KERNEL-6). The
//! next key is fresh OS randomness born at precommit, never derivable from the current one, held
//! where a theft of the workspace does not reach it:
//! - [`Separate`] (a member): `ws/seed` (current secret), `ws/next.pub` (next PUBLIC key), and the
//!   next secret in `HOLDING/next` (`HOLDING/pending` mid-rotation), on removable media or under
//!   another account, needed only to rotate.
//! - [`SameRecord`] (a hosted resident, which has no offline): `ws/keys = current ‖ next
//!   [‖ pending]`, replaced atomically; a thief of it has both keys, so for it the `rotate` row
//!   holds only against a leak of the current key alone.
//!
//! Every custody file is read under the custody checks and written durably (`fsx`). Custody signs
//! the bytes it is handed (what is signed is follow's decision) and advances ONLY on its own
//! settlement of the rotate call (`settle`), never on a follow verb; each advance step is guarded by
//! the rotation's public keys, so a crash anywhere is finished by the next `settle`.

use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

use ed25519_dalek::{Signer as _, SigningKey};
use zeroize::Zeroizing;

use crate::fsx;
pub use crate::fsx::Refused;
use crate::generated::layout::SignResult;

/// Seed length in bytes.
pub const SEED_BYTES: usize = 32;

/// An Ed25519 public key.
pub type Public = [u8; 32];

/// Why custody refused.
#[derive(Debug)]
pub enum CustodyError {
    /// A custody file or the holding directory failed the custody checks.
    File(PathBuf, Refused),
    /// A key file already exists where a new one was asked for.
    Exists,
    /// The workspace has both custody shapes (`seed` and `keys`), or neither.
    Shape,
    /// The separate holding is not named (`ND_HOLDING`) or not present.
    HoldingAbsent,
    /// `signNext` without a precommitted pending key.
    NoPending,
    /// A rotation is already armed; it is settled first.
    RotationInFlight,
    /// A key file disagrees with the keys the rotation or the workspace names.
    Mismatch(&'static str),
    /// The file system failed.
    Io(io::Error),
}

impl std::fmt::Display for CustodyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File(p, Refused::Mode(m)) => write!(f, "custody: {}: mode {m:o}", p.display()),
            Self::File(p, r) => write!(f, "custody: {}: {r:?}", p.display()),
            Self::Mismatch(w) => write!(f, "custody: mismatch: {w}"),
            Self::Io(e) => write!(f, "custody: {e}"),
            e => write!(f, "custody: {e:?}"),
        }
    }
}

impl std::error::Error for CustodyError {}

impl From<io::Error> for CustodyError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

fn refused(path: &Path, r: Refused) -> CustodyError {
    CustodyError::File(path.to_path_buf(), r)
}

fn read(path: &Path, lens: &[usize]) -> Result<Zeroizing<Vec<u8>>, CustodyError> {
    fsx::read_private(path, lens).map_err(|r| refused(path, r))
}

/// `Ok(None)` when the file does not exist.
fn read_optional(path: &Path, len: usize) -> Result<Option<Zeroizing<Vec<u8>>>, CustodyError> {
    match fsx::read_private(path, &[len]) {
        Err(Refused::Io(e)) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        r => r.map(Some).map_err(|r| refused(path, r)),
    }
}

fn key(seed: &[u8]) -> SigningKey {
    let mut s = Zeroizing::new([0u8; SEED_BYTES]);
    s.copy_from_slice(&seed[..SEED_BYTES]);
    SigningKey::from_bytes(&s)
}

fn public(k: &SigningKey) -> Public {
    k.verifying_key().to_bytes()
}

fn fresh_seed() -> Result<Zeroizing<[u8; SEED_BYTES]>, CustodyError> {
    let mut seed = Zeroizing::new([0u8; SEED_BYTES]);
    File::open("/dev/urandom")?.read_exact(seed.as_mut())?;
    Ok(seed)
}

fn exists(e: io::Error) -> CustodyError {
    match e.kind() {
        io::ErrorKind::AlreadyExists => CustodyError::Exists,
        _ => CustodyError::Io(e),
    }
}

/// Where the current, next and pending keys live. Two implementations: [`Separate`] and
/// [`SameRecord`]. Each transition is durable before it returns and idempotent.
pub trait Keys {
    /// The key that signs every call.
    fn current(&self) -> Result<SigningKey, CustodyError>;
    /// The precommitted next key's public half (no holding needed).
    fn next_public(&self) -> Result<Public, CustodyError>;
    /// The precommitted next key itself (the holding must be present).
    fn next(&self) -> Result<SigningKey, CustodyError>;
    /// The key minted for the rotation after the next one, if any.
    fn pending(&self) -> Result<Option<SigningKey>, CustodyError>;
    /// Store `seed` as the pending key; `Exists` if one is there.
    fn mint_pending(&self, seed: &[u8; SEED_BYTES]) -> Result<(), CustodyError>;
    /// `current := next`, `next := pending`, where next is `r.incoming` and pending `r.pending`.
    fn advance(&self, r: &Rotation) -> Result<(), CustodyError>;
    /// Forget the pending key if it is `pending`.
    fn drop_pending(&self, pending: &Public) -> Result<(), CustodyError>;
}

/// A member's keys: the current one in the workspace, the next one in a separate holding.
pub struct Separate {
    ws: PathBuf,
    holding: Option<PathBuf>,
}

impl Separate {
    fn holding(&self) -> Result<&Path, CustodyError> {
        let h = self.holding.as_deref().ok_or(CustodyError::HoldingAbsent)?;
        match fsx::check_private_dir(h) {
            Err(Refused::Io(e)) if e.kind() == io::ErrorKind::NotFound => {
                Err(CustodyError::HoldingAbsent)
            }
            r => r.map_err(|r| refused(h, r)),
        }?;
        Ok(h)
    }
}

impl Keys for Separate {
    fn current(&self) -> Result<SigningKey, CustodyError> {
        Ok(key(&read(&self.ws.join("seed"), &[SEED_BYTES])?))
    }
    fn next_public(&self) -> Result<Public, CustodyError> {
        let b = read(&self.ws.join("next.pub"), &[32])?;
        Ok(key_bytes(&b))
    }
    fn next(&self) -> Result<SigningKey, CustodyError> {
        let next = key(&read(&self.holding()?.join("next"), &[SEED_BYTES])?);
        if public(&next) != self.next_public()? {
            return Err(CustodyError::Mismatch("holding next ≠ workspace next.pub"));
        }
        Ok(next)
    }
    fn pending(&self) -> Result<Option<SigningKey>, CustodyError> {
        Ok(read_optional(&self.holding()?.join("pending"), SEED_BYTES)?.map(|s| key(&s)))
    }
    fn mint_pending(&self, seed: &[u8; SEED_BYTES]) -> Result<(), CustodyError> {
        fsx::create_once(self.holding()?, "pending", seed).map_err(exists)
    }
    fn advance(&self, r: &Rotation) -> Result<(), CustodyError> {
        if public(&self.current()?) != r.incoming {
            let next = self.next()?;
            if public(&next) != r.incoming {
                return Err(CustodyError::Mismatch("next ≠ the rotation's incoming key"));
            }
            fsx::replace(&self.ws, "seed", next.as_bytes())?;
        }
        if self.next_public()? != r.pending {
            fsx::replace(&self.ws, "next.pub", &r.pending)?;
        }
        let h = self.holding()?;
        let held = key(&read(&h.join("next"), &[SEED_BYTES])?);
        if public(&held) == r.incoming {
            match self.pending()? {
                Some(p) if public(&p) == r.pending => fsx::rename(h, "pending", "next")?,
                _ => return Err(CustodyError::Mismatch("pending ≠ the rotation's")),
            }
        } else if public(&held) != r.pending {
            return Err(CustodyError::Mismatch("holding next is neither key"));
        }
        Ok(())
    }
    fn drop_pending(&self, pending: &Public) -> Result<(), CustodyError> {
        match self.pending()? {
            Some(p) if public(&p) == *pending => Ok(fsx::remove(self.holding()?, "pending")?),
            _ => Ok(()),
        }
    }
}

fn key_bytes(b: &[u8]) -> Public {
    let mut p = [0u8; 32];
    p.copy_from_slice(&b[..32]);
    p
}

/// A hosted resident's keys: one record `ws/keys = current ‖ next [‖ pending]`.
pub struct SameRecord {
    ws: PathBuf,
}

impl SameRecord {
    fn record(&self) -> Result<Zeroizing<Vec<u8>>, CustodyError> {
        read(&self.ws.join("keys"), &[2 * SEED_BYTES, 3 * SEED_BYTES])
    }
    fn seed(&self, i: usize) -> Result<Option<SigningKey>, CustodyError> {
        let r = self.record()?;
        Ok(r.get(i * SEED_BYTES..(i + 1) * SEED_BYTES).map(key))
    }
    fn write(&self, keys: &[&SigningKey]) -> Result<(), CustodyError> {
        let bytes = Zeroizing::new(keys.iter().flat_map(|k| *k.as_bytes()).collect::<Vec<_>>());
        Ok(fsx::replace(&self.ws, "keys", &bytes)?)
    }
}

impl Keys for SameRecord {
    fn current(&self) -> Result<SigningKey, CustodyError> {
        self.seed(0)?.ok_or(CustodyError::Shape)
    }
    fn next_public(&self) -> Result<Public, CustodyError> {
        Ok(public(&self.next()?))
    }
    fn next(&self) -> Result<SigningKey, CustodyError> {
        self.seed(1)?.ok_or(CustodyError::Shape)
    }
    fn pending(&self) -> Result<Option<SigningKey>, CustodyError> {
        self.seed(2)
    }
    fn mint_pending(&self, seed: &[u8; SEED_BYTES]) -> Result<(), CustodyError> {
        if self.pending()?.is_some() {
            return Err(CustodyError::Exists);
        }
        self.write(&[&self.current()?, &self.next()?, &key(seed)])
    }
    fn advance(&self, r: &Rotation) -> Result<(), CustodyError> {
        let (current, next) = (self.current()?, self.next()?);
        if public(&current) == r.incoming && public(&next) == r.pending {
            return Ok(()); // already advanced
        }
        match self.pending()? {
            Some(p) if public(&next) == r.incoming && public(&p) == r.pending => {
                self.write(&[&next, &p])
            }
            _ => Err(CustodyError::Mismatch("record ≠ the rotation's keys")),
        }
    }
    fn drop_pending(&self, pending: &Public) -> Result<(), CustodyError> {
        match self.pending()? {
            Some(p) if public(&p) == *pending => self.write(&[&self.current()?, &self.next()?]),
            _ => Ok(()),
        }
    }
}

/// A rotation in flight: the incoming (next) key that signs it and the pending key it precommits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rotation {
    /// The next key, becoming current.
    pub incoming: Public,
    /// The pending key, becoming next.
    pub pending: Public,
}

/// The armed rotation's record in the workspace: `u64le attempt ‖ incoming ‖ pending`.
const ROTATION: &str = "rotation";

/// A member's custody over its workspace.
pub struct Custody {
    ws: PathBuf,
    keys: Box<dyn Keys>,
}

impl Custody {
    /// A new member: `ws/seed` and `ws/next.pub`, the next secret in `holding/next` (a directory,
    /// mode 0700, that must exist). Refuses if any of them exists.
    pub fn create_separate(ws: &Path, holding: &Path) -> Result<(), CustodyError> {
        fsx::check_private_dir(holding).map_err(|r| refused(holding, r))?;
        let (current, next) = (fresh_seed()?, fresh_seed()?);
        fsx::create_once(holding, "next", next.as_ref()).map_err(exists)?;
        fsx::create_once(ws, "next.pub", &public(&key(next.as_ref()))).map_err(exists)?;
        fsx::create_once(ws, "seed", current.as_ref()).map_err(exists)
    }

    /// A new hosted resident: `ws/keys = current ‖ next`.
    pub fn create_same_record(ws: &Path) -> Result<(), CustodyError> {
        let (current, next) = (fresh_seed()?, fresh_seed()?);
        let bytes = Zeroizing::new([current.as_ref(), next.as_ref()].concat());
        fsx::create_once(ws, "keys", &bytes).map_err(exists)
    }

    /// Open the workspace's custody: `Separate` if `ws/seed` exists (the holding is needed only
    /// to rotate), `SameRecord` if `ws/keys` does; both or neither is `Shape`.
    pub fn open(ws: &Path, holding: Option<PathBuf>) -> Result<Self, CustodyError> {
        let keys: Box<dyn Keys> = match (ws.join("seed").exists(), ws.join("keys").exists()) {
            (true, false) => Box::new(Separate {
                ws: ws.to_path_buf(),
                holding,
            }),
            (false, true) => Box::new(SameRecord {
                ws: ws.to_path_buf(),
            }),
            _ => return Err(CustodyError::Shape),
        };
        let c = Self {
            ws: ws.to_path_buf(),
            keys,
        };
        c.keys.current()?;
        c.keys.next_public()?;
        Ok(c)
    }

    /// The current public key.
    pub fn public_key(&self) -> Result<Public, CustodyError> {
        Ok(public(&self.keys.current()?))
    }

    /// The precommitted next public key.
    pub fn next_public_key(&self) -> Result<Public, CustodyError> {
        self.keys.next_public()
    }

    /// A `sign` step's result: the current key, the next key, the current key's signature over
    /// exactly `message`.
    pub fn sign(&self, message: &[u8]) -> Result<SignResult, CustodyError> {
        let k = self.keys.current()?;
        Ok(SignResult {
            key: public(&k).to_vec(),
            next: self.keys.next_public()?.to_vec(),
            signature: k.sign(message).to_bytes().to_vec(),
        })
    }

    /// `(next, pending)`: the pending key is minted from OS randomness and stored durably unless
    /// one already exists, which is returned instead (idempotent: a retried command never mints a
    /// second one, so no frozen rotate call names a key custody lost).
    pub fn precommit(&self) -> Result<(Public, Public), CustodyError> {
        let next = self.keys.next_public()?;
        if let Some(p) = self.keys.pending()? {
            return Ok((next, public(&p)));
        }
        let seed = fresh_seed()?;
        self.keys.mint_pending(&seed)?;
        Ok((next, public(&key(&*seed))))
    }

    /// A `signNext` step's result: the next key signs exactly `message`, and the result names the
    /// pending key as its next. Refused while a rotation is armed or with nothing precommitted.
    pub fn sign_next(&self, message: &[u8]) -> Result<(SignResult, Rotation), CustodyError> {
        if self.armed()?.is_some() {
            return Err(CustodyError::RotationInFlight);
        }
        let next = self.keys.next()?;
        let pending = self.keys.pending()?.ok_or(CustodyError::NoPending)?;
        let r = Rotation {
            incoming: public(&next),
            pending: public(&pending),
        };
        let result = SignResult {
            key: r.incoming.to_vec(),
            next: r.pending.to_vec(),
            signature: next.sign(message).to_bytes().to_vec(),
        };
        Ok((result, r))
    }

    /// Record that attempt `n` carries rotation `r`, durably, before the attempt is first sent.
    pub fn arm(&self, n: u64, r: &Rotation) -> Result<(), CustodyError> {
        let bytes = [&n.to_le_bytes()[..], &r.incoming, &r.pending].concat();
        fsx::create_once(&self.ws, ROTATION, &bytes).map_err(|e| match e.kind() {
            io::ErrorKind::AlreadyExists => CustodyError::RotationInFlight,
            _ => CustodyError::Io(e),
        })
    }

    /// The armed rotation and its attempt number, if any.
    pub fn armed(&self) -> Result<Option<(u64, Rotation)>, CustodyError> {
        let Some(b) = read_optional(&self.ws.join(ROTATION), 72)? else {
            return Ok(None);
        };
        let mut n = [0u8; 8];
        n.copy_from_slice(&b[..8]);
        let r = Rotation {
            incoming: key_bytes(&b[8..40]),
            pending: key_bytes(&b[40..72]),
        };
        Ok(Some((u64::from_le_bytes(n), r)))
    }

    /// The armed rotation's attempt settled: committed advances the keys, a definitive refusal
    /// drops the pending key; then the arm is cleared. Idempotent (each step is guarded).
    pub fn settle(&self, committed: bool) -> Result<(), CustodyError> {
        let Some((_, r)) = self.armed()? else {
            return Ok(());
        };
        if committed {
            self.keys.advance(&r)?;
        } else {
            self.keys.drop_pending(&r.pending)?;
        }
        Ok(fsx::remove(&self.ws, ROTATION)?)
    }
}
