//! Custody plants (CLIENT-13). A member's next secret is born fresh, lives only in its separate
//! holding (never in the workspace), and becomes current only when custody settles the rotate
//! committed; a refusal drops the pending key; every advance finishes after a crash; a tampered
//! next.pub or a second rotation is refused by name. The hosted one-record shape rotates the same
//! way. Every custody file is refused unless regular, 0600, the owner's, and exactly its length.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use ed25519_dalek::{Signature, VerifyingKey};
use nanodregg_client::custody::{Custody, CustodyError, Refused, Rotation};

fn scratch(name: &str) -> (PathBuf, PathBuf) {
    let d = nanodregg_devtools::scratch(&format!("nd-custody-{}-{name}", std::process::id()));
    let (ws, h) = (d.join("ws"), d.join("holding"));
    nanodregg_devtools::mkdirs(&ws).unwrap();
    nanodregg_devtools::mkdirs(&h).unwrap();
    fs::set_permissions(&h, fs::Permissions::from_mode(0o700)).unwrap();
    (ws, h)
}

fn done(ws: &Path) {
    fs::remove_dir_all(ws.parent().unwrap()).unwrap();
}

fn verifies(key: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let k = VerifyingKey::from_bytes(key.try_into().unwrap()).unwrap();
    k.verify_strict(msg, &Signature::from_slice(sig).unwrap())
        .is_ok()
}

fn files(dir: &Path) -> Vec<Vec<u8>> {
    fs::read_dir(dir)
        .unwrap()
        .map(|e| fs::read(e.unwrap().path()).unwrap_or_default())
        .collect()
}

#[test]
fn a_member_signs_with_current_names_next_and_never_holds_the_next_secret() {
    let (ws, h) = scratch("member");
    Custody::create_separate(&ws, &h).unwrap();
    assert!(matches!(
        Custody::create_separate(&ws, &h),
        Err(CustodyError::Exists)
    ));
    // Opened WITHOUT the holding: daily signing needs only the workspace.
    let c = Custody::open(&ws, None).unwrap();
    let s = c.sign(b"header").unwrap();
    assert_eq!(s.key, c.public_key().unwrap());
    assert_eq!(s.next, fs::read(ws.join("next.pub")).unwrap());
    assert!(verifies(&s.key, b"header", &s.signature));
    let next_secret = fs::read(h.join("next")).unwrap();
    assert!(
        files(&ws).iter().all(|f| *f != next_secret),
        "the next secret is in the workspace"
    );
    assert!(matches!(c.precommit(), Err(CustodyError::HoldingAbsent)));
    done(&ws);
}

#[test]
fn a_committed_rotation_advances_and_finishes_after_a_crash() {
    let (ws, h) = scratch("rotate");
    Custody::create_separate(&ws, &h).unwrap();
    let c = Custody::open(&ws, Some(h.clone())).unwrap();
    let (old_current, old_next) = (c.public_key().unwrap(), c.sign(b"").unwrap().next);
    let (next, pending) = c.precommit().unwrap();
    assert_eq!(
        c.precommit().unwrap(),
        (next, pending),
        "precommit is idempotent"
    );
    assert_eq!(next.to_vec(), old_next);
    let (s, r) = c.sign_next(b"rotate").unwrap();
    assert_eq!(
        (s.key.clone(), s.next.clone()),
        (next.to_vec(), pending.to_vec())
    );
    assert!(
        verifies(&next, b"rotate", &s.signature),
        "signed by the NEXT key"
    );
    c.arm(7, &r).unwrap();
    assert!(matches!(
        c.sign_next(b"x"),
        Err(CustodyError::RotationInFlight)
    ));
    assert_eq!(c.armed().unwrap(), Some((7, r)));
    // Not yet settled: still the old key.
    assert_eq!(c.public_key().unwrap(), old_current);
    // A crash after advance's first step: the seed already replaced, the holding not.
    fs::copy(h.join("next"), ws.join("seed")).unwrap();
    c.settle(true).unwrap();
    c.settle(true).unwrap(); // idempotent
    assert_eq!(c.public_key().unwrap(), next);
    assert_eq!(fs::read(ws.join("next.pub")).unwrap(), pending);
    assert!(!h.join("pending").exists() && !ws.join("rotation").exists());
    let held = fs::read(h.join("next")).unwrap();
    let held = ed25519_dalek::SigningKey::from_bytes(&held.try_into().unwrap());
    assert_eq!(
        held.verifying_key().to_bytes(),
        pending,
        "the holding holds the new next"
    );
    done(&ws);
}

#[test]
fn a_refused_rotation_drops_the_pending_key_and_keeps_the_keys() {
    let (ws, h) = scratch("refused");
    Custody::create_separate(&ws, &h).unwrap();
    let c = Custody::open(&ws, Some(h.clone())).unwrap();
    let before = (c.public_key().unwrap(), c.sign(b"").unwrap().next);
    let (_, pending) = c.precommit().unwrap();
    let (_, r) = c.sign_next(b"rotate").unwrap();
    c.arm(0, &r).unwrap();
    c.settle(false).unwrap();
    assert_eq!((c.public_key().unwrap(), c.sign(b"").unwrap().next), before);
    assert!(!h.join("pending").exists());
    assert_ne!(
        c.precommit().unwrap().1,
        pending,
        "a fresh pending key next time"
    );
    done(&ws);
}

#[test]
fn a_tampered_next_pub_is_refused() {
    let (ws, h) = scratch("tamper");
    Custody::create_separate(&ws, &h).unwrap();
    fs::write(ws.join("next.pub"), [7u8; 32]).unwrap();
    let c = Custody::open(&ws, Some(h)).unwrap();
    c.precommit().unwrap();
    assert!(matches!(
        c.sign_next(b"rotate"),
        Err(CustodyError::Mismatch(_))
    ));
    done(&ws);
}

#[test]
fn a_hosted_record_rotates_the_same_way() {
    let (ws, _) = scratch("hosted");
    Custody::create_same_record(&ws).unwrap();
    let c = Custody::open(&ws, None).unwrap();
    let (next, pending) = c.precommit().unwrap();
    assert_eq!(fs::metadata(ws.join("keys")).unwrap().len(), 96);
    let (s, r) = c.sign_next(b"rotate").unwrap();
    assert!(verifies(&next, b"rotate", &s.signature));
    c.arm(1, &r).unwrap();
    c.settle(true).unwrap();
    assert_eq!(c.public_key().unwrap(), next);
    assert_eq!(c.sign(b"").unwrap().next, pending);
    assert_eq!(fs::metadata(ws.join("keys")).unwrap().len(), 64);
    // A settle naming keys the record does not hold is refused, not applied.
    let wrong = Rotation {
        incoming: [1; 32],
        pending: [2; 32],
    };
    c.arm(2, &wrong).unwrap();
    assert!(matches!(c.settle(true), Err(CustodyError::Mismatch(_))));
    done(&ws);
}

#[test]
fn custody_files_are_refused_unless_private_regular_and_exact() {
    let (ws, h) = scratch("checks");
    Custody::create_separate(&ws, &h).unwrap();
    fs::set_permissions(ws.join("seed"), fs::Permissions::from_mode(0o640)).unwrap();
    assert!(matches!(
        Custody::open(&ws, None),
        Err(CustodyError::File(_, Refused::Mode(0o640)))
    ));
    fs::remove_file(ws.join("seed")).unwrap();
    std::os::unix::fs::symlink(h.join("next"), ws.join("seed")).unwrap();
    assert!(matches!(
        Custody::open(&ws, None),
        Err(CustodyError::File(_, Refused::Link))
    ));
    fs::remove_file(ws.join("seed")).unwrap();
    fs::write(ws.join("seed"), [0u8; 33]).unwrap();
    fs::set_permissions(ws.join("seed"), fs::Permissions::from_mode(0o600)).unwrap();
    assert!(matches!(
        Custody::open(&ws, None),
        Err(CustodyError::File(_, Refused::Length(33)))
    ));
    fs::write(ws.join("keys"), [0u8; 64]).unwrap();
    assert!(matches!(Custody::open(&ws, None), Err(CustodyError::Shape)));
    fs::set_permissions(&h, fs::Permissions::from_mode(0o755)).unwrap();
    assert!(matches!(
        Custody::create_separate(&ws, &h),
        Err(CustodyError::File(_, Refused::Mode(0o755)))
    ));
    done(&ws);
}

/// CLIENT-22: an observer record signs read envelopes only. A message that starts with the
/// emitted envelope domain is signed by the record's current key; any other message (a call's)
/// and every rotation step are refused `EnvelopeOnly`, and nothing in the record changes. The fence
/// is prefix-only until PROTOCOL-7's `envelope_call_disjoint` (call messages domain-separated).
#[test]
fn an_observer_signs_read_envelopes_only() {
    use nanodregg_client::generated::ENVELOPE_DOMAIN;
    let (ws, _) = scratch("observer");
    Custody::create_observer(&ws).unwrap();
    let before = fs::read(ws.join("observer")).unwrap();
    assert_eq!(before.len(), 64);
    let c = Custody::open(&ws, None).unwrap();
    let envelope = [ENVELOPE_DOMAIN, b"window"].concat();
    let s = c.sign(&envelope).unwrap();
    assert_eq!(s.key, c.public_key().unwrap().to_vec());
    assert!(verifies(&s.key, &envelope, &s.signature));
    for call in [&b"a call's unsigned bytes"[..], &ENVELOPE_DOMAIN[1..], b""] {
        assert!(matches!(c.sign(call), Err(CustodyError::EnvelopeOnly)));
    }
    assert!(matches!(c.precommit(), Err(CustodyError::EnvelopeOnly)));
    assert!(matches!(
        c.sign_next(&envelope),
        Err(CustodyError::EnvelopeOnly)
    ));
    assert_eq!(
        fs::read(ws.join("observer")).unwrap(),
        before,
        "the record never changed"
    );
    assert_eq!(
        CustodyError::EnvelopeOnly.refusal(),
        nanodregg_client::generated::CustodyRefusal::EnvelopeOnly
    );
    // One shape only: an observer beside a member's or a resident's keys is refused.
    fs::write(ws.join("keys"), [0u8; 64]).unwrap();
    assert!(matches!(Custody::open(&ws, None), Err(CustodyError::Shape)));
    fs::remove_file(ws.join("keys")).unwrap();
    // The record is read under the custody checks like every other.
    fs::set_permissions(ws.join("observer"), fs::Permissions::from_mode(0o640)).unwrap();
    assert!(matches!(
        Custody::open(&ws, None),
        Err(CustodyError::File(_, Refused::Mode(0o640)))
    ));
    done(&ws);
}

/// ROOT's ruling (A): a joined one-record custody signs anything (the control: it enrolls like any
/// member), then `seal_observer` RENAMES its record (same inode, same bytes, `next` kept) and from
/// then on it signs read envelopes only. A second seal is `Exists`; a seal with a rotation armed is
/// `RotationInFlight`; a member's separate custody cannot be sealed (`Shape`).
#[test]
fn a_joined_record_is_sealed_as_an_observer_by_one_rename() {
    use nanodregg_client::generated::ENVELOPE_DOMAIN;
    use std::os::unix::fs::MetadataExt;
    let (ws, h) = scratch("seal");
    Custody::create_same_record(&ws).unwrap();
    let c = Custody::open(&ws, None).unwrap();
    assert!(
        c.sign(b"a call").is_ok(),
        "control: unsealed, it signs a call"
    );
    let (key, next) = (c.public_key().unwrap(), c.next_public_key().unwrap());
    let (bytes, ino) = (
        fs::read(ws.join("keys")).unwrap(),
        fs::metadata(ws.join("keys")).unwrap().ino(),
    );
    Custody::seal_observer(&ws).unwrap();
    assert!(!ws.join("keys").exists());
    assert_eq!(
        fs::metadata(ws.join("observer")).unwrap().ino(),
        ino,
        "a rename, not a copy"
    );
    assert_eq!(fs::read(ws.join("observer")).unwrap(), bytes);
    let o = Custody::open(&ws, None).unwrap();
    assert_eq!(
        (o.public_key().unwrap(), o.next_public_key().unwrap()),
        (key, next)
    );
    assert!(matches!(o.sign(b"a call"), Err(CustodyError::EnvelopeOnly)));
    assert!(o.sign(&[ENVELOPE_DOMAIN, b"w"].concat()).is_ok());
    assert!(matches!(
        Custody::seal_observer(&ws),
        Err(CustodyError::Exists)
    ));
    done(&ws);
    // A seal with a rotation armed is refused by name.
    let (ws, _) = scratch("seal-armed");
    Custody::create_same_record(&ws).unwrap();
    let c = Custody::open(&ws, None).unwrap();
    c.arm(
        1,
        &Rotation {
            incoming: [1; 32],
            pending: [2; 32],
        },
    )
    .unwrap();
    assert!(matches!(
        Custody::seal_observer(&ws),
        Err(CustodyError::RotationInFlight)
    ));
    assert!(ws.join("keys").exists() && !ws.join("observer").exists());
    done(&ws);
    // A pending key minted (precommit before its rotate) is a rotation in progress too.
    let (ws, _) = scratch("seal-pending");
    Custody::create_same_record(&ws).unwrap();
    Custody::open(&ws, None).unwrap().precommit().unwrap();
    assert!(matches!(
        Custody::seal_observer(&ws),
        Err(CustodyError::RotationInFlight)
    ));
    done(&ws);
    // A member's separate custody is not a one-record custody.
    let (ws, h2) = scratch("seal-separate");
    Custody::create_separate(&ws, &h2).unwrap();
    assert!(matches!(
        Custody::seal_observer(&ws),
        Err(CustodyError::Shape)
    ));
    done(&ws);
    let _ = h;
}

/// CLIENT-24: the custody `nd --stdio` opens refuses precommit and signNext (`noRotation`), so a
/// resident's command can never rotate the key it runs under; it still signs.
#[test]
fn a_stdio_custody_signs_but_never_rotates() {
    let (ws, _) = scratch("stdio-custody");
    Custody::create_same_record(&ws).unwrap();
    let c = Custody::open(&ws, None).unwrap();
    assert!(
        c.precommit().is_ok(),
        "control: an ordinary custody precommits"
    );
    let (ws2, _) = scratch("stdio-custody-2");
    Custody::create_same_record(&ws2).unwrap();
    let c = Custody::open(&ws2, None).unwrap().refusing_rotation();
    assert!(c.sign(b"a call").is_ok());
    assert!(matches!(c.precommit(), Err(CustodyError::NoRotation)));
    assert!(matches!(
        c.sign_next(b"rotate"),
        Err(CustodyError::NoRotation)
    ));
    assert_eq!(
        fs::metadata(ws2.join("keys")).unwrap().len(),
        64,
        "no pending key minted"
    );
    done(&ws);
    done(&ws2);
}
