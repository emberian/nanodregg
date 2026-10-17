//! Attempt plants: a crash after the send marker reloads as uncertain; an uncertain attempt only
//! looks up; absent permits a resend of the SAME bytes; the send bound holds; one call per attempt.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::fs;

use nanodregg_client::attempt::{Attempt, AttemptError, Settlement, State};
use nanodregg_client::generated::attempt::{Action, Request};

fn scratch(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("nd-attempt-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir(&d).unwrap();
    d.join("a")
}

#[test]
fn signed_then_committed() {
    let d = scratch("commit");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let mut seen = Vec::new();
    let s = a
        .drive(State::Signed, 3, |r, b| {
            seen.push((r, b.to_vec()));
            Settlement::Committed(b"R".to_vec())
        })
        .unwrap();
    assert_eq!(
        s,
        State::Settled {
            committed: true,
            reply: b"R".to_vec()
        }
    );
    assert_eq!(seen, vec![(Request::Submit, b"CALL".to_vec())]);
    assert_eq!(Attempt::load(&d).unwrap().1, s, "the settlement is durable");
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}

#[test]
fn lost_reply_is_uncertain_and_only_looked_up() {
    let d = scratch("lost");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    assert_eq!(
        a.drive(State::Signed, 3, |_, _| Settlement::Unknown)
            .unwrap(),
        State::Uncertain { sends: 1 }
    );
    // Crash: reload from disk.
    let (a, s) = Attempt::load(&d).unwrap();
    assert_eq!(s, State::Uncertain { sends: 1 });
    let mut seen = Vec::new();
    let s = a
        .drive(s, 3, |r, b| {
            seen.push((r, b.to_vec()));
            Settlement::Committed(b"R".to_vec())
        })
        .unwrap();
    assert_eq!(
        seen,
        vec![(Request::Lookup, b"CALL".to_vec())],
        "never resubmitted while uncertain"
    );
    assert!(matches!(
        s,
        State::Settled {
            committed: true,
            ..
        }
    ));
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}

#[test]
fn absent_resends_the_same_bytes_up_to_the_bound() {
    let d = scratch("absent");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let mut seen = Vec::new();
    let r = a.drive(State::Signed, 2, |r, b| {
        seen.push((r, b.to_vec()));
        match r {
            Request::Submit => Settlement::Unknown,
            Request::Lookup => Settlement::Absent,
        }
    });
    assert!(matches!(r, Err(AttemptError::Ended(Action::Absent))));
    assert_eq!(
        seen.iter().filter(|(r, _)| *r == Request::Submit).count(),
        2
    );
    assert!(seen.iter().all(|(_, b)| b == b"CALL"));
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}

#[test]
fn one_call_per_attempt_and_refusal_is_final() {
    let d = scratch("once");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    assert!(matches!(
        Attempt::freeze(&d, b"OTHER"),
        Err(AttemptError::AlreadyFrozen)
    ));
    let s = a
        .drive(State::Signed, 3, |_, _| {
            Settlement::NotCommitted(b"staleRoot".to_vec())
        })
        .unwrap();
    assert_eq!(
        s,
        State::Settled {
            committed: false,
            reply: b"staleRoot".to_vec()
        }
    );
    let s2 = a
        .drive(s.clone(), 3, |_, _| {
            unreachable!("a settled attempt sends nothing")
        })
        .unwrap();
    assert_eq!(s2, s);
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}

#[test]
fn a_gap_in_send_markers_is_inconsistent() {
    let d = scratch("gap");
    Attempt::freeze(&d, b"CALL").unwrap();
    fs::write(d.join("sent.1"), []).unwrap();
    assert!(matches!(Attempt::load(&d), Err(AttemptError::Inconsistent)));
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}
