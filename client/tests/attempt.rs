//! Attempt plants (PROTOCOL-46 over PROTOCOL-17/41): a crash after the send marker reloads as
//! uncertain; an uncertain attempt only looks up; absent permits a resend of the SAME bytes; the
//! send bound holds; one call per attempt. The Host's word never settles: a claimed final is
//! confirmed by the member's own follow, whose three lines are what `settled` holds. A Host that
//! lies is contradicted (`ok` for an absent call) or overruled (`refused` for a committed one), and
//! an absent call whose window is live stays OPEN, never "safe to run again".
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::fs;

use nanodregg_client::attempt::{Attempt, AttemptError, Receipt, Reply, State};
use nanodregg_client::generated::attempt::{Action, Request, Seen};

fn scratch(name: &str) -> std::path::PathBuf {
    let d = nanodregg_devtools::scratch(&format!("nd-attempt-{}-{name}", std::process::id()));
    nanodregg_devtools::mkdirs(&d).unwrap();
    d.join("a")
}

fn done(d: &std::path::Path) {
    fs::remove_dir_all(d.parent().unwrap()).unwrap();
}

fn lines(verdict: &str) -> Vec<u8> {
    format!("receipt 00ab\nhead 7 3 cd\nsettle {verdict}\n").into_bytes()
}

/// Follow's answer to `receipt CALL` with `verdict`.
fn follow(verdict: &str) -> Reply {
    Reply::Follow(Receipt::read(&lines(verdict)).unwrap())
}

fn host(seen: Seen) -> Reply {
    Reply::Host(seen, b"hostSaid".to_vec())
}

type R = Result<Reply, AttemptError>;

fn settled(committed: bool, verdict: &str) -> State {
    State::Settled {
        committed,
        receipt: Receipt::read(&lines(verdict)).unwrap(),
    }
}

#[test]
fn a_host_ok_is_confirmed_and_the_settlement_is_follows_receipt() {
    let d = scratch("commit");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let mut seen = Vec::new();
    let s = a
        .drive(State::Signed, 3, |r, b| -> R {
            seen.push((r, b.to_vec()));
            Ok(match r {
                Request::Submit => host(Seen::Committed),
                _ => follow("committed 3 77"),
            })
        })
        .unwrap();
    assert_eq!(s, settled(true, "committed 3 77"));
    assert_eq!(
        seen,
        vec![
            (Request::Submit, b"CALL".to_vec()),
            (Request::Confirm, b"CALL".to_vec())
        ]
    );
    assert_eq!(
        fs::read(d.join("settled")).unwrap(),
        lines("committed 3 77"),
        "never the Host's reply"
    );
    assert_eq!(Attempt::load(&d).unwrap().1, s, "the settlement is durable");
    done(&d);
}

/// A Host that answers `ok` for a call its World does not hold: follow's receipt says `open`, the
/// run ends `contradicted` naming both, and nothing is settled.
#[test]
fn a_host_ok_for_an_absent_call_is_contradicted_and_stays_open() {
    let d = scratch("lie-ok");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Committed),
                _ => follow("open"),
            })
        })
        .unwrap();
    assert_eq!(
        s,
        State::Open {
            sends: 1,
            end: Action::Contradicted,
            payload: b"committed open".to_vec()
        }
    );
    assert_eq!(
        Attempt::load(&d).unwrap().1,
        State::Uncertain { sends: 1 },
        "open on disk"
    );
    done(&d);
}

/// A Host that answers `refused` for a call that committed: follow's receipt settles it committed.
#[test]
fn a_host_refused_for_a_committed_call_settles_committed() {
    let d = scratch("lie-refused");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Refused),
                _ => follow("committed 4 99"),
            })
        })
        .unwrap();
    assert_eq!(s, settled(true, "committed 4 99"));
    done(&d);
}

/// Sends exhausted and the Host has no record: the call's window is live, so a relay holding the
/// bytes can still land them. The member's probe says `open`; the attempt stays open and the next
/// run looks it up again (never a fresh call: no double effect).
#[test]
fn absent_with_sends_exhausted_and_a_live_window_stays_open() {
    let d = scratch("absent");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let mut seen = Vec::new();
    let s = a
        .drive(State::Signed, 2, |r, b| -> R {
            seen.push((r, b.to_vec()));
            Ok(match r {
                Request::Submit => host(Seen::Unknown),
                Request::Lookup => host(Seen::Absent),
                _ => follow("open"),
            })
        })
        .unwrap();
    assert_eq!(
        s,
        State::Open {
            sends: 2,
            end: Action::Open,
            payload: Vec::new()
        }
    );
    let requests: Vec<Request> = seen.iter().map(|(r, _)| *r).collect();
    assert_eq!(
        requests,
        [
            Request::Submit,
            Request::Lookup,
            Request::Submit,
            Request::Lookup,
            Request::Probe
        ]
    );
    assert!(seen.iter().all(|(_, b)| b == b"CALL"));
    assert_eq!(Attempt::load(&d).unwrap().1, State::Uncertain { sends: 2 });
    // After the window: the same probe says `expired`, which is final.
    let (a, s) = Attempt::load(&d).unwrap();
    let s = a
        .drive(s, 2, |r, _| -> R {
            Ok(match r {
                Request::Lookup => host(Seen::Absent),
                _ => follow("expired"),
            })
        })
        .unwrap();
    assert_eq!(s, settled(false, "expired"));
    done(&d);
}

#[test]
fn lost_reply_is_uncertain_and_only_looked_up() {
    let d = scratch("lost");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let open = |sends| State::Open {
        sends,
        end: Action::Uncertain,
        payload: Vec::new(),
    };
    assert_eq!(
        a.drive(State::Signed, 3, |_, _| -> R { Ok(Reply::Lost) })
            .unwrap(),
        open(1)
    );
    // Crash: reload from disk.
    let (a, s) = Attempt::load(&d).unwrap();
    assert_eq!(s, State::Uncertain { sends: 1 });
    let mut seen = Vec::new();
    let s = a
        .drive(s, 3, |r, _| -> R {
            seen.push(r);
            Ok(match r {
                Request::Lookup => host(Seen::Committed),
                _ => follow("committed 1 2"),
            })
        })
        .unwrap();
    assert_eq!(
        seen,
        [Request::Lookup, Request::Confirm],
        "never resubmitted while uncertain"
    );
    assert_eq!(s, settled(true, "committed 1 2"));
    // A confirm that cannot reach follow settles nothing.
    let d2 = scratch("lost-confirm");
    let a = Attempt::freeze(&d2, b"CALL").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Committed),
                _ => Reply::Lost,
            })
        })
        .unwrap();
    assert_eq!(s, open(1));
    done(&d);
    done(&d2);
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
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Refused),
                _ => follow("refused 3"),
            })
        })
        .unwrap();
    assert_eq!(s, settled(false, "refused 3"));
    let s2 = a
        .drive(s.clone(), 3, |_, _| -> R {
            unreachable!("a settled attempt sends nothing")
        })
        .unwrap();
    assert_eq!(s2, s);
    done(&d);
}

/// The directory refuses to load unless it is exactly this layout: a gap in the markers, a file
/// of an older layout (`committed`), or a settlement that is not a final verdict.
#[test]
fn only_this_layout_loads() {
    for (name, file, bytes) in [
        ("gap", "sent.1", Vec::new()),
        ("old", "committed", b"the Host's reply".to_vec()),
        ("notfinal", "settled", lines("open")),
        ("garbled", "settled", b"settle committed 1 2\n".to_vec()),
    ] {
        let d = scratch(name);
        Attempt::freeze(&d, b"CALL").unwrap();
        if name != "gap" {
            fs::write(d.join("sent.0"), []).unwrap();
        }
        fs::write(d.join(file), bytes).unwrap();
        assert!(
            matches!(Attempt::load(&d), Err(AttemptError::Inconsistent)),
            "{name}"
        );
        done(&d);
    }
}

/// PROTOCOL-41: `declined` is not final. The run ends with nothing written but the send marker, the
/// attempt reloads as uncertain, and the next run LOOKS IT UP (the same bytes), never resubmits blind.
#[test]
fn declined_leaves_the_attempt_open_and_the_next_run_looks_up() {
    let d = scratch("declined");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let s = a
        .drive(State::Signed, 3, |_, _| -> R {
            Ok(Reply::Host(Seen::Declined, b"unknownKey".to_vec()))
        })
        .unwrap();
    assert_eq!(
        s,
        State::Open {
            sends: 1,
            end: Action::Declined,
            payload: b"unknownKey".to_vec()
        }
    );
    let (a, s) = Attempt::load(&d).unwrap();
    assert_eq!(s, State::Uncertain { sends: 1 }, "open on disk");
    let mut seen = Vec::new();
    a.drive(s, 3, |r, _| -> R {
        seen.push(r);
        Ok(match r {
            Request::Lookup => host(Seen::Committed),
            _ => follow("committed 1 2"),
        })
    })
    .unwrap();
    assert_eq!(
        seen,
        [Request::Lookup, Request::Confirm],
        "the next run looks up"
    );
    done(&d);
}

/// A lookup is never judged, so a `declined` answer to one cannot answer it: `badReply`.
#[test]
fn a_declined_lookup_is_a_bad_reply() {
    let d = scratch("declined-lookup");
    let a = Attempt::freeze(&d, b"CALL").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Unknown),
                _ => Reply::Host(Seen::Declined, b"wrongWorld".to_vec()),
            })
        })
        .unwrap();
    assert!(matches!(
        s,
        State::Open {
            end: Action::BadReply,
            ..
        }
    ));
    assert_eq!(Attempt::load(&d).unwrap().1, State::Uncertain { sends: 1 });
    done(&d);
}

/// Follow's output reads only as the three lines with a verdict the table names.
#[test]
fn a_receipt_reads_only_as_three_lines_with_a_named_verdict() {
    assert_eq!(
        Receipt::read(&lines("committed 3 77")).unwrap().seen,
        Seen::Committed
    );
    assert_eq!(
        Receipt::read(&lines("expired")).unwrap().seen,
        Seen::Refused
    );
    assert_eq!(
        Receipt::read(&lines("forgotten")).unwrap().seen,
        Seen::Forgotten
    );
    for bad in [
        lines("absent"),
        b"receipt 00\nhead 1 1 cd\n".to_vec(),
        b"head 1 1 cd\nreceipt 00\nsettle open\n".to_vec(),
        [lines("open"), b"extra\n".to_vec()].concat(),
    ] {
        assert!(
            Receipt::read(&bad).is_none(),
            "{}",
            String::from_utf8_lossy(&bad)
        );
    }
}
