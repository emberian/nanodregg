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
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
/// bytes can still land them. Every absent lookup is probed before a resend (KERNEL-54); the last
/// probe says `open`; the attempt stays open and the next
/// run looks it up again (never a fresh call: no double effect).
#[test]
fn absent_with_sends_exhausted_and_a_live_window_stays_open() {
    let d = scratch("absent");
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
            Request::Probe,
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
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
    let open = |sends| State::Open {
        sends,
        end: Action::Uncertain,
        payload: Vec::new(),
    };
    assert_eq!(
        a.drive(State::Signed, 3, |_, _| -> R {
            Ok(Reply::Lost(Vec::new()))
        })
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
    let a = Attempt::freeze(&d2, b"CALL", b"ARGV", b"K").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Committed),
                _ => Reply::Lost(Vec::new()),
            })
        })
        .unwrap();
    assert_eq!(s, open(1));
    done(&d);
    done(&d2);
}

/// cv 01a150b1 (PROTOCOL-58): a confirm follow did not settle ends `uncertain` carrying follow's own
/// words, so a refusal never renders as the Host's failed append. The keep rule: the last non-empty
/// within HINT_BYTES_MAX; one longer is no hint (never cut); a transport loss says nothing.
#[test]
fn an_uncertain_end_carries_follows_last_words_within_the_bound() {
    use nanodregg_client::generated::HINT_BYTES_MAX;
    let max = HINT_BYTES_MAX as usize;
    let cases: [(&str, Vec<u8>, Vec<u8>); 4] = [
        (
            "refused",
            b"refused badResult\n".to_vec(),
            b"refused badResult\n".to_vec(),
        ),
        ("at-bound", vec![b'r'; max], vec![b'r'; max]),
        ("past-bound", vec![b'r'; max + 1], Vec::new()),
        ("transport", Vec::new(), Vec::new()),
    ];
    for (tag, said, want) in cases {
        let d = scratch(&format!("hint-{tag}"));
        let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
        let s = a
            .drive(State::Signed, 3, |r, _| -> R {
                Ok(match r {
                    Request::Submit => host(Seen::Committed),
                    _ => Reply::Lost(said.clone()),
                })
            })
            .unwrap();
        let end = Action::Uncertain;
        assert_eq!(
            s,
            State::Open {
                sends: 1,
                end,
                payload: want
            },
            "{tag}"
        );
        done(&d);
    }
}

#[test]
fn one_call_per_attempt_and_refusal_is_final() {
    let d = scratch("once");
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
    assert!(matches!(
        Attempt::freeze(&d, b"OTHER", b"ARGV", b"K"),
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
        Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
/// attempt reloads as uncertain, and a drive from disk LOOKS IT UP (the same bytes), never
/// resubmits blind. That the next RUN is this drive is `run.rs`'s
/// `a_rerun_of_the_same_argv_continues_its_open_attempt_and_signs_nothing` (CLIENT-37).
#[test]
fn declined_leaves_the_attempt_open_and_a_reload_looks_up() {
    let d = scratch("declined");
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
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
        "a reload looks up"
    );
    done(&d);
}

/// HOST-74: the writer declines a lookup it decided nothing about (bytes it cannot decode, a frame
/// still queued when it stopped). The run ends `declined` with the Host's name, nothing settled,
/// never `confirm` (so never `contradicted`), and the attempt reloads open.
#[test]
fn a_declined_lookup_ends_the_run_declined() {
    let d = scratch("declined-lookup");
    let a = Attempt::freeze(&d, b"CALL", b"ARGV", b"K").unwrap();
    let s = a
        .drive(State::Signed, 3, |r, _| -> R {
            Ok(match r {
                Request::Submit => host(Seen::Unknown),
                _ => Reply::Host(Seen::Declined, b"stopped".to_vec()),
            })
        })
        .unwrap();
    assert_eq!(
        s,
        State::Open {
            sends: 1,
            end: Action::Declined,
            payload: b"stopped".to_vec()
        }
    );
    assert_eq!(Attempt::load(&d).unwrap().1, State::Uncertain { sends: 1 });
    done(&d);
}

/// CLIENT-37: the lookup a run starts with. The newest unsettled attempt frozen for the argv is
/// found; a settled one, another argv's, and a crashed freeze (no `call`: never sent) are passed
/// over; a `call` without `argv` (an older layout) refuses to load.
#[test]
fn open_for_finds_the_newest_unsettled_attempt_of_its_argv() {
    let at = scratch("open-for");
    fs::create_dir(&at).unwrap();
    let a0 = Attempt::freeze(&at.join("0"), b"C0", b"ARGV", b"K0").unwrap();
    a0.drive(State::Signed, 3, |_, _| -> R {
        Ok(Reply::Lost(Vec::new()))
    })
    .unwrap();
    Attempt::freeze(&at.join("1"), b"C1", b"OTHER", b"K1").unwrap();
    let a2 = Attempt::freeze(&at.join("2"), b"C2", b"ARGV", b"K2").unwrap();
    a2.drive(State::Signed, 3, |r, _| -> R {
        Ok(match r {
            Request::Submit => host(Seen::Committed),
            _ => follow("committed 1 2"),
        })
    })
    .unwrap();
    fs::create_dir(at.join("3")).unwrap();
    fs::write(at.join("3/argv"), b"ARGV").unwrap();
    let (n, a, s) = Attempt::open_for(&at, b"ARGV").unwrap().unwrap();
    assert_eq!((n, a.call(), a.cont()), (0, &b"C0"[..], &b"K0"[..]));
    assert_eq!(s, State::Uncertain { sends: 1 });
    assert!(Attempt::open_for(&at, b"NONE").unwrap().is_none());
    fs::create_dir(at.join("4")).unwrap();
    fs::write(at.join("4/call"), b"C4").unwrap();
    assert!(matches!(
        Attempt::open_for(&at, b"ARGV"),
        Err(AttemptError::Inconsistent)
    ));
    done(&at);
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

/// CLIENT-39 (A18): a writer killed (SIGKILL) at any instant of `freeze` leaves each attempt's `call`
/// absent or WHOLE. A child of this test freezes 4 MiB calls in a loop and is killed after a random
/// few milliseconds, twenty times; every `call` present has all its bytes. Written in place (the old
/// `create_once`), a kill inside the write leaves a short `call` that reloads as a different call.
#[test]
fn a_killed_freeze_leaves_its_call_absent_or_whole() {
    const BIG: usize = 4 << 20;
    let at = scratch("killed-freeze");
    fs::create_dir(&at).unwrap();
    let mut short = Vec::new();
    for round in 0..20u64 {
        let dir = at.join(round.to_string());
        fs::create_dir(&dir).unwrap();
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "freeze_forever", "--ignored", "--nocapture"])
            .env("ND_FREEZE_AT", &dir)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        // past the test harness's start, into the loop: a few ms, varied by round
        std::thread::sleep(std::time::Duration::from_millis(40 + (round * 7) % 23));
        child.kill().unwrap();
        child.wait().unwrap();
        for e in fs::read_dir(&dir).unwrap() {
            let call = e.unwrap().path().join("call");
            if let Ok(m) = fs::metadata(&call)
                && m.len() as usize != BIG
            {
                short.push((call, m.len()));
            }
        }
    }
    done(&at);
    assert!(short.is_empty(), "short calls after a kill: {short:?}");
}

/// The writer `a_killed_freeze_leaves_its_call_absent_or_whole` kills (only as its child).
#[test]
#[ignore = "run only as a_killed_freeze_leaves_its_call_absent_or_whole's child"]
fn freeze_forever() {
    let Some(at) = std::env::var_os("ND_FREEZE_AT") else {
        return;
    };
    let at = std::path::PathBuf::from(at);
    let big = vec![7u8; 4 << 20];
    // until this test's parent kills it (bounded by u64, never reached)
    for n in 0..u64::MAX {
        let _ = Attempt::freeze(&at.join(n.to_string()), &big, b"ARGV", b"K");
    }
}
