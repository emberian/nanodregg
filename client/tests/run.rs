//! The step loop against a scripted follow and host: challenge → sign → prepare → sign → submit
//! (reply lost) → lookup → done. Follow decides every step; the loop only performs them.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::collections::VecDeque;
use std::io;

use nanodregg_client::custody::Custody;
use nanodregg_client::generated::layout::{Op, Step};
use nanodregg_client::run::{self, Follow, Host, Outcome, RunError, Table};

// Test values, not the protocol's: the real ones are generated from Protocol/Table.lean.
const T: Table = Table {
    steps_max: 8,
    sends_max: 2,
    submit: 1,
    lookup: 2,
    ok: 0,
    refused: 1,
    absent: 3,
    uncertain: 2,
    declined: 5,
};

struct ScriptedFollow {
    steps: VecDeque<Step>,
    seen: Vec<(Vec<u8>, Outcome)>,
}
impl Follow for ScriptedFollow {
    fn command(&mut self, _argv: &[Vec<u8>]) -> io::Result<Step> {
        Ok(self.steps.pop_front().unwrap())
    }
    fn resume(&mut self, k: &[u8], o: &Outcome) -> io::Result<Step> {
        self.seen.push((k.to_vec(), o.clone()));
        Ok(self.steps.pop_front().unwrap())
    }
}

struct ScriptedHost {
    replies: VecDeque<io::Result<(u8, Vec<u8>)>>,
    asked: Vec<(u8, Vec<u8>)>,
}
impl Host for ScriptedHost {
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        self.asked.push((op, payload.to_vec()));
        self.replies.pop_front().unwrap()
    }
}

fn setup(name: &str) -> (std::path::PathBuf, Custody) {
    let d = nanodregg_devtools::scratch(&format!("nd-run-{}-{name}", std::process::id()));
    nanodregg_devtools::mkdirs(&d.join("attempts")).unwrap();
    Custody::create_same_record(&d).unwrap();
    let c = Custody::open(&d, None).unwrap();
    (d, c)
}

#[test]
fn round_trip_with_a_lost_submit_reply() {
    let (d, custody) = setup("trip");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::Host {
                op: Op::Read,
                payload: b"challenge?".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Sign {
                message: b"observation".to_vec(),
                k: b"k2".to_vec(),
            },
            Step::Sign {
                message: b"plan".to_vec(),
                k: b"k3".to_vec(),
            },
            Step::Submit {
                call: b"CALL".to_vec(),
                k: b"k4".to_vec(),
            },
            Step::Done {
                exit: 0,
                stdout: b"ok\n".to_vec(),
                stderr: vec![],
            },
        ]),
        seen: vec![],
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([
            Ok((0, b"challenge".to_vec())),
            Err(io::Error::from(io::ErrorKind::ConnectionReset)), // the submit's reply is lost
            Ok((0, b"receipt".to_vec())),                         // lookup: committed
        ]),
        asked: vec![],
    };
    let (exit, out, _) = run::run(
        &[b"nd".to_vec()],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!((exit, out), (0, b"ok\n".to_vec()));
    assert_eq!(
        host.asked,
        vec![
            (3, b"challenge?".to_vec()),
            (1, b"CALL".to_vec()),
            (2, b"CALL".to_vec())
        ]
    );
    assert_eq!(
        follow.seen[1].1,
        Outcome {
            status: 0,
            payload: custody.sign(b"observation").unwrap().encode().unwrap(),
        }
    );
    assert_eq!(
        follow.seen[3],
        (
            b"k4".to_vec(),
            Outcome {
                status: 0,
                payload: b"receipt".to_vec()
            }
        )
    );
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_follow_that_never_finishes_is_stopped_by_the_bound() {
    let (d, custody) = setup("bound");
    let sign = || Step::Sign {
        message: b"m".to_vec(),
        k: vec![],
    };
    let mut follow = ScriptedFollow {
        steps: (0..20).map(|_| sign()).collect(),
        seen: vec![],
    };
    let mut host = ScriptedHost {
        replies: VecDeque::new(),
        asked: vec![],
    };
    let r = run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    );
    assert!(matches!(r, Err(RunError::StepsExhausted)));
    assert_eq!(follow.seen.len(), T.steps_max as usize);
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn an_unsettled_call_is_reported_uncertain_with_its_attempt() {
    let (d, custody) = setup("uncertain");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([Step::Submit {
            call: b"C".to_vec(),
            k: vec![],
        }]),
        seen: vec![],
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((2, vec![])), Ok((2, vec![]))]),
        asked: vec![],
    };
    let r = run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    );
    assert!(matches!(r, Err(RunError::Uncertain(ref p)) if p.ends_with("0")));
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn an_armed_rotation_is_settled_by_lookup_before_the_command() {
    use nanodregg_client::attempt::{Attempt, Settlement, State};
    let (d, custody) = setup("reconcile");
    let (next, _) = custody.precommit().unwrap();
    let (_, r) = custody.sign_next(b"rotate").unwrap();
    let a = Attempt::freeze(&d.join("attempts/0"), b"ROTATE").unwrap();
    custody.arm(0, &r).unwrap();
    // Sent, and its reply lost: uncertain on disk.
    a.drive(State::Signed, 1, |_, _| Settlement::Unknown)
        .unwrap();
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([Step::Done {
            exit: 0,
            stdout: Vec::new(),
            stderr: Vec::new(),
        }]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((0, b"receipt".to_vec()))]),
        asked: Vec::new(),
    };
    run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(
        host.asked,
        vec![(T.lookup, b"ROTATE".to_vec())],
        "a lookup of the frozen bytes, never a resend"
    );
    assert_eq!(
        custody.public_key().unwrap(),
        next,
        "advanced on custody's own settlement"
    );
    assert!(custody.armed().unwrap().is_none());
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn sign_next_then_a_committed_submit_advances_custody_in_one_command() {
    let (d, custody) = setup("signnext");
    let (next, pending) = custody.precommit().unwrap();
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::SignNext {
                message: b"rotate".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Submit {
                call: b"ROTATE".to_vec(),
                k: b"k2".to_vec(),
            },
            Step::Done {
                exit: 0,
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
        ]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((0, b"receipt".to_vec()))]),
        asked: Vec::new(),
    };
    run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(follow.seen[0].1.status, T.ok);
    let bytes = follow.seen[0].1.payload.clone();
    let s = nanodregg_client::generated::layout::SignResult::decode(&bytes).unwrap();
    assert_eq!((s.key, s.next), (next.to_vec(), pending.to_vec()));
    assert_eq!(
        custody.public_key().unwrap(),
        next,
        "advanced on the committed settlement"
    );
    assert_eq!(custody.sign(b"").unwrap().next, pending.to_vec());
    assert!(custody.armed().unwrap().is_none());
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_refused_rotation_submit_leaves_custody_on_its_current_key() {
    let (d, custody) = setup("signnext-refused");
    let before = custody.public_key().unwrap();
    custody.precommit().unwrap();
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::SignNext {
                message: b"rotate".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Submit {
                call: b"ROTATE".to_vec(),
                k: b"k2".to_vec(),
            },
            Step::Done {
                exit: 0,
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
        ]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.refused, b"notPrecommitted".to_vec()))]),
        asked: Vec::new(),
    };
    run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(
        custody.public_key().unwrap(),
        before,
        "a refused rotation never advances"
    );
    assert!(custody.armed().unwrap().is_none());
    std::fs::remove_dir_all(&d).unwrap();
}

/// A submit answered `closed` (the supervisor ended the connection, PROTOCOL-22) is not a verdict:
/// the call is settled by lookup, never resent blind and never reported refused.
#[test]
fn a_submit_answered_closed_is_settled_by_lookup() {
    let (d, custody) = setup("closed");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::Submit {
                call: b"CALL".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Done {
                exit: 0,
                stdout: b"ok\n".to_vec(),
                stderr: vec![],
            },
        ]),
        seen: vec![],
    };
    let closed = nanodregg_client::generated::status::CLOSED;
    let idle = nanodregg_client::generated::CloseReason::Idle.name();
    let mut host = ScriptedHost {
        replies: VecDeque::from([
            Ok((closed, idle.as_bytes().to_vec())), // the submit's connection closed `idle`
            Ok((0, b"receipt".to_vec())),           // lookup: committed
        ]),
        asked: vec![],
    };
    let (exit, _, _) = run::run(
        &[b"nd".to_vec()],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(exit, 0);
    assert_eq!(
        host.asked,
        vec![(1, b"CALL".to_vec()), (2, b"CALL".to_vec())]
    );
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_custody_refusal_is_a_result_follow_renders_not_an_exit() {
    let (d, custody) = setup("custody-refused");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            // No precommit came first: custody has no pending key.
            Step::SignNext {
                message: b"rotate".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Done {
                exit: 1,
                stdout: Vec::new(),
                stderr: b"refused noPending\n".to_vec(),
            },
        ]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::new(),
        asked: Vec::new(),
    };
    let (exit, _, _) = run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(exit, 1, "follow's done, not an nd error");
    let o = &follow.seen[0].1;
    assert_eq!(o.status, T.refused);
    let r = nanodregg_client::generated::layout::CustodyRefused::decode(&o.payload).unwrap();
    assert_eq!(r.refusal.name(), "noPending");
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_submit_whose_reply_is_lost_is_looked_up_never_resent() {
    let (d, custody) = setup("lost");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::Submit {
                call: b"CALL".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Done {
                exit: 0,
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
        ]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([
            Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "timeout (replyMsMax)",
            )),
            Ok((T.ok, b"receipt".to_vec())),
        ]),
        asked: Vec::new(),
    };
    run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(
        host.asked,
        vec![(T.submit, b"CALL".to_vec()), (T.lookup, b"CALL".to_vec())]
    );
    std::fs::remove_dir_all(&d).unwrap();
}

/// PROTOCOL-41: a rotation submit answered `declined` (not recorded, not final) is handed to
/// follow as `declined`, leaves the rotation ARMED and custody on its current key, and leaves the
/// attempt open on disk (uncertain), so the next run looks it up and never re-signs.
#[test]
fn a_declined_rotation_submit_stays_armed_and_open() {
    use nanodregg_client::attempt::{Attempt, State};
    let (d, custody) = setup("signnext-declined");
    let before = custody.public_key().unwrap();
    custody.precommit().unwrap();
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::SignNext {
                message: b"rotate".to_vec(),
                k: b"k1".to_vec(),
            },
            Step::Submit {
                call: b"ROTATE".to_vec(),
                k: b"k2".to_vec(),
            },
            Step::Done {
                exit: 53,
                stdout: Vec::new(),
                stderr: b"declined unknownKey\n".to_vec(),
            },
        ]),
        seen: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.declined, b"unknownKey".to_vec()))]),
        asked: Vec::new(),
    };
    run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(
        host.asked,
        vec![(T.submit, b"ROTATE".to_vec())],
        "one submit, no lookup"
    );
    assert_eq!(
        follow.seen[1].1.status, T.declined,
        "follow is told declined"
    );
    assert_eq!(follow.seen[1].1.payload, b"unknownKey".to_vec());
    assert_eq!(custody.public_key().unwrap(), before, "never advanced");
    assert!(custody.armed().unwrap().is_some(), "still armed: not final");
    let (_, s) = Attempt::load(&d.join("attempts/0")).unwrap();
    assert_eq!(s, State::Uncertain { sends: 1 }, "open on disk");
    std::fs::remove_dir_all(&d).unwrap();
}
