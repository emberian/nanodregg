//! The step loop against a scripted follow and host: challenge → sign → prepare → sign → submit
//! (reply lost) → lookup → confirm → done. Follow decides every step; the loop only performs them.
//! A Host's status byte only steers: what settles a call, and custody's rotation, is the member's
//! own follow answering `receipt CALL` (PROTOCOL-46). A lying Host is contradicted or overruled.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::collections::VecDeque;
use std::io;

use nanodregg_client::custody::Custody;
use nanodregg_client::generated::attempt::Action;
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
    exit_ok: 0,
    host_contradicted: 55,
};

/// A command's steps from `steps`; a `receipt CALL` command's (the attempt's confirm or probe)
/// from `receipts`, its argv kept in `asked`.
struct ScriptedFollow {
    steps: VecDeque<Step>,
    seen: Vec<(Vec<u8>, Outcome)>,
    receipts: VecDeque<Step>,
    asked: Vec<Vec<Vec<u8>>>,
}
impl Follow for ScriptedFollow {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        if argv.first().is_some_and(|v| v == b"receipt") {
            self.asked.push(argv.to_vec());
            return Ok(self.receipts.pop_front().unwrap());
        }
        Ok(self.steps.pop_front().unwrap())
    }
    fn resume(&mut self, k: &[u8], o: &Outcome) -> io::Result<Step> {
        self.seen.push((k.to_vec(), o.clone()));
        Ok(self.steps.pop_front().unwrap())
    }
}

/// Follow's `receipt CALL` answer: its three lines under exit ok.
fn receipt(verdict: &str) -> Step {
    Step::Done {
        exit: 0,
        stdout: format!("receipt 00ab\nhead 7 3 cd\nsettle {verdict}\n").into_bytes(),
        stderr: Vec::new(),
    }
}

fn hex(b: &[u8]) -> Vec<u8> {
    b.iter()
        .map(|x| format!("{x:02x}"))
        .collect::<String>()
        .into_bytes()
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
        receipts: VecDeque::from([receipt("committed 3 77")]),
        asked: Vec::new(),
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
                status: Action::Committed.code(),
                payload: b"committed 3 77".to_vec()
            }
        ),
        "follow is told its own verdict, never the Host's reply"
    );
    assert_eq!(follow.asked, vec![vec![b"receipt".to_vec(), hex(b"CALL")]]);
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
        receipts: VecDeque::new(),
        asked: Vec::new(),
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
fn an_unsettled_call_is_handed_to_follow_uncertain() {
    let (d, custody) = setup("uncertain");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::Submit {
                call: b"C".to_vec(),
                k: vec![],
            },
            Step::Done {
                exit: 2,
                stdout: vec![],
                stderr: vec![],
            },
        ]),
        seen: vec![],
        receipts: VecDeque::new(),
        asked: Vec::new(),
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
    )
    .unwrap();
    assert_eq!(r.0, 2);
    let told = &follow.seen[0].1;
    assert_eq!(
        (told.status, told.payload.len()),
        (Action::Uncertain.code(), 0)
    );
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn an_armed_rotation_is_settled_by_its_receipt_before_the_command() {
    use nanodregg_client::attempt::{Attempt, AttemptError, Reply, State};
    let (d, custody) = setup("reconcile");
    let (next, _) = custody.precommit().unwrap();
    let (_, r) = custody.sign_next(b"rotate").unwrap();
    let a = Attempt::freeze(&d.join("attempts/0"), b"ROTATE").unwrap();
    custody.arm(0, &r).unwrap();
    // Sent, and its reply lost: uncertain on disk.
    a.drive(State::Signed, 1, |_, _| Ok::<_, AttemptError>(Reply::Lost))
        .unwrap();
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([Step::Done {
            exit: 0,
            stdout: Vec::new(),
            stderr: Vec::new(),
        }]),
        seen: Vec::new(),
        receipts: VecDeque::from([receipt("committed 2 aa")]),
        asked: Vec::new(),
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
        receipts: VecDeque::from([receipt("committed 2 aa")]),
        asked: Vec::new(),
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
        receipts: VecDeque::from([receipt("refused 3")]),
        asked: Vec::new(),
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
        receipts: VecDeque::from([receipt("committed 2 aa")]),
        asked: Vec::new(),
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
        receipts: VecDeque::new(),
        asked: Vec::new(),
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
        receipts: VecDeque::from([receipt("committed 2 aa")]),
        asked: Vec::new(),
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
        receipts: VecDeque::new(),
        asked: Vec::new(),
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
        follow.seen[1].1.status,
        Action::Declined.code(),
        "follow is told declined"
    );
    assert_eq!(follow.seen[1].1.payload, b"unknownKey".to_vec());
    assert_eq!(custody.public_key().unwrap(), before, "never advanced");
    assert!(custody.armed().unwrap().is_some(), "still armed: not final");
    let (_, s) = Attempt::load(&d.join("attempts/0")).unwrap();
    assert_eq!(s, State::Uncertain { sends: 1 }, "open on disk");
    std::fs::remove_dir_all(&d).unwrap();
}

/// An armed rotation whose attempt was sent and whose reply was lost: `(dir, custody, old, next)`.
fn armed(name: &str) -> (std::path::PathBuf, Custody, [u8; 32], [u8; 32]) {
    use nanodregg_client::attempt::{Attempt, AttemptError, Reply, State};
    let (d, custody) = setup(name);
    let old = custody.public_key().unwrap();
    let (next, _) = custody.precommit().unwrap();
    let (_, r) = custody.sign_next(b"rotate").unwrap();
    let a = Attempt::freeze(&d.join("attempts/0"), b"ROTATE").unwrap();
    custody.arm(0, &r).unwrap();
    a.drive(State::Signed, 1, |_, _| Ok::<_, AttemptError>(Reply::Lost))
        .unwrap();
    (d, custody, old, next)
}

fn done_step() -> Step {
    Step::Done {
        exit: 0,
        stdout: Vec::new(),
        stderr: Vec::new(),
    }
}

/// The Host says `ok` for a rotation its World never installed. The member's own receipt says
/// `open`: the run ends `hostContradicted`, custody stays on its current key and the rotation stays
/// armed (the old code advanced custody to a key the World never installed: a lockout).
#[test]
fn a_host_ok_for_an_unlanded_rotation_is_contradicted_and_custody_stays_armed() {
    let (d, custody, old, _) = armed("lie-ok");
    let mut follow = ScriptedFollow {
        steps: VecDeque::new(),
        seen: Vec::new(),
        receipts: VecDeque::from([receipt("open")]),
        asked: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.ok, b"receipt".to_vec()))]),
        asked: Vec::new(),
    };
    let (exit, _, stderr) = run::run(
        &[],
        &mut follow,
        &mut host,
        &custody,
        &d.join("attempts"),
        T,
    )
    .unwrap();
    assert_eq!(exit, T.host_contradicted);
    let stderr = String::from_utf8(stderr).unwrap();
    assert!(
        stderr.starts_with("hostContradicted committed open"),
        "{stderr}"
    );
    assert_eq!(
        custody.public_key().unwrap(),
        old,
        "never advanced on the Host's word"
    );
    assert!(custody.armed().unwrap().is_some(), "still armed");
    std::fs::remove_dir_all(&d).unwrap();
}

/// The Host says `refused` for a rotation that committed. The member's own receipt says committed:
/// custody advances (the old code dropped the pending key and kept a revoked one: a lockout).
#[test]
fn a_host_refused_for_a_landed_rotation_settles_committed() {
    let (d, custody, _, next) = armed("lie-refused");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([done_step()]),
        seen: Vec::new(),
        receipts: VecDeque::from([receipt("committed 2 aa")]),
        asked: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.refused, b"staleRoot".to_vec()))]),
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
        next,
        "advanced on the member's receipt"
    );
    assert!(custody.armed().unwrap().is_none());
    std::fs::remove_dir_all(&d).unwrap();
}

/// At the submit step: a rotation answered `ok` whose receipt says `open` is handed to follow as
/// `contradicted` with both names, and stays armed.
#[test]
fn a_contradicted_rotation_submit_is_handed_to_follow_and_stays_armed() {
    let (d, custody) = setup("submit-contradicted");
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
            done_step(),
        ]),
        seen: Vec::new(),
        receipts: VecDeque::from([receipt("open")]),
        asked: Vec::new(),
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.ok, b"receipt".to_vec()))]),
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
    let told = &follow.seen[1].1;
    assert_eq!(
        (told.status, told.payload.as_slice()),
        (Action::Contradicted.code(), &b"committed open"[..])
    );
    assert_eq!(custody.public_key().unwrap(), before);
    assert!(custody.armed().unwrap().is_some());
    std::fs::remove_dir_all(&d).unwrap();
}

/// Follow's catch-up as the Machine and the Host's `Envelope.check` together: an envelope signed
/// by a key other than the World's current one is refused `unknownKey`, and follow re-signs it ONCE
/// with `signIncoming`; a second refusal ends `receipt` refused. Main commands are `done`.
struct EnvelopeFollow {
    world_key: [u8; 32],
    incoming_asked: u32,
}
impl Follow for EnvelopeFollow {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        if argv.first().is_some_and(|v| v == b"receipt") {
            return Ok(Step::Sign {
                message: envelope(),
                k: b"sign".to_vec(),
            });
        }
        Ok(done_step())
    }
    fn resume(&mut self, k: &[u8], o: &Outcome) -> io::Result<Step> {
        use nanodregg_client::generated::layout::SignResult;
        let s = SignResult::decode(&o.payload)
            .ok()
            .filter(|_| o.status == T.ok);
        if s.as_ref()
            .is_some_and(|s| s.key == self.world_key && verifies(s))
        {
            return Ok(receipt("committed 2 aa"));
        }
        if k == b"sign" {
            self.incoming_asked += 1;
            return Ok(Step::SignIncoming {
                message: envelope(),
                k: b"incoming".to_vec(),
            });
        }
        Ok(Step::Done {
            exit: 1,
            stdout: Vec::new(),
            stderr: b"refused unknownKey\n".to_vec(),
        })
    }
}

fn envelope() -> Vec<u8> {
    [nanodregg_client::generated::ENVELOPE_DOMAIN, b"window"].concat()
}

fn verifies(s: &nanodregg_client::generated::layout::SignResult) -> bool {
    use ed25519_dalek::{Signature, VerifyingKey};
    let k = VerifyingKey::from_bytes(s.key.as_slice().try_into().unwrap()).unwrap();
    k.verify_strict(&envelope(), &Signature::from_slice(&s.signature).unwrap())
        .is_ok()
}

/// CLIENT-27's lockout: a rotation that COMMITTED leaves custody armed on the old key, which the
/// World no longer accepts, so a confirm signed only by the current key could never build its
/// receipt and the rotation would stay armed forever. The incoming key reads once; custody advances.
#[test]
fn a_landed_rotation_is_confirmed_through_the_incoming_key() {
    let (d, custody, _, next) = armed("lockout");
    let mut follow = EnvelopeFollow {
        world_key: next,
        incoming_asked: 0,
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.ok, b"receipt".to_vec()))]),
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
    assert_eq!(follow.incoming_asked, 1);
    assert_eq!(
        custody.public_key().unwrap(),
        next,
        "settled from the member's receipt"
    );
    assert!(custody.armed().unwrap().is_none());
    std::fs::remove_dir_all(&d).unwrap();
}

/// A Host that refuses the incoming key too: one retry, then the receipt ends refused, the attempt
/// is uncertain, the rotation stays armed, and the command goes on (never a loop).
#[test]
fn a_second_unknown_key_ends_the_confirm_uncertain() {
    let (d, custody, old, _) = armed("lockout-twice");
    let mut follow = EnvelopeFollow {
        world_key: [7; 32],
        incoming_asked: 0,
    };
    let mut host = ScriptedHost {
        replies: VecDeque::from([Ok((T.ok, b"receipt".to_vec()))]),
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
    assert_eq!((exit, follow.incoming_asked), (0, 1));
    assert_eq!(custody.public_key().unwrap(), old);
    assert!(custody.armed().unwrap().is_some());
    std::fs::remove_dir_all(&d).unwrap();
}

/// A `receipt` that does not end `ok`, or that asks custody to rotate, is no answer: nothing
/// settles, follow is told `uncertain`, and custody mints nothing.
#[test]
fn a_receipt_not_ok_or_asking_to_rotate_settles_nothing() {
    for (name, answer) in [
        (
            "not-ok",
            Step::Done {
                exit: 1,
                stdout: b"receipt 00ab\nhead 7 3 cd\nsettle committed 3 77\n".to_vec(),
                stderr: Vec::new(),
            },
        ),
        ("rotates", Step::Precommit { k: b"k".to_vec() }),
    ] {
        let (d, custody) = setup(name);
        let mut follow = ScriptedFollow {
            steps: VecDeque::from([
                Step::Submit {
                    call: b"CALL".to_vec(),
                    k: b"k1".to_vec(),
                },
                done_step(),
            ]),
            seen: Vec::new(),
            receipts: VecDeque::from([answer]),
            asked: Vec::new(),
        };
        let mut host = ScriptedHost {
            replies: VecDeque::from([Ok((T.ok, b"receipt".to_vec()))]),
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
        assert_eq!(follow.seen[0].1.status, Action::Uncertain.code(), "{name}");
        assert!(!d.join("attempts/0/settled").exists(), "{name}");
        assert_eq!(
            std::fs::metadata(d.join("keys")).unwrap().len(),
            64,
            "{name}: no pending key"
        );
        std::fs::remove_dir_all(&d).unwrap();
    }
}
