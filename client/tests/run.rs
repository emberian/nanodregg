//! The step loop against a scripted follow and host: challenge → sign → prepare → sign → submit
//! (reply lost) → lookup → done. Follow decides every step; the loop only performs them.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::collections::VecDeque;
use std::io;

use nanodregg_client::custody::Custody;
use nanodregg_client::run::{self, Follow, Host, Outcome, RunError, Step, Table};

// Test values, not the protocol's: the real ones are generated from Protocol/Table.lean.
const T: Table = Table {
    steps_max: 8,
    sends_max: 2,
    submit: 1,
    lookup: 2,
    ok: 0,
    refused: 1,
    absent: 3,
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
    let d = std::env::temp_dir().join(format!("nd-run-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(d.join("attempts")).unwrap();
    Custody::create(&d, "seed").unwrap();
    let c = Custody::open(&d.join("seed")).unwrap();
    (d, c)
}

#[test]
fn round_trip_with_a_lost_submit_reply() {
    let (d, custody) = setup("trip");
    let mut follow = ScriptedFollow {
        steps: VecDeque::from([
            Step::Host {
                op: 3,
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
        Outcome::Signature(custody.sign(b"observation").to_vec())
    );
    assert_eq!(
        follow.seen[3],
        (
            b"k4".to_vec(),
            Outcome::Reply {
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
