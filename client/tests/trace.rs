//! The member rows' conversations with nd, replayed (DESIGN-QA Q5). Each `tests/traces/ROW.trace`
//! is what `lake exe emit-traces` recorded when member row ROW ran, and passed, at the deployed
//! parameters: every `nd` run's argv, every exchange on follow's socket and on the Host's, and the
//! command's end (the format is `Emit/Traces.lean`'s). Here nd's own step loop (`run::run`), attempt
//! store and custody run each recorded run against a peer that answers exactly what follow and the
//! Host answered. A run fails at the first request nd makes that the trace does not hold, byte for
//! byte, at a request it leaves unmade, or at an end that differs. Nothing in this file says what
//! nd should do: the trace is the rows' run, and `gates/generated.tsv` re-emits and compares it.
#![allow(clippy::unwrap_used, clippy::panic)] // a replay that cannot set up is a failed replay
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::fs;
use std::io::{self, Write as _};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::rc::Rc;

use nanodregg_client::custody::Custody;
use nanodregg_client::generated::layout::Step;
use nanodregg_client::run::{self, Follow, Host, Outcome};
use nanodregg_client::{sockets, table};

/// One exchange the trace holds: what nd sent and what it read back (`None`: no reply at all).
#[derive(Debug)]
enum Exchange {
    Follow {
        op: u8,
        req: Vec<u8>,
        status: u8,
        reply: Vec<u8>,
    },
    Host {
        op: u8,
        req: Vec<u8>,
        reply: Option<(u8, Vec<u8>)>,
    },
}

/// One `nd` run: who ran it, its argv, its exchanges in order, and its end (`None`: `end N error`).
struct Run {
    actor: String,
    argv: Vec<Vec<u8>>,
    exchanges: VecDeque<Exchange>,
    end: Option<(u8, Vec<u8>, Vec<u8>)>,
}

struct Trace {
    /// Each actor's key-file seeds (generations 0, 1, 2).
    custody: Vec<(String, Vec<Vec<u8>>)>,
    runs: BTreeMap<u64, Run>,
}

fn hex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn show(b: &[u8]) -> String {
    let h: String = b.iter().take(48).map(|x| format!("{x:02x}")).collect();
    if b.len() > 48 {
        format!("{h}… ({} bytes)", b.len())
    } else {
        format!("{h} ({} bytes)", b.len())
    }
}

/// Where `sent` first differs from `held`: the offset and the 16 bytes from it on each side.
fn first_difference(sent: &[u8], held: &[u8]) -> String {
    let at = sent
        .iter()
        .zip(held)
        .position(|(a, b)| a != b)
        .unwrap_or(sent.len().min(held.len()));
    let from = |b: &[u8]| -> String { b.iter().skip(at).take(16).map(|x| format!("{x:02x}")).collect() };
    format!(
        "first difference at byte {at}: nd {} | trace {}",
        from(sent),
        from(held)
    )
}

fn parse(text: &str) -> Trace {
    let mut t = Trace {
        custody: Vec::new(),
        runs: BTreeMap::new(),
    };
    for line in text.lines().filter(|l| !l.starts_with('#')) {
        let w: Vec<&str> = line.split(' ').collect();
        let n = || w[1].parse::<u64>().unwrap();
        fn run(t: &mut Trace, n: u64) -> &mut Run {
            t.runs.get_mut(&n).unwrap()
        }
        match w[0] {
            "custody" => t
                .custody
                .push((w[1].to_string(), w[2..].iter().map(|s| hex(s)).collect())),
            "run" => {
                let r = Run {
                    actor: w[2].to_string(),
                    argv: w[3..].iter().map(|s| hex(s)).collect(),
                    exchanges: VecDeque::new(),
                    end: None,
                };
                t.runs.insert(n(), r);
            }
            "follow" => run(&mut t, n()).exchanges.push_back(Exchange::Follow {
                op: w[2].parse().unwrap(),
                req: hex(w[3]),
                status: w[4].parse().unwrap(),
                reply: hex(w[5]),
            }),
            "host" => run(&mut t, n()).exchanges.push_back(Exchange::Host {
                op: w[2].parse().unwrap(),
                req: hex(w[3]),
                reply: (w[4] != "lost").then(|| (w[4].parse().unwrap(), hex(w[5]))),
            }),
            "end" if w[2] == "error" => {}
            "end" => run(&mut t, n()).end = Some((w[2].parse().unwrap(), hex(w[3]), hex(w[4]))),
            other => panic!("trace: unknown line kind {other}"),
        }
    }
    t
}

/// The peer of one run: follow and the Host as the trace heard them. The first request nd makes that
/// is not the trace's next one is kept, and every request after it fails.
struct Peer {
    exchanges: VecDeque<Exchange>,
    diverged: Option<String>,
}

impl Peer {
    fn diverge(&mut self, what: String) -> io::Error {
        let e = io::Error::other(format!("trace: {what}"));
        self.diverged.get_or_insert(what);
        e
    }

    fn follow(&mut self, op: u8, req: &[u8]) -> io::Result<Step> {
        if self.diverged.is_some() {
            return Err(io::Error::other("trace: diverged"));
        }
        match self.exchanges.pop_front() {
            Some(Exchange::Follow {
                op: o,
                req: r,
                status,
                reply,
            }) if o == op && r == req => sockets::step(status, &reply),
            held => Err(self.diverge(format!(
                "nd sent follow op {op} {}; the trace holds {}{}",
                show(req),
                expected(held.as_ref()),
                difference(req, held.as_ref())
            ))),
        }
    }

    fn host(&mut self, op: u8, req: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        if self.diverged.is_some() {
            return Err(io::Error::other("trace: diverged"));
        }
        match self.exchanges.pop_front() {
            Some(Exchange::Host {
                op: o,
                req: r,
                reply,
            }) if o == op && r == req => {
                reply.ok_or_else(|| io::Error::from(io::ErrorKind::ConnectionReset))
            }
            held => Err(self.diverge(format!(
                "nd sent host op {op} {}; the trace holds {}{}",
                show(req),
                expected(held.as_ref()),
                difference(req, held.as_ref())
            ))),
        }
    }
}

fn difference(sent: &[u8], held: Option<&Exchange>) -> String {
    match held {
        Some(Exchange::Follow { req, .. } | Exchange::Host { req, .. }) => {
            format!("; {}", first_difference(sent, req))
        }
        None => String::new(),
    }
}

fn expected(e: Option<&Exchange>) -> String {
    match e {
        None => "nothing more".to_string(),
        Some(Exchange::Follow { op, req, .. }) => format!("follow op {op} {}", show(req)),
        Some(Exchange::Host { op, req, .. }) => format!("host op {op} {}", show(req)),
    }
}

struct TraceFollow(Rc<RefCell<Peer>>);
struct TraceHost(Rc<RefCell<Peer>>);

impl Follow for TraceFollow {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        let (op, p) = sockets::command(argv)?;
        self.0.borrow_mut().follow(op, &p)
    }
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step> {
        let (op, p) = sockets::resume(k, outcome)?;
        self.0.borrow_mut().follow(op, &p)
    }
}

impl Host for TraceHost {
    fn exchange(&mut self, op: u8, payload: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        self.0.borrow_mut().host(op, payload)
    }
}

/// A one-record custody (`keys = current ‖ next ‖ pending`) holding the trace's seeds.
fn workspace(root: &Path, actor: &str, seeds: &[Vec<u8>]) {
    let ws = root.join(actor);
    nanodregg_devtools::mkdirs(&ws.join("attempts")).unwrap();
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(ws.join("keys"))
        .unwrap()
        .write_all(&seeds.concat())
        .unwrap();
}

/// Replay every run of trace `text` (named `row`) in the order the runs started, each actor's runs
/// over one workspace (so an attempt one run left open is the next run's). The first failure, named
/// by row, run, actor and argv.
fn replay(row: &str, text: &str) -> Result<(), String> {
    let t = parse(text);
    if t.runs.is_empty() {
        return Err(format!("{row}: no runs"));
    }
    let root = nanodregg_devtools::scratch(&format!("nd-trace-{}-{row}", std::process::id()));
    for (actor, seeds) in &t.custody {
        workspace(&root, actor, seeds);
    }
    let mut verdict = Ok(());
    for (n, r) in t.runs {
        let ws = root.join(&r.actor);
        let custody = Custody::open(&ws, None).unwrap();
        let peer = Rc::new(RefCell::new(Peer {
            exchanges: r.exchanges,
            diverged: None,
        }));
        let got = run::run(
            &r.argv,
            &mut TraceFollow(peer.clone()),
            &mut TraceHost(peer.clone()),
            &custody,
            &ws.join("attempts"),
            table::RUN,
        );
        let argv: Vec<String> = r
            .argv
            .iter()
            .map(|a| String::from_utf8_lossy(a).chars().take(40).collect())
            .collect();
        let at = format!("{row} run {n} ({} nd {})", r.actor, argv.join(" "));
        let p = peer.borrow();
        let failed = if let Some(d) = &p.diverged {
            Some(d.clone())
        } else if !p.exchanges.is_empty() {
            Some(format!(
                "nd ended with {} exchanges of the trace unmade, the next {}",
                p.exchanges.len(),
                expected(p.exchanges.front())
            ))
        } else {
            match (got, r.end) {
                (Ok(done), Some(end)) if done == end => None,
                (Err(_), None) => None,
                (got, end) => Some(format!("nd ended {got:?}; the trace ends {end:?}")),
            }
        };
        if let Some(why) = failed {
            verdict = Err(format!("{at}: {why}"));
            break;
        }
    }
    fs::remove_dir_all(&root).unwrap();
    verdict
}

fn traces() -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/traces");
    let mut ts: Vec<(String, String)> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "trace"))
        .map(|p| {
            let row = p.file_stem().unwrap().to_string_lossy().into_owned();
            (row, fs::read_to_string(&p).unwrap())
        })
        .collect();
    ts.sort();
    ts
}

/// Every emitted trace replays: nd sends exactly what the rows' client sent, and ends as it ended.
#[test]
fn every_trace_replays() {
    let ts = traces();
    assert!(
        ts.iter().any(|(r, _)| r == "rerun"),
        "the rerun trace (CLIENT-37, A6) is missing"
    );
    let failed: Vec<String> = ts
        .iter()
        .filter_map(|(row, text)| replay(row, text).err())
        .collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// The control: a trace whose re-run expects one request byte nd does not send is refused at that
/// request. The rerun trace's lookup of the frozen call (CLIENT-37: the request A6's re-run never
/// made) with its last byte flipped.
#[test]
fn a_request_the_trace_does_not_hold_is_refused() {
    let (_, text) = traces().into_iter().find(|(r, _)| r == "rerun").unwrap();
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    // the re-run: the run whose actor and argv an earlier run already had
    let mut seen = Vec::new();
    let rerun = lines
        .iter()
        .filter_map(|l| l.strip_prefix("run "))
        .find_map(|r| {
            let (n, who) = r.split_once(' ').unwrap();
            if seen.contains(&who) {
                return Some(n.to_string());
            }
            seen.push(who);
            None
        })
        .unwrap();
    let i = lines
        .iter()
        .position(|l| l.starts_with(&format!("host {rerun} ")))
        .unwrap();
    let mut w: Vec<String> = lines[i].split(' ').map(str::to_string).collect();
    let req = &mut w[3];
    let last = u8::from_str_radix(&req[req.len() - 2..], 16).unwrap() ^ 1;
    req.replace_range(req.len() - 2.., &format!("{last:02x}"));
    lines[i] = w.join(" ");
    let err = replay("rerun-flipped", &lines.join("\n")).unwrap_err();
    assert!(err.contains("nd sent host op"), "{err}");
}
