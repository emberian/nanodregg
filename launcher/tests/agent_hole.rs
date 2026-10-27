//! The hole the agent fills, hosted (`cargo:launcher:agent_hole`, HOSTING-58, DESIGN-AGENT A2): the
//! deployed resident answers an AIMED ring of its Bell, and the answer is delivered, in the same Turn,
//! as a candidate of a document's section (`world/doc/Section`, LANG-83's `Std.hole` at bytes): the
//! Bell OBJECT holds the owner's grant on the section's `propose`, the resident only signs.
//!
//! Everything is the deployed path, as `resident_bell.rs` runs it: a real Store, keybroker on its unit's
//! argv, grain-launch over the real `hosting-controller`, the resident's member served by nd-members.
//!
//! - H1, the inbox: the operator installs the section's four shipped texts, creates a section (the
//!   operator its editor), grants THE BELL OBJECT `invoke:3` (propose) on it, and posts the fact of that
//!   grant (`(record (cell #G) (pin #G))`, owner call). It rings the Bell aimed at the section:
//!   `(to (some (record (cand #G) (method 3) (target #S) (via #G))))`.
//! - H2a, the pin is load-bearing (CONTROL): the resident's own member answers the ring, aim echoed,
//!   WITHOUT the fact pin: refused, `unpinned support0` (the hole's coverage check, LANG-79), the
//!   ring still pending. No derivation adds that pin.
//! - H2, delivered: the resident answers with the provider's text; `read S candidates` holds ONE
//!   candidate, key G, `by` the resident's member (the signer; the authority is the Bell object's
//!   grant), `value` exactly the text `rings` holds, status `verified`; the ring left `pending`.
//!   The resident pins the section's fact row the forward's support cites
//!   (`--pin S/facts (record (cell #G))`, `Lang.Bell.forwardKey`): the hole's reads are the
//!   caller's points (`Std.hole`'s `(reads (facts 3))`), which no derivation can choose.
//! - H3, withdrawn by name: the operator revokes G; `rejudge` suspends the candidate
//!   `support0 dead`, and `select` of it is refused `select: refused support0 dead`.
//! - H4, the resident withdraws by name (the `use` hole): with G retired, a ring aimed through G and
//!   then a plain ring. The first is asked about once, its answer refused; the resident probes the
//!   cells it cites, finds G gone and withdraws it by that name (`... its support <G> is gone`);
//!   the plain ring is answered in the same process, the first stays pending and is never asked again.
//!
//! The standing row runs the FAKE provider (`hello back`, HOSTING-27: "the real upstream is never in a
//! test"). `a_real_model_fills_the_section` runs the same tour on the real model, OPT-IN, never
//! standing (`#[ignore]`, as `agent_real.rs`):
//!
//!     ND_PROVIDER_KEY_FILE=~/.nd-agent/provider.key cargo test --locked -p nanodregg-launcher \
//!         --test agent_hole -- --ignored --nocapture
//!
//! Needs the built Lean exes (`resident`, `hosting-controller`, `hosting-broker`, `host`,
//! `hosting-residents`) and the client's `nd`/`nd-supervise`. A missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

use common::*;
use nanodregg_client::generated::layout::{Command as NdCommand, CommandReply};
use nanodregg_client::generated::{command_exit, follow_op, status};
use nanodregg_client::{frame, table};
use nanodregg_devtools::{lean_bin, repo};

/// One command through a member socket (the client's own frame and layout code): exit, stdout,
/// stderr (as `resident_bell.rs`).
fn member_cmd(sock: &Path, argv: &[&str]) -> (u8, String, String) {
    let mut s = UnixStream::connect(sock).unwrap();
    s.set_read_timeout(Some(table::REPLY)).unwrap();
    let c = NdCommand {
        argv: argv.iter().map(|a| a.as_bytes().to_vec()).collect(),
    }
    .encode()
    .unwrap();
    frame::write(&mut s, table::LIMITS, follow_op::COMMAND, &c).unwrap();
    let f = frame::read(&mut s, table::LIMITS).unwrap();
    assert_eq!(f.op, status::OK, "the member socket's reply status");
    let r = CommandReply::decode(&f.payload).unwrap();
    (
        r.exit,
        String::from_utf8_lossy(&r.stdout).into_owned(),
        String::from_utf8_lossy(&r.stderr).into_owned(),
    )
}

/// `sync` through a member socket until its follower is caught up (`behind` is run again).
fn member_sync(sock: &Path) {
    for _ in 0..64 {
        if member_cmd(sock, &["sync"]).0 != command_exit::BEHIND {
            return;
        }
    }
}

const LABEL: &str = "w";

/// The text between `pre` and the next `end` in `l`.
fn between<'a>(l: &'a str, pre: &str, end: char) -> &'a str {
    let i = l.find(pre).unwrap_or_else(|| panic!("no `{pre}` in {l}")) + pre.len();
    let rest = &l[i..];
    &rest[..rest.find(end).unwrap()]
}

/// The answer texts of the Bell's answered rings, in key order.
fn answered(out: &str) -> Vec<String> {
    out.lines()
        .filter(|l| l.contains("(answered (some (ask \""))
        .map(|l| between(l, "(answered (some (ask \"", '"').to_owned())
        .collect()
}

/// Whether `t` is one of the resident's NAMED answer texts (`Resident.named`).
fn named_text(t: &str) -> bool {
    t.starts_with("(refused ")
        || t.starts_with("(status ")
        || t.starts_with("(unanswered ")
        || t == "(empty reply)"
}

/// The section's shipped texts, helpers first: the root's imports name the helpers' ids.
fn section_texts() -> Vec<String> {
    let dir = repo().join("world/doc");
    ["Section.lib0", "Section.lib1", "Section.lib2", "Section"]
        .iter()
        .map(|f| fs::read_to_string(dir.join(f)).unwrap())
        .collect()
}

/// Where the resident's asks go.
enum Provider {
    /// the fake provider over the test's own PKI, answering `hello back`
    Fake,
    /// the real provider: keybroker's key file and the model
    Real { keys: PathBuf, model: String },
}

/// The tour, H1–H3, on `provider`; the candidate's text.
fn tour(provider: Provider) -> String {
    let real = matches!(provider, Provider::Real { .. });
    // each tour its own scratch, sockets and roots: the two may run in one process
    let (name, tag) = if real { ("holer", 'j') } else { ("hole", 'x') };
    let d = dir(name);
    // the provider: keys, anchors, the dial address, the model, the allowance's window
    let (keys, anchors, up, model, _fake) = match provider {
        Provider::Fake => {
            let keys = key_file(&d, 0o600);
            let pki = Pki::new();
            let anchors = pki.anchors(&d, 0o644);
            let server = pki.server(HOST, false);
            pki.pin(&d, &[&server]);
            let (up, seen) = upstream(Mode::Ok, &server);
            (keys, anchors, up, "claude-m".to_owned(), Some((pki, seen)))
        }
        Provider::Real { keys, model } => {
            let anchors = d.join("anchors.pem");
            fs::copy(repo().join("deploy/tls/anchors.pem"), &anchors).unwrap();
            fs::set_permissions(&anchors, fs::Permissions::from_mode(0o644)).unwrap();
            let pins = fs::read(repo().join("deploy/tls/pins")).unwrap();
            assert!(
                pins.starts_with(HOST.as_bytes()),
                "plant: deploy/tls/pins holds no pin for {HOST}"
            );
            pins_file(&d, &pins);
            (keys, anchors, format!("{HOST}:443"), model, None)
        }
    };
    let sock = Short::new(&tag.to_string());
    sockdir(&sock.0);
    let sock = &sock.0;
    let hosting = Gone(nanodregg_devtools::scratch(&format!(
        "kbh{}{tag}",
        std::process::id()
    )));
    let hosting = &hosting.0;
    let world = hosting.join("worlds").join(LABEL);
    nanodregg_devtools::mkdirs(&world).unwrap();
    let roots = Roots::new(tag);
    let (uid, _) = me(sock);
    let w = World::genesis_following(name, Some(world.join("store")));
    let g = w.resident("resident");
    // the allowance: one ask of at most 300 tokens, in a window long enough for the tour
    let state = format!(
        "(record (cap 100000) (keySlot 7) (maxTokens 300) (microPerKTok 1000) (model \"{model}\") (resident #{g}) (revoked false) (windowMs {}))",
        if real { 120_000 } else { WINDOW_MS }
    );
    w.run(&["create", "--pkg", &w.pkg, &state]);
    let m = w.provision(&roots, &g);
    let members = Members::start(&w, &roots, uid);
    let msock = roots.sock(&g);
    until(
        "nd-members binds the resident's member socket",
        60,
        || msock.exists(),
        &|| members.log(),
    );
    let op = w.operator.clone();

    // H1: the Bell (its resident the grain's member) and the section (the operator its editor)
    let bell_pkg = w.install("world/resident/Bell");
    let b = line(
        &w.run(&[
            "create",
            "--pkg",
            &bell_pkg,
            &format!("(record (open true) (resident #{m}))"),
        ]),
        "id ",
    )
    .to_owned();
    let gb = line(&w.run(&["grant", &b, &m, "observe,invoke:0"]), "id ").to_owned();
    let mut ids = Vec::new();
    for t in section_texts() {
        ids.push(line(&w.run(&["install", &t]), "id ").to_owned());
    }
    let section = ids.last().unwrap().clone();
    let s = line(
        &w.run(&[
            "create",
            "--pkg",
            &section,
            &format!(
                "(record (accepted false) (acceptor #{op}) (cap 2000) (chooser #{op}) (closes 100000) (selected none))"
            ),
        ]),
        "id ",
    )
    .to_owned();
    let desc = w.run(&["read", &s, "?"]);
    for meth in [
        "method 2 post",
        "method 3 propose",
        "method 5 rejudge",
        "method 9 select",
    ] {
        assert!(desc.contains(meth), "the section's methods: {desc}");
    }
    // the owner grants THE BELL OBJECT propose on the section, and posts the fact of that grant
    let gs = line(&w.run(&["grant", &s, &b, "invoke:3"]), "id ").to_owned();
    w.run(&[
        "invoke",
        &s,
        "2",
        &format!("(record (cell #{gs}) (pin #{gs}))"),
    ]);
    let question = if real {
        "Write one short sentence for the first section of a document about lighthouses."
    } else {
        "what should the first section say?"
    };
    w.run(&[
        "invoke",
        &b,
        "4",
        &format!(
            "(record (text \"{question}\") (to (some (record (cand #{gs}) (method 3) (target #{s}) (via #{gs})))))"
        ),
    ]);
    w.run(&["sync"]);
    let pending = w.run(&["read", &b, "pending", "64"]);
    assert!(
        pending.contains(&format!("(target #{s})")),
        "H1: the pending ring holds the aim: {pending}"
    );

    // H2a: the resident's member answers as the resident does but without the fact pin: refused by
    // the section's coverage check, and the ring stays pending for the grain
    let nb = between(&pending, "(notBefore ", ')').to_owned();
    let aim = format!("(some (record (cand #{gs}) (method 3) (target #{s}) (via #{gs})))");
    let unpinned = format!(
        "(record (notBefore {nb}) (ringText \"{question}\") (ringer #{op}) (text \"no pin\") (to {aim}))"
    );
    member_sync(&msock);
    let (exit, out, err) = member_cmd(&msock, &["invoke", &b, "0", &unpinned, "--via", &gb]);
    assert_ne!(
        exit, 0,
        "H2a: an answer without the fact pin was admitted: {out}{err}"
    );
    assert!(
        format!("{out}{err}").contains("unpinned support0"),
        "H2a: the refusal names the missing support pin: {out}{err}"
    );
    assert!(
        w.run(&["read", &b, "pending", "64"])
            .contains(&format!("(target #{s})")),
        "H2a: the ring is still pending"
    );

    // the grain's package: the resident and its config
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(&lean_bin("resident"), &pkg.join("resident"));
    let system = if real {
        "Answer with one plain sentence and nothing else."
    } else {
        ""
    };
    fs::write(
        pkg.join("resident.conf"),
        format!(
            "(record (bell #{b}) (grant #{gb}) (maxTokens 300) (model \"{model}\") (system \"{system}\"))"
        ),
    )
    .unwrap();
    let kb = start_residents(
        sock,
        &d.join("pids"),
        &keys,
        &anchors,
        &up,
        &w,
        &[g.as_str(), w.r1.as_str()],
        uid,
    );
    let t1 = now_ms();
    // the broker's start window is spent (HOSTING-13): the first ask is decided in the next one
    let window = if real { 120_000 } else { WINDOW_MS };
    while now_ms() / window <= t1 / window {
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    let gl_pids = d.join("gl-pids");
    nanodregg_devtools::mkdirs(&gl_pids).unwrap();
    let store = world.join("store");
    let controller = lean_bin("hosting-controller");
    let gl = Logged::spawn(
        grain_launch_rendered(&[
            ("/srv/nd-hosted", hosting.as_os_str()),
            ("/run/nd-broker", sock.as_os_str()),
            ("/run/nd-member", roots.member.0.as_os_str()),
            ("%i", LABEL.as_ref()),
            ("/run/nd-grain-launch/%i", gl_pids.as_os_str()),
            ("/opt/nd/bin/hosting-controller", controller.as_os_str()),
            ("/srv/nd-hosted/worlds/%i/store", store.as_os_str()),
        ]),
        d.join("grain-launch.pid"),
    );
    let log = || gl.log();
    w.run(&["invoke", &g, "1", "(record)"]);
    w.run(&["sync"]);

    // H2: the answer lands in `rings` AND as the section's candidate, in one Turn
    let answers = || answered(&w.run(&["read", &b, "rings", "64"]));
    until(
        "H2: the aimed ring is answered",
        150,
        || {
            w.run(&["sync"]);
            answers().len() == 1
        },
        &|| {
            format!(
                "pending {}\ncandidates {}\n{}",
                w.run(&["read", &b, "pending", "64"]),
                w.run(&["read", &s, "candidates", "8"]),
                log()
            )
        },
    );
    let text = answers().remove(0);
    if real {
        assert!(
            !text.is_empty() && !named_text(&text),
            "H2: the answer is a named text, not the model's words: {text:?}\n{}",
            log()
        );
    } else {
        assert_eq!(text.as_bytes(), REPLY, "H2: the fake provider's text");
    }
    let cands = w.run(&["read", &s, "candidates", "8"]);
    let rows: Vec<&str> = cands.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(rows.len(), 1, "H2: one candidate: {cands}");
    let row = rows[0];
    assert!(
        row.contains(&format!("(cand #{gs})")),
        "H2: the candidate's key is the aim's: {row}"
    );
    assert!(
        row.contains(&format!("(by #{m})")),
        "H2: by the resident's member: {row}"
    );
    assert!(
        row.contains(&format!("(value \"{text}\")")),
        "H2: the section holds exactly the text the Bell's rings row holds: {row}"
    );
    assert!(
        row.contains("verified"),
        "H2: the candidate is verified: {row}"
    );
    assert_eq!(
        w.run(&["read", &b, "pending", "64"]).trim(),
        "",
        "H2: the ring left pending"
    );
    assert_eq!(
        log().matches("resident: asked; answer").count(),
        1,
        "H2: exactly one ask:\n{}",
        log()
    );
    eprintln!("H2: the agent's text {text:?} is the section's candidate");

    // H3: the owner revokes the Bell's grant: the candidate is suspended by name, its selection refused
    let cand = format!("(record (cand #{gs}))");
    let fact = format!("(record (cell #{gs}))");
    let judged = |method: &str| {
        w.nd(&[
            "invoke",
            &s,
            method,
            &cand,
            "--pin",
            "candidates",
            &cand,
            "--pin",
            "facts",
            &fact,
        ])
    };
    w.run(&["retire", &gs]);
    let o = judged("5");
    assert!(o.status.success(), "H3: rejudge: {}", both(&o));
    let cands = w.run(&["read", &s, "candidates", "8"]);
    assert!(
        cands.contains("suspended") && cands.contains("support0 dead"),
        "H3: the revoked support suspends the candidate by name: {cands}"
    );
    let o = judged("9");
    assert!(
        !o.status.success(),
        "H3: a select of the withdrawn text was admitted"
    );
    assert!(
        both(&o).contains("select: refused support0 dead"),
        "H3: the select is refused by name: {}",
        both(&o)
    );
    if !real {
        h4(&w, &b, &s, &gs, &aim, &answers, &log);
    }
    drop(gl);
    drop(kb);
    drop(members);
    text
}

/// H4, a ring through a retired grant is withdrawn by name and the queue goes on: with `gs` retired
/// (H3), a ring aimed through it, then a plain ring. The resident asks about the first, its answer is
/// refused (`refused missingCell`: the member's line names no cell, MEASURED), the resident probes the
/// cells the answer cites (`read CELL ?`), finds the grant gone, and the `use` slot WITHDRAWS the answer
/// by that name (`resident: answer withdrawn ... its support <cell> is gone (<the line>)`); the second
/// ring is asked about and answered in the same process. The first stays pending, never asked again;
/// no `answerRefused`.
fn h4(
    w: &World,
    b: &str,
    s: &str,
    gs: &str,
    aim: &str,
    answers: &dyn Fn() -> Vec<String>,
    log: &dyn Fn() -> String,
) {
    w.run(&[
        "invoke",
        b,
        "4",
        &format!("(record (text \"through a retired grant\") (to {aim}))"),
    ]);
    w.run(&["sync"]);
    w.run(&[
        "invoke",
        b,
        "4",
        "(record (text \"a plain question\") (to none))",
    ]);
    until(
        "H4: the plain ring is answered past the withdrawn one",
        150,
        || {
            w.run(&["sync"]);
            answers().len() == 2
        },
        &|| format!("pending {}\n{}", w.run(&["read", b, "pending", "64"]), log()),
    );
    let l = log();
    let withdrawn: Vec<&str> = l
        .lines()
        .filter(|x| x.contains("resident: answer withdrawn"))
        .collect();
    assert_eq!(withdrawn.len(), 1, "H4: one withdrawal:\n{l}");
    let named = withdrawn[0];
    assert!(
        named.contains(&format!("its support {gs} is gone"))
            || named.contains(&format!("its support {s} is gone")),
        "H4: the withdrawal names the aim's via or target: {named}"
    );
    eprintln!("H4 (measured): {named}");
    assert!(!l.contains("answerRefused"), "H4: the queue stopped:\n{l}");
    let pending = w.run(&["read", b, "pending", "64"]);
    assert!(
        pending.contains("through a retired grant") && !pending.contains("a plain question"),
        "H4: the withdrawn ring waits, the plain one was answered: {pending}"
    );
    assert!(
        answers().iter().any(|t| t.as_bytes() == REPLY),
        "H4: the plain ring's answer"
    );
    // more ticks: the withdrawn ring is never asked about again while it waits
    std::thread::sleep(std::time::Duration::from_secs(5));
    assert_eq!(
        log().matches("resident: asked; answer").count(),
        3,
        "H4: three asks in all (H2, the withdrawn ring once, the plain ring):\n{}",
        log()
    );
}

#[test]
fn the_agent_fills_the_section_and_the_revoke_withdraws_it() {
    tour(Provider::Fake);
}

#[test]
#[ignore = "spends the operator's money through the real provider: run by hand with ND_PROVIDER_KEY_FILE"]
fn a_real_model_fills_the_section() {
    let keys = PathBuf::from(
        std::env::var_os("ND_PROVIDER_KEY_FILE")
            .expect("plant: ND_PROVIDER_KEY_FILE names keybroker's key file (RUNBOOK §2a)"),
    );
    assert!(keys.is_file(), "plant: no key file at {}", keys.display());
    let model = std::env::var("ND_REAL_MODEL").unwrap_or_else(|_| "claude-haiku-5-5".into());
    assert!(
        model.starts_with("claude-"),
        "plant: ND_REAL_MODEL {model} is in no row of Broker.providers"
    );
    let text = tour(Provider::Real { keys, model });
    eprintln!("the model wrote the section's candidate: {text:?}");
}
