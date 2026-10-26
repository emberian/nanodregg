//! A REAL model answers the Bell (HOSTING-52, DESIGN-AGENT A0): the deployed resident, keybroker and
//! its Lean decider, the repository's anchors (`deploy/tls/anchors.pem`) and THE PIN
//! (`deploy/tls/pins`, OPS-19), the Anthropic API at Lean's host, and the operator's provider key.
//! Nothing is faked. The founder rings; the model answers; the founder reads the receipt.
//!
//! OPT-IN, never a standing row (HOSTING-27: "the real upstream is never in a test" stands for
//! `gates/runs.tsv`): it is `#[ignore]`, it spends the operator's money, and it needs the network.
//! Run it by hand:
//!
//!     ND_PROVIDER_KEY_FILE=~/.nd-agent/provider.key cargo test --locked -p nanodregg-launcher \
//!         --test agent_real -- --ignored --nocapture
//!
//! `ND_PROVIDER_KEY_FILE` names keybroker's key file (`7 <key>` on one line, mode 0600, every
//! directory above it custody-clean: RUNBOOK §2a) and is handed to keybroker as KEYS, unread by this
//! test; the key is never printed. `ND_REAL_MODEL` (default `claude-haiku-5-5`) must start with
//! `claude-` (`Broker.providerOf`). Without the file the test fails by name, never silently.
//!
//! - R1, the receipt: the operator rings `(reply with the single word pong)`; the resident asks ONCE
//!   through keybroker; the answer the Bell's `rings` row holds is the model's text: a non-empty
//!   text that is none of the resident's NAMED texts (`(refused …)`, `(status …)`, `(unanswered …)`,
//!   `(empty reply)`), so the reply came from the provider and not from a refusal rendered as text
//!   (law 7 at the agent's grain). The key is in no file of the resident's volume (control).
//! - R2, the budget: the allowance's cap is sized for exactly ONE worst-case ask (the printed body
//!   plus `maxTokens`), so the second ring, in the same window, is answered `(refused overSpend)`:
//!   the World's receipt that the agent hit its cap (`Broker.capped_decide`). The window is long
//!   (`WINDOW_MS_REAL`) so both asks fall in one; a roll between them is reported by name as
//!   inconclusive, never read as green.
//!
//! Needs the built Lean exes (`resident`, `hosting-controller`, `hosting-broker`, `host`,
//! `hosting-residents`) and the client's `nd`/`nd-supervise`. A missing one fails by name.
#![cfg(target_os = "linux")]
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)] // a plant that cannot set up is a failed plant

mod common;

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;

use common::*;
use nanodregg_devtools::{lean_bin, repo};

const LABEL: &str = "w";
/// The allowance's window: long enough that two asks a few seconds apart share it.
const WINDOW_MS_REAL: u64 = 120_000;
/// The most output tokens one ask may request: the model thinks before it answers (adaptive
/// thinking, on by default), and thinking counts toward `max_tokens`; a tight cap yields an empty
/// text, which the resident answers `(empty reply)` by name.
const MAX_TOKENS: u64 = 300;
/// The cap: one worst-case ask fits (the printed body is well under 300 bytes, so one ask charges
/// under 600 micro-units at 1000 per kTok), two do not.
const CAP: u64 = 600;

/// The Bell's state for a new bell whose resident is `resident`.
fn bell_state(resident: &str) -> String {
    format!("(record (open true) (resident #{resident}))")
}

/// The resident's config for bell `bell`: the model from the environment, a system line asking for
/// one word, `MAX_TOKENS` per ask.
fn conf(bell: &str, grant: &str, model: &str) -> String {
    format!(
        "(record (bell #{bell}) (grant #{grant}) (maxTokens {MAX_TOKENS}) (model \"{model}\") (system \"Answer with one word and nothing else.\"))"
    )
}

/// The text between `pre` and the next `end` in `l`.
fn between<'a>(l: &'a str, pre: &str, end: char) -> &'a str {
    let i = l.find(pre).unwrap_or_else(|| panic!("no `{pre}` in {l}")) + pre.len();
    let rest = &l[i..];
    &rest[..rest.find(end).unwrap()]
}

/// The answered rings of the log, as (ring text, answer text), in key order.
fn answered(out: &str) -> Vec<(String, String)> {
    out.lines()
        .filter(|l| l.contains("(answered (some (ask \""))
        .map(|l| {
            (
                between(l, "(text \"", '"').to_owned(),
                between(l, "(answered (some (ask \"", '"').to_owned(),
            )
        })
        .collect()
}

/// Whether `t` is one of the resident's NAMED answer texts (`Resident.named`): what it answers when
/// the ask brought no reply text.
fn named_text(t: &str) -> bool {
    t.starts_with("(refused ")
        || t.starts_with("(status ")
        || t.starts_with("(unanswered ")
        || t == "(empty reply)"
}

#[test]
#[ignore = "spends the operator's money through the real provider: run by hand with ND_PROVIDER_KEY_FILE"]
fn a_real_model_answers_the_bell_once_within_its_budget() {
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
    let d = dir("real");
    // the repository's anchors and pins, as the operator installs them (RUNBOOK §2a)
    let anchors = d.join("anchors.pem");
    fs::copy(repo().join("deploy/tls/anchors.pem"), &anchors).unwrap();
    fs::set_permissions(&anchors, fs::Permissions::from_mode(0o644)).unwrap();
    let pins = fs::read(repo().join("deploy/tls/pins")).unwrap();
    assert!(
        pins.starts_with(HOST.as_bytes()),
        "plant: deploy/tls/pins holds no pin for {HOST}"
    );
    pins_file(&d, &pins);
    let up = format!("{HOST}:443");
    let sock = Short::new("a");
    sockdir(&sock.0);
    let sock = &sock.0;
    let hosting = Gone(nanodregg_devtools::scratch(&format!(
        "kba{}",
        std::process::id()
    )));
    let hosting = &hosting.0;
    let world = hosting.join("worlds").join(LABEL);
    nanodregg_devtools::mkdirs(&world).unwrap();
    let roots = Roots::new('a');
    let (uid, _) = me(sock);
    let w = World::genesis_following("real", Some(world.join("store")));
    let g = w.resident("resident");
    // the allowance: one worst-case ask per window, on the real model
    let state = format!(
        "(record (cap {CAP}) (keySlot 7) (maxTokens {MAX_TOKENS}) (microPerKTok 1000) (model \"{model}\") (resident #{g}) (revoked false) (windowMs {WINDOW_MS_REAL}))"
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
    let bell_pkg = w.install("world/resident/Bell");
    let b = line(
        &w.run(&["create", "--pkg", &bell_pkg, &bell_state(&m)]),
        "id ",
    )
    .to_owned();
    let gb = line(&w.run(&["grant", &b, &m, "observe,invoke:0"]), "id ").to_owned();
    let gdir = world.join("grains").join(&g);
    let (pkg, vol) = (gdir.join("pkg"), gdir.join("vol"));
    nanodregg_devtools::mkdirs(&pkg).unwrap();
    nanodregg_devtools::mkdirs(&vol).unwrap();
    place_exe(&lean_bin("resident"), &pkg.join("resident"));
    fs::write(pkg.join("resident.conf"), conf(&b, &gb, &model)).unwrap();

    // keybroker: the real anchors, THE PIN, the operator's key, the real dial address
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
    let answers = |o: &str| answered(&w.run(&["read", o, "rings", "64"]));
    let pending = |o: &str| {
        w.run(&["read", o, "pending", "64"])
            .lines()
            .filter(|l| !l.is_empty())
            .count()
    };
    let ring = |text: &str| {
        w.run(&[
            "invoke",
            &b,
            "4",
            &format!("(record (text \"{text}\") (to none))"),
        ]);
        w.run(&["sync"]);
    };
    let window = |t: u64| t / WINDOW_MS_REAL;

    // The broker's start window is spent (`Broker.start`, HOSTING-13): nothing that costs is
    // granted until the window after keybroker's start. Wait for it, THEN ring, THEN start the
    // grain, so the first ask is decided in a fresh window.
    let waited = std::time::Instant::now();
    while window(now_ms()) <= window(t1) {
        assert!(
            waited.elapsed().as_secs() < WINDOW_MS_REAL / 1000 + 5,
            "hang: the start window did not roll"
        );
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
    let t_ring1 = now_ms();
    ring("Reply with the single word pong.");
    w.run(&["invoke", &g, "1", "(record)"]);
    w.run(&["sync"]);
    until(
        "the resident learns the bell",
        90,
        || log().contains("resident: bell answer method 0 pending limit 64"),
        &log,
    );
    until(
        "R1: the model's answer lands in rings",
        150,
        || answers(&b).len() == 1,
        &|| format!("pending {}\n{}", pending(&b), log()),
    );
    let got = answers(&b);
    let (ring1, answer1) = &got[0];
    assert_eq!(
        ring1, "Reply with the single word pong.",
        "R1: the ring's own text is captured"
    );
    assert!(
        !answer1.is_empty() && !named_text(answer1),
        "R1: the answer is not the model's words but a named text: {answer1:?}\n{}",
        log()
    );
    assert_eq!(pending(&b), 0, "R1: the ring left pending");
    assert_eq!(
        log().matches("resident: asked; answer").count(),
        1,
        "R1: exactly one ask was spent:\n{}",
        log()
    );
    for e in fs::read_dir(&vol).unwrap().filter_map(Result::ok) {
        let bytes = fs::read(e.path()).unwrap();
        let key = fs::read(&keys).unwrap();
        let secret = key.split(|b| *b == b' ').nth(1).unwrap_or(&[]);
        let secret = secret.strip_suffix(b"\n").unwrap_or(secret);
        assert!(
            secret.len() > 8 && !contains(&bytes, secret),
            "control: the key reached the resident's volume"
        );
    }
    eprintln!("R1: the model answered {answer1:?} to {ring1:?}");

    // R2: the second ring in the same window is over the cap: answered `(refused overSpend)`
    ring("Reply with the single word ping.");
    until(
        "R2: the second ring is answered",
        150,
        || answers(&b).len() == 2,
        &|| format!("pending {}\n{}", pending(&b), log()),
    );
    let t_answer2 = now_ms();
    let got = answers(&b);
    let (_, answer2) = &got[1];
    assert_eq!(
        window(t_answer2),
        window(t_ring1),
        "R2 inconclusive: the window rolled between the two asks ({} s); run again",
        (t_answer2 - t_ring1) / 1000
    );
    assert_eq!(
        answer2,
        "(refused overSpend)",
        "R2: the second ask in the window was not refused over the cap:\n{}",
        log()
    );
    assert_eq!(
        log().matches("resident: asked; answer").count(),
        2,
        "R2: two rings, two asks (the second refused before a byte left):\n{}",
        log()
    );
    eprintln!("R2: the second ring was answered {answer2:?}: the cap of {CAP} held");
    drop(gl);
    drop(kb);
    drop(members);
}
