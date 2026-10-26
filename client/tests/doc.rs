//! The DOCUMENT, driven by two real members over `nd` (DESIGN-CTX §4, S1; decisions/lang.md LANG-83):
//! a section is a `Std.hole` at `bytes` whose candidates are texts members POST, each justified by
//! the poster's own grant (a kernel cell, read LIVE: LANG-75.1), chosen by the section's editor.
//! The shipped texts `world/doc/Section.lib0..2` and `world/doc/Section` (the root, linked by the
//! helpers' deployed ids) are what `lang-journey --write world/doc` emits and what its DC0 rows
//! check; here they are installed for real, over `host serve` and two `host follow`s (the founder
//! A, the editor; B, joined over a signed invitation as `join.rs` joins, the contributor).
//!
//! What a member sees: B's text is proposed under B's grant and A selects it; A revokes the grant
//! and the next judgment records the text `suspended "support0 dead"` BY NAME (a `select` of it is
//! refused `support0 dead`); B contributes again under a new grant and A selects the new text. The
//! document repaired; nobody re-installed anything. Every verdict here is Lean's; nd moves bytes
//! and signs.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use nanodregg_client::generated::command_exit;
use nanodregg_devtools::{Supervisor, mkdirs};

fn line<'a>(out: &'a str, key: &str) -> &'a str {
    out.lines()
        .find_map(|l| l.strip_prefix(key).map(str::trim))
        .unwrap_or_else(|| panic!("no `{key}` line in:\n{out}"))
}

fn text(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn err(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

fn supervise(sock: &Path, ws: &Path, store: &Path, args: &[&str]) -> Supervisor {
    let sup = Path::new(env!("CARGO_BIN_EXE_nd-supervise"));
    nanodregg_devtools::supervise_host(sup, sock, ws, store, args)
}

/// A member: its workspace, its holding and the writer's socket (as `join.rs`).
struct Member {
    ws: PathBuf,
    holding: PathBuf,
    host_sock: PathBuf,
}

impl Member {
    fn new(root: &Path, name: &str, host_sock: &Path) -> Self {
        let holding = root.join(format!("{name}-holding"));
        mkdirs(&holding).unwrap();
        let m = Self {
            ws: root.join(name),
            holding,
            host_sock: host_sock.to_owned(),
        };
        assert!(m.nd(&["--init"]).status.success());
        m
    }
    fn nd(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_nd"))
            .env("ND_WORKSPACE", &self.ws)
            .env("ND_HOLDING", &self.holding)
            .env("ND_HOST_SOCK", &self.host_sock)
            .args(args)
            .output()
            .unwrap()
    }
    fn ok(&self, args: &[&str]) -> String {
        let o = self.nd(args);
        assert!(o.status.success(), "nd {args:?}: {}{}", text(&o), err(&o));
        text(&o)
    }
    /// (stderr, stdout) of a refused command.
    fn refused(&self, args: &[&str]) -> (String, String) {
        let o = self.nd(args);
        assert_eq!(
            o.status.code(),
            Some(i32::from(command_exit::REFUSED)),
            "nd {args:?}: {}{}",
            text(&o),
            err(&o)
        );
        (err(&o), text(&o))
    }
}

/// The shipped texts, in install order: the three helpers, then the root.
fn shipped() -> Vec<String> {
    let dir = nanodregg_devtools::repo().join("world/doc");
    ["Section.lib0", "Section.lib1", "Section.lib2", "Section"]
        .iter()
        .map(|f| std::fs::read_to_string(dir.join(f)).unwrap())
        .collect()
}

#[test]
fn a_section_repairs_across_a_revoked_contributor() {
    let host = nanodregg_devtools::lean_bin("host");
    let root = nanodregg_devtools::scratch(&format!("nddoc-{}", std::process::id()));
    for d in ["stores/W", "stores/F", "stores/B", "keys"] {
        mkdirs(&root.join(d)).unwrap();
    }
    let root = root.canonicalize().unwrap();
    let host_sock = root.join("a.host.sock");
    let a = Member::new(&root, "a", &host_sock);
    let keys = a.ok(&["--keys"]);
    let (key, next) = (
        line(&keys, "key ").to_owned(),
        line(&keys, "next ").to_owned(),
    );
    let genesis = |s: &Path, nonce: Option<&str>| {
        let mut cmd = Command::new(&host);
        cmd.arg("genesis").arg(s).arg("nano");
        if let Some(n) = nonce {
            cmd.args(["--nonce", n]);
        }
        let o = cmd.args([&key, &next]).output().unwrap();
        assert!(o.status.success(), "genesis: {}", err(&o));
        text(&o)
    };
    let (w, f) = (root.join("stores/W"), root.join("stores/F"));
    let g = genesis(&w, None);
    genesis(&f, Some(line(&g, "nonce ")));
    a.ok(&["--input", line(&g, "input ")]);
    let (member, grant) = line(&g, "founder 0 member ").split_once(" grant ").unwrap();
    let _writer = supervise(&host_sock, &a.ws, &w, &["serve", w.to_str().unwrap()]);
    let _fa = supervise(
        &a.ws.join("follow.sock"),
        &a.ws,
        &f,
        &["follow", f.to_str().unwrap(), member, grant],
    );

    // The shipped texts install, helpers first; the root's imports name the helpers' ids.
    let mut ids = Vec::new();
    for t in shipped() {
        ids.push(line(&a.ok(&["install", &t]), "id ").to_owned());
    }
    let section = ids.last().unwrap().clone();
    let state = format!(
        "(record (accepted false) (acceptor #{member}) (cap 2000) (chooser #{member}) (closes 100000) (selected none))"
    );
    let obj = line(&a.ok(&["create", "--pkg", &section, &state]), "id ").to_owned();
    let desc = a.ok(&["read", &obj, "?"]);
    for m in [
        "method 2 post",
        "method 3 propose",
        "method 5 rejudge",
        "method 9 select",
    ] {
        assert!(desc.contains(m), "{desc}");
    }

    // B joins over A's signed invitation and follows with its own Store (as join.rs).
    let invitation = line(&a.ok(&["invite"]), "invite ").to_owned();
    let key_file = root.join("keys/sponsor.pub");
    std::fs::write(&key_file, format!("{key}\n")).unwrap();
    std::fs::set_permissions(&key_file, PermissionsExt::from_mode(0o644)).unwrap();
    let b = Member::new(&root, "b", &host_sock);
    let store_b = root.join("stores/B");
    let joined = b.nd(&[
        "--join",
        key_file.to_str().unwrap(),
        &invitation,
        store_b.to_str().unwrap(),
        host.to_str().unwrap(),
    ]);
    assert!(joined.status.success(), "{}", err(&joined));
    let joined = text(&joined);
    let b_id = line(&a.ok(&["enroll", line(&joined, "join ")]), "id ").to_owned();
    let observe = line(
        &a.ok(&["grant", "world", &b_id, "observe", "--via", grant]),
        "id ",
    )
    .to_owned();
    let _fb = supervise(
        &b.ws.join("follow.sock"),
        &b.ws,
        &store_b,
        &["follow", store_b.to_str().unwrap(), &b_id, &observe],
    );

    // A contributor's grant: post (its support fact) and propose (its text). The fact names the
    // grant cell itself; the candidate's support cites it; the reads of it are LIVE.
    let contribute = |text: &str| -> (String, String) {
        let g = line(&a.ok(&["grant", &obj, &b_id, "invoke:2,invoke:3"]), "id ").to_owned();
        b.ok(&[
            "invoke",
            &obj,
            "2",
            &format!("(record (cell #{g}) (pin #{g}))"),
            "--via",
            &g,
        ]);
        // the candidate's key is the grant's own id: one text per contribution
        let proposal = format!(
            "(record (cand #{g}) (s0 (some (record (cell #{g}) (pin #{g})))) (s1 none) (value \"{text}\"))"
        );
        b.ok(&[
            "invoke",
            &obj,
            "3",
            &proposal,
            "--pin",
            "facts",
            &format!("(record (cell #{g}))"),
            "--via",
            &g,
        ]);
        (g.clone(), g)
    };
    let (g1, c1) = contribute("a light on the rock");
    let rows = a.ok(&["read", &obj, "candidates", "8"]);
    assert!(
        rows.contains("verified") && rows.contains("a light on the rock"),
        "{rows}"
    );
    let cand = |c: &str| format!("(record (cand #{c}))");
    let fact = |g: &str| format!("(record (cell #{g}))");
    // The editor selects B's text, pinning the candidate row and the support's fact row.
    a.ok(&[
        "invoke",
        &obj,
        "9",
        &cand(&c1),
        "--pin",
        "candidates",
        &cand(&c1),
        "--pin",
        "facts",
        &fact(&g1),
    ]);
    // the section's state, printed by the one printer: `selected` names B's text
    let state = a.ok(&["read", &obj]);
    assert!(state.contains(&c1), "selected: {state}");

    // The grant revoked: the justification is withdrawn, and the next judgment says so by name.
    a.ok(&["revoke", &g1]);
    a.ok(&[
        "invoke",
        &obj,
        "5",
        &cand(&c1),
        "--pin",
        "candidates",
        &cand(&c1),
        "--pin",
        "facts",
        &fact(&g1),
    ]);
    let rows = a.ok(&["read", &obj, "candidates", "8"]);
    assert!(
        rows.contains("suspended") && rows.contains("support0 dead"),
        "{rows}"
    );
    let (e, o) = a.refused(&[
        "invoke",
        &obj,
        "9",
        &cand(&c1),
        "--pin",
        "candidates",
        &cand(&c1),
        "--pin",
        "facts",
        &fact(&g1),
    ]);
    assert_eq!(e, "refused program\n");
    assert!(o.contains("select: refused support0 dead"), "{o}");

    // B contributes again under a new grant; the editor selects the new text: repaired.
    let (g2, c2) = contribute("a ship in the fog");
    a.ok(&[
        "invoke",
        &obj,
        "9",
        &cand(&c2),
        "--pin",
        "candidates",
        &cand(&c2),
        "--pin",
        "facts",
        &fact(&g2),
    ]);
    let rows = a.ok(&["read", &obj, "candidates", "8"]);
    assert!(rows.contains("a ship in the fog"), "{rows}");
    let state = a.ok(&["read", &obj]);
    assert!(
        state.contains(&c2) && !state.contains(&c1),
        "selected: {state}"
    );
    drop((_fb, _fa, _writer));
    std::fs::remove_dir_all(&root).unwrap();
}
