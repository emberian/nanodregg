//! A member's own Store from an invitation its sponsor signed (CLIENT-26, PROTOCOL-42):
//! `nd --join KEY_FILE INVITATION STORE /ABS/HOST`. The sponsor's public key arrives as a FILE
//! (the trust root, read under custody's chain rule); the invitation as a hex ARGUMENT (untrusted
//! until Lean accepts it). nd decides nothing: `host join` runs `Invite.accept` under the key and
//! writes STORE only if it passed (`join_genesis_iff`); `init SPONSOR` is follow's. nd keeps two
//! non-secret files: `invitation` (read by `nd adopt KEY_FILE`) and `input`, the World's genesis
//! inputs as host printed them (read by bare `nd invite`; a founder keeps its own with `nd --input
//! HEX`).

use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::os::fd::OwnedFd;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Command, Stdio};

use nanodregg_sandbox::Policy;
use nanodregg_sandbox::custody::{read_private, read_public};

use crate::custody::Custody;
use crate::generated::{ARGV_BYTES_MAX, command_exit, host_status, layout::Step};
use crate::run::{self, Follow, Host, Outcome};
use crate::{frame, fsx, sockets, table};

/// The kept invitation (hex, as received).
pub const INVITATION: &str = "invitation";
/// The kept genesis inputs (hex, as `host genesis` or `host join` printed them).
pub const INPUT: &str = "input";

/// The one way nd starts `host`: the member follower's policy in the flag words its unit renders
/// (`--write STORE --exec HOST --hide …`), read by the `Policy::list` nd-supervise reads them with,
/// launched by `nanodregg_sandbox::command`. `host join` and init's one-shot follower share it.
pub fn confined(host: &Path, store: &Path, hide: &[&Path], args: &[&OsStr]) -> io::Result<Command> {
    let mut p = Policy::default();
    let words = [("--write", store), ("--exec", host)];
    for (flag, path) in words.into_iter().chain(hide.iter().map(|h| ("--hide", *h))) {
        if let Some(list) = p.list(OsStr::new(flag)) {
            list.push(path.to_path_buf());
        }
    }
    nanodregg_sandbox::command(&p, host.as_os_str(), args).map_err(io::Error::other)
}

/// A kept file, read back under the chain rule (0600, owner, every parent trusted).
fn kept_file(ws: &Path, name: &str) -> Result<OsString, String> {
    let b = read_private(&ws.join(name), 1..=ARGV_BYTES_MAX as usize);
    Ok(OsString::from_vec(
        b.map_err(|r| format!("{name}: {r:?}"))?.to_vec(),
    ))
}

/// The sponsor's key file: hex, one optional newline, under the chain rule.
fn key_file(path: &OsStr) -> Result<OsString, String> {
    let mut b = read_public(Path::new(path), 64..=65).map_err(|r| format!("key file: {r:?}"))?;
    if b.last() == Some(&b'\n') {
        b.pop();
    }
    Ok(OsString::from_vec(b))
}

/// Bare `nd invite` and `nd adopt KEY_FILE` from the kept files; any other argv unchanged.
pub fn kept(ws: &Path, argv: Vec<OsString>) -> Result<Vec<OsString>, String> {
    Ok(match argv.as_slice() {
        [v] if v == "invite" => vec![v.clone(), kept_file(ws, INPUT)?],
        [v, key] if v == "adopt" => vec![v.clone(), kept_file(ws, INVITATION)?, key_file(key)?],
        _ => argv,
    })
}

/// init's follower: `host follow` on a socket pair, the mux's child wire with one connection.
struct Child(UnixStream);

impl Child {
    fn ask(&mut self, (op, payload): (u8, Vec<u8>)) -> io::Result<Step> {
        let max = table::LIMITS.frame_bytes_max.saturating_add(4);
        let bad = |e: String| io::Error::new(io::ErrorKind::InvalidData, e);
        frame::write_body(&mut self.0, max, &[&[0; 4], &[op], &payload])
            .map_err(|e| bad(e.to_string()))?;
        let b = frame::read_body(&mut self.0, max).map_err(|e| bad(e.to_string()))?;
        let (Some(&status), Some(reply)) = (b.get(4), b.get(5..)) else {
            return Err(bad("short child frame".into()));
        };
        sockets::step(status, reply)
    }
}

impl Follow for Child {
    fn command(&mut self, argv: &[Vec<u8>]) -> io::Result<Step> {
        self.ask(sockets::command(argv)?)
    }
    fn resume(&mut self, k: &[u8], outcome: &Outcome) -> io::Result<Step> {
        self.ask(sockets::resume(k, outcome)?)
    }
}

/// init asks no Host step: it needs no World (`Machine.start`).
struct NoHost;

impl Host for NoHost {
    fn exchange(&mut self, _: u8, _: &[u8]) -> io::Result<(u8, Vec<u8>)> {
        Err(io::Error::other("init asked for the Host"))
    }
}

type Ran = Result<(u8, Vec<u8>, Vec<u8>), String>;

fn join(ws: &Path, hide: &[&Path], custody: &Custody, a: &[OsString]) -> Ran {
    let [key, invitation, store, host] = a else {
        return Err("usage: nd --join KEY_FILE INVITATION STORE /ABS/HOST".into());
    };
    let key = key_file(key)?;
    if let Some(k) = [INVITATION, INPUT]
        .into_iter()
        .find(|k| ws.join(k).symlink_metadata().is_ok())
    {
        return Err(format!("{k}: exists (this workspace has joined)"));
    }
    let (store, host) = (Path::new(store), Path::new(host));
    let s = store.as_os_str();
    let out = confined(host, store, hide, &["join".as_ref(), s, invitation, &key])
        .and_then(|mut c| c.stdin(Stdio::null()).output())
        .map_err(|e| format!("host join: {e}"))?;
    match out.status.code().map(u8::try_from) {
        Some(Ok(0)) => {}
        Some(Ok(host_status::INVITE_REFUSED)) => {
            return Ok((command_exit::REFUSED, vec![], out.stderr));
        }
        _ => {
            return Err(format!(
                "host join: {}",
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
    }
    let said = String::from_utf8_lossy(&out.stdout);
    let line = |k: &str| {
        let l = said.lines().find_map(|l| l.strip_prefix(k));
        l.map(str::to_owned)
            .ok_or(format!("host join printed no `{k}` line"))
    };
    let (sponsor, input) = (line("sponsor ")?, line("input ")?);
    let keep = |name, b: &[u8]| fsx::create_once(ws, name, b).map_err(|e| format!("{name}: {e}"));
    keep(INVITATION, invitation.as_bytes())?;
    keep(INPUT, input.as_bytes())?;
    let (mine, theirs) = UnixStream::pair().map_err(|e| e.to_string())?;
    let zero = OsString::from("00".repeat(32));
    let mut child = (|| {
        mine.set_read_timeout(Some(table::REPLY))?;
        mine.set_write_timeout(Some(table::REPLY))?;
        let i = Stdio::from(OwnedFd::from(theirs.try_clone()?));
        let args = ["follow".as_ref(), s, &zero, &zero];
        confined(host, store, hide, &args)?
            .stdin(i)
            .stdout(OwnedFd::from(theirs))
            .stderr(Stdio::null())
            .spawn()
    })()
    .map_err(|e| format!("host follow: {e}"))?;
    let mut f = Child(mine);
    let argv = [b"init".to_vec(), sponsor.into_bytes()];
    let ran = run::run(
        &argv,
        &mut f,
        &mut NoHost,
        custody,
        &ws.join("attempts"),
        table::RUN,
    );
    drop(f); // follow exits on stdin EOF
    let _ = child.wait();
    let (exit, stdout, stderr) = ran.map_err(|e| e.to_string())?;
    Ok((exit, [out.stdout, stdout].concat(), stderr))
}

/// `nd --join …` and `nd --input HEX`; `None` for any other argv.
pub fn from_argv(
    ws: &Path,
    holding: Option<&Path>,
    custody: &Custody,
    argv: &[OsString],
) -> Option<Result<u8, String>> {
    let hide: Vec<&Path> = std::iter::once(ws).chain(holding).collect();
    let ran = match argv {
        [v, a @ ..] if v == "--join" => join(ws, &hide, custody, a),
        [v, hex] if v == "--input" => {
            let made = fsx::create_once(ws, INPUT, hex.as_bytes());
            made.map(|()| (0, vec![], vec![]))
                .map_err(|e| format!("{INPUT}: {e}"))
        }
        _ => return None,
    };
    Some(ran.map(|(exit, out, err)| {
        let _ = io::stdout().write_all(&out);
        let _ = io::stderr().write_all(&err);
        exit
    }))
}
