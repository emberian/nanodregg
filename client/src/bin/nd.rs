//! `nd ARG…` — one member command. The workspace is `$ND_WORKSPACE` (`seed`, `follow.sock`,
//! `host.sock`, `attempts/`). Every argument goes to `host follow` unread; `nd` performs the steps
//! follow returns and prints what follow says to print. The local verbs are custody, not protocol
//! (CLIENT-13): `nd --init` creates a member's keys, the next secret in `$ND_HOLDING` (a 0700
//! directory on removable media or under another account); `nd --init-hosted` creates a hosted
//! resident's one-record keys; `nd --init-observer` an observe-only follower driver's record,
//! which signs read envelopes only (CLIENT-22); `nd --keys` prints custody's public keys (`key HEX`, `next HEX`)
//! for the operator's `host genesis`. `$ND_HOLDING` is read again only to rotate.
//! `$ND_FOLLOW_SOCK` / `$ND_HOST_SOCK` name the two sockets when they are not the workspace's
//! (HOSTING-17 §7: nd, as nd, drives the nd-hosted follower through its socket in /run/nd-follow).

use std::ffi::OsString;
use std::io::Write;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::process::ExitCode;

use nanodregg_client::custody::Custody;
use nanodregg_client::run;
use nanodregg_client::sockets::{FollowSocket, HostSocket};
use nanodregg_client::table;

fn main() -> ExitCode {
    match go() {
        Ok(code) => ExitCode::from(code),
        Err(e) => {
            eprintln!("nd: {e}");
            // nd's own failure is its own class, never follow's `uncertain` (PROTOCOL-7).
            ExitCode::from(nanodregg_client::generated::command_exit::CLIENT)
        }
    }
}

fn go() -> Result<u8, String> {
    let ws = PathBuf::from(std::env::var_os("ND_WORKSPACE").ok_or("ND_WORKSPACE is not set")?);
    let argv: Vec<OsString> = std::env::args_os().skip(1).collect();
    let holding = std::env::var_os("ND_HOLDING").map(PathBuf::from);
    if argv.len() == 1
        && (argv[0] == "--init" || argv[0] == "--init-hosted" || argv[0] == "--init-observer")
    {
        nd_dir(&ws.join("attempts"))?;
        let made = match holding {
            _ if argv[0] == "--init-hosted" => Custody::create_same_record(&ws),
            _ if argv[0] == "--init-observer" => Custody::create_observer(&ws),
            Some(h) => Custody::create_separate(&ws, &h),
            None => return Err("nd --init: ND_HOLDING is not set (CLIENT-13)".into()),
        };
        made.map_err(|e| e.to_string())?;
        return Ok(0);
    }
    let custody = Custody::open(&ws, holding).map_err(|e| e.to_string())?;
    if argv.len() == 1 && argv[0] == "--keys" {
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let key = custody.public_key().map_err(|e| e.to_string())?;
        let next = custody.next_public_key().map_err(|e| e.to_string())?;
        println!("key {}\nnext {}", hex(&key), hex(&next));
        return Ok(0);
    }
    let sock =
        |var: &str, name: &str| std::env::var_os(var).map_or_else(|| ws.join(name), PathBuf::from);
    let mut follow = FollowSocket::connect(&sock("ND_FOLLOW_SOCK", "follow.sock"), table::REPLY)
        .map_err(|e| format!("follow.sock: {e}"))?;
    let mut host = HostSocket::connect(&sock("ND_HOST_SOCK", "host.sock"), table::REPLY)
        .map_err(|e| format!("host.sock: {e}"))?;
    let argv: Vec<Vec<u8>> = argv.into_iter().map(OsString::into_vec).collect();
    let (exit, stdout, stderr) = run::run(
        &argv,
        &mut follow,
        &mut host,
        &custody,
        &ws.join("attempts"),
        table::RUN,
    )
    .map_err(|e| e.to_string())?;
    let _ = std::io::stdout().write_all(&stdout);
    let _ = std::io::stderr().write_all(&stderr);
    Ok(exit)
}

/// `mkdir -p` at 0700 whatever the umask: the workspace is the member's alone (custody's chain).
fn nd_dir(p: &std::path::Path) -> Result<(), String> {
    std::os::unix::fs::DirBuilderExt::mode(std::fs::DirBuilder::new().recursive(true), 0o700)
        .create(p)
        .map_err(|e| e.to_string())
}
