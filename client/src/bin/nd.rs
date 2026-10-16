//! `nd ARG…` — one member command. The workspace is `$ND_WORKSPACE` (`seed`, `follow.sock`,
//! `host.sock`, `attempts/`). Every argument goes to `host follow` unread; `nd` performs the steps
//! follow returns and prints what follow says to print. The one local verb is `nd --init`, which
//! creates the workspace's seed and attempts directory (custody, not protocol).

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
            ExitCode::from(2)
        }
    }
}

fn go() -> Result<u8, String> {
    let ws = PathBuf::from(std::env::var_os("ND_WORKSPACE").ok_or("ND_WORKSPACE is not set")?);
    let argv: Vec<OsString> = std::env::args_os().skip(1).collect();
    if argv.len() == 1 && argv[0] == "--init" {
        std::fs::create_dir_all(ws.join("attempts")).map_err(|e| e.to_string())?;
        Custody::create(&ws, "seed").map_err(|e| e.to_string())?;
        return Ok(0);
    }
    let custody = Custody::open(&ws.join("seed")).map_err(|e| e.to_string())?;
    let mut follow =
        FollowSocket::connect(&ws.join("follow.sock")).map_err(|e| format!("follow.sock: {e}"))?;
    let mut host =
        HostSocket::connect(&ws.join("host.sock")).map_err(|e| format!("host.sock: {e}"))?;
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
