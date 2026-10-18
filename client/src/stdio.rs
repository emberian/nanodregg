//! `nd --stdio` (HOSTING-20, CLIENT-24): nd-supervise's child serving one hosted resident over the
//! mux's child wire. Each request is one nd command (`follow_op::COMMAND ‖ layout::Command`), each
//! reply its done step (`status::OK ‖ layout::CommandReply`). The surface is this mode's property,
//! never a peer's choice: a verb not in `STDIO_VERBS` (flags and custody words included) is refused
//! `notOnSurface` before follow sees it; a request that does not decode is `undecodable`; custody
//! is opened rotation-refusing (`noRotation`); the workspace and the two sockets are nd's argv at
//! start (`nd --stdio WORKSPACE FOLLOW_SOCK HOST_SOCK`; the sandbox clears the environment). No argument is ever resolved against the file system (nothing in nd or follow reads an
//! argv path).

use std::io::{self, Read, Write};
use std::path::Path;

use crate::custody::Custody;
use crate::frame;
use crate::generated::layout::{Command, CommandReply};
use crate::generated::{HANGUP, STDIO_VERBS, StdioRefusal, command_exit, follow_op, status};
use crate::run;
use crate::sockets::{FollowSocket, HostSocket};
use crate::table;

/// Where the two sockets and the attempts live; fixed when `nd --stdio` starts.
pub struct Place<'a> {
    /// `follow.sock` of the resident's follower.
    pub follow: &'a Path,
    /// The writer's `host.sock`.
    pub host: &'a Path,
    /// The workspace's `attempts/`.
    pub attempts: &'a Path,
}

fn refused(r: StdioRefusal, what: &str) -> CommandReply {
    let line = match what {
        "" => format!("refused {}\n", r.name()),
        w => format!("refused {} {w}\n", r.name()),
    };
    CommandReply {
        exit: command_exit::REFUSED,
        stdout: Vec::new(),
        stderr: line.into_bytes(),
    }
}

/// The custody `nd --stdio` signs with: the workspace's, refusing rotation (`noRotation`).
pub fn custody(ws: &Path) -> Result<Custody, crate::custody::CustodyError> {
    Ok(Custody::open(ws, None)?.refusing_rotation())
}

/// One request's reply, against `surface` (`STDIO_VERBS` when served; a plant widens it to show the
/// custody fence holds behind it).
pub fn answer(
    op: u8,
    payload: &[u8],
    at: &Place,
    custody: &Custody,
    surface: &[&str],
) -> CommandReply {
    let argv = match (op, Command::decode(payload)) {
        (follow_op::COMMAND, Ok(c)) => c.argv,
        _ => return refused(StdioRefusal::Undecodable, ""),
    };
    let verb = argv
        .first()
        .map(|v| String::from_utf8_lossy(v).into_owned());
    match verb {
        Some(v) if surface.contains(&v.as_str()) => {}
        v => return refused(StdioRefusal::NotOnSurface, &v.unwrap_or_default()),
    }
    let ran = FollowSocket::connect(at.follow, table::REPLY)
        .map_err(|e| format!("follow.sock: {e}"))
        .and_then(|mut f| {
            let mut h = HostSocket::connect(at.host, table::REPLY)
                .map_err(|e| format!("host.sock: {e}"))?;
            run::run(&argv, &mut f, &mut h, custody, at.attempts, table::RUN)
                .map_err(|e| e.to_string())
        });
    match ran {
        Ok((exit, stdout, stderr)) => CommandReply {
            exit,
            stdout,
            stderr,
        },
        Err(e) => CommandReply {
            exit: command_exit::CLIENT,
            stdout: Vec::new(),
            stderr: format!("nd: {e}\n").into_bytes(),
        },
    }
}

/// Serve the mux's child wire until stdin closes: `u32le conn ‖ op ‖ payload` in, `u32le conn ‖
/// status ‖ payload` out; a hang-up frame is skipped. Requests are answered in order.
pub fn serve(mut r: impl Read, mut w: impl Write, at: &Place, custody: &Custody) -> io::Result<()> {
    let max = table::LIMITS.frame_bytes_max.saturating_add(4);
    loop {
        let body = match frame::read_body(&mut r, max) {
            Ok(b) => b,
            Err(frame::FrameError::Closed) => return Ok(()),
            Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidData, e.to_string())),
        };
        let (Some(conn), Some(&op)) = (body.get(..4), body.get(4)) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short child frame",
            ));
        };
        if op == HANGUP {
            continue;
        }
        let reply = answer(op, &body[5..], at, custody, STDIO_VERBS);
        let bytes = reply
            .encode()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("{e:?}")))?;
        frame::write_body(&mut w, max, &[conn, &[status::OK], &bytes])
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        w.flush()?;
    }
}

/// `nd --stdio WORKSPACE FOLLOW_SOCK HOST_SOCK`: `None` for any other argv (nd's other modes).
pub fn from_argv(argv: &[std::ffi::OsString]) -> Option<Result<u8, String>> {
    let [mode, ws, follow, host] = argv else {
        return None;
    };
    if mode != "--stdio" {
        return None;
    }
    let (ws, follow, host) = (Path::new(ws), Path::new(follow), Path::new(host));
    let attempts = ws.join("attempts");
    let at = Place {
        follow,
        host,
        attempts: &attempts,
    };
    Some(
        custody(ws)
            .map_err(|e| e.to_string())
            .and_then(|c| {
                let (i, o) = (io::stdin().lock(), io::stdout().lock());
                serve(i, o, &at, &c).map_err(|e| e.to_string())
            })
            .map(|()| 0),
    )
}
