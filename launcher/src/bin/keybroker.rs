//! `keybroker KEYS SOCKDIR PIDS UPSTREAM RESIDENTS DECIDER [ARG...]`
//!
//! The provider-key broker's byte mover (HOSTING-12). It holds the operator's provider keys (the
//! file KEYS, read once under the custody checks of `nanodregg_sandbox::custody`) and serves one Unix
//! socket per resident, `SOCKDIR/<resident>.sock` for each name in the comma-separated RESIDENTS.
//! Identity is the socket: keybroker puts a `decide` frame naming that socket's resident in front
//! of each ask, unread, and hands both to DECIDER (the Lean `hosting-broker`, started confined with
//! the operator clock `T0` as its first argument, then ARG...). A `grant` names a key slot and the
//! upstream request Lean printed; keybroker sends it to UPSTREAM (`host:port`, HTTP/1.0) with the
//! slot's key in the header Lean named, and relays the status and body, unless the response holds
//! the key (`keyEchoed`, withheld). It decides nothing: every verdict is the decider's, and every
//! way it ends is a name on stderr. One ask at a time per resident (`busy`).

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::process::{ChildStdin, ChildStdout, ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use nanodregg_launcher::broker_generated::wire::{Answer, BrokerRefusal, Request, Verdict};
use nanodregg_launcher::broker_generated::{FRAME_MAX, read_frame, write_frame};
use nanodregg_launcher::grain_name_ok;
use nanodregg_sandbox::custody::{self, Refused};
use nanodregg_sandbox::{Policy, command};
use zeroize::Zeroizing;

/// The largest key file read.
const KEYFILE_MAX: usize = 65536;
/// How long one upstream call may take, connect to last byte.
const UPSTREAM_TIMEOUT: Duration = Duration::from_secs(120);
/// How long a resident's connection may sit idle between asks.
const RESIDENT_IDLE: Duration = Duration::from_secs(60);
/// Connections one socket accepts, and asks one connection carries: centuries of use.
const LIFETIME: u64 = 1 << 48;
/// The largest upstream response read: its body must fit one `answer` frame.
const RESPONSE_MAX: usize = FRAME_MAX as usize - 64;

enum End {
    Usage,
    KeyFile(&'static str),
    KeyFileFormat,
    Socket(String),
    DeciderRefused(String),
    DeciderEnded(Option<i32>),
    Pid(String),
}

impl End {
    fn describe(&self) -> String {
        match self {
            End::Usage => {
                "usage: keybroker KEYS SOCKDIR PIDS UPSTREAM RESIDENTS DECIDER [ARG...]".into()
            }
            End::KeyFile(n) => (*n).into(),
            End::KeyFileFormat => "keyFileFormat".into(),
            End::Socket(e) => format!("socket {e}"),
            End::DeciderRefused(e) => format!("deciderRefused {e}"),
            End::DeciderEnded(c) => format!("deciderEnded {c:?}"),
            End::Pid(e) => format!("pidFile {e}"),
        }
    }
}

fn main() -> ExitCode {
    let end = run();
    eprintln!("keybroker: {}", end.describe());
    match end {
        End::DeciderEnded(Some(0)) => ExitCode::SUCCESS,
        End::Usage => ExitCode::from(2),
        _ => ExitCode::from(1),
    }
}

/// The key file's custody refusal, by name (one per `custody::Refused` case).
fn key_file_name(e: &Refused) -> &'static str {
    match e {
        Refused::Link => "keyFileLink",
        Refused::NotRegular => "keyFileNotRegular",
        Refused::Owner(_) => "keyFileOwner",
        Refused::Mode(_) => "keyFileMode",
        Refused::Length(_) => "keyFileLength",
        Refused::Io(_) => "keyFileIo",
    }
}

type Keys = BTreeMap<u32, Zeroizing<Vec<u8>>>;

/// `SLOT KEY` per line: a decimal slot, one space, the key's bytes (printable ASCII, no space).
fn parse_keys(text: &[u8]) -> Option<Keys> {
    let mut keys = Keys::new();
    for line in text.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let sp = line.iter().position(|b| *b == b' ')?;
        let slot: u32 = std::str::from_utf8(&line[..sp]).ok()?.parse().ok()?;
        let key = &line[sp + 1..];
        if key.is_empty() || !key.iter().all(|b| b.is_ascii_graphic()) {
            return None;
        }
        if keys.insert(slot, Zeroizing::new(key.to_vec())).is_some() {
            return None;
        }
    }
    if keys.is_empty() { None } else { Some(keys) }
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
        .unwrap_or(0)
}

struct Shared {
    decider: Mutex<(ChildStdin, ChildStdout)>,
    keys: Keys,
    upstream: String,
}

fn run() -> End {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let [
        keys_path,
        sockdir,
        pids,
        upstream,
        residents,
        decider,
        rest @ ..,
    ] = args.as_slice()
    else {
        return End::Usage;
    };
    let keys_path = PathBuf::from(keys_path);
    let text = match custody::read_private(&keys_path, 1..=KEYFILE_MAX) {
        Ok(t) => t,
        Err(e) => return End::KeyFile(key_file_name(&e)),
    };
    let Some(keys) = parse_keys(&text) else {
        return End::KeyFileFormat;
    };
    let Some(upstream) = upstream.to_str().map(str::to_owned) else {
        return End::Usage;
    };
    let Some(residents) = residents.to_str() else {
        return End::Usage;
    };
    let residents: Vec<&str> = residents.split(',').collect();
    if !residents.iter().all(|r| grain_name_ok(r.as_bytes())) {
        return End::Usage;
    }
    let decider = PathBuf::from(decider);
    let pid_file = PathBuf::from(pids).join("decider.pid");

    // The decider sees nothing but its own program; the key file is hidden as a second barrier.
    let policy = Policy {
        read: vec![],
        write: vec![],
        exec: vec![decider.clone()],
        hidden: vec![keys_path.clone()],
    };
    let t0 = OsString::from(now_ms().to_string());
    let mut dargs: Vec<&std::ffi::OsStr> = vec![t0.as_os_str()];
    dargs.extend(rest.iter().map(OsString::as_os_str));
    let mut cmd = match command(&policy, decider.as_os_str(), &dargs) {
        Ok(c) => c,
        Err(e) => return End::DeciderRefused(format!("{e:?}")),
    };
    let mut child = match cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn() {
        Ok(c) => c,
        Err(e) => return End::DeciderRefused(e.to_string()),
    };
    if let Err(e) = std::fs::write(&pid_file, format!("{}\n", child.id())) {
        let _ = child.kill();
        let _ = child.wait();
        return End::Pid(e.to_string());
    }
    let (Some(din), Some(dout)) = (child.stdin.take(), child.stdout.take()) else {
        let _ = child.kill();
        let _ = child.wait();
        let _ = std::fs::remove_file(&pid_file);
        return End::DeciderRefused("pipes".into());
    };
    let shared = Arc::new(Shared {
        decider: Mutex::new((din, dout)),
        keys,
        upstream,
    });

    for r in residents {
        let path = PathBuf::from(sockdir).join(format!("{r}.sock"));
        let listener = match UnixListener::bind(&path) {
            Ok(l) => l,
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = std::fs::remove_file(&pid_file);
                return End::Socket(format!("{} {e}", path.display()));
            }
        };
        let sh = Arc::clone(&shared);
        let resident = r.as_bytes().to_vec();
        std::thread::spawn(move || serve_socket(listener, resident, sh));
    }

    // The decider's end is keybroker's end: an ask could no longer be decided.
    let status = child.wait();
    let _ = std::fs::remove_file(&pid_file);
    End::DeciderEnded(status.ok().and_then(|s| s.code()))
}

/// One resident's socket: one connection at a time; a second, while one is open, is told `busy`.
fn serve_socket(listener: UnixListener, resident: Vec<u8>, sh: Arc<Shared>) {
    let open = Arc::new(AtomicBool::new(false));
    for conn in listener.incoming().take(LIFETIME as usize) {
        let Ok(mut s) = conn else { continue };
        if open.swap(true, Ordering::SeqCst) {
            let _ = answer(&mut s, &refused(BrokerRefusal::Busy));
            continue;
        }
        let (open, sh, resident) = (Arc::clone(&open), Arc::clone(&sh), resident.clone());
        std::thread::spawn(move || {
            serve_conn(s, &resident, &sh);
            open.store(false, Ordering::SeqCst);
        });
    }
}

fn refused(r: BrokerRefusal) -> Answer {
    Answer::Refused { broker_refusal: r }
}

fn answer(s: &mut UnixStream, a: &Answer) -> Option<()> {
    let bytes = a.encode().ok()?;
    write_frame(s, &bytes).ok()?;
    s.flush().ok()
}

fn serve_conn(mut s: UnixStream, resident: &[u8], sh: &Shared) {
    if s.set_read_timeout(Some(RESIDENT_IDLE)).is_err() {
        return;
    }
    for _ in 0..LIFETIME {
        let Ok(ask) = read_frame(&mut s) else { return };
        let Some(a) = ask_once(sh, resident, &ask) else {
            return;
        };
        if answer(&mut s, &a).is_none() {
            return;
        }
    }
}

/// One ask: the decider's verdict, then (for a grant) the upstream call. `None` when the decider
/// cannot be reached: the connection closes and keybroker ends when the decider does.
fn ask_once(sh: &Shared, resident: &[u8], ask: &[u8]) -> Option<Answer> {
    let req = Request::Decide {
        resident: resident.to_vec(),
        at_ms: now_ms(),
    }
    .encode()
    .ok()?;
    let verdict = {
        let mut d = sh.decider.lock().ok()?;
        let (din, dout) = &mut *d;
        write_frame(din, &req).ok()?;
        write_frame(din, ask).ok()?;
        din.flush().ok()?;
        Verdict::decode(&read_frame(dout).ok()?).ok()?
    };
    Some(match verdict {
        Verdict::Refuse { broker_refusal } => refused(broker_refusal),
        Verdict::Grant {
            key_slot,
            target,
            headers,
            key_header,
            body,
            ..
        } => {
            let Some(key) = sh.keys.get(&key_slot) else {
                return Some(refused(BrokerRefusal::KeyMissing));
            };
            match call(&sh.upstream, &target, &headers, &key_header, key, &body) {
                None => refused(BrokerRefusal::UpstreamFailed),
                Some(resp) if contains(&resp, key) => refused(BrokerRefusal::KeyEchoed),
                Some(resp) => match split_response(&resp) {
                    Some((status, body)) => Answer::Answer {
                        status,
                        body: body.to_vec(),
                    },
                    None => refused(BrokerRefusal::UpstreamFailed),
                },
            }
        }
    })
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty() && hay.windows(needle.len()).any(|w| w == needle)
}

/// `POST target HTTP/1.0` with Lean's headers, the key header, and Lean's body; the whole response,
/// at most `RESPONSE_MAX` bytes.
fn call(
    upstream: &str,
    target: &[u8],
    headers: &[u8],
    key_header: &[u8],
    key: &[u8],
    body: &[u8],
) -> Option<Vec<u8>> {
    let addr = upstream.to_socket_addrs().ok()?.next()?;
    let mut t = TcpStream::connect_timeout(&addr, UPSTREAM_TIMEOUT).ok()?;
    t.set_read_timeout(Some(UPSTREAM_TIMEOUT)).ok()?;
    t.set_write_timeout(Some(UPSTREAM_TIMEOUT)).ok()?;
    let host = upstream.rsplit_once(':').map_or(upstream, |(h, _)| h);
    let mut req = Zeroizing::new(Vec::with_capacity(body.len() + 512));
    req.extend_from_slice(b"POST ");
    req.extend_from_slice(target);
    req.extend_from_slice(b" HTTP/1.0\r\nHost: ");
    req.extend_from_slice(host.as_bytes());
    req.extend_from_slice(b"\r\n");
    req.extend_from_slice(headers);
    req.extend_from_slice(key_header);
    req.extend_from_slice(b": ");
    req.extend_from_slice(key);
    req.extend_from_slice(format!("\r\nContent-Length: {}\r\n\r\n", body.len()).as_bytes());
    req.extend_from_slice(body);
    t.write_all(&req).ok()?;
    t.flush().ok()?;
    let mut resp = Vec::new();
    let n = t
        .take(RESPONSE_MAX as u64 + 1)
        .read_to_end(&mut resp)
        .ok()?;
    if n > RESPONSE_MAX {
        return None;
    }
    Some(resp)
}

/// The status code of `HTTP/1.x NNN …` and the bytes after the blank line.
fn split_response(resp: &[u8]) -> Option<(u32, &[u8])> {
    let end = resp.windows(4).position(|w| w == b"\r\n\r\n")?;
    let line = resp[..end].split(|b| *b == b'\r').next()?;
    let mut parts = line.split(|b| *b == b' ');
    let proto = parts.next()?;
    if !proto.starts_with(b"HTTP/1.") {
        return None;
    }
    let code: u32 = std::str::from_utf8(parts.next()?).ok()?.parse().ok()?;
    Some((code, &resp[end + 4..]))
}
