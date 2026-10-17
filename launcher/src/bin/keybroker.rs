//! `keybroker KEYS ANCHORS SOCKDIR PIDS UPSTREAM STORE OPERATOR RESIDENTS DECIDER`
//!
//! The provider-key broker's byte mover (HOSTING-12). It holds the operator's provider keys (the
//! file KEYS, read once under the custody checks of `nanodregg_sandbox::custody`) and the TLS trust
//! anchors (the PEM file ANCHORS, the operator's data: in production the installed copy of
//! `deploy/tls/anchors.pem`, read once under `custody::read_public`), and serves one Unix
//! socket per resident, `SOCKDIR/<resident>.sock` for each name in the comma-separated RESIDENTS.
//! Identity is the socket: keybroker puts a `decide` frame naming that socket's resident in front
//! of each ask, unread, and hands both to DECIDER (the Lean `hosting-broker`, started confined as
//! `DECIDER T0 SLOTS STORE OPERATOR`: the operator clock, the comma-separated key slots the key file
//! holds (so Lean refuses `keyMissing` before it charges anything), and the World it follows for
//! the allowances OPERATOR owns, which it may read and nothing else). A `grant` names a key slot and the
//! upstream request Lean printed; keybroker dials UPSTREAM (`addr:port`, the operator's dial
//! address), speaks TLS 1.3 (rustls with the ring provider, HOSTING-15) with SNI and certificate
//! verification for the HOST the grant names (Lean's provider table, never the dial address), sends
//! the request (HTTP/1.0, `Host:` Lean's host) with the slot's key in the header Lean named, and
//! relays the status and body, unless the response holds the key (`keyEchoed`, withheld). A TLS
//! failure is `tlsCertificate`, `tlsHostname` or `tlsProtocol`, never the upstream's text. It
//! decides nothing: every verdict is the decider's, and every way it ends is a name on stderr. One
//! ask at a time per resident (`busy`).

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::ErrorKind;
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::process::{ChildStdin, ChildStdout, ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use nanodregg_launcher::broker_generated::wire::{Answer, BrokerRefusal, Request, Verdict};
use nanodregg_launcher::broker_generated::{FRAME_MAX, keybroker_exit, read_frame, write_frame};
use nanodregg_launcher::grain_name_ok;
use nanodregg_sandbox::custody::{self, Refused};
use nanodregg_sandbox::{Policy, command};
use rustls::pki_types::pem::{PemObject, SectionKind};
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{CertificateError, ClientConfig, ClientConnection, RootCertStore, StreamOwned};
use zeroize::Zeroizing;

/// The largest key file read.
const KEYFILE_MAX: usize = 65536;
/// The largest anchor file read (the pinned webpki bundle is about 200 KB).
const ANCHORS_MAX: usize = 1 << 20;
/// How long one upstream call may take, connect to last byte.
const UPSTREAM_TIMEOUT: Duration = Duration::from_secs(120);
/// How long a resident's connection may sit idle between asks.
const RESIDENT_IDLE: Duration = Duration::from_secs(60);
/// Connections one socket accepts, and asks one connection carries: centuries of use.
const LIFETIME: u64 = 1 << 48;
/// The largest upstream response read: its body must fit one `answer` frame.
const RESPONSE_MAX: usize = FRAME_MAX as usize - 64;

/// How keybroker ends. Each end's exit code is Lean's (`Hosting.KeybrokerExit`, emitted as
/// `keybroker_exit`); a decider that exits is passed through with its own code (`DeciderExit`).
enum End {
    Usage,
    /// a key-file or anchor-file refusal: its name and its code
    File(&'static str, u8),
    Tls(String),
    Socket(String),
    DeciderRefused(String),
    /// the decider's exit code, or `None` for a signal
    DeciderEnded(Option<i32>),
    /// `wait` on the decider failed
    DeciderLost(String),
    Pid(String),
}

impl End {
    fn describe(&self) -> String {
        match self {
            End::Usage => {
                "usage: keybroker KEYS ANCHORS SOCKDIR PIDS UPSTREAM STORE OPERATOR RESIDENTS DECIDER"
                    .into()
            }
            End::File(n, _) => (*n).into(),
            End::Tls(e) => format!("tlsConfig {e}"),
            End::Socket(e) => format!("socket {e}"),
            End::DeciderRefused(e) => format!("deciderRefused {e}"),
            End::DeciderEnded(Some(c)) => format!("deciderEnded {c}"),
            End::DeciderEnded(None) => "deciderSignaled".into(),
            End::DeciderLost(e) => format!("deciderLost {e}"),
            End::Pid(e) => format!("pidFile {e}"),
        }
    }
}

fn main() -> ExitCode {
    let end = run();
    eprintln!("keybroker: {}", end.describe());
    ExitCode::from(match end {
        End::Usage => keybroker_exit::USAGE,
        End::File(_, code) => code,
        End::Tls(_) => keybroker_exit::TLS_CONFIG,
        End::Socket(_) => keybroker_exit::SOCKET,
        End::DeciderRefused(_) => keybroker_exit::DECIDER_REFUSED,
        End::Pid(_) => keybroker_exit::PID_FILE,
        // the decider's own code, passed through; a code past u8 is not an exit status
        End::DeciderEnded(Some(c)) => u8::try_from(c).unwrap_or(keybroker_exit::DECIDER_SIGNALED),
        End::DeciderEnded(None) => keybroker_exit::DECIDER_SIGNALED,
        End::DeciderLost(_) => keybroker_exit::DECIDER_LOST,
    })
}

/// The key file's custody refusal, by name (one per `custody::Refused` case).
fn key_file_end(e: &Refused) -> End {
    use keybroker_exit as k;
    match e {
        Refused::Link => End::File("keyFileLink", k::KEY_FILE_LINK),
        Refused::NotRegular => End::File("keyFileNotRegular", k::KEY_FILE_NOT_REGULAR),
        Refused::Owner(_) => End::File("keyFileOwner", k::KEY_FILE_OWNER),
        Refused::Mode(_) => End::File("keyFileMode", k::KEY_FILE_MODE),
        Refused::Length(_) => End::File("keyFileLength", k::KEY_FILE_LENGTH),
        Refused::Dir(_) => End::File("keyFileDir", k::KEY_FILE_DIR),
        Refused::Io(_) => End::File("keyFileIo", k::KEY_FILE_IO),
    }
}

/// The anchor file's custody refusal, by name. A file that is not there is `anchorsMissing`.
fn anchors_end(e: &Refused) -> End {
    use keybroker_exit as k;
    match e {
        Refused::Link => End::File("anchorsLink", k::ANCHORS_LINK),
        Refused::NotRegular => End::File("anchorsNotRegular", k::ANCHORS_NOT_REGULAR),
        Refused::Owner(_) => End::File("anchorsOwner", k::ANCHORS_OWNER),
        Refused::Mode(_) => End::File("anchorsMode", k::ANCHORS_MODE),
        Refused::Length(_) => End::File("anchorsLength", k::ANCHORS_LENGTH),
        Refused::Dir(_) => End::File("anchorsDir", k::ANCHORS_DIR),
        Refused::Io(e) if e.kind() == ErrorKind::NotFound => {
            End::File("anchorsMissing", k::ANCHORS_MISSING)
        }
        Refused::Io(_) => End::File("anchorsIo", k::ANCHORS_IO),
    }
}

/// Concatenated PEM `CERTIFICATE` blocks, each a trust anchor webpki accepts. Any other PEM
/// section, a block that does not decode, an anchor webpki refuses, or no block at all is `None`
/// (`anchorsMalformed`): the file is the operator's whole trust set, so nothing in it is skipped.
fn parse_anchors(pem: &[u8]) -> Option<RootCertStore> {
    let mut roots = RootCertStore::empty();
    for item in <(SectionKind, Vec<u8>)>::pem_slice_iter(pem) {
        let (kind, der) = item.ok()?;
        if kind != SectionKind::Certificate {
            return None;
        }
        roots.add(CertificateDer::from(der)).ok()?;
    }
    if roots.is_empty() { None } else { Some(roots) }
}

/// The client side of every upstream call: TLS 1.3 only, ring's primitives, the operator's anchors,
/// SNI on, rustls' own WebPKI verifier (no custom verifier), no client certificate.
fn tls_config(roots: RootCertStore) -> Result<ClientConfig, rustls::Error> {
    Ok(
        ClientConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
            .with_protocol_versions(&[&rustls::version::TLS13])?
            .with_root_certificates(roots)
            .with_no_client_auth(),
    )
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
    tls: Arc<ClientConfig>,
}

fn run() -> End {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let [
        keys_path,
        anchors_path,
        sockdir,
        pids,
        upstream,
        store,
        operator,
        residents,
        decider,
    ] = args.as_slice()
    else {
        return End::Usage;
    };
    let keys_path = PathBuf::from(keys_path);
    let text = match custody::read_private(&keys_path, 1..=KEYFILE_MAX) {
        Ok(t) => t,
        Err(e) => return key_file_end(&e),
    };
    let Some(keys) = parse_keys(&text) else {
        return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
    };
    let anchors = match custody::read_public(&PathBuf::from(anchors_path), 1..=ANCHORS_MAX) {
        Ok(a) => a,
        Err(e) => return anchors_end(&e),
    };
    let Some(roots) = parse_anchors(&anchors) else {
        return End::File("anchorsMalformed", keybroker_exit::ANCHORS_MALFORMED);
    };
    let tls = match tls_config(roots) {
        Ok(c) => Arc::new(c),
        Err(e) => return End::Tls(e.to_string()),
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

    // The decider sees its own program and reads the Store; the key file is hidden as a second barrier.
    let store = PathBuf::from(store);
    let policy = Policy {
        read: vec![store.clone()],
        write: vec![],
        exec: vec![decider.clone()],
        hidden: vec![keys_path.clone()],
    };
    let t0 = OsString::from(now_ms().to_string());
    let slots = OsString::from(
        keys.keys()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(","),
    );
    let dargs: Vec<&std::ffi::OsStr> = vec![
        t0.as_os_str(),
        slots.as_os_str(),
        store.as_os_str(),
        operator.as_os_str(),
    ];
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
        tls,
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
    match status {
        Ok(s) => End::DeciderEnded(s.code()),
        Err(e) => End::DeciderLost(e.to_string()),
    }
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
            host,
            target,
            headers,
            key_header,
            body,
            ..
        } => {
            let Some(key) = sh.keys.get(&key_slot) else {
                return Some(refused(BrokerRefusal::KeyMissing));
            };
            let req = Call {
                host: &host,
                target: &target,
                headers: &headers,
                key_header: &key_header,
                body: &body,
            };
            match call(sh, &req, key) {
                Err(why) => refused(why),
                Ok(resp) if contains(&resp, key) => refused(BrokerRefusal::KeyEchoed),
                Ok(resp) => match split_response(&resp) {
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

/// The request Lean printed for one grant.
struct Call<'a> {
    host: &'a [u8],
    target: &'a [u8],
    headers: &'a [u8],
    key_header: &'a [u8],
    body: &'a [u8],
}

/// A TLS error, by name: a certificate for another name is `tlsHostname`, any other certificate
/// fault (an unknown issuer, an expired or malformed certificate) `tlsCertificate`, and everything
/// else (a protocol version, an alert, a bad record) `tlsProtocol`.
fn tls_refusal(e: &rustls::Error) -> BrokerRefusal {
    match e {
        rustls::Error::InvalidCertificate(
            CertificateError::NotValidForName | CertificateError::NotValidForNameContext { .. },
        ) => BrokerRefusal::TlsHostname,
        rustls::Error::InvalidCertificate(_) => BrokerRefusal::TlsCertificate,
        _ => BrokerRefusal::TlsProtocol,
    }
}

/// An I/O error on the TLS stream: rustls' own error by its name, a plain transport fault
/// `upstreamFailed`.
fn io_refusal(e: &std::io::Error) -> BrokerRefusal {
    match e.get_ref().and_then(|i| i.downcast_ref::<rustls::Error>()) {
        Some(t) => tls_refusal(t),
        None => BrokerRefusal::UpstreamFailed,
    }
}

/// Dial UPSTREAM, complete a TLS 1.3 handshake verified for Lean's host, then `POST target
/// HTTP/1.0` with `Host:` Lean's host, Lean's headers, the key header, and Lean's body; the whole
/// response, at most `RESPONSE_MAX` bytes, ended by the server's `close_notify` (a close without
/// it is a truncation nobody authenticated: `tlsProtocol`).
fn call(sh: &Shared, r: &Call<'_>, key: &[u8]) -> Result<Vec<u8>, BrokerRefusal> {
    let name = std::str::from_utf8(r.host)
        .ok()
        .and_then(|h| ServerName::try_from(h.to_owned()).ok())
        .ok_or(BrokerRefusal::TlsHostname)?;
    let failed = |_: std::io::Error| BrokerRefusal::UpstreamFailed;
    let addr = sh
        .upstream
        .to_socket_addrs()
        .map_err(failed)?
        .next()
        .ok_or(BrokerRefusal::UpstreamFailed)?;
    let mut t = TcpStream::connect_timeout(&addr, UPSTREAM_TIMEOUT).map_err(failed)?;
    t.set_read_timeout(Some(UPSTREAM_TIMEOUT)).map_err(failed)?;
    t.set_write_timeout(Some(UPSTREAM_TIMEOUT))
        .map_err(failed)?;
    let mut conn = ClientConnection::new(Arc::clone(&sh.tls), name).map_err(|e| tls_refusal(&e))?;
    while conn.is_handshaking() {
        conn.complete_io(&mut t).map_err(|e| io_refusal(&e))?;
    }
    let mut s = StreamOwned::new(conn, t);
    let mut req = Zeroizing::new(Vec::with_capacity(r.body.len() + 512));
    req.extend_from_slice(b"POST ");
    req.extend_from_slice(r.target);
    req.extend_from_slice(b" HTTP/1.0\r\nHost: ");
    req.extend_from_slice(r.host);
    req.extend_from_slice(b"\r\n");
    req.extend_from_slice(r.headers);
    req.extend_from_slice(r.key_header);
    req.extend_from_slice(b": ");
    req.extend_from_slice(key);
    req.extend_from_slice(format!("\r\nContent-Length: {}\r\n\r\n", r.body.len()).as_bytes());
    req.extend_from_slice(r.body);
    s.write_all(&req).map_err(|e| io_refusal(&e))?;
    s.flush().map_err(|e| io_refusal(&e))?;
    let mut resp = Vec::new();
    let n = (&mut s)
        .take(RESPONSE_MAX as u64 + 1)
        .read_to_end(&mut resp)
        .map_err(|e| match e.kind() {
            ErrorKind::UnexpectedEof => BrokerRefusal::TlsProtocol,
            _ => io_refusal(&e),
        })?;
    if n > RESPONSE_MAX {
        return Err(BrokerRefusal::UpstreamFailed);
    }
    Ok(resp)
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
