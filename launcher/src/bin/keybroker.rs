//! `keybroker KEYS ANCHORS PINS SOCKDIR PIDS UPSTREAM STORE OPERATOR PEER DECIDER`
//!
//! The provider-key broker's byte mover (HOSTING-12). It holds the operator's provider keys (the
//! file KEYS, read once under the custody checks of `nanodregg_sandbox::custody`) and the TLS trust
//! anchors (the PEM file ANCHORS, the operator's data: in production the installed copy of
//! `deploy/tls/anchors.pem`, read once under `custody::read_public`), the leaf-key pins (the file
//! PINS, the operator's data shaped like ANCHORS: `HOST SHA256-HEX` lines, the SHA-256 of the
//! provider's leaf certificate's SubjectPublicKeyInfo; in production the installed copy of
//! `deploy/tls/pins`, emitted from Lean's `Hosting.Pins.pins`, HOSTING-28), and serves one Unix
//! socket per resident, `SOCKDIR/<resident>/broker.sock` (HOSTING-17), for exactly the residents the
//! World holds: it asks its decider `residents` at start and every `TICK`, binds a socket for each
//! name newly answered (a resident grain's birth) and closes and removes the socket of each name no
//! longer answered (its removal) (HOSTING-26; no operator list). SOCKDIR is the operator's (nd:nd-hosted, mode 02710, every directory above
//! it StrictModes-clean); keybroker makes each resident's directory in it (02710, SOCKDIR's group by
//! the setgid bit), puts nothing there but the socket, and sets the socket 0660 (0600 when PEER is
//! keybroker's own uid: a one-uid box, where no group is needed and the sandbox's connect rule
//! accepts exactly 0600; HOSTING-17 §5, HOSTING-21). Anything else at
//! those paths ends it `sockDir` before any socket opens. On every accept the peer's credentials must
//! be uid PEER (the hosted uid) and SOCKDIR's group, or the connection is answered `peerRefused`.
//! Identity is the socket: keybroker puts a `decide` frame naming that socket's resident in front
//! of each ask, unread, and hands both to DECIDER (the Lean `hosting-broker`, started confined as
//! `DECIDER T0 SLOTS STORE OPERATOR`: the operator clock, the comma-separated key slots the key file
//! holds (so Lean refuses `keyMissing` before it charges anything), and the World it follows for
//! the allowances OPERATOR owns, which it may read and nothing else). A `grant` names a key slot and the
//! upstream request Lean printed; keybroker dials UPSTREAM (`addr:port`, the operator's dial
//! address), speaks TLS 1.3 (rustls with the ring provider, HOSTING-15) with SNI and certificate
//! verification for the HOST the grant names (Lean's provider table, never the dial address), then
//! checks that the verified leaf's key is one PINS names for that host (`pinMismatch` otherwise,
//! before any request byte, a host with no pin included), sends the request (HTTP/1.0, `Host:`
//! Lean's host) with the slot's key in the header Lean named, and hands the upstream's status and
//! body back to the decider (`reply`), which answers the reply TEXT Lean read from the provider's
//! JSON, the status, or `replyMalformed` (HOSTING-29): the resident never receives the provider's
//! body. A response holding the key is `keyEchoed` before Lean sees it, and a reply text holding it
//! is `keyEchoed` before the resident does (an escape can spell the key without its bytes). A TLS
//! failure is `tlsCertificate`, `tlsHostname` or `tlsProtocol`, never the upstream's text. It
//! decides nothing: every verdict is the decider's, and every way it ends is a name on stderr. One
//! ask at a time per resident (`busy`).
//!
//! THE WRITER'S CERTIFY KEY (HOSTING-56, DESIGN-TRUST §4.4b). KEYS may also hold the line
//! `certify HEX` (an Ed25519 seed, 64 lowercase hex digits). The NEXT seed, the one a rotation
//! brings in, never lives in KEYS: a thief of this file would hold it with the current one, and
//! pre-commitment protects a rotation only from an adversary without the successor secret
//! (DESIGN-TRUST §4.4c, HOSTING-60). A KEYS file with a `certify.next` line is refused
//! `keyFileFormat`. With `certify`, keybroker binds ONE more socket, `SOCKDIR/.writer/certify.sock`
//! (0600 in a 0700 directory of its own: the writer, `host serve --certify`, runs as the key holder;
//! a leading dot, so no grain name can take it), whose peer must be keybroker's own uid. The writer
//! sends one frame, the certified bytes of a head; keybroker puts `certify atMs` in front, unread,
//! and hands both to the decider, now started with a fifth argument, CERTIFIED (`KEYS.certified`, the
//! last head this key signed, 0600 beside KEYS, made empty when absent). A `sign` verdict names the
//! bytes the decider granted (`Hosting.Certify.decide`: a head of its own fold, never below or beside
//! the last one); keybroker FIRST replaces CERTIFIED by them durably (`certifyState` if it cannot:
//! nothing is signed), then signs `CERTIFY_DOMAIN ‖ bytes` with the certify seed and answers
//! `signed` with the public key. The seed signs nothing else: no path signs raw bytes with it, and
//! the domain is pairwise disjoint from every other a key signs under (`Protocol.Proofs.Domains`).
//! `keybroker --certify-pub KEYS` prints the certify public key (`certify HEX`), for `host genesis
//! --certifier HEX --threshold 1`.
//!
//! THE OPERATOR'S DAILY ASK CAP (HOSTING-62). KEYS may also hold the line `asks N` (N ≥ 1, decimal):
//! at most N asks a day are sent upstream, whatever the World's allowances say. The count lives in
//! ASKS (`KEYS.asks`, 0600 beside KEYS, made empty when absent), which the decider reads at its start
//! (`--asks N ASKS`, ASKS read-only to it). A grant under the cap carries `asked`, the day and count
//! the decider reached; keybroker FIRST replaces ASKS by those bytes durably (`askState` if it
//! cannot: nothing is sent), and only then calls. So a restart reads back every ask it sent and never
//! refunds the day. Past N the decider refuses `askCap` and charges no allowance.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::ErrorKind;
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nanodregg_client::generated::BROKER_SOCK;
use nanodregg_launcher::broker_generated::wire::{
    Answer, BrokerRefusal, CertifyAnswer, Request, Verdict,
};
use nanodregg_launcher::broker_generated::{
    CERTIFY_DOMAIN, CERTIFY_SOCK, DECIDER_TICK_MS, FRAME_MAX, WRITER_DIR, keybroker_exit,
    read_frame, write_frame,
};
use nanodregg_launcher::grain_name_ok;
use nanodregg_launcher::residents::{self, DeciderEnd};
use nanodregg_sandbox::custody::{self, Refused};
use nanodregg_sandbox::{Policy, command};
use rustls::pki_types::pem::{PemObject, SectionKind};
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{CertificateError, ClientConfig, ClientConnection, RootCertStore, StreamOwned};
use webpki::EndEntityCert;
use zeroize::Zeroizing;

/// The largest key file read.
const KEYFILE_MAX: usize = 65536;
/// The largest anchor file read (the pinned webpki bundle is about 200 KB).
const ANCHORS_MAX: usize = 1 << 20;
/// The largest pin file read.
const PINS_MAX: usize = 1 << 16;
/// How long one upstream call may take, connect to last byte: one deadline over the whole call
/// (`frame::Deadline`, CLIENT-39), never per read.
const UPSTREAM_TIMEOUT: Duration = Duration::from_secs(120);
/// How long a resident's connection may sit idle between asks.
const RESIDENT_IDLE: Duration = Duration::from_secs(60);
/// Connections one socket accepts, and asks one connection carries: centuries of use.
const LIFETIME: u64 = 1 << 48;
/// The largest upstream response read: its body must fit one `answer` frame.
const RESPONSE_MAX: usize = FRAME_MAX as usize - 64;
/// How often keybroker asks its decider which residents the World holds (HOSTING-26). Liveness
/// only: a socket appears within a tick of the decider seeing a grain's birth.
const TICK: Duration = Duration::from_millis(DECIDER_TICK_MS as u64);
/// Ticks a decider that answered out of turn has to end on its own before it is stopped.
const ENDING_TICKS: u32 = 10;

/// How keybroker ends. Each end's exit code is Lean's (`Hosting.KeybrokerExit`, emitted as
/// `keybroker_exit`); a decider that exits is passed through with its own code (`DeciderExit`).
enum End {
    Usage,
    /// a key-file or anchor-file refusal: its name and its code
    File(&'static str, u8),
    Tls(String),
    Socket(String),
    /// the socket directory, a resident's directory or a socket path fails HOSTING-17's checks
    SockDir(String),
    DeciderRefused(String),
    /// the decider's exit code, or `None` for a signal
    DeciderEnded(Option<i32>),
    /// the decider's process ended with a code `DeciderExit` does not name (`decider_exit::ALL`):
    /// the mechanism's, not the decider's (HOSTING-23)
    DeciderMechanism(i32),
    /// `wait` on the decider failed
    DeciderLost(String),
    Pid(String),
    /// the parent-death link could not be set (`die_with_parent`, CLIENT-38)
    ParentDeath(String),
    /// `--certify-pub` printed the keys
    Printed,
}

impl End {
    fn describe(&self) -> String {
        match self {
            End::Usage => {
                "usage: keybroker KEYS ANCHORS PINS SOCKDIR PIDS UPSTREAM STORE OPERATOR PEER DECIDER"
                    .into()
            }
            End::File(n, _) => (*n).into(),
            End::Tls(e) => format!("tlsConfig {e}"),
            End::Socket(e) => format!("socket {e}"),
            End::SockDir(e) => format!("sockDir {e}"),
            End::DeciderRefused(e) => format!("deciderRefused {e}"),
            End::DeciderEnded(Some(c)) => format!("deciderEnded {c}"),
            End::DeciderEnded(None) => "deciderSignaled".into(),
            End::DeciderMechanism(c) => format!("deciderMechanism {c}"),
            End::DeciderLost(e) => format!("deciderLost {e}"),
            End::Pid(e) => format!("pidFile {e}"),
            End::ParentDeath(e) => format!("parentDeath {e}"),
            End::Printed => "certifyPub".into(),
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    if let [flag, keys] = args.as_slice()
        && flag == "--certify-pub"
    {
        return match certify_pub(Path::new(keys)) {
            End::Printed => ExitCode::SUCCESS,
            end => {
                nanodregg_launcher::say("keybroker", &end.describe());
                ExitCode::from(match end {
                    End::File(_, code) => code,
                    _ => keybroker_exit::USAGE,
                })
            }
        };
    }
    let end = run();
    // One write (`nanodregg_launcher::say`): the decider shares this stderr.
    nanodregg_launcher::say("keybroker", &end.describe());
    ExitCode::from(match end {
        End::Usage => keybroker_exit::USAGE,
        End::File(_, code) => code,
        End::Tls(_) => keybroker_exit::TLS_CONFIG,
        End::Socket(_) => keybroker_exit::SOCKET,
        End::SockDir(_) => keybroker_exit::SOCK_DIR,
        End::DeciderRefused(_) => keybroker_exit::DECIDER_REFUSED,
        End::Pid(_) => keybroker_exit::PID_FILE,
        // the decider's own code, passed through (`run` made every other code DeciderMechanism or
        // a signal, so every code here is one of DeciderExit's and fits u8)
        End::DeciderEnded(Some(c)) => u8::try_from(c).unwrap_or(keybroker_exit::DECIDER_MECHANISM),
        End::DeciderEnded(None) => keybroker_exit::DECIDER_SIGNALED,
        End::DeciderMechanism(_) => keybroker_exit::DECIDER_MECHANISM,
        End::DeciderLost(_) => keybroker_exit::DECIDER_LOST,
        End::ParentDeath(_) => keybroker_exit::PARENT_DEATH,
        End::Printed => keybroker_exit::USAGE,
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

/// The pin file's custody refusal, by name. A file that is not there is `pinsMissing`.
fn pins_end(e: &Refused) -> End {
    use keybroker_exit as k;
    match e {
        Refused::Link => End::File("pinsLink", k::PINS_LINK),
        Refused::NotRegular => End::File("pinsNotRegular", k::PINS_NOT_REGULAR),
        Refused::Owner(_) => End::File("pinsOwner", k::PINS_OWNER),
        Refused::Mode(_) => End::File("pinsMode", k::PINS_MODE),
        Refused::Length(_) => End::File("pinsLength", k::PINS_LENGTH),
        Refused::Dir(_) => End::File("pinsDir", k::PINS_DIR),
        Refused::Io(e) if e.kind() == ErrorKind::NotFound => {
            End::File("pinsMissing", k::PINS_MISSING)
        }
        Refused::Io(_) => End::File("pinsIo", k::PINS_IO),
    }
}

/// Each host's pinned leaf keys: the SHA-256 of a SubjectPublicKeyInfo.
type Pins = BTreeMap<Vec<u8>, Vec<[u8; 32]>>;

/// The value of one lowercase hexadecimal digit.
fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        _ => None,
    }
}

/// `HOST HEX` per line, each ended by LF: HOST printable ASCII without a space, HEX exactly 64
/// lowercase hexadecimal digits. An empty file is no pin at all (every call is refused
/// `pinMismatch`). Any other line, or a pin given twice, is `None` (`pinsMalformed`): the file is
/// the operator's whole pin set, so nothing in it is skipped.
fn parse_pins(text: &[u8]) -> Option<Pins> {
    let mut pins = Pins::new();
    if text.is_empty() {
        return Some(pins);
    }
    let body = text.strip_suffix(b"\n")?;
    for line in body.split(|b| *b == b'\n') {
        let sp = line.iter().position(|b| *b == b' ')?;
        let (host, hex) = (&line[..sp], &line[sp + 1..]);
        if host.is_empty() || !host.iter().all(u8::is_ascii_graphic) || hex.len() != 64 {
            return None;
        }
        let mut pin = [0u8; 32];
        for (i, pair) in hex.chunks(2).enumerate() {
            pin[i] = hex_val(pair[0])? * 16 + hex_val(pair[1])?;
        }
        let set = pins.entry(host.to_vec()).or_default();
        if set.contains(&pin) {
            return None;
        }
        set.push(pin);
    }
    Some(pins)
}

/// The SHA-256 of the leaf certificate's SubjectPublicKeyInfo (DER, with its SEQUENCE header), as
/// rustls verified it: the only certificate of the sent chain a pin can soundly name, since the
/// verified path is not exposed and anything else in the sent chain is the server's choice.
fn leaf_pin(conn: &ClientConnection) -> Option<[u8; 32]> {
    let leaf = conn.peer_certificates()?.first()?;
    let cert = EndEntityCert::try_from(leaf).ok()?;
    let spki = cert.subject_public_key_info();
    let d = ring::digest::digest(&ring::digest::SHA256, spki.as_ref());
    d.as_ref().try_into().ok()
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

/// An Ed25519 seed.
type Seed = Zeroizing<[u8; 32]>;

/// 64 lowercase hexadecimal digits as a seed.
fn parse_seed(hex: &[u8]) -> Option<Seed> {
    if hex.len() != 64 {
        return None;
    }
    let mut seed = Zeroizing::new([0u8; 32]);
    for (i, pair) in hex.chunks(2).enumerate() {
        seed[i] = hex_val(pair[0])? * 16 + hex_val(pair[1])?;
    }
    Some(seed)
}

/// `SLOT KEY` per line: a decimal slot, one space, the key's bytes (printable ASCII, no space); at
/// most once the certify slot's line, `certify HEX`; and at most once the daily ask cap, `asks N`
/// (HOSTING-62). A `certify.next` line is refused: the next seed has its own custody (DESIGN-TRUST
/// §4.4c). At least one provider key.
fn parse_keys(text: &[u8]) -> Option<(Keys, Option<Seed>, Option<u32>)> {
    let mut keys = Keys::new();
    let mut certify = None;
    let mut asks = None;
    for line in text.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let sp = line.iter().position(|b| *b == b' ')?;
        let (word, key) = (&line[..sp], &line[sp + 1..]);
        if word == b"certify.next" {
            return None;
        }
        if word == b"asks" {
            let n: u32 = std::str::from_utf8(key).ok()?.parse().ok()?;
            if n == 0 || key.first() == Some(&b'0') || asks.replace(n).is_some() {
                return None;
            }
            continue;
        }
        if word == b"certify" {
            if certify.replace(parse_seed(key)?).is_some() {
                return None;
            }
            continue;
        }
        let slot: u32 = std::str::from_utf8(word).ok()?.parse().ok()?;
        if key.is_empty() || !key.iter().all(|b| b.is_ascii_graphic()) {
            return None;
        }
        if keys.insert(slot, Zeroizing::new(key.to_vec())).is_some() {
            return None;
        }
    }
    if keys.is_empty() {
        None
    } else {
        Some((keys, certify, asks))
    }
}

/// The certify slot's signer: the seed's key pair (ring's Ed25519, already in the TCB under rustls).
struct Certifier {
    pair: ring::signature::Ed25519KeyPair,
    /// where the last certified head is kept (`KEYS.certified`)
    state: PathBuf,
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn key_pair(seed: &Seed) -> Option<ring::signature::Ed25519KeyPair> {
    ring::signature::Ed25519KeyPair::from_seed_unchecked(seed.as_slice()).ok()
}

/// `KEYS.<suffix>` (`certified`, `asks`): beside KEYS, so a sandbox that hides KEYS' directory hides
/// it too.
fn state_path(keys: &Path, suffix: &str) -> Option<PathBuf> {
    let mut name = keys.file_name()?.to_os_string();
    name.push(".");
    name.push(suffix);
    Some(keys.with_file_name(name))
}

/// `keybroker --certify-pub KEYS`: the certify slot's public key.
fn certify_pub(keys_path: &Path) -> End {
    use ring::signature::KeyPair as _;
    let text = match custody::read_private(keys_path, 1..=KEYFILE_MAX) {
        Ok(t) => t,
        Err(e) => return key_file_end(&e),
    };
    let Some((_, Some(seed), _)) = parse_keys(&text) else {
        return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
    };
    let Some(cur) = key_pair(&seed) else {
        return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
    };
    println!("certify {}", hex(cur.public_key().as_ref()));
    End::Printed
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
        .unwrap_or(0)
}

struct Shared {
    decider: Mutex<residents::Decider>,
    keys: Keys,
    pins: Pins,
    upstream: String,
    tls: Arc<ClientConfig>,
    /// the only uid served (`PEER`, the hosted uid)
    peer: u32,
    /// the only gid served: SOCKDIR's group
    group: u32,
    /// the writer's certify slot, when KEYS holds one
    certify: Option<Certifier>,
    /// the daily ask cap's count file (`KEYS.asks`), when KEYS sets `asks N`
    asks: Option<PathBuf>,
}

fn run() -> End {
    // First: a keybroker whose parent dies (a killed test, never systemd) does not outlive it.
    if let Err(e) = nanodregg_sandbox::die_with_parent() {
        return End::ParentDeath(e.to_string());
    }
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let [
        keys_path,
        anchors_path,
        pins_path,
        sockdir,
        pids,
        upstream,
        store,
        operator,
        peer,
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
    let Some((keys, seed, asks_limit)) = parse_keys(&text) else {
        return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
    };
    // the certify slot: its key pair, and the last certified head's file, made empty when absent
    let certify = match seed {
        None => None,
        Some(seed) => {
            let (Some(pair), Some(state)) = (key_pair(&seed), state_path(&keys_path, "certified"))
            else {
                return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
            };
            if !private_state(&state) {
                return End::File("certifiedState", keybroker_exit::CERTIFIED_STATE);
            }
            Some(Certifier { pair, state })
        }
    };
    // the daily ask cap: its count file, made empty when absent (HOSTING-62)
    let asks = match asks_limit {
        None => None,
        Some(n) => {
            let Some(state) = state_path(&keys_path, "asks") else {
                return End::File("keyFileFormat", keybroker_exit::KEY_FILE_FORMAT);
            };
            if !private_state(&state) {
                return End::File("asksState", keybroker_exit::ASKS_STATE);
            }
            Some((n, state))
        }
    };
    let anchors = match custody::read_public(&PathBuf::from(anchors_path), 1..=ANCHORS_MAX) {
        Ok(a) => a,
        Err(e) => return anchors_end(&e),
    };
    let Some(roots) = parse_anchors(&anchors) else {
        return End::File("anchorsMalformed", keybroker_exit::ANCHORS_MALFORMED);
    };
    let pins = match custody::read_public(&PathBuf::from(pins_path), 0..=PINS_MAX) {
        Ok(p) => p,
        Err(e) => return pins_end(&e),
    };
    let Some(pins) = parse_pins(&pins) else {
        return End::File("pinsMalformed", keybroker_exit::PINS_MALFORMED);
    };
    let tls = match tls_config(roots) {
        Ok(c) => Arc::new(c),
        Err(e) => return End::Tls(e.to_string()),
    };
    let Some(upstream) = upstream.to_str().map(str::to_owned) else {
        return End::Usage;
    };
    let Some(peer) = peer.to_str().and_then(|p| p.parse::<u32>().ok()) else {
        return End::Usage;
    };
    let sockdir = PathBuf::from(sockdir);
    let (group, own) = match sockdir_shape(&sockdir) {
        Ok(v) => v,
        Err(why) => return End::SockDir(why),
    };
    // The socket admits exactly PEER: its owner alone when PEER is this uid, else SOCKDIR's group.
    let mode = if peer == own { 0o600 } else { 0o660 };
    let decider = PathBuf::from(decider);
    let pid_file = PathBuf::from(pids).join("decider.pid");

    // The decider sees its own program and reads the Store; the key file is hidden as a second barrier.
    let store = PathBuf::from(store);
    let mut read = vec![store.clone()];
    if let Some(c) = &certify {
        read.push(c.state.clone());
    }
    if let Some((_, a)) = &asks {
        read.push(a.clone());
    }
    let policy = Policy {
        read,
        write: vec![],
        exec: vec![decider.clone()],
        hidden: vec![keys_path.clone()],
        connect: vec![],
        landlock_abi: 0,
    };
    let t0 = OsString::from(now_ms().to_string());
    let slots = OsString::from(
        keys.keys()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(","),
    );
    let mut dargs: Vec<&std::ffi::OsStr> = vec![
        t0.as_os_str(),
        slots.as_os_str(),
        store.as_os_str(),
        operator.as_os_str(),
    ];
    if let Some(c) = &certify {
        dargs.push(c.state.as_os_str());
    }
    let asks_n = asks.as_ref().map(|(n, _)| OsString::from(n.to_string()));
    if let (Some(n), Some((_, a))) = (&asks_n, &asks) {
        dargs.extend([std::ffi::OsStr::new("--asks"), n.as_os_str(), a.as_os_str()]);
    }
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
        decider: Mutex::new(residents::Decider::new(din, dout, residents::ANSWER)),
        keys,
        pins,
        upstream,
        tls,
        peer,
        group,
        certify,
        asks: asks.map(|(_, a)| a),
    });
    // the writer's socket, before any resident's: it lives as long as keybroker
    if shared.certify.is_some() {
        match writer_socket(&sockdir, own) {
            Ok(l) => {
                let sh = Arc::clone(&shared);
                std::thread::spawn(move || serve_writer(l, own, sh));
            }
            Err(end) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = std::fs::remove_file(&pid_file);
                return end;
            }
        }
    }

    // Which sockets to serve is the World's: asked at start and every tick, until the decider ends
    // (its end is keybroker's: an ask could no longer be decided).
    let mut served: BTreeMap<Vec<u8>, Served> = BTreeMap::new();
    let ended = 'life: {
        for _ in 0..LIFETIME {
            if let Ok(Some(st)) = child.try_wait() {
                break 'life Ok(st);
            }
            match residents(&shared) {
                Some(names) => {
                    let place = Place {
                        sockdir: &sockdir,
                        group,
                        mode,
                    };
                    if let Err(end) = serve_residents(&place, &names, &mut served, &shared) {
                        let _ = child.kill();
                        let _ = child.wait();
                        let _ = std::fs::remove_file(&pid_file);
                        return end;
                    }
                }
                // the decider is gone, or answered out of turn: its own end names the run when it
                // comes within a bounded while, else keybroker stops it and says so
                None => {
                    for _ in 0..ENDING_TICKS {
                        if let Ok(Some(st)) = child.try_wait() {
                            break 'life Ok(st);
                        }
                        std::thread::sleep(TICK);
                    }
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = std::fs::remove_file(&pid_file);
                    return End::DeciderLost("no residents answer".into());
                }
            }
            std::thread::sleep(TICK);
        }
        child.wait()
    };
    let status = ended;
    let _ = std::fs::remove_file(&pid_file);
    // only a code Lean's DeciderExit names is the decider's own end (`residents::decider_end`)
    match status.map(residents::decider_end) {
        Ok(DeciderEnd::Own(c)) => End::DeciderEnded(Some(i32::from(c))),
        Ok(DeciderEnd::Signaled) => End::DeciderEnded(None),
        Ok(DeciderEnd::Mechanism(c)) => End::DeciderMechanism(c),
        Err(e) => End::DeciderLost(e.to_string()),
    }
}

/// HOSTING-17's check of SOCKDIR, before any socket opens: it passes `custody::check_shared_dir`
/// (owned by the euid, mode exactly 02710, every directory above it StrictModes-clean). Returns its
/// group and its owner (the euid, by `check_shared_dir`).
fn sockdir_shape(sockdir: &Path) -> Result<(u32, u32), String> {
    let at = |p: &Path, e: &dyn std::fmt::Debug| format!("{} {e:?}", p.display());
    let group = custody::check_shared_dir(sockdir).map_err(|e| at(sockdir, &e))?;
    let owner = std::fs::symlink_metadata(sockdir)
        .map_err(|e| at(sockdir, &e))?
        .uid();
    Ok((group, owner))
}

/// One resident's socket path, after HOSTING-17's checks of its directory: made here when absent, it
/// must pass `custody::check_shared_dir` with SOCKDIR's group and hold nothing but its socket (the
/// sandbox binds the directory: anything else here would be in the resident's view); a socket already
/// there must be a socket of this uid, the last life's, which is unlinked to be bound again.
fn resident_socket(sockdir: &Path, group: u32, r: &str) -> Result<PathBuf, String> {
    let at = |p: &Path, e: &dyn std::fmt::Debug| format!("{} {e:?}", p.display());
    let d = sockdir.join(r);
    match std::fs::symlink_metadata(&d) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            nanodregg_launcher::make_dir(&d, 0o710).map_err(|e| at(&d, &e))?;
        }
        Err(e) => return Err(at(&d, &e)),
        Ok(_) => {}
    }
    let g = custody::check_shared_dir(&d).map_err(|e| at(&d, &e))?;
    if g != group {
        return Err(format!("{} group {g}, not SOCKDIR's {group}", d.display()));
    }
    for entry in std::fs::read_dir(&d).map_err(|e| at(&d, &e))? {
        let name = entry.map_err(|e| at(&d, &e))?.file_name();
        if name != BROKER_SOCK {
            return Err(format!("{} holds {name:?}", d.display()));
        }
    }
    let sock = d.join(BROKER_SOCK);
    let own = std::fs::symlink_metadata(&d).map_err(|e| at(&d, &e))?.uid();
    match std::fs::symlink_metadata(&sock) {
        Err(e) if e.kind() == ErrorKind::NotFound => {}
        Ok(m) if m.file_type().is_socket() && m.uid() == own => {
            std::fs::remove_file(&sock).map_err(|e| at(&sock, &e))?
        }
        Ok(_) => return Err(format!("{} is not this broker's socket", sock.display())),
        Err(e) => return Err(at(&sock, &e)),
    }
    Ok(sock)
}

/// Where resident sockets are bound.
struct Place<'a> {
    sockdir: &'a Path,
    group: u32,
    mode: u32,
}

/// A socket keybroker serves: its path, and the flag that ends its accept loop.
struct Served {
    path: PathBuf,
    stop: Arc<AtomicBool>,
}

/// The residents the decider answers, or `None` when it cannot be reached or answers anything else.
fn residents(sh: &Shared) -> Option<Vec<Vec<u8>>> {
    residents::ask(&mut *sh.decider.lock().ok()?, now_ms())
}

/// Serve exactly `names`: bind a socket for each name not yet served (HOSTING-17's checks first),
/// and close and remove the socket and directory of each served name no longer answered. A name
/// that is not a grain directory name, or a socket path failing its checks, ends keybroker
/// `sockDir`, as at start.
fn serve_residents(
    place: &Place<'_>,
    names: &[Vec<u8>],
    served: &mut BTreeMap<Vec<u8>, Served>,
    shared: &Arc<Shared>,
) -> Result<(), End> {
    for n in names {
        if served.contains_key(n) {
            continue;
        }
        let r = std::str::from_utf8(n)
            .ok()
            .filter(|r| grain_name_ok(r.as_bytes()))
            .ok_or_else(|| End::SockDir(format!("resident name {n:?}")))?;
        let path = resident_socket(place.sockdir, place.group, r).map_err(End::SockDir)?;
        let listener = bind(&path, place.group, place.mode)?;
        let stop = Arc::new(AtomicBool::new(false));
        let (sh, st, resident) = (Arc::clone(shared), Arc::clone(&stop), n.clone());
        std::thread::spawn(move || serve_socket(listener, resident, st, sh));
        served.insert(n.clone(), Served { path, stop });
    }
    let gone: Vec<Vec<u8>> = served
        .keys()
        .filter(|k| !names.contains(k))
        .cloned()
        .collect();
    for g in gone {
        if let Some(s) = served.remove(&g) {
            s.stop.store(true, Ordering::SeqCst);
            // wake the accept loop so it sees the flag; then the socket and its directory go
            let _ = UnixStream::connect(&s.path);
            let _ = std::fs::remove_file(&s.path);
            if let Some(d) = s.path.parent() {
                let _ = std::fs::remove_dir(d);
            }
        }
    }
    Ok(())
}

/// Bind one resident's socket at `mode`: 0660 opens it to the hosted group, with SOCKDIR's group
/// (from the setgid bit), 0600 to this uid alone; otherwise keybroker ends `sockDir` (the bit was
/// lost).
fn bind(path: &Path, group: u32, mode: u32) -> Result<UnixListener, End> {
    let socket = |e: std::io::Error| End::Socket(format!("{} {e}", path.display()));
    let l = UnixListener::bind(path).map_err(socket)?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).map_err(socket)?;
    let m = std::fs::symlink_metadata(path).map_err(socket)?;
    if m.gid() != group || m.permissions().mode() & 0o7777 != mode {
        return Err(End::SockDir(format!(
            "{} group {} mode {:o}, not {group} {mode:o}",
            path.display(),
            m.gid(),
            m.permissions().mode() & 0o7777
        )));
    }
    Ok(l)
}

/// One resident's socket: one connection at a time; a second, while one is open, is told `busy`.
/// A peer that is not uid PEER with SOCKDIR's group is told `peerRefused`, and nothing it sent is
/// read. When `stop` is set (the resident left the World) the loop ends and the listener closes.
fn serve_socket(listener: UnixListener, resident: Vec<u8>, stop: Arc<AtomicBool>, sh: Arc<Shared>) {
    let open = Arc::new(AtomicBool::new(false));
    for conn in listener.incoming().take(LIFETIME as usize) {
        if stop.load(Ordering::SeqCst) {
            return;
        }
        let Ok(mut s) = conn else { continue };
        match custody::peer_cred(&s) {
            Ok((uid, gid)) if uid == sh.peer && gid == sh.group => {}
            _ => {
                let _ = answer(&mut s, &refused(BrokerRefusal::PeerRefused));
                continue;
            }
        }
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
    let verdict = sh.decider.lock().ok()?.exchange(&[&req, ask])?;
    Some(match verdict {
        Verdict::Refuse { broker_refusal } => refused(broker_refusal),
        // a residents answer to a decide is the decider out of turn: the connection closes
        Verdict::Residents { .. } => return None,
        Verdict::Grant {
            key_slot,
            host,
            target,
            headers,
            key_header,
            body,
            asked,
            ..
        } => {
            let Some(key) = sh.keys.get(&key_slot) else {
                return Some(refused(BrokerRefusal::KeyMissing));
            };
            // the day's count first, durably; only then the call (HOSTING-62). A grant that carries a
            // count with no cap set, or none with one, is the decider out of turn.
            match (&sh.asks, asked.is_empty()) {
                (None, true) => {}
                (Some(state), false) => {
                    let (Some(dir), Some(name)) =
                        (state.parent(), state.file_name().and_then(|n| n.to_str()))
                    else {
                        return Some(refused(BrokerRefusal::AskState));
                    };
                    if nanodregg_client::fsx::replace(dir, name, &asked).is_err() {
                        return Some(refused(BrokerRefusal::AskState));
                    }
                }
                _ => return None,
            }
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
                    Some((status, body)) => return reply(sh, status, body, key),
                    None => refused(BrokerRefusal::UpstreamFailed),
                },
            }
        }
        // a reply, status or sign verdict to a decide is the decider out of turn: the connection closes
        Verdict::Reply { .. } | Verdict::Status { .. } | Verdict::Sign { .. } => return None,
    })
}

/// The upstream's answer, read by the decider (`reply`): the reply text Lean read from a 200 body,
/// the status of any other, or a refusal. A text holding the key is withheld (`keyEchoed`). `None`
/// when the decider cannot be reached or answers out of turn.
fn reply(sh: &Shared, status: u32, body: &[u8], key: &[u8]) -> Option<Answer> {
    let req = Request::Reply {
        status,
        body: body.to_vec(),
    }
    .encode()
    .ok()?;
    let verdict = sh.decider.lock().ok()?.exchange(&[&req])?;
    Some(match verdict {
        Verdict::Reply { text } if contains(&text, key) => refused(BrokerRefusal::KeyEchoed),
        Verdict::Reply { text } => Answer::Reply { text },
        Verdict::Status { status } => Answer::Status { status },
        Verdict::Refuse { broker_refusal } => refused(broker_refusal),
        Verdict::Grant { .. } | Verdict::Residents { .. } | Verdict::Sign { .. } => return None,
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

/// Dial UPSTREAM, complete a TLS 1.3 handshake verified for Lean's host, check the leaf's key
/// against the host's pins (`pinMismatch`, no request byte written), then `POST target
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
    let until = Instant::now() + UPSTREAM_TIMEOUT;
    let t = TcpStream::connect_timeout(&addr, UPSTREAM_TIMEOUT).map_err(failed)?;
    let mut io = nanodregg_client::frame::Deadline::until(&t, until);
    let mut conn = ClientConnection::new(Arc::clone(&sh.tls), name).map_err(|e| tls_refusal(&e))?;
    while conn.is_handshaking() {
        conn.complete_io(&mut io).map_err(|e| io_refusal(&e))?;
    }
    // the verified leaf's key must be one the operator pinned for Lean's host (HOSTING-28)
    let pinned = sh.pins.get(r.host).map(Vec::as_slice).unwrap_or(&[]);
    match leaf_pin(&conn) {
        Some(p) if pinned.contains(&p) => {}
        _ => return Err(BrokerRefusal::PinMismatch),
    }
    let mut s = StreamOwned::new(conn, io);
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

/// A state file beside KEYS (the last certified head, the day's ask count): there and private (the
/// custody checks, 0600), or made empty (durably, 0600) when absent. `false` ends keybroker by the
/// file's name.
fn private_state(state: &Path) -> bool {
    match custody::read_private(state, 0..=FRAME_MAX as usize) {
        Ok(_) => true,
        Err(Refused::Io(e)) if e.kind() == ErrorKind::NotFound => {
            let (Some(dir), Some(name)) =
                (state.parent(), state.file_name().and_then(|n| n.to_str()))
            else {
                return false;
            };
            nanodregg_client::fsx::create_once(dir, name, &[]).is_ok()
        }
        Err(_) => false,
    }
}

/// `SOCKDIR/.writer/certify.sock`: the directory made 0700 (SOCKDIR's setgid bit cleared) when absent
/// and then required private
/// (`custody::check_private_dir`) and holding nothing but the socket; a socket of this uid already
/// there (the last life's) is unlinked; the socket bound 0600.
fn writer_socket(sockdir: &Path, own: u32) -> Result<UnixListener, End> {
    use std::os::unix::ffi::OsStrExt as _;
    let at = |p: &Path, e: &dyn std::fmt::Debug| End::SockDir(format!("{} {e:?}", p.display()));
    let d = sockdir.join(std::ffi::OsStr::from_bytes(WRITER_DIR));
    let name = std::ffi::OsStr::from_bytes(CERTIFY_SOCK);
    match std::fs::symlink_metadata(&d) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            nanodregg_launcher::make_dir(&d, 0o700).map_err(|e| at(&d, &e))?;
            // SOCKDIR's setgid bit is inherited by what is made in it: the writer's directory is
            // this uid's alone, so it is cleared (0700, `check_private_dir`)
            std::fs::set_permissions(&d, std::fs::Permissions::from_mode(0o700))
                .map_err(|e| at(&d, &e))?;
        }
        Err(e) => return Err(at(&d, &e)),
        Ok(_) => {}
    }
    custody::check_private_dir(&d).map_err(|e| at(&d, &e))?;
    for entry in std::fs::read_dir(&d).map_err(|e| at(&d, &e))? {
        let n = entry.map_err(|e| at(&d, &e))?.file_name();
        if n != name {
            return Err(End::SockDir(format!("{} holds {n:?}", d.display())));
        }
    }
    let sock = d.join(name);
    match std::fs::symlink_metadata(&sock) {
        Err(e) if e.kind() == ErrorKind::NotFound => {}
        Ok(m) if m.file_type().is_socket() && m.uid() == own => {
            std::fs::remove_file(&sock).map_err(|e| at(&sock, &e))?
        }
        Ok(_) => {
            return Err(End::SockDir(format!(
                "{} is not this broker's socket",
                sock.display()
            )));
        }
        Err(e) => return Err(at(&sock, &e)),
    }
    let socket = |e: std::io::Error| End::Socket(format!("{} {e}", sock.display()));
    let l = UnixListener::bind(&sock).map_err(socket)?;
    std::fs::set_permissions(&sock, std::fs::Permissions::from_mode(0o600)).map_err(socket)?;
    Ok(l)
}

/// The writer's socket: one connection at a time (`busy`), a peer of keybroker's own uid only
/// (`peerRefused`, nothing it sent read).
fn serve_writer(listener: UnixListener, own: u32, sh: Arc<Shared>) {
    let open = Arc::new(AtomicBool::new(false));
    for conn in listener.incoming().take(LIFETIME as usize) {
        let Ok(mut s) = conn else { continue };
        match custody::peer_cred(&s) {
            Ok((uid, _)) if uid == own => {}
            _ => {
                let _ = certify_answer(&mut s, &certify_refused(BrokerRefusal::PeerRefused));
                continue;
            }
        }
        if open.swap(true, Ordering::SeqCst) {
            let _ = certify_answer(&mut s, &certify_refused(BrokerRefusal::Busy));
            continue;
        }
        let (open, sh) = (Arc::clone(&open), Arc::clone(&sh));
        std::thread::spawn(move || {
            serve_writer_conn(s, &sh);
            open.store(false, Ordering::SeqCst);
        });
    }
}

fn certify_refused(r: BrokerRefusal) -> CertifyAnswer {
    CertifyAnswer::Refused { broker_refusal: r }
}

fn certify_answer(s: &mut UnixStream, a: &CertifyAnswer) -> Option<()> {
    let bytes = a.encode().ok()?;
    write_frame(s, &bytes).ok()?;
    s.flush().ok()
}

fn serve_writer_conn(mut s: UnixStream, sh: &Shared) {
    if s.set_read_timeout(Some(RESIDENT_IDLE)).is_err() {
        return;
    }
    for _ in 0..LIFETIME {
        let Ok(bytes) = read_frame(&mut s) else {
            return;
        };
        let Some(a) = certify_once(sh, &bytes) else {
            return;
        };
        if certify_answer(&mut s, &a).is_none() {
            return;
        }
    }
}

/// One certify ask: the decider's verdict; for a `sign`, the head made durable in CERTIFIED and
/// only then signed. `None` when the decider cannot be reached or answers out of turn.
fn certify_once(sh: &Shared, certified: &[u8]) -> Option<CertifyAnswer> {
    use ring::signature::KeyPair as _;
    let c = sh.certify.as_ref()?;
    let req = Request::Certify { at_ms: now_ms() }.encode().ok()?;
    let verdict = sh.decider.lock().ok()?.exchange(&[&req, certified])?;
    Some(match verdict {
        Verdict::Refuse { broker_refusal } => certify_refused(broker_refusal),
        Verdict::Sign { certified } => {
            let (Some(dir), Some(name)) = (
                c.state.parent(),
                c.state.file_name().and_then(|n| n.to_str()),
            ) else {
                return Some(certify_refused(BrokerRefusal::CertifyState));
            };
            if nanodregg_client::fsx::replace(dir, name, &certified).is_err() {
                return Some(certify_refused(BrokerRefusal::CertifyState));
            }
            let mut msg = Vec::with_capacity(CERTIFY_DOMAIN.len() + certified.len());
            msg.extend_from_slice(CERTIFY_DOMAIN);
            msg.extend_from_slice(&certified);
            CertifyAnswer::Signed {
                key: c.pair.public_key().as_ref().to_vec(),
                signature: c.pair.sign(&msg).as_ref().to_vec(),
            }
        }
        // any other verdict to a certify is the decider out of turn: the connection closes
        Verdict::Grant { .. }
        | Verdict::Residents { .. }
        | Verdict::Reply { .. }
        | Verdict::Status { .. } => return None,
    })
}
