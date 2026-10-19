//! `nd-members MEMBER MEMBERS STATE FOLLOW PIDS HOST_SOCK PEER SUPERVISE ND HOST STORE [--hide PATH]…
//! -- /ABS/DECIDER [ARG]…`
//!
//! Each resident's member socket, for exactly the resident grains the World holds (HOSTING-30,
//! CLIENT-29). It asks its decider `residents` at start and every `TICK` (the frames keybroker reads,
//! `residents::ask`). For each name answered whose member is provisioned it runs two existing
//! `nd-supervise` children, which bind, check peers, bound fds and name every close exactly as
//! nd-supervise does:
//! - the resident's own follower (a follower is ONE member's command machine: every call and
//!   envelope it plans names its MEMBER, so it is never shared), `FOLLOW/<name>/follow.sock` →
//!   `host follow STATE/<name>/store MEMBER GRANT`, MEMBER and GRANT read from the provisioning
//!   step's `STATE/<name>/follow` (`HEX HEX` and LF, 0600, chain-checked), confined to write that
//!   Store, with MEMBERS hidden;
//! - once that socket exists, `MEMBER/<name>/nd.sock` → `nd --stdio MEMBERS/<name>
//!   FOLLOW/<name>/follow.sock HOST_SOCK`, confined to write the workspace and connect [HOST_SOCK,
//!   its own follow socket] (CLIENT-24), with STATE hidden: it reads the World only through the
//!   follow socket and can neither write nor read a follower Store or a `follow` file (HOSTING-32,
//!   cv 01a1507c-7245; `Hosting.Proofs.Plan.roots_disjoint`: MEMBERS and STATE are disjoint trees).
//!   The socket is 0660 for uid PEER in MEMBER's group (`--group --peer`), or 0600 when PEER is
//!   this uid (HOSTING-21).
//!
//! Each child hides STORE and every `--hide` path; each has a PID file in PIDS. A child that ends is
//! started again at most every `RESTART_AFTER`; past `STARTS_MAX` starts in `STARTS_WINDOW` the name
//! is `memberCrashLoop`, left unbound until the answer changes. A member not yet provisioned is
//! retried every tick and named once (`memberMissing`), so provisioning just after the birth
//! binds it within a tick. A name no longer answered loses both sockets, both directories and both
//! children, each SIGTERMed to name every peer's close (CLIENT-30), reaped on later ticks, SIGKILLed
//! past `GRACE`, counted until gone; a rebirth of its name waits. A resident's own trouble is a name
//! on stderr and that resident unbound, never an end (`memberMissing`, `socketDirShared`,
//! `memberCrashLoop`, `memberSpawn`, `memberStopping`, `memberStopForced`): one resident must not stop the others.
//! Its own ends are `members_exit` (Lean's `Hosting.MembersExit`); the decider's own end is passed
//! through, and a World past `RESIDENTS_MAX` ends it with the decider's code for that fact (7).

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::io::{ErrorKind, Write};
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitCode, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use nanodregg_launcher::broker_generated::{GRAIN_NAME_MAX, RESIDENTS_MAX, SOCK_PATH_MAX};
use nanodregg_launcher::broker_generated::{decider_exit, members_exit as exit};
use nanodregg_launcher::residents::{self, DeciderEnd};
use nanodregg_launcher::{grain_name_ok, pairwise_apart};
use nanodregg_sandbox::custody;
use nanodregg_sandbox::{Policy, command};
use rustix::process::{Pid, Signal, kill_process};

const USAGE: &str = "usage: nd-members MEMBER MEMBERS STATE FOLLOW PIDS HOST_SOCK PEER SUPERVISE ND HOST STORE [--hide PATH]... -- /ABS/DECIDER [ARG]...";
/// How often the decider is asked (keybroker's tick): liveness only.
const TICK: Duration = Duration::from_millis(200);
/// Ticks a decider that stopped answering has to end on its own before it is stopped.
const ENDING_TICKS: u32 = 10;
/// Ticks: centuries.
const LIFETIME: u64 = 1 << 48;
/// nd-member@'s RestartSec, StartLimitBurst and StartLimitIntervalSec, per resident.
const RESTART_AFTER: Duration = Duration::from_secs(2);
const STARTS_MAX: usize = 5;
const STARTS_WINDOW: Duration = Duration::from_secs(120);
/// The largest `follow` file read: two digests in hex, a space and LF.
const FOLLOW_MAX: usize = 256;
/// After SIGTERM, an nd-supervise's writers deliver a queued reply and the close, each within
/// `reply_write` (CLIENT-28); one more for its child's death and its own exit. Then SIGKILL.
const GRACE: Duration = nanodregg_client::table::MUX.reply_write.saturating_mul(3);

/// How nd-members ends: the line on stderr (a Lean name first) and the exit code.
struct End(String, u8);

fn main() -> ExitCode {
    let End(line, code) = run();
    say(&line);
    ExitCode::from(code)
}

/// A decider's end, as keybroker reads it (`residents::decider_end`).
fn decider(e: DeciderEnd) -> End {
    match e {
        DeciderEnd::Own(c) => End(format!("deciderEnded {c}"), c),
        DeciderEnd::Signaled => End("deciderSignaled".into(), exit::DECIDER_SIGNALED),
        DeciderEnd::Mechanism(c) => End(format!("deciderMechanism {c}"), exit::DECIDER_MECHANISM),
    }
}

/// One write per line: the children share this stderr.
fn say(line: &str) {
    let _ = std::io::stderr().write_all(format!("nd-members: {line}\n").as_bytes());
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
        .unwrap_or(0)
}

/// Everything fixed at start.
struct Conf {
    member: PathBuf,
    members: PathBuf,
    /// STATE: each resident's follower Store and `follow` file (`Hosting.stateRoot`)
    state: PathBuf,
    follow: PathBuf,
    pids: PathBuf,
    host_sock: PathBuf,
    supervise: PathBuf,
    nd: PathBuf,
    host: PathBuf,
    /// MEMBER's group: the only gid a member socket admits
    group: u32,
    /// `--group G --peer P`, or nothing when PEER is this uid (a 0600 socket)
    admit: Vec<OsString>,
    /// `--hide` for every child: STORE, then each `--hide` path
    hide: Vec<OsString>,
}

fn run() -> End {
    let usage = || End(USAGE.into(), exit::USAGE);
    let mut argv = std::env::args_os().skip(1);
    let fixed: Vec<PathBuf> = argv.by_ref().take(11).map(PathBuf::from).collect();
    let Ok(
        [
            member,
            members,
            state,
            follow,
            pids,
            host_sock,
            peer,
            supervise,
            nd,
            host,
            store,
        ],
    ) = <[PathBuf; 11]>::try_from(fixed)
    else {
        return usage();
    };
    let mut hidden = Vec::new();
    let decider_path = loop {
        match (argv.next(), argv.next()) {
            (Some(a), Some(p)) if a == "--hide" => hidden.push(PathBuf::from(p)),
            (Some(a), Some(d)) if a == "--" => break PathBuf::from(d),
            _ => return usage(),
        }
    };
    let dargs: Vec<OsString> = argv.collect();
    let Some(peer) = peer.to_str().and_then(|s| s.parse::<u32>().ok()) else {
        return usage();
    };
    // Law 4 (CLIENT-28): every child inherits this limit and refuses at launch below its bound.
    let need = nanodregg_client::table::MUX.fds_max();
    if let Some(have) = rustix::process::getrlimit(rustix::process::Resource::Nofile).current
        && have < need
    {
        let why = format!(
            "RLIMIT_NOFILE {have} is below the {need} fds one resident's nd-supervise may hold (CLIENT-28)"
        );
        return End(format!("fdLimit {why}"), exit::FD_LIMIT);
    }
    let root = |n: &str, c: u8, p: &Path, e: &dyn std::fmt::Debug| {
        End(format!("{n} {} {e:?}", p.display()), c)
    };
    // MEMBER passes check_shared_dir: owned by this euid, so PEER == euid is the one-uid shape
    let own = rustix::process::geteuid().as_raw();
    let group = match custody::check_shared_dir(&member) {
        Ok(g) => g,
        Err(e) => return root("memberRoot", exit::MEMBER_ROOT, &member, &e),
    };
    if let Err(e) = custody::check_private_dir(&members) {
        return root("membersRoot", exit::MEMBERS_ROOT, &members, &e);
    }
    if let Err(e) = custody::check_private_dir(&state) {
        return root("stateRoot", exit::STATE_ROOT, &state, &e);
    }
    if let Err(e) = custody::check_private_dir(&follow) {
        return root("followRoot", exit::FOLLOW_ROOT, &follow, &e);
    }
    // ROOT/<name>/SOCK for the longest grain name must fit sun_path (Lean's sockets_fit, any root)
    for (n, c, r, sock) in [
        ("memberRoot", exit::MEMBER_ROOT, &member, "nd.sock"),
        ("followRoot", exit::FOLLOW_ROOT, &follow, "follow.sock"),
    ] {
        let len = r.as_os_str().len() + GRAIN_NAME_MAX as usize + sock.len() + 2;
        if len > SOCK_PATH_MAX as usize {
            return root(
                n,
                c,
                r,
                &format!("socket path {len} bytes > {SOCK_PATH_MAX}"),
            );
        }
    }
    // the stdio child writes MEMBERS/<n> and the follower STATE/<n>/store: nested roots would put a
    // Store in a workspace (or a socket directory in either), so they must be disjoint trees
    let canon: Vec<PathBuf> = [&member, &members, &state, &follow]
        .iter()
        .filter_map(|p| p.canonicalize().ok())
        .collect();
    let refs: Vec<&Path> = canon.iter().map(PathBuf::as_path).collect();
    if refs.len() != 4 || !pairwise_apart(&refs) {
        let shown: Vec<String> = refs.iter().map(|p| p.display().to_string()).collect();
        return End(
            format!("rootsOverlap {}", shown.join(" ")),
            exit::ROOTS_OVERLAP,
        );
    }
    // the socket admits exactly PEER: its owner alone when PEER is this uid, else MEMBER's group
    let admit: Vec<OsString> = match peer == own {
        true => vec![],
        false => vec![
            "--group".into(),
            group.to_string().into(),
            "--peer".into(),
            peer.to_string().into(),
        ],
    };
    let hide = std::iter::once(&store)
        .chain(&hidden)
        .flat_map(|h| [OsString::from("--hide"), h.clone().into()])
        .collect();
    let conf = Conf {
        member,
        members: members.clone(),
        state: state.clone(),
        follow,
        pids,
        host_sock,
        supervise,
        nd,
        host,
        group,
        admit,
        hide,
    };

    // The decider reads the Store and runs itself; the member workspaces and the follower state
    // are hidden from it.
    let policy = Policy {
        read: vec![store.clone()],
        write: vec![],
        exec: vec![decider_path.clone()],
        hidden: [members, state].into_iter().chain(hidden).collect(),
        connect: vec![],
    };
    let dargs: Vec<&OsStr> = dargs.iter().map(OsString::as_os_str).collect();
    let spawned = command(&policy, decider_path.as_os_str(), &dargs)
        .map_err(|e| format!("{e:?}"))
        .and_then(|mut c| {
            c.stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .map_err(|e| e.to_string())
        });
    let mut child = match spawned {
        Ok(c) => c,
        Err(e) => return End(format!("deciderRefused {e}"), exit::DECIDER_REFUSED),
    };
    let pid_file = conf.pids.join("decider.pid");
    let (Some(din), Some(dout)) = (child.stdin.take(), child.stdout.take()) else {
        stop(&mut child, None);
        return End("deciderRefused pipes".into(), exit::DECIDER_REFUSED);
    };
    if let Err(e) = std::fs::write(&pid_file, format!("{}\n", child.id())) {
        stop(&mut child, None);
        return End(format!("pidFile {e}"), exit::PID_FILE);
    }
    let (mut served, mut stopping) = (BTreeMap::new(), Vec::new());
    let end = serve(&conf, &mut child, din, dout, &mut served, &mut stopping);
    for (n, p) in &mut served {
        p.stop(&conf, n, &mut stopping);
    }
    while !stopping.is_empty() {
        reap(&mut stopping, usize::MAX);
        std::thread::sleep(Duration::from_millis(10));
    }
    stop(&mut child, Some(&pid_file));
    end
}

/// Stop a child by its own handle, reap it, and remove its PID file.
fn stop(c: &mut Child, pid_file: Option<&Path>) {
    let _ = c.kill();
    let _ = c.wait();
    if let Some(p) = pid_file {
        let _ = std::fs::remove_file(p);
    }
}

/// nd-supervise children sent SIGTERM, each with its resident's name and its SIGKILL deadline. They
/// stay counted against the 2·RESIDENTS_MAX supervisors (law 4) until each is seen gone.
type Stopping = Vec<(String, Proc, Instant)>;

/// Reap the stopping children that ended. SIGKILL and reap each past its deadline, and the oldest
/// while more than `keep` are held (a birth's room); each named `memberStopForced`.
fn reap(stopping: &mut Stopping, keep: usize) {
    let mut over = stopping.len().saturating_sub(keep);
    stopping.retain_mut(|(name, p, until)| {
        if over > 0 || Instant::now() >= *until {
            over = over.saturating_sub(1);
            if let Ok(None) = p.child.try_wait() {
                say(&format!("memberStopForced {name}"));
            }
            let _ = (p.child.kill(), p.child.wait());
        }
        let gone = matches!(p.child.try_wait(), Ok(Some(_)));
        if gone {
            let _ = std::fs::remove_file(&p.pid_file);
        }
        !gone
    });
}

/// The decider's life: ask, serve exactly the names answered, until it ends.
fn serve(
    conf: &Conf,
    child: &mut Child,
    mut din: ChildStdin,
    mut dout: ChildStdout,
    served: &mut BTreeMap<String, Pair>,
    stopping: &mut Stopping,
) -> End {
    // names not provisioned, retried every tick and reported once until they are; names left
    // unbound after a crash loop until the answer changes; the answer they were for
    let mut reported: BTreeSet<String> = BTreeSet::new();
    let mut looped: BTreeSet<String> = BTreeSet::new();
    let mut last: Vec<Vec<u8>> = Vec::new();
    for _ in 0..LIFETIME {
        if let Ok(Some(st)) = child.try_wait() {
            return decider(residents::decider_end(st));
        }
        let Some(names) = residents::ask(&mut din, &mut dout, now_ms()) else {
            for _ in 0..ENDING_TICKS {
                if let Ok(Some(st)) = child.try_wait() {
                    return decider(residents::decider_end(st));
                }
                std::thread::sleep(TICK);
            }
            return End("deciderLost no residents answer".into(), exit::DECIDER_LOST);
        };
        if names.len() > RESIDENTS_MAX as usize {
            let line = format!("residentsPastBound {} > {RESIDENTS_MAX}", names.len());
            return End(line, decider_exit::RESIDENTS_PAST_BOUND);
        }
        let mut now: Vec<String> = Vec::with_capacity(names.len());
        for n in &names {
            match std::str::from_utf8(n)
                .ok()
                .filter(|r| grain_name_ok(r.as_bytes()))
            {
                Some(r) => now.push(r.to_owned()),
                None => return End(format!("memberRoot resident name {n:?}"), exit::MEMBER_ROOT),
            }
        }
        if names != last {
            looped.clear();
            last = names;
        }
        reported.retain(|n| now.contains(n));
        let gone: Vec<String> = served
            .keys()
            .filter(|k| !now.contains(k))
            .cloned()
            .collect();
        for g in gone {
            if let Some(mut pair) = served.remove(&g) {
                pair.stop(conf, &g, stopping);
                say(&format!("removed {g}"));
            }
        }
        reap(stopping, usize::MAX);
        for name in &now {
            if looped.contains(name) {
                continue;
            }
            // a rebirth waits for its stopping supervisors: never a second one on its socket path
            if stopping.iter().any(|s| s.0 == *name) {
                if reported.insert(name.clone()) {
                    say(&format!("memberStopping {name}"));
                }
                continue;
            }
            if !served.contains_key(name) {
                let room = (RESIDENTS_MAX as usize).saturating_sub(served.len() + 1);
                reap(stopping, 2 * room);
                match provision(conf, name) {
                    Ok(id) => {
                        reported.remove(name);
                        served.insert(name.clone(), Pair::new(id));
                    }
                    Err(why) => {
                        if reported.insert(name.clone()) {
                            say(&why);
                        }
                        continue;
                    }
                }
            }
            let Some(pair) = served.get_mut(name) else {
                continue;
            };
            if let Err(why) = pair.tend(conf, name) {
                pair.stop(conf, name, stopping);
                served.remove(name);
                say(&why);
                looped.insert(name.clone());
            }
        }
        std::thread::sleep(TICK);
    }
    End("deciderLost lifetime".into(), exit::DECIDER_LOST)
}

/// A resident's follower identity, from its `follow` file: `MEMBER GRANT`.
struct Id {
    member: OsString,
    grant: OsString,
}

/// `HEX HEX` and LF, each lowercase hexadecimal.
fn parse_id(text: &[u8]) -> Option<Id> {
    let line = text.strip_suffix(b"\n")?;
    let line = std::str::from_utf8(line).ok()?;
    let (m, g) = line.split_once(' ')?;
    let hex = |w: &str| {
        !w.is_empty()
            && w.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    };
    (hex(m) && hex(g)).then(|| Id {
        member: m.into(),
        grant: g.into(),
    })
}

/// Is resident `name` provisioned, and are its two socket directories made, checked and alone?
/// `Err` is the line naming why not.
fn provision(conf: &Conf, name: &str) -> Result<Id, String> {
    let missing = |why: String| format!("memberMissing {name} {why}");
    let st = conf.state.join(name);
    let file = st.join("follow");
    let text = custody::read_private(&file, 1..=FOLLOW_MAX)
        .map_err(|e| missing(format!("{} {e:?}", file.display())))?;
    let id = parse_id(&text).ok_or_else(|| missing(format!("{} malformed", file.display())))?;
    let store = st.join("store");
    if !std::fs::symlink_metadata(&store).is_ok_and(|m| m.is_dir()) {
        return Err(missing(format!("{} not a directory", store.display())));
    }
    let shared = |why: String| format!("socketDirShared {name} {why}");
    socket_dir(&conf.member.join(name), 0o2710, Some(conf.group), "nd.sock").map_err(shared)?;
    socket_dir(&conf.follow.join(name), 0o700, None, "follow.sock").map_err(shared)?;
    Ok(id)
}

/// One socket's directory, made at `mode` when absent: it must pass `check_shared_dir` with
/// `group` (or `check_private_dir`) and hold nothing but `sock`. A connect grant is a view of the
/// socket's whole directory (CLIENT-20), so anything else here would be in a connector's view.
fn socket_dir(d: &Path, mode: u32, group: Option<u32>, sock: &str) -> Result<(), String> {
    let at = |e: &dyn std::fmt::Debug| format!("{} {e:?}", d.display());
    match std::fs::symlink_metadata(d) {
        Err(e) if e.kind() == ErrorKind::NotFound => {
            std::fs::create_dir(d).map_err(|e| at(&e))?;
            std::fs::set_permissions(d, std::fs::Permissions::from_mode(mode))
                .map_err(|e| at(&e))?;
        }
        Err(e) => return Err(at(&e)),
        Ok(_) => {}
    }
    match group {
        Some(g) => match custody::check_shared_dir(d).map_err(|e| at(&e))? {
            got if got == g => {}
            got => return Err(format!("{} group {got}, not {g}", d.display())),
        },
        None => custody::check_private_dir(d).map_err(|e| at(&e))?,
    }
    for entry in std::fs::read_dir(d).map_err(|e| at(&e))? {
        let n = entry.map_err(|e| at(&e))?.file_name();
        if n != sock {
            return Err(format!("{} holds {n:?}", d.display()));
        }
    }
    Ok(())
}

/// One running nd-supervise and its PID file.
struct Proc {
    child: Child,
    pid_file: PathBuf,
}

/// One role of a resident (its follower, its stdio): the running child and its recent starts.
#[derive(Default)]
struct Slot {
    proc: Option<Proc>,
    starts: Vec<Instant>,
}

impl Slot {
    /// Reap the child if it ended.
    fn reap(&mut self, name: &str, role: &str) {
        if let Some(p) = &mut self.proc
            && let Ok(Some(st)) = p.child.try_wait()
        {
            say(&format!("{name} {role} ended {st}"));
            let _ = std::fs::remove_file(&p.pid_file);
            self.proc = None;
        }
    }

    /// Is a start due now? Past `STARTS_MAX` starts in `STARTS_WINDOW` it is a crash loop (`Err`);
    /// within `RESTART_AFTER` of the last start it waits for a later tick.
    fn due(&mut self, name: &str, role: &str) -> Result<bool, String> {
        if self.proc.is_some() {
            return Ok(false);
        }
        self.starts.retain(|t| t.elapsed() < STARTS_WINDOW);
        if self.starts.len() >= STARTS_MAX {
            return Err(format!("memberCrashLoop {name} {role}"));
        }
        Ok(self
            .starts
            .last()
            .is_none_or(|t| t.elapsed() >= RESTART_AFTER))
    }

    fn start(
        &mut self,
        conf: &Conf,
        name: &str,
        role: &str,
        args: &[&OsStr],
    ) -> Result<(), String> {
        self.proc = Some(spawn(conf, name, role, args)?);
        self.starts.push(Instant::now());
        Ok(())
    }
}

/// A resident's two children.
struct Pair {
    id: Id,
    follow: Slot,
    stdio: Slot,
}

impl Pair {
    fn new(id: Id) -> Pair {
        Pair {
            id,
            follow: Slot::default(),
            stdio: Slot::default(),
        }
    }

    /// Reap ended children and start what is due: the follower first, the stdio child only once
    /// the follow socket exists (its connect grant resolves the socket at launch). `Err` names
    /// the crash loop or the failed spawn.
    fn tend(&mut self, conf: &Conf, name: &str) -> Result<(), String> {
        self.follow.reap(name, "follow");
        self.stdio.reap(name, "stdio");
        let ws = conf.members.join(name);
        let fsock = conf.follow.join(name).join("follow.sock");
        let o = OsStr::new;
        if self.follow.due(name, "follow")? {
            let store = conf.state.join(name).join("store");
            let (f, h, st) = (fsock.as_os_str(), conf.host.as_os_str(), store.as_os_str());
            let mut a = vec![f, o("--write"), st, o("--exec"), h];
            a.extend(conf.hide.iter().map(OsString::as_os_str));
            a.extend([o("--hide"), conf.members.as_os_str()]);
            a.extend([o("--"), h, o("follow"), st, &self.id.member, &self.id.grant]);
            self.follow.start(conf, name, "follow", &a)?;
        }
        let bound = std::fs::symlink_metadata(&fsock).is_ok_and(|m| m.file_type().is_socket());
        if bound && self.stdio.due(name, "stdio")? {
            let msock = conf.member.join(name).join("nd.sock");
            let (f, n, hs, w) = (
                fsock.as_os_str(),
                conf.nd.as_os_str(),
                conf.host_sock.as_os_str(),
                ws.as_os_str(),
            );
            let mut a = vec![msock.as_os_str()];
            a.extend(conf.admit.iter().map(OsString::as_os_str));
            a.extend([
                o("--write"),
                w,
                o("--exec"),
                n,
                o("--connect"),
                hs,
                o("--connect"),
                f,
            ]);
            a.extend(conf.hide.iter().map(OsString::as_os_str));
            a.extend([o("--hide"), conf.state.as_os_str()]);
            a.extend([o("--"), n, o("--stdio"), w, f, hs]);
            self.stdio.start(conf, name, "stdio", &a)?;
        }
        Ok(())
    }

    /// Remove both sockets and both directories (a connect is then `ENOENT`), and SIGTERM both
    /// children, so each names every peer's close (CLIENT-30): `stopping` holds them, the tick goes on.
    fn stop(&mut self, conf: &Conf, name: &str, stopping: &mut Stopping) {
        let msock = conf.member.join(name).join("nd.sock");
        let fsock = conf.follow.join(name).join("follow.sock");
        for s in [msock, fsock] {
            let _ = std::fs::remove_file(&s);
            if let Some(d) = s.parent() {
                let _ = std::fs::remove_dir(d);
            }
        }
        for p in [self.stdio.proc.take(), self.follow.proc.take()]
            .into_iter()
            .flatten()
        {
            let _ = kill_process(Pid::from_child(&p.child), Signal::TERM);
            stopping.push((name.to_owned(), p, Instant::now() + GRACE));
        }
    }
}

/// Start one nd-supervise with `args` (null stdin and stdout, this stderr) and write its PID file
/// `PIDS/<name>.<role>.pid`.
fn spawn(conf: &Conf, name: &str, role: &str, args: &[&OsStr]) -> Result<Proc, String> {
    let mut child = Command::new(&conf.supervise)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .spawn()
        .map_err(|e| format!("memberSpawn {name} {role} {e}"))?;
    let pid_file = conf.pids.join(format!("{name}.{role}.pid"));
    if let Err(e) = std::fs::write(&pid_file, format!("{}\n", child.id())) {
        stop(&mut child, None);
        return Err(format!("memberSpawn {name} {role} pidFile {e}"));
    }
    say(&format!("{name} {role} {}", child.id()));
    Ok(Proc { child, pid_file })
}
