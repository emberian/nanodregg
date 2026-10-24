//! `grain-launch ROOT BROKER MEMBER LABEL PIDS CONTROLLER [ARG...]`
//!
//! Starts CONTROLLER (the Lean `hosting-controller`, or the test's `hosting-drive`) confined, with
//! read access to `ROOT/worlds/LABEL/store` only, and two pipes: it reads action frames from the
//! controller's stdout and writes report frames to its stdin. Each launch is one
//! `nanodregg_sandbox::command` over the frame's plan joined onto ROOT, its `broker` sockets onto
//! BROKER (keybroker's socket root, HOSTING-17) and its `member` sockets onto MEMBER (where nd serves
//! each resident's member socket, HOSTING-20/25). The three roots must be pairwise disjoint trees,
//! or the launcher ends `rootsOverlap` before it starts anything. A launch naming a path that is not
//! its own grain's (a program, read, write or exec path outside `worlds/LABEL/grains/<grain>/`, or a
//! socket of either root other than `<grain>/<name>`) ends the run `foreignPath` (a defect in the
//! controller: another grain's socket is another grain's identity). Every child's argv is its plan's
//! paths as joined, field for field (`plan_argv`, HOSTING-27). Each child gets a PID file
//! `PIDS/<grain>.pid`, removed when the child is reaped. A kill stops the child by its own handle
//! (the PID in that file). When the controller's pipe closes, every child is killed and reaped,
//! then the launcher exits with a name on stderr. While idle it reports its clock (`tick`, every
//! `TICK_MS`, HOSTING-38). It decides nothing: a frame it cannot decode, or
//! a frame that breaks a law, ends the run by name.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ExitCode, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::{Duration, Instant};

use nanodregg_launcher::generated::wire::{Action, LaunchFailure, Report};
use nanodregg_launcher::generated::{
    FrameError, LAYOUT_HIDDEN, TICK_MS, controller_exit, launch_exit, read_frame, write_frame,
};
use nanodregg_launcher::{
    PlanPaths, Roots, failure_of, foreign_path, grain_name_ok, plan_argv, policy, roots_disjoint,
    under,
};
use nanodregg_sandbox::{Policy, command};

/// How often children are polled for exit while no action arrives.
const TICK: Duration = Duration::from_millis(50);
/// Ticks a failed report waits for the controller's own end (2 s at `TICK`).
const REPORT_PIPE_WAIT_TICKS: u32 = 40;
/// Ticks in one process: centuries at `TICK`.
const LIFETIME_TICKS: u64 = 1 << 48;

/// How the launcher ended (stderr names; exit code 0 only when the controller ended cleanly).
enum End {
    Usage,
    RootsOverlap,
    ControllerRefused(String),
    /// the controller's exit code, or `None` for a signal
    ControllerEnded(Option<i32>),
    /// `wait` on the controller failed
    ControllerLost(String),
    /// the controller's process ended, not by a signal, with a code `ControllerExit` does not name
    /// (`controller_exit::ALL`): the mechanism's, not the controller's (HOSTING-23)
    ControllerMechanism(i32),
    /// a directory the World's layout hides is absent (`LAYOUT_HIDDEN`, HOSTING-24)
    LayoutMissing(PathBuf),
    /// a launch names a path that is not its grain's own (HOSTING-25)
    ForeignPath(String),
    Frame(String),
    BadAction(String),
    BadGrain,
    DuplicateLaunch,
    ReportPipe(String),
    Pid(String),
    Lifetime,
    /// the parent-death link could not be set (`die_with_parent`, CLIENT-38)
    ParentDeath(String),
}

impl End {
    fn describe(&self) -> String {
        match self {
            End::Usage => {
                "usage: grain-launch ROOT BROKER MEMBER LABEL PIDS CONTROLLER [ARG...]".into()
            }
            End::RootsOverlap => "rootsOverlap".into(),
            End::ControllerRefused(e) => format!("controllerRefused {e}"),
            End::ControllerEnded(Some(c)) => format!("controllerEnded {c}"),
            End::ControllerEnded(None) => "controllerSignaled".into(),
            End::ControllerLost(e) => format!("controllerLost {e}"),
            End::ControllerMechanism(c) => format!("controllerMechanism {c}"),
            End::LayoutMissing(p) => format!("layoutMissing {}", p.display()),
            End::ForeignPath(e) => format!("foreignPath {e}"),
            End::Frame(e) => format!("frame {e}"),
            End::BadAction(e) => format!("badAction {e}"),
            End::BadGrain => "badGrain".into(),
            End::DuplicateLaunch => "duplicateLaunch".into(),
            End::ReportPipe(e) => format!("reportPipe {e}"),
            End::Pid(e) => format!("pidFile {e}"),
            End::Lifetime => "lifetime".into(),
            End::ParentDeath(e) => format!("parentDeath {e}"),
        }
    }
}

/// One write per line (`nanodregg_launcher::say`): the controller and every child share this stderr.
fn say(line: &str) {
    nanodregg_launcher::say("grain-launch", line);
}

fn main() -> ExitCode {
    let end = run();
    say(&end.describe());
    use launch_exit as k;
    ExitCode::from(match end {
        End::Usage => k::USAGE,
        End::RootsOverlap => k::ROOTS_OVERLAP,
        End::ControllerRefused(_) => k::CONTROLLER_REFUSED,
        // the controller's own code, passed through: `ended` made every code Lean's `ControllerExit`
        // does not name ControllerMechanism, and a signal death ControllerEnded(None)
        End::ControllerEnded(Some(c)) => match u8::try_from(c) {
            Ok(c) if controller_exit::ALL.contains(&c) => c,
            _ => k::CONTROLLER_MECHANISM,
        },
        End::ControllerMechanism(_) => k::CONTROLLER_MECHANISM,
        End::LayoutMissing(_) => k::LAYOUT_MISSING,
        End::ForeignPath(_) => k::FOREIGN_PATH,
        End::ControllerEnded(None) => k::CONTROLLER_SIGNALED,
        End::ControllerLost(_) => k::CONTROLLER_LOST,
        End::Frame(_) => k::FRAME,
        End::BadAction(_) => k::BAD_ACTION,
        End::BadGrain => k::BAD_GRAIN,
        End::DuplicateLaunch => k::DUPLICATE_LAUNCH,
        End::ReportPipe(_) => k::REPORT_PIPE,
        End::Pid(_) => k::PID_FILE,
        End::Lifetime => k::LIFETIME,
        End::ParentDeath(_) => k::PARENT_DEATH,
    })
}

enum Msg {
    Action(Action),
    End(End),
}

/// The controller's frames, decoded on their own thread (a blocking read never stalls reaping).
fn reader(mut out: std::process::ChildStdout, tx: mpsc::Sender<Msg>) {
    loop {
        let msg = match read_frame(&mut out) {
            Ok(payload) => match Action::decode(&payload) {
                Ok(a) => Msg::Action(a),
                Err(e) => Msg::End(End::BadAction(format!("{e:?}"))),
            },
            Err(FrameError::End) => Msg::End(End::ControllerEnded(None)),
            Err(e) => Msg::End(End::Frame(format!("{e:?}"))),
        };
        let last = matches!(msg, Msg::End(_));
        if tx.send(msg).is_err() || last {
            return;
        }
    }
}

struct Grain {
    child: Child,
    pid_file: PathBuf,
}

struct Launcher {
    root: PathBuf,
    broker: PathBuf,
    member: PathBuf,
    /// the Store label (`worlds/LABEL`), the root of every grain path a frame may name
    label: Vec<u8>,
    pids: PathBuf,
    start: Instant,
    to_controller: ChildStdin,
    children: BTreeMap<Vec<u8>, Grain>,
}

impl Launcher {
    fn now(&self) -> u64 {
        u64::try_from(self.start.elapsed().as_millis()).unwrap_or(u64::MAX)
    }

    fn report(&mut self, r: Report) -> Result<(), End> {
        let bytes = r.encode().map_err(|e| End::ReportPipe(format!("{e:?}")))?;
        write_frame(&mut self.to_controller, &bytes)
            .and_then(|()| self.to_controller.flush().map_err(FrameError::Io))
            .map_err(|e| End::ReportPipe(format!("{e:?}")))
    }

    /// A launch refused: the Lean name, then what was refused (the path a confine check missed,
    /// the spawn's error), so a row can tell one missing socket from another.
    fn failed(&mut self, grain: Vec<u8>, why: LaunchFailure, what: &str) -> Result<(), End> {
        say(&format!(
            "{} failed {} {what}",
            String::from_utf8_lossy(&grain),
            why.name()
        ));
        let at_ms = self.now();
        self.report(Report::Failed {
            grain,
            launch_failure: why,
            at_ms,
        })
    }

    fn launch(
        &mut self,
        grain: Vec<u8>,
        program: &[u8],
        policy: &Policy,
        argv: &[OsString],
    ) -> Result<(), End> {
        if !grain_name_ok(&grain) {
            return Err(End::BadGrain);
        }
        if self.children.contains_key(&grain) {
            return Err(End::DuplicateLaunch);
        }
        // The plan's writable directories exist before the sandbox checks its paths.
        for w in &policy.write {
            if let Err(e) = std::fs::create_dir_all(w) {
                let what = format!("{}: {e}", w.display());
                return self.failed(grain, LaunchFailure::PathMissing, &what);
            }
        }
        let program = under(&self.root, program);
        // Each socket the plan lets this grain connect to, as joined onto its root (BROKER, then
        // MEMBER): the resident row reads its connect paths here, never computes them (PROTOCOL-7's R1).
        for c in &policy.connect {
            say(&format!(
                "{} connect {}",
                String::from_utf8_lossy(&grain),
                c.display()
            ));
        }
        let argv: Vec<&std::ffi::OsStr> = argv.iter().map(OsString::as_os_str).collect();
        let mut cmd = match command(policy, program.as_os_str(), &argv) {
            Ok(c) => c,
            Err(e) => return self.failed(grain, failure_of(&e), &e.to_string()),
        };
        let child = match cmd.stdin(Stdio::null()).spawn() {
            Ok(c) => c,
            Err(e) => return self.failed(grain, LaunchFailure::SpawnFailed, &e.to_string()),
        };
        let name = String::from_utf8_lossy(&grain).into_owned();
        let pid_file = self.pids.join(format!("{name}.pid"));
        std::fs::write(&pid_file, format!("{}\n", child.id()))
            .map_err(|e| End::Pid(e.to_string()))?;
        say(&format!("{name} started pid {}", child.id()));
        self.children
            .insert(grain.clone(), Grain { child, pid_file });
        let at_ms = self.now();
        self.report(Report::Started { grain, at_ms })
    }

    /// Stop a grain's child by its own handle; its exit is reported when it is reaped. A kill for
    /// a grain with no child is the controller's view lagging an exit already on the pipe.
    fn kill(&mut self, grain: &[u8]) {
        if let Some(g) = self.children.get_mut(grain) {
            let _ = g.child.kill();
        }
    }

    /// Reap every child that has exited, reporting each.
    fn reap(&mut self) -> Result<(), End> {
        let done: Vec<(Vec<u8>, u32)> = self
            .children
            .iter_mut()
            .filter_map(|(g, c)| match c.child.try_wait() {
                Ok(Some(st)) => Some((g.clone(), st.into_raw() as u32)),
                _ => None,
            })
            .collect();
        for (grain, status) in done {
            if let Some(g) = self.children.remove(&grain) {
                let _ = std::fs::remove_file(&g.pid_file);
            }
            say(&format!(
                "{} exited {status}",
                String::from_utf8_lossy(&grain)
            ));
            let at_ms = self.now();
            self.report(Report::Exited {
                grain,
                status,
                at_ms,
            })?;
        }
        Ok(())
    }

    /// Kill and reap every child (the controller is gone).
    fn stop_all(&mut self) {
        for (_, mut g) in std::mem::take(&mut self.children) {
            let _ = g.child.kill();
            let _ = g.child.wait();
            let _ = std::fs::remove_file(&g.pid_file);
        }
    }

    fn act(&mut self, a: Action) -> Result<(), End> {
        match a {
            Action::Launch {
                grain,
                program,
                read,
                write,
                exec,
                broker,
                member,
                hidden,
            } => {
                let paths = PlanPaths {
                    read: &read,
                    write: &write,
                    exec: &exec,
                    broker: &broker,
                    member: &member,
                    hidden: &hidden,
                };
                if let Some(e) = foreign_path(&self.label, &grain, &program, &paths) {
                    return Err(End::ForeignPath(format!(
                        "{} {}",
                        String::from_utf8_lossy(&grain),
                        String::from_utf8_lossy(e)
                    )));
                }
                let roots = Roots {
                    root: &self.root,
                    broker: &self.broker,
                    member: &self.member,
                };
                let p = policy(&roots, &paths);
                let argv = plan_argv(&roots, &program, &paths);
                self.launch(grain, &program, &p, &argv)
            }
            Action::Kill { grain } => {
                self.kill(&grain);
                Ok(())
            }
            Action::Refuse {
                grain,
                grain_refusal,
            } => {
                say(&format!(
                    "{} refused {}",
                    String::from_utf8_lossy(&grain),
                    grain_refusal.name()
                ));
                Ok(())
            }
        }
    }

    /// While idle, the clock: a `tick` every `TICK_MS` (Lean's `Hosting.tickMs`), so the
    /// controller's crash-loop window passes without a Turn (HOSTING-38). The launcher decides
    /// nothing by it.
    fn tick(&mut self, last: &mut u64) -> Result<(), End> {
        let at_ms = self.now();
        if at_ms >= last.saturating_add(u64::from(TICK_MS)) {
            *last = at_ms;
            self.report(Report::Tick { at_ms })?;
        }
        Ok(())
    }

    fn serve(&mut self, rx: &Receiver<Msg>) -> End {
        let mut last_tick = 0;
        for _ in 0..LIFETIME_TICKS {
            match rx.recv_timeout(TICK) {
                Ok(Msg::Action(a)) => {
                    if let Err(e) = self.act(a) {
                        return e;
                    }
                }
                Ok(Msg::End(e)) => return e,
                Err(RecvTimeoutError::Timeout) => {}
                Err(RecvTimeoutError::Disconnected) => return End::ControllerEnded(None),
            }
            if let Err(e) = self.reap() {
                return e;
            }
            if let Err(e) = self.tick(&mut last_tick) {
                return e;
            }
        }
        End::Lifetime
    }
}

/// How the controller's process ended: a signal (`nanodregg_sandbox::killed_by_signal`, the
/// platform's fact: under bwrap a status of 128 or more, the OOM killer); its own code if Lean's
/// `ControllerExit` names it; otherwise the mechanism's.
fn ended(status: std::process::ExitStatus) -> End {
    match status.code() {
        _ if nanodregg_sandbox::killed_by_signal(status) => End::ControllerEnded(None),
        Some(c) if !u8::try_from(c).is_ok_and(|c| controller_exit::ALL.contains(&c)) => {
            End::ControllerMechanism(c)
        }
        c => End::ControllerEnded(c),
    }
}

fn run() -> End {
    // First: a grain-launch whose parent dies (a killed test, never systemd) does not outlive it.
    if let Err(e) = nanodregg_sandbox::die_with_parent() {
        return End::ParentDeath(e.to_string());
    }
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let [root, broker, member, label, pids, controller, rest @ ..] = args.as_slice() else {
        return End::Usage;
    };
    let (Ok(root), Ok(broker), Ok(member)) = (
        PathBuf::from(root).canonicalize(),
        PathBuf::from(broker).canonicalize(),
        PathBuf::from(member).canonicalize(),
    ) else {
        return End::Usage;
    };
    let roots = Roots {
        root: &root,
        broker: &broker,
        member: &member,
    };
    if !roots_disjoint(&roots) {
        return End::RootsOverlap;
    }
    // every directory Lean's plans hide must exist, or every launch would be refused pathMissing
    for name in LAYOUT_HIDDEN {
        let d = root.join("worlds").join(label).join(name);
        if !d.is_dir() {
            return End::LayoutMissing(d);
        }
    }
    let store = root.join("worlds").join(label).join("store");
    let ctl = Policy {
        read: vec![store],
        exec: vec![PathBuf::from(controller)],
        ..Policy::default()
    };
    let rest: Vec<&std::ffi::OsStr> = rest.iter().map(|a| a.as_os_str()).collect();
    let mut cmd = match command(&ctl, controller, &rest) {
        Ok(c) => c,
        Err(e) => return End::ControllerRefused(e.to_string()),
    };
    let mut ctl_child = match cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn() {
        Ok(c) => c,
        Err(e) => return End::ControllerRefused(e.to_string()),
    };
    let (Some(to_controller), Some(from_controller)) =
        (ctl_child.stdin.take(), ctl_child.stdout.take())
    else {
        let _ = ctl_child.kill();
        return End::ControllerRefused("no pipes".into());
    };
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || reader(from_controller, tx));
    let mut l = Launcher {
        root,
        broker,
        member,
        label: label.as_bytes().to_vec(),
        pids: PathBuf::from(pids),
        start: Instant::now(),
        to_controller,
        children: BTreeMap::new(),
    };
    let end = l.serve(&rx);
    l.stop_all();
    drop(l);
    match end {
        End::ControllerEnded(None) => match ctl_child.wait() {
            Ok(s) => ended(s),
            Err(e) => End::ControllerLost(e.to_string()),
        },
        // A report the controller could not take: it is most likely gone, and then ITS end names
        // the run (a fatal Store refusal must not surface as a restartable reportPipe,
        // VACUITY-READER-H4). Wait for it a bounded while; only a controller still alive after the
        // bound makes this reportPipe.
        End::ReportPipe(why) => {
            for _ in 0..REPORT_PIPE_WAIT_TICKS {
                match ctl_child.try_wait() {
                    Ok(Some(s)) => return ended(s),
                    Ok(None) => std::thread::sleep(TICK),
                    Err(e) => return End::ControllerLost(e.to_string()),
                }
            }
            let _ = ctl_child.kill();
            let _ = ctl_child.wait();
            End::ReportPipe(why)
        }
        other => {
            let _ = ctl_child.kill();
            let _ = ctl_child.wait();
            other
        }
    }
}
