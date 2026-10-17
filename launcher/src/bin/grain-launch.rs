//! `grain-launch ROOT LABEL PIDS CONTROLLER [ARG...]`
//!
//! Starts CONTROLLER (the Lean `hosting-controller`, or the test's `hosting-drive`) confined, with
//! read access to `ROOT/worlds/LABEL/store` only, and two pipes: it reads action frames from the
//! controller's stdout and writes report frames to its stdin. Each launch is one
//! `nanodregg_sandbox::command` over the frame's plan joined onto ROOT; each child gets a PID file
//! `PIDS/<grain>.pid`, removed when the child is reaped. A kill stops the child by its own handle
//! (the PID in that file). When the controller's pipe closes, every child is killed and reaped,
//! then the launcher exits with a name on stderr. It decides nothing: a frame it cannot decode, or
//! a frame that breaks a law, ends the run by name.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::Write;
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ExitCode, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::{Duration, Instant};

use nanodregg_launcher::generated::wire::{Action, LaunchFailure, Report};
use nanodregg_launcher::generated::{FrameError, read_frame, write_frame};
use nanodregg_launcher::{failure_of, grain_name_ok, policy, under};
use nanodregg_sandbox::{Policy, command};

/// How often children are polled for exit while no action arrives.
const TICK: Duration = Duration::from_millis(50);
/// Ticks in one process: centuries at `TICK`.
const LIFETIME_TICKS: u64 = 1 << 48;

/// How the launcher ended (stderr names; exit code 0 only when the controller ended cleanly).
enum End {
    Usage,
    ControllerRefused(String),
    ControllerEnded(Option<i32>),
    Frame(String),
    BadAction(String),
    BadGrain,
    DuplicateLaunch,
    ReportPipe(String),
    Pid(String),
    Lifetime,
}

impl End {
    fn describe(&self) -> String {
        match self {
            End::Usage => "usage: grain-launch ROOT LABEL PIDS CONTROLLER [ARG...]".into(),
            End::ControllerRefused(e) => format!("controllerRefused {e}"),
            End::ControllerEnded(c) => format!("controllerEnded {c:?}"),
            End::Frame(e) => format!("frame {e}"),
            End::BadAction(e) => format!("badAction {e}"),
            End::BadGrain => "badGrain".into(),
            End::DuplicateLaunch => "duplicateLaunch".into(),
            End::ReportPipe(e) => format!("reportPipe {e}"),
            End::Pid(e) => format!("pidFile {e}"),
            End::Lifetime => "lifetime".into(),
        }
    }
}

fn main() -> ExitCode {
    let end = run();
    eprintln!("grain-launch: {}", end.describe());
    match end {
        End::ControllerEnded(Some(0)) => ExitCode::SUCCESS,
        End::Usage => ExitCode::from(2),
        _ => ExitCode::from(1),
    }
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

    fn failed(&mut self, grain: Vec<u8>, why: LaunchFailure) -> Result<(), End> {
        eprintln!(
            "grain-launch: {} failed {}",
            String::from_utf8_lossy(&grain),
            why.name()
        );
        let at_ms = self.now();
        self.report(Report::Failed {
            grain,
            launch_failure: why,
            at_ms,
        })
    }

    fn launch(&mut self, grain: Vec<u8>, program: &[u8], policy: &Policy) -> Result<(), End> {
        if !grain_name_ok(&grain) {
            return Err(End::BadGrain);
        }
        if self.children.contains_key(&grain) {
            return Err(End::DuplicateLaunch);
        }
        // The plan's writable directories exist before the sandbox checks its paths.
        for w in &policy.write {
            if std::fs::create_dir_all(w).is_err() {
                return self.failed(grain, LaunchFailure::PathMissing);
            }
        }
        let program = under(&self.root, program);
        let mut cmd = match command(policy, program.as_os_str(), &[]) {
            Ok(c) => c,
            Err(e) => return self.failed(grain, failure_of(&e)),
        };
        let child = match cmd.stdin(Stdio::null()).spawn() {
            Ok(c) => c,
            Err(_) => return self.failed(grain, LaunchFailure::SpawnFailed),
        };
        let name = String::from_utf8_lossy(&grain).into_owned();
        let pid_file = self.pids.join(format!("{name}.pid"));
        std::fs::write(&pid_file, format!("{}\n", child.id()))
            .map_err(|e| End::Pid(e.to_string()))?;
        eprintln!("grain-launch: {name} started pid {}", child.id());
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
            eprintln!(
                "grain-launch: {} exited {status}",
                String::from_utf8_lossy(&grain)
            );
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
                hidden,
            } => {
                let p = policy(&self.root, &read, &write, &exec, &hidden);
                self.launch(grain, &program, &p)
            }
            Action::Kill { grain } => {
                self.kill(&grain);
                Ok(())
            }
            Action::Refuse {
                grain,
                grain_refusal,
            } => {
                eprintln!(
                    "grain-launch: {} refused {}",
                    String::from_utf8_lossy(&grain),
                    grain_refusal.name()
                );
                Ok(())
            }
        }
    }

    fn serve(&mut self, rx: &Receiver<Msg>) -> End {
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
        }
        End::Lifetime
    }
}

fn run() -> End {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let [root, label, pids, controller, rest @ ..] = args.as_slice() else {
        return End::Usage;
    };
    let root = PathBuf::from(root);
    if !root.is_absolute() {
        return End::Usage;
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
        pids: PathBuf::from(pids),
        start: Instant::now(),
        to_controller,
        children: BTreeMap::new(),
    };
    let end = l.serve(&rx);
    l.stop_all();
    drop(l);
    match end {
        End::ControllerEnded(None) => {
            End::ControllerEnded(ctl_child.wait().ok().and_then(|s| s.code()))
        }
        other => {
            let _ = ctl_child.kill();
            let _ = ctl_child.wait();
            other
        }
    }
}
