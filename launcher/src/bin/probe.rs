//! The isolation test's grain (`launcher/tests/isolation.rs`). Run as `<grain>/pkg/probe`, with no
//! arguments and an empty environment (the sandbox clears both), it reads `probe.targets` beside
//! itself — lines `NAME read|write PATH` — tries each, and writes one line per target,
//! `NAME ok` or `NAME denied <errno name>`, to `<grain>/vol/probe.out`. It finds itself by argv[0]
//! (no /proc under bwrap). Exit 3 when it cannot write its own volume.

use std::io::{ErrorKind, Read};
use std::path::PathBuf;
use std::process::ExitCode;

fn attempt(op: &str, path: &str) -> String {
    let r = match op {
        "read" => std::fs::File::open(path).and_then(|mut f| {
            let mut b = Vec::new();
            f.read_to_end(&mut b).map(|_| ())
        }),
        "write" => std::fs::write(path, b"probe"),
        _ => return "bad-op".into(),
    };
    match r {
        Ok(()) => "ok".into(),
        Err(e) => {
            let name = match e.kind() {
                ErrorKind::PermissionDenied => "EACCES/EPERM".to_string(),
                ErrorKind::NotFound => "ENOENT".to_string(),
                ErrorKind::ReadOnlyFilesystem => "EROFS".to_string(),
                k => format!("{k:?}"),
            };
            format!("denied {name}")
        }
    }
}

fn main() -> ExitCode {
    let Some(me) = std::env::args_os().next().map(PathBuf::from) else {
        return ExitCode::from(2);
    };
    let Some(pkg) = me.parent() else {
        return ExitCode::from(2);
    };
    let Some(grain) = pkg.parent() else {
        return ExitCode::from(2);
    };
    let Ok(targets) = std::fs::read_to_string(pkg.join("probe.targets")) else {
        return ExitCode::from(2);
    };
    let mut out = String::new();
    for line in targets.lines() {
        let mut f = line.splitn(3, ' ');
        if let (Some(name), Some(op), Some(path)) = (f.next(), f.next(), f.next()) {
            out += &format!("{name} {}\n", attempt(op, path));
        }
    }
    match std::fs::write(grain.join("vol").join("probe.out"), out) {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::from(3),
    }
}
