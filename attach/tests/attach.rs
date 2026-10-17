//! `nd-attach` (CLIENT-12 B) with two pipes standing in for sshd: the friend's supervisor (the
//! client library's `mux::serve`, in this process) runs nd-attach as its child; nd-attach connects
//! to the box's socket, served by a second `mux::serve` in front of the REAL Lean `host serve`.
//! Lean's refusal crosses the bridge by name; a session past `PEER_CONNECTIONS_MAX` is answered
//! `closed full`; a connection that ends frees its slot by the hang-up (PROTOCOL-23), so the next
//! connection is served; a box that is gone is `closed unreachable`.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::Duration;

use nanodregg_client::frame::{self, Frame, FrameError, Limits};
use nanodregg_client::generated::{self as g, CloseReason, status};
use nanodregg_client::{mux, table};

/// A process this test started, stopped by its own handle even when an assertion fails.
struct Held(Child);
impl Drop for Held {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// The lake-built Lean `host` (`$ND_HOST_EXE`, else this tree's); missing, the test FAILS by name.
fn lean_host() -> PathBuf {
    let p = std::env::var_os("ND_HOST_EXE").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("../.lake/build/bin/host"),
        PathBuf::from,
    );
    assert!(
        p.is_file(),
        "plant: no lake-built host at {} (run `lake build host`)",
        p.display()
    );
    p
}

fn ask(s: &mut UnixStream, l: Limits, op: u8, p: &[u8]) -> Result<Frame, FrameError> {
    frame::write(s, l, op, p)?;
    frame::read(s, l)
}

fn assert_closed(s: &mut UnixStream, l: Limits, why: CloseReason) {
    s.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    let f = frame::read(s, l).unwrap();
    assert_eq!(
        (f.op, f.payload.as_slice()),
        (status::CLOSED, why.name().as_bytes()),
        "closed {why:?}"
    );
}

#[test]
fn nd_attach_bridges_to_the_real_host_caps_a_session_and_frees_a_slot_on_hang_up() {
    let t = table::LIMITS;
    let root = std::env::temp_dir().join(format!("nd-attach-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    let store = root.join("store");
    let made = Command::new(lean_host())
        .arg("genesis")
        .arg(&store)
        .arg("w")
        .stdout(Stdio::null())
        .status()
        .unwrap();
    assert!(made.success(), "host genesis");
    let mut host = Held(
        Command::new(lean_host())
            .arg("serve")
            .arg(&store)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let (hin, hout) = (host.0.stdin.take().unwrap(), host.0.stdout.take().unwrap());
    let box_sock = root.join("box.sock");
    let box_l = UnixListener::bind(&box_sock).unwrap();
    thread::spawn(move || mux::serve(box_l, hin, hout, table::MUX));
    let mut attach = Held(
        Command::new(env!("CARGO_BIN_EXE_nd-attach"))
            .arg(&box_sock)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let (ain, aout) = (
        attach.0.stdin.take().unwrap(),
        attach.0.stdout.take().unwrap(),
    );
    let friend_sock = root.join("friend.sock");
    let friend_l = UnixListener::bind(&friend_sock).unwrap();
    thread::spawn(move || mux::serve(friend_l, ain, aout, table::MUX));
    let open = |label: &str| {
        let mut c = UnixStream::connect(&friend_sock).unwrap();
        c.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
        let r = ask(&mut c, t, g::host_op::LOOKUP, b"not a call").unwrap();
        assert_eq!(
            (r.op, r.payload.as_slice()),
            (status::REFUSED, &b"undecodableCall"[..]),
            "{label}: Lean's refusal, by name, over the bridge"
        );
        c
    };
    let cap = g::PEER_CONNECTIONS_MAX as usize;
    let mut held: Vec<UnixStream> = (0..cap).map(|i| open(&format!("conn {i}"))).collect();
    let mut over = UnixStream::connect(&friend_sock).unwrap();
    frame::write(&mut over, t, g::host_op::LOOKUP, b"x").unwrap();
    assert_closed(&mut over, t, CloseReason::Full);
    // One connection of the session ends: the friend's supervisor hangs it up, nd-attach frees
    // its slot, and the next connection is served (ROOT's plant: freed within one frame).
    drop(held.pop());
    thread::sleep(Duration::from_millis(300));
    held.push(open("the connection after a hang-up"));
    drop(held);
    drop(host); // the box's Store process is gone
    thread::sleep(Duration::from_millis(300));
    let _ = std::fs::remove_file(&box_sock);
    let mut late = UnixStream::connect(&friend_sock).unwrap();
    frame::write(&mut late, t, g::host_op::LOOKUP, b"x").unwrap();
    assert_closed(&mut late, t, CloseReason::Unreachable);
    let _ = std::fs::remove_dir_all(&root);
}
