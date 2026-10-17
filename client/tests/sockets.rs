//! The sockets' deadline (PROTOCOL-20): a peer that never replies is a `timeout` by name within
//! the bound, never a hang. The bound is a parameter; nd passes `table::REPLY` (replyMsMax).
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::io;
use std::os::unix::net::UnixListener;
use std::sync::mpsc;
use std::time::Duration;

use nanodregg_client::run::Host;
use nanodregg_client::sockets::HostSocket;

#[test]
fn a_silent_peer_is_a_timeout_by_name() {
    let path = std::env::temp_dir().join(format!("nd-sock-{}.sock", std::process::id()));
    let _ = std::fs::remove_file(&path);
    let listener = UnixListener::bind(&path).unwrap();
    // Accepts and never answers; it lives as long as this test.
    let silent = std::thread::spawn(move || listener.accept().map(|(s, _)| s));
    let mut host = HostSocket::connect(&path, Duration::from_millis(200)).unwrap();
    // The exchange runs on its own thread so a missing deadline fails this test by name, not
    // by hanging it.
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(host.exchange(1, b"CALL").map(|_| ()));
    });
    let e = rx
        .recv_timeout(Duration::from_secs(5))
        .unwrap_or_else(|_| Err(io::Error::other("HANG: no reply and no timeout in 5 s")))
        .unwrap_err();
    assert_eq!(e.kind(), io::ErrorKind::TimedOut, "{e}");
    assert!(e.to_string().contains("timeout"));
    let _ = silent.join();
    let _ = std::fs::remove_file(&path);
}
