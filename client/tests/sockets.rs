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

/// CLIENT-39 (A18): the bound is per REPLY, not per read. A Host that answers a frame header and then
/// one byte every 100 ms (a 1000-byte body: 100 s) is a `timeout` by name within the 1 s bound. Each
/// byte arrives well inside the bound, so a per-read timeout (the old `SO_RCVTIMEO`) never fires and
/// the exchange runs the full 100 s: this test's 5 s backstop reads that as a HANG.
#[test]
fn a_trickling_peer_is_a_timeout_within_one_reply_bound() {
    use nanodregg_client::{frame, table::LIMITS};
    use std::io::Write;
    let path = std::env::temp_dir().join(format!("nd-trickle-{}.sock", std::process::id()));
    let _ = std::fs::remove_file(&path);
    let listener = UnixListener::bind(&path).unwrap();
    std::thread::spawn(move || {
        let Ok((mut s, _)) = listener.accept() else {
            return;
        };
        if frame::read(&mut s, LIMITS).is_err() {
            return;
        }
        let _ = s.write_all(&1000u32.to_le_bytes());
        for _ in 0..1000 {
            std::thread::sleep(Duration::from_millis(100));
            if s.write_all(&[0]).is_err() {
                return;
            }
        }
    });
    let mut host = HostSocket::connect(&path, Duration::from_secs(1)).unwrap();
    let (tx, rx) = mpsc::channel();
    let started = std::time::Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(host.exchange(1, b"CALL").map(|_| ()));
    });
    let e = rx
        .recv_timeout(Duration::from_secs(5))
        .unwrap_or_else(|_| Err(io::Error::other("HANG: a trickling reply past 5 s")))
        .unwrap_err();
    assert_eq!(e.kind(), io::ErrorKind::TimedOut, "{e}");
    assert!(
        started.elapsed() < Duration::from_secs(3),
        "{:?}",
        started.elapsed()
    );
    let _ = std::fs::remove_file(&path);
}
