//! Mux plants: replies reach the connection that asked, by id, with nothing parsed; a reply for a
//! closed connection is dropped; the child closing its stdout closes every connection and ends
//! `serve`. And every way the mux ends a connection, each NAMED to the peer
//! (`status::CLOSED ‖ CloseReason::name()`, PROTOCOL-22): one connection past the bound is `full`;
//! a peer that stops reading is `replyBacklog` and never starves another connection; a silent
//! connection is `idle`, but not one waiting on a slow reply; a trickled header is `frameStalled`;
//! a request the child never answers is `replyTimeout`; a `closed` from the child ends the
//! connection.
#![allow(clippy::unwrap_used, clippy::panic)] // a plant that cannot set up is a failed plant
use std::io::{self, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use nanodregg_client::frame::{self, Frame, FrameError, Limits};
use nanodregg_client::generated::{self as g, CloseReason, status};
use nanodregg_client::mux::{self, MuxEnd, MuxLimits};

const L: Limits = Limits {
    frame_bytes_max: 64,
}; // test bound, not a protocol constant

fn socket(name: &str) -> (UnixListener, PathBuf) {
    let p = std::env::temp_dir().join(format!("nd-mux-{}-{name}.sock", std::process::id()));
    let _ = std::fs::remove_file(&p);
    (UnixListener::bind(&p).unwrap(), p)
}

/// Test limits: the given connection bound and idle window; frame and write deadlines 300 ms, the
/// reply backstop 2 s unless a test shortens it.
fn limits(connections_max: u32, idle_ms: u64) -> MuxLimits {
    MuxLimits {
        frame: L,
        connections_max,
        idle: Duration::from_millis(idle_ms),
        frame_deadline: Duration::from_millis(300),
        reply: Duration::from_secs(2),
        reply_write: Duration::from_millis(300),
    }
}

/// A child that answers every request with status = op + 1 and the payload reversed (padded to
/// `pad` bytes), after `delay`, until it has answered `n`; then it closes its stdout.
fn child_with(n: usize, delay: Duration, pad: usize, max: u32) -> (io::PipeWriter, io::PipeReader) {
    child_hearing(n, delay, pad, max, None)
}

/// `child_with`, and every hang-up it is sent (PROTOCOL-23) goes to `hangs` and is acknowledged
/// `closed ‖ name` (the mux drops the ack: the connection is gone); hang-ups do not count in `n`.
fn child_hearing(
    n: usize,
    delay: Duration,
    pad: usize,
    max: u32,
    hangs: Option<mpsc::Sender<(u32, Vec<u8>)>>,
) -> (io::PipeWriter, io::PipeReader) {
    let (mut req_r, req_w) = io::pipe().unwrap();
    let (rep_r, mut rep_w) = io::pipe().unwrap();
    thread::spawn(move || {
        let mut answered = 0;
        while answered < n {
            let Ok(body) = frame::read_body(&mut req_r, max + 4) else {
                return;
            };
            if body[4] == g::HANGUP {
                let conn = u32::from_le_bytes([body[0], body[1], body[2], body[3]]);
                if let Some(tx) = &hangs {
                    let _ = tx.send((conn, body[5..].to_vec()));
                }
                let _ = frame::write_body(
                    &mut rep_w,
                    max + 4,
                    &[&body[..4], &[status::CLOSED], &body[5..]],
                );
                continue;
            }
            answered += 1;
            thread::sleep(delay);
            let (conn, rest) = body.split_at(4);
            let mut payload = rest[1..].to_vec();
            payload.reverse();
            payload.resize(payload.len().max(pad), 7);
            if frame::write_body(&mut rep_w, max + 4, &[conn, &[rest[0] + 1], &payload]).is_err() {
                return;
            }
        }
    });
    (req_w, rep_r)
}

fn echo_child(n: usize) -> (io::PipeWriter, io::PipeReader) {
    child_with(n, Duration::ZERO, 0, L.frame_bytes_max)
}

/// The next frame must be the named close `why`, then end of stream.
fn assert_closed(s: &mut UnixStream, limits: Limits, why: CloseReason) {
    s.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let f = frame::read(s, limits).unwrap();
    assert_eq!(
        (f.op, f.payload.as_slice()),
        (status::CLOSED, why.name().as_bytes()),
        "closed {why:?}"
    );
    assert!(matches!(frame::read(s, limits), Err(FrameError::Closed)));
}

fn ask(s: &mut UnixStream, limits: Limits, op: u8, p: &[u8]) -> Result<Frame, FrameError> {
    frame::write(s, limits, op, p)?;
    frame::read(s, limits)
}

#[test]
fn replies_route_by_connection_and_child_close_ends_serve() {
    let (listener, path) = socket("route");
    let (child_in, child_out) = echo_child(2);
    let server = thread::spawn(move || mux::serve(listener, child_in, child_out, limits(4, 5000)));
    let mut a = UnixStream::connect(&path).unwrap();
    a.set_read_timeout(Some(Duration::from_secs(5))).unwrap(); // before: macOS refuses it after shutdown
    let mut b = UnixStream::connect(&path).unwrap();
    let ra = ask(&mut a, L, 7, b"abc").unwrap();
    let rb = ask(&mut b, L, 9, b"xy").unwrap();
    assert_eq!((ra.op, ra.payload), (8, b"cba".to_vec()));
    assert_eq!((rb.op, rb.payload), (10, b"yx".to_vec()));
    // The child has answered its two and closed: serve ends and every connection is told
    // `unreachable` by name (law 7), never a bare EOF.
    assert!(matches!(server.join().unwrap(), MuxEnd::ChildClosed));
    for s in [&mut a, &mut b] {
        let f = frame::read(s, L).unwrap();
        assert_eq!((f.op, f.payload), (status::CLOSED, b"unreachable".to_vec()));
        assert!(matches!(frame::read(s, L), Err(FrameError::Closed)));
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn past_the_connection_bound_is_closed_full() {
    let (listener, path) = socket("bound");
    let (child_in, child_out) = echo_child(3);
    thread::spawn(move || mux::serve(listener, child_in, child_out, limits(1, 5000)));
    let mut a = UnixStream::connect(&path).unwrap();
    assert_eq!(ask(&mut a, L, 1, b"q").unwrap().op, 2); // a is registered before b connects
    let mut b = UnixStream::connect(&path).unwrap();
    assert_closed(&mut b, L, CloseReason::Full);
    drop(a);
    thread::sleep(Duration::from_millis(200));
    let mut c = UnixStream::connect(&path).unwrap();
    c.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    assert_eq!(
        ask(&mut c, L, 1, b"q").unwrap().op,
        2,
        "the slot frees when a leaves"
    );
    let _ = std::fs::remove_file(&path);
}

#[test]
fn a_child_frame_without_a_status_is_malformed() {
    let (listener, path) = socket("malformed");
    let (_req_r, req_w) = io::pipe().unwrap();
    let (rep_r, mut rep_w) = io::pipe().unwrap();
    frame::write_body(&mut rep_w, 68, &[&0u32.to_le_bytes()]).unwrap();
    let end = mux::serve(listener, req_w, rep_r, limits(1, 5000));
    assert!(matches!(
        end,
        MuxEnd::ChildMalformed(FrameError::BadLength { len: 4 })
    ));
    let _ = std::fs::remove_file(&path);
}

/// T2's head-of-line plant: a peer that sends requests and never reads its replies must not delay
/// another connection's reply (the old `route` wrote synchronously and starved B for 3 s+).
#[test]
fn a_peer_that_stops_reading_starves_no_one() {
    let big = Limits {
        frame_bytes_max: 262_144,
    };
    let (listener, path) = socket("hol");
    let (child_in, child_out) = child_with(64, Duration::ZERO, 200_000, big.frame_bytes_max);
    // A write deadline longer than B's patience: only the one-slot writer keeps B answered.
    let lim = MuxLimits {
        frame: big,
        reply_write: Duration::from_secs(10),
        ..limits(8, 10_000)
    };
    thread::spawn(move || mux::serve(listener, child_in, child_out, lim));
    let mut stuck = UnixStream::connect(&path).unwrap();
    for _ in 0..30 {
        let _ = frame::write(&mut stuck, big, 5, b"");
    }
    thread::sleep(Duration::from_millis(300));
    let mut b = UnixStream::connect(&path).unwrap();
    b.set_read_timeout(Some(Duration::from_secs(3))).unwrap();
    let t = Instant::now();
    let r = ask(&mut b, big, 5, b"").unwrap();
    assert_eq!(r.payload.len(), 200_000);
    assert!(
        t.elapsed() < Duration::from_secs(1),
        "B answered in {:?}",
        t.elapsed()
    );
}

/// T2's idle plants: silent at a boundary with nothing in flight is `idle`; a connection waiting on
/// a reply slower than the idle window is NOT closed; a trickled header is `frameStalled`.
#[test]
fn idle_closes_the_silent_one_not_the_one_awaiting_a_slow_reply() {
    let (listener, path) = socket("idle");
    let (child_in, child_out) = child_with(4, Duration::from_millis(700), 0, L.frame_bytes_max);
    thread::spawn(move || mux::serve(listener, child_in, child_out, limits(8, 250)));
    let mut waiting = UnixStream::connect(&path).unwrap();
    let mut silent = UnixStream::connect(&path).unwrap();
    let mut loris = UnixStream::connect(&path).unwrap();
    loris.write_all(&[9, 0, 0]).unwrap(); // 3 of 4 header bytes, then nothing
    waiting
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    assert_eq!(
        ask(&mut waiting, L, 5, b"x").unwrap().payload,
        b"x",
        "an in-flight request outlives idle"
    );
    assert_closed(&mut silent, L, CloseReason::Idle);
    assert_closed(&mut loris, L, CloseReason::FrameStalled);
}

/// CLIENT-2's backstop: a request the child never answers ends `replyTimeout`, never a hang.
#[test]
fn a_request_with_no_reply_is_closed_reply_timeout() {
    let (listener, path) = socket("noreply");
    let (_req_r, req_w) = io::pipe().unwrap(); // a child that reads nothing and answers nothing
    let (rep_r, _rep_w) = io::pipe().unwrap();
    let lim = MuxLimits {
        reply: Duration::from_millis(400),
        ..limits(8, 10_000)
    };
    thread::spawn(move || mux::serve(listener, req_w, rep_r, lim));
    let mut a = UnixStream::connect(&path).unwrap();
    frame::write(&mut a, L, 5, b"x").unwrap();
    let t = Instant::now();
    assert_closed(&mut a, L, CloseReason::ReplyTimeout);
    assert!(t.elapsed() < Duration::from_secs(3));
}

/// A `closed` reply from the child (nd-attach relaying the box's close) is delivered and ends the
/// connection.
#[test]
fn a_closed_from_the_child_ends_the_connection() {
    let (listener, path) = socket("relay");
    let (mut req_r, req_w) = io::pipe().unwrap();
    let (rep_r, mut rep_w) = io::pipe().unwrap();
    thread::spawn(move || {
        let body = frame::read_body(&mut req_r, 68).unwrap();
        frame::write_body(&mut rep_w, 68, &[&body[..4], &[status::CLOSED], b"idle"]).unwrap();
        thread::sleep(Duration::from_secs(5)); // keep the child's stdout open
    });
    thread::spawn(move || mux::serve(listener, req_w, rep_r, limits(8, 10_000)));
    let mut a = UnixStream::connect(&path).unwrap();
    frame::write(&mut a, L, 5, b"x").unwrap();
    assert_closed(&mut a, L, CloseReason::Idle);
}

/// PROTOCOL-23: the child is told, by name, of every connection the mux ends: a client that leaves
/// is `peerLeft`, an idle one `idle`, one that sends the child wire's own byte `frameRefused`.
#[test]
fn the_child_hears_every_end_by_name() {
    let (listener, path) = socket("hang");
    let (tx, rx) = mpsc::channel();
    let (child_in, child_out) = child_hearing(8, Duration::ZERO, 0, L.frame_bytes_max, Some(tx));
    thread::spawn(move || mux::serve(listener, child_in, child_out, limits(8, 300)));
    let next =
        |rx: &mpsc::Receiver<(u32, Vec<u8>)>| rx.recv_timeout(Duration::from_secs(3)).unwrap();
    let mut a = UnixStream::connect(&path).unwrap();
    a.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    assert_eq!(ask(&mut a, L, 5, b"x").unwrap().op, 6);
    drop(a);
    assert_eq!(next(&rx), (0, b"peerLeft".to_vec()), "a client that leaves");
    let mut b = UnixStream::connect(&path).unwrap();
    assert_closed(&mut b, L, CloseReason::Idle);
    assert_eq!(next(&rx), (1, b"idle".to_vec()), "an idle close");
    let mut c = UnixStream::connect(&path).unwrap();
    frame::write(&mut c, L, g::HANGUP, b"idle").unwrap();
    assert_closed(&mut c, L, CloseReason::FrameRefused);
    assert_eq!(
        next(&rx),
        (2, b"frameRefused".to_vec()),
        "a client sending the hang-up byte"
    );
}

/// CLIENT-28: a connection counts against the bound until its fd closes, not until it leaves the
/// routing table. A has left (`peerLeft`) but its reader still holds it, blocked handing the child
/// its hang-up through a full pipe: B is `full`. Once the child reads, A's fd closes and C is
/// admitted with the next id.
#[cfg(target_os = "linux")]
#[test]
fn a_connection_counts_until_its_fd_closes() {
    let (listener, path) = socket("live");
    let (mut req_r, req_w) = io::pipe().unwrap();
    let (rep_r, _rep_w) = io::pipe().unwrap();
    req_w.try_clone().unwrap().write_all(&[0; 65_536]).unwrap(); // Linux's pipe capacity: full
    thread::spawn(move || mux::serve(listener, req_w, rep_r, limits(1, 10_000)));
    drop(UnixStream::connect(&path).unwrap());
    thread::sleep(Duration::from_millis(300));
    let mut b = UnixStream::connect(&path).unwrap();
    assert_closed(&mut b, L, CloseReason::Full);
    req_r.read_exact(&mut [0; 65_536]).unwrap();
    let hang = frame::read_body(&mut req_r, 68).unwrap();
    assert_eq!(
        (&hang[..5], &hang[5..]),
        (&[0, 0, 0, 0, g::HANGUP][..], &b"peerLeft"[..])
    );
    thread::sleep(Duration::from_millis(300));
    let mut c = UnixStream::connect(&path).unwrap();
    frame::write(&mut c, L, 5, b"x").unwrap();
    assert_eq!(
        frame::read_body(&mut req_r, 68).unwrap(),
        [1, 0, 0, 0, 5, b'x']
    );
}
