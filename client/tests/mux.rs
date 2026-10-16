//! Mux plants: replies reach the connection that asked, by id, with nothing parsed; a reply for a
//! closed connection is dropped; one connection past the bound is closed; the child closing its
//! stdout closes every connection and ends `serve`.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use std::io::{self, Read};
use std::os::unix::net::{UnixListener, UnixStream};
use std::thread;
use std::time::Duration;

use nanodregg_client::frame::{self, FrameError, Limits};
use nanodregg_client::mux::{self, MuxEnd, MuxLimits};

const L: Limits = Limits {
    frame_bytes_max: 64,
}; // test bound, not a protocol constant

fn socket(name: &str) -> (UnixListener, std::path::PathBuf) {
    let p = std::env::temp_dir().join(format!("nd-mux-{}-{name}.sock", std::process::id()));
    let _ = std::fs::remove_file(&p);
    (UnixListener::bind(&p).unwrap(), p)
}

/// A child that answers every request with status = op + 1 and the payload reversed, until it
/// has answered `n`; then it closes its stdout.
fn echo_child(n: usize) -> (io::PipeWriter, io::PipeReader) {
    let (mut req_r, req_w) = io::pipe().unwrap();
    let (rep_r, mut rep_w) = io::pipe().unwrap();
    thread::spawn(move || {
        for _ in 0..n {
            let body = frame::read_body(&mut req_r, L.frame_bytes_max + 4).unwrap();
            let (conn, rest) = body.split_at(4);
            let mut payload = rest[1..].to_vec();
            payload.reverse();
            frame::write_body(
                &mut rep_w,
                L.frame_bytes_max + 4,
                &[conn, &[rest[0] + 1], &payload],
            )
            .unwrap();
        }
    });
    (req_w, rep_r)
}

#[test]
fn replies_route_by_connection_and_child_close_ends_serve() {
    let (listener, path) = socket("route");
    let (child_in, child_out) = echo_child(2);
    let server = thread::spawn(move || {
        mux::serve(
            listener,
            child_in,
            child_out,
            MuxLimits {
                frame: L,
                connections_max: 4,
            },
        )
    });
    let mut a = UnixStream::connect(&path).unwrap();
    a.set_read_timeout(Some(Duration::from_secs(5))).unwrap(); // before: macOS refuses it after shutdown
    let mut b = UnixStream::connect(&path).unwrap();
    frame::write(&mut a, L, 7, b"abc").unwrap();
    let ra = frame::read(&mut a, L).unwrap();
    frame::write(&mut b, L, 9, b"xy").unwrap();
    let rb = frame::read(&mut b, L).unwrap();
    assert_eq!((ra.op, ra.payload), (8, b"cba".to_vec()));
    assert_eq!((rb.op, rb.payload), (10, b"yx".to_vec()));
    // The child has answered its two and closed: serve ends and every connection sees EOF.
    assert!(matches!(server.join().unwrap(), MuxEnd::ChildClosed));
    let mut rest = Vec::new();
    assert_eq!(a.read_to_end(&mut rest).unwrap(), 0);
    let _ = std::fs::remove_file(&path);
}

#[test]
fn past_the_connection_bound_is_closed() {
    let (listener, path) = socket("bound");
    let (child_in, child_out) = echo_child(2); // stays alive after the first answer
    thread::spawn(move || {
        mux::serve(
            listener,
            child_in,
            child_out,
            MuxLimits {
                frame: L,
                connections_max: 1,
            },
        )
    });
    let mut a = UnixStream::connect(&path).unwrap();
    frame::write(&mut a, L, 1, b"q").unwrap();
    assert_eq!(frame::read(&mut a, L).unwrap().op, 2); // a is registered before b connects
    let mut b = UnixStream::connect(&path).unwrap();
    b.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    assert!(matches!(frame::read(&mut b, L), Err(FrameError::Closed)));
    let _ = std::fs::remove_file(&path);
}

#[test]
fn a_child_frame_without_a_status_is_malformed() {
    let (listener, _path) = socket("malformed");
    let (_req_r, req_w) = io::pipe().unwrap();
    let (rep_r, mut rep_w) = io::pipe().unwrap();
    frame::write_body(&mut rep_w, 68, &[&0u32.to_le_bytes()]).unwrap();
    let end = mux::serve(
        listener,
        req_w,
        rep_r,
        MuxLimits {
            frame: L,
            connections_max: 1,
        },
    );
    assert!(matches!(
        end,
        MuxEnd::ChildMalformed(FrameError::Truncated { .. })
    ));
    let _ = std::fs::remove_file(&_path);
}
