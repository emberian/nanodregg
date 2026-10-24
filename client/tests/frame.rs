//! Frame plants: each malformed stream is refused by its name.
#![allow(clippy::unwrap_used)] // a plant that cannot set up is a failed plant
use nanodregg_client::frame::{self, FrameError, Limits};

// A test bound, not a protocol constant: the real one comes from the generated table.
const L: Limits = Limits { frame_bytes_max: 8 };

fn bytes(len: u32, body: &[u8]) -> Vec<u8> {
    let mut v = len.to_le_bytes().to_vec();
    v.extend_from_slice(body);
    v
}

#[test]
fn round_trip_at_the_bound() {
    let mut buf = Vec::new();
    frame::write(&mut buf, L, 3, &[1, 2, 3, 4, 5, 6, 7]).unwrap();
    let f = frame::read(&mut buf.as_slice(), L).unwrap();
    assert_eq!((f.op, f.payload), (3, vec![1, 2, 3, 4, 5, 6, 7]));
}

#[test]
fn one_byte_over_is_refused_both_ways() {
    let mut buf = Vec::new();
    assert!(matches!(
        frame::write(&mut buf, L, 3, &[0; 8]),
        Err(FrameError::PastBound { len: 9, max: 8 })
    ));
    assert!(buf.is_empty(), "nothing is written past the bound");
    assert!(matches!(
        frame::read(&mut bytes(9, &[0; 9]).as_slice(), L),
        Err(FrameError::PastBound { len: 9, .. })
    ));
}

#[test]
fn a_huge_declared_length_allocates_nothing() {
    assert!(matches!(
        frame::read(&mut bytes(u32::MAX, &[]).as_slice(), L),
        Err(FrameError::PastBound { .. })
    ));
}

#[test]
fn empty_closed_and_truncated() {
    assert!(matches!(
        frame::read(&mut bytes(0, &[]).as_slice(), L),
        Err(FrameError::Empty)
    ));
    assert!(matches!(
        frame::read(&mut [].as_slice(), L),
        Err(FrameError::Closed)
    ));
    assert!(matches!(
        frame::read(&mut [1u8, 0].as_slice(), L),
        Err(FrameError::Truncated {
            offset: 0,
            wanted: 4,
            got: 2
        })
    ));
    assert!(matches!(
        frame::read(&mut bytes(5, &[1, 2]).as_slice(), L),
        Err(FrameError::Truncated {
            offset: 4,
            wanted: 5,
            got: 2
        })
    ));
}
