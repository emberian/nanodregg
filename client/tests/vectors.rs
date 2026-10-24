//! CLIENT-40 (A17, law 2): the client's hand-read byte layouts against Lean's codec. Every row of
//! the codec vectors' `wire/frame`, `wire/child` and `client/rotation` sites (`gates/codec-vectors.tsv`,
//! drawn and printed by `Emit.Vectors` from `Protocol.socketFrame`, `Host.childFrame` and
//! `Protocol.rotationFrame`) is decoded here by the Rust that reads those bytes in deployment
//! (`frame::read`, `frame::read_body` + `frame::child_parts`, `layout::ArmedRotation`), rendered as
//! Lean renders its verdict, compared, and an accepted row re-encoded by the Rust writer
//! (`frame::encode_body`, `frame::child_frame`, `ArmedRotation::encode`) to the same bytes. The
//! table is Lean's; a Rust reader or writer that disagrees with it on any row is red here by row.
#![allow(clippy::unwrap_used, clippy::expect_used)] // a table that cannot be read is a failed test

use nanodregg_client::frame::{self, FrameError, Limits};
use nanodregg_client::generated::layout::{ArmedRotation, Refusal};
use nanodregg_client::generated::{CHILD_BODY_MAX, FRAME_BYTES_MAX, FRAME_LEN_BYTES};
use nanodregg_client::table;

const R: &str = "refused Nanodregg.Codec.Refusal";

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex"))
        .collect()
}

/// Lean's text for a frame refusal: `Stream.bytesOf`'s, at the same offsets.
fn frame_refusal(e: &FrameError, max: u32) -> String {
    match e {
        FrameError::Closed => format!("{R}.truncated 0 {FRAME_LEN_BYTES}"),
        FrameError::Truncated { offset, wanted, .. } => format!("{R}.truncated {offset} {wanted}"),
        FrameError::PastBound { len, .. } => format!("{R}.pastBound 0 {max} {len}"),
        FrameError::Empty => "refused empty".into(),
        FrameError::BadLength { len } => format!("refused badLength {len}"),
        FrameError::Io(e) => format!("io {e}"),
    }
}

/// One whole frame out of `b` with `read`, or Lean's refusal; bytes after it are `trailing`.
fn whole<T>(
    b: &[u8],
    max: u32,
    read: impl FnOnce(&mut &[u8]) -> Result<T, FrameError>,
) -> Result<T, String> {
    let mut r = b;
    let v = read(&mut r).map_err(|e| frame_refusal(&e, max))?;
    match r.len() {
        0 => Ok(v),
        left => Err(format!("{R}.trailing {}", b.len() - left)),
    }
}

/// The site's rows: (vector, bytes, Lean's text).
fn rows(site: &str) -> Vec<(String, Vec<u8>, String)> {
    let path = nanodregg_devtools::repo().join("gates/codec-vectors.tsv");
    let table = std::fs::read_to_string(&path).expect("gates/codec-vectors.tsv");
    let rows: Vec<_> = table
        .lines()
        .filter(|l| !l.starts_with('#'))
        .filter_map(|l| {
            let f: Vec<&str> = l.splitn(5, '\t').collect();
            (f[0] == site).then(|| (f[1].to_owned(), unhex(f[3]), f[4].to_owned()))
        })
        .collect();
    assert!(!rows.is_empty(), "{site}: no vectors in {}", path.display());
    rows
}

#[test]
fn the_lengths_the_rust_reads_are_leans() {
    assert_eq!(frame::child_max(table::LIMITS), CHILD_BODY_MAX);
    assert_eq!(table::LIMITS.frame_bytes_max, FRAME_BYTES_MAX);
}

#[test]
fn every_socket_frame_vector_reads_and_writes_as_lean_says() {
    let limits = Limits {
        frame_bytes_max: FRAME_BYTES_MAX,
    };
    let rows = rows("wire/frame");
    for (v, b, lean) in &rows {
        let rust = match whole(b, FRAME_BYTES_MAX, |r| frame::read(r, limits)) {
            Ok(f) => {
                let again = frame::encode_body(FRAME_BYTES_MAX, &[&[f.op], &f.payload]).unwrap();
                assert_eq!(&again, b, "wire/frame {v}: re-encoded");
                format!("ok op={} payload={}", f.op, hex(&f.payload))
            }
            Err(t) => t,
        };
        assert_eq!(&rust, lean, "wire/frame {v}");
    }
    assert!(
        rows.iter().any(|r| r.2.starts_with("ok "))
            && rows.iter().any(|r| r.2.starts_with("refused "))
    );
}

#[test]
fn every_child_wire_vector_reads_and_writes_as_lean_says() {
    let rows = rows("wire/child");
    for (v, b, lean) in &rows {
        let read = whole(b, CHILD_BODY_MAX, |r| frame::read_body(r, CHILD_BODY_MAX));
        let rust = match read.and_then(|body| {
            let (conn, byte, payload) =
                frame::child_parts(&body).map_err(|e| frame_refusal(&e, CHILD_BODY_MAX))?;
            let again = frame::child_frame(CHILD_BODY_MAX, conn, byte, payload).unwrap();
            assert_eq!(&again, b, "wire/child {v}: re-encoded");
            Ok(format!("ok conn={conn} op={byte} payload={}", hex(payload)))
        }) {
            Ok(t) | Err(t) => t,
        };
        assert_eq!(&rust, lean, "wire/child {v}");
    }
    assert!(
        rows.iter().any(|r| r.2.starts_with("ok "))
            && rows.iter().any(|r| r.2.starts_with("refused "))
    );
}

#[test]
fn every_rotation_record_vector_reads_and_writes_as_lean_says() {
    let rows = rows("client/rotation");
    for (v, b, lean) in &rows {
        let rust = match ArmedRotation::decode(b) {
            Ok(a) => {
                assert_eq!(&a.encode().unwrap(), b, "client/rotation {v}: re-encoded");
                format!(
                    "ok attempt={} incoming={} pending={}",
                    a.attempt,
                    hex(&a.incoming),
                    hex(&a.pending)
                )
            }
            Err(Refusal::Truncated { offset, need }) => format!("{R}.truncated {offset} {need}"),
            Err(Refusal::Trailing { offset }) => format!("{R}.trailing {offset}"),
            Err(Refusal::PastBound { offset, limit, got }) => {
                format!("{R}.pastBound {offset} {limit} {got}")
            }
            Err(Refusal::BadTag { offset, tag }) => format!("{R}.badTag {offset} {tag}"),
        };
        assert_eq!(&rust, lean, "client/rotation {v}");
    }
    assert!(
        rows.iter().any(|r| r.2.starts_with("ok "))
            && rows.iter().any(|r| r.2.starts_with("refused "))
    );
}
