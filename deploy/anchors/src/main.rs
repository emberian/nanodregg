//! `emit-anchors PATH` writes the broker's production trust anchors; `emit-anchors --check PATH`
//! exits 1 if the file at PATH differs from them by one byte (a hand edit widens trust).
//!
//! The anchors are `webpki_root_certs::TLS_SERVER_ROOT_CERTS`, pinned by Cargo.toml, rendered as
//! concatenated PEM `CERTIFICATE` blocks in the crate's order: base64 (RFC 4648, padded) of each
//! DER at 64 columns, LF line ends. Nothing here chooses a root.

use std::process::ExitCode;

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// RFC 4648 base64 with padding.
fn base64(der: &[u8]) -> String {
    let mut out = String::with_capacity(der.len().div_ceil(3) * 4);
    for chunk in der.chunks(3) {
        let b = [
            chunk[0],
            *chunk.get(1).unwrap_or(&0),
            *chunk.get(2).unwrap_or(&0),
        ];
        let n = (u32::from(b[0]) << 16) | (u32::from(b[1]) << 8) | u32::from(b[2]);
        for (i, shift) in [18u32, 12, 6, 0].into_iter().enumerate() {
            if i <= chunk.len() {
                out.push(char::from(B64[((n >> shift) & 63) as usize]));
            } else {
                out.push('=');
            }
        }
    }
    out
}

/// The whole anchors file.
fn anchors() -> String {
    let mut s = String::new();
    for cert in webpki_root_certs::TLS_SERVER_ROOT_CERTS {
        s.push_str("-----BEGIN CERTIFICATE-----\n");
        let b = base64(cert.as_ref());
        for line in b.as_bytes().chunks(64) {
            s.push_str(std::str::from_utf8(line).unwrap_or_default());
            s.push('\n');
        }
        s.push_str("-----END CERTIFICATE-----\n");
    }
    s
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let want = anchors();
    match args.as_slice() {
        [path] => match std::fs::write(path, want) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("emit-anchors: write {path}: {e}");
                ExitCode::from(2)
            }
        },
        [flag, path] if flag == "--check" => match std::fs::read(path) {
            Ok(have) if have == want.as_bytes() => ExitCode::SUCCESS,
            Ok(_) => {
                eprintln!(
                    "emit-anchors: {path} differs from webpki-root-certs' pinned roots; regenerate it"
                );
                ExitCode::from(1)
            }
            Err(e) => {
                eprintln!("emit-anchors: read {path}: {e}");
                ExitCode::from(1)
            }
        },
        _ => {
            eprintln!("usage: emit-anchors [--check] PATH");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 4648 §10's vectors: the encoder the file depends on.
    #[test]
    fn base64_rfc4648_vectors() {
        for (i, o) in [
            ("", ""),
            ("f", "Zg=="),
            ("fo", "Zm8="),
            ("foo", "Zm9v"),
            ("foob", "Zm9vYg=="),
            ("fooba", "Zm9vYmE="),
            ("foobar", "Zm9vYmFy"),
        ] {
            assert_eq!(base64(i.as_bytes()), o);
        }
    }

    /// One block per pinned root, so a root dropped or added in rendering is red.
    #[test]
    fn one_block_per_root() {
        let n = anchors().matches("-----BEGIN CERTIFICATE-----\n").count();
        assert_eq!(n, webpki_root_certs::TLS_SERVER_ROOT_CERTS.len());
        assert!(n > 100);
    }
}
