//! `emit-anchors PATH` writes the broker's production trust anchors; `emit-anchors --check PATH`
//! exits 1 if the file at PATH differs from them by one byte (a hand edit widens trust).
//!
//! The anchors are the roots of `webpki_root_certs::TLS_SERVER_ROOT_CERTS` (pinned by Cargo.toml)
//! whose DER's SHA-256 is in `PROVIDER_ROOTS`, rendered as concatenated PEM `CERTIFICATE` blocks in
//! the crate's order: base64 (RFC 4648, padded) of each DER at 64 columns, LF line ends.
//!
//! `PROVIDER_ROOTS` narrows keybroker's trust from the crate's 121 roots to the roots that issue
//! for the providers in Lean's table (`Hosting.Broker.providers`: today `api.anthropic.com` only),
//! HOSTING-28: a mis-issuing CA outside it can no longer be handed the operator's key. Provenance
//! (2026-10-18, from Certificate Transparency, never a handshake with the provider): crt.sh's
//! unexpired certificates for `api.anthropic.com` are issued by Google Trust Services WR3, WR1 and
//! WE1 (under GTS Root R1 and R4) and by Cloudflare TLS Issuing ECC/RSA CA 4 (SSL.com's transit
//! CAs, under SSL.com's TLS roots). Kept: GTS Root R1, R3, R4 (R2 is not in the crate) and SSL.com's
//! four TLS roots (Root Certification Authority RSA and ECC, TLS RSA and ECC Root CA 2022). A
//! provider added to Lean's table adds its roots here, or keybroker refuses it `tlsCertificate`.

use std::process::ExitCode;

/// The kept roots: (subject CN, lowercase hex SHA-256 of the root certificate's DER).
const PROVIDER_ROOTS: [(&str, &str); 7] = [
    (
        "GTS Root R1",
        "d947432abde7b7fa90fc2e6b59101b1280e0e1c7e4e40fa3c6887fff57a7f4cf",
    ),
    (
        "GTS Root R3",
        "34d8a73ee208d9bcdb0d956520934b4e40e69482596e8b6f73c8426b010a6f48",
    ),
    (
        "GTS Root R4",
        "349dfa4058c5e263123b398ae795573c4e1313c83fe68f93556cd5e8031b3c7d",
    ),
    (
        "SSL.com Root Certification Authority RSA",
        "85666a562ee0be5ce925c1d8890a6f76a87ec16d4d7d5f29ea7419cf20123b69",
    ),
    (
        "SSL.com Root Certification Authority ECC",
        "3417bb06cc6007da1b961c920b8ab4ce3fad820e4aa30b9acbc4a74ebdcebc65",
    ),
    (
        "SSL.com TLS RSA Root CA 2022",
        "8faf7d2e2cb4709bb8e0b33666bf75a5dd45b5de480f8ea8d4bfe6bebc17f2ed",
    ),
    (
        "SSL.com TLS ECC Root CA 2022",
        "c32ffd9f46f936d16c3673990959434b9ad60aafbb9e7cf33654f144cc1ba143",
    ),
];

/// The lowercase hex SHA-256 of `der`.
fn fingerprint(der: &[u8]) -> String {
    ring::digest::digest(&ring::digest::SHA256, der)
        .as_ref()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Whether a crate root is one `PROVIDER_ROOTS` keeps.
fn kept(der: &[u8]) -> bool {
    let f = fingerprint(der);
    PROVIDER_ROOTS.iter().any(|(_, k)| *k == f)
}

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
    for cert in webpki_root_certs::TLS_SERVER_ROOT_CERTS
        .iter()
        .filter(|c| kept(c.as_ref()))
    {
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
                    "emit-anchors: {path} differs from the provider roots of webpki-root-certs' pinned roots; regenerate it"
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

    /// One block per kept root, and every kept fingerprint is exactly one root of the pinned crate:
    /// a crate update that drops a provider root, or a fingerprint that names none, is red.
    #[test]
    fn one_block_per_provider_root() {
        let n = anchors().matches("-----BEGIN CERTIFICATE-----\n").count();
        assert_eq!(n, PROVIDER_ROOTS.len());
        for (name, f) in PROVIDER_ROOTS {
            let hits = webpki_root_certs::TLS_SERVER_ROOT_CERTS
                .iter()
                .filter(|c| fingerprint(c.as_ref()) == f)
                .count();
            assert_eq!(hits, 1, "{name}: {hits} roots of the crate");
        }
        assert!(webpki_root_certs::TLS_SERVER_ROOT_CERTS.len() > 100);
    }
}
