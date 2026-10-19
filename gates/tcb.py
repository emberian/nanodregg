"""gates/tcb.py — the TCB table (ROOT ruling 10-18): every component a verdict trusts without a proof in
this tree has a row in gates/tcb.tsv, so the trust is written down where it enters, not discovered later.

gates/tcb.tsv rows, `component<TAB>pin<TAB>kind<TAB>owner<TAB>trusted for<TAB>lift condition`; kind is
trusted-unverified | verified | platform-fact; owner is a layer named in gates/OWNERS (or ROOT).
Red, by name, on:
  - a malformed row, an unknown kind or owner, or two rows for one component;
  - a crate of the root Cargo.lock on the crypto/TLS list below (CRATES/PREFIXES: a primitive, TLS, a
    certificate or key parser, trust anchors, randomness; UNSAFE_HOLDERS: the unsafe a forbid-unsafe crate delegates) with no row whose component is the crate's
    name, or whose pin does not list every locked version of it (a version bump re-reads the row);
    the list is the lock, not one platform's build graph: a locked crate is one feature away from built;
  - a row naming a crate that is on the list and no longer locked (stale);
  - no `lean4` row, or its pin is not the lean-toolchain version;
  - a native_decide allow row in gates/axioms-allow.tsv (axiom `…._native.native_decide.ax_…` or
    Lean.ofReduceBool / Lean.ofReduceNat / Lean.trustCompiler) whose theorem has no
    `native_decide:<theorem>` row, or whose row's pin is not the toolchain version; such a row with no
    allow row is stale;
  - a module in gates/native-allow.tsv (it may declare @[extern]: its C is trusted) with no
    `extern:<module>` row; such a row with no allow row is stale;
  - a lake-manifest.json package with no row whose component is its name.
"""
from __future__ import annotations

import json
import os
import re
import tomllib

TABLE = os.path.join("gates", "tcb.tsv")
KINDS = {"trusted-unverified", "verified", "platform-fact"}
# The crypto/TLS match list (data). A crate matches if its name is in CRATES or starts with a PREFIX.
CRATES = {
    "ring", "untrusted", "sha1", "sha2", "sha3", "blake2", "blake3", "hmac", "hkdf", "digest",
    "block-buffer", "crypto-common", "signature", "subtle", "zeroize", "fiat-crypto", "cpufeatures",
    "der", "der-parser", "spki", "pkcs1", "pkcs8", "const-oid", "base64ct", "oid-registry", "yasna", "pem",
    "rcgen", "x509-parser", "x509-cert", "rand", "rand_core", "rand_chacha", "getrandom", "native-tls",
    "p256", "p384", "p521", "rsa", "ecdsa", "elliptic-curve", "argon2", "scrypt", "pbkdf2", "bcrypt",
}
# Crates that hold the unsafe a forbid(unsafe_code) crate delegates, admitted by name (ROOT ruling,
# CLIENT-30): signal dispositions (sigaction) for nd-supervise SIGTERM.
UNSAFE_HOLDERS = {"signal-hook", "signal-hook-registry"}
PREFIXES = ("rustls", "webpki", "ed25519", "ed448", "curve25519", "x25519", "aes", "chacha20", "poly1305",
            "aws-lc", "openssl", "boring", "asn1-rs", "schannel", "security-framework")
NATIVE_AXIOMS = {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
NATIVE_AUX = re.compile(r"\._native\.native_decide\.ax_\d+(_\d+)*$")


def matches(crate: str) -> bool:
    return crate in CRATES or crate in UNSAFE_HOLDERS or crate.startswith(PREFIXES)


def _tsv(path: str) -> list[list[str]]:
    if not os.path.isfile(path):
        return []
    return [line.rstrip("\n").split("\t") for line in open(path, encoding="utf-8")
            if line.strip() and not line.startswith("#")]


def layers(root: str) -> set[str]:
    return {r[1] for r in _tsv(os.path.join(root, "gates", "OWNERS")) if len(r) == 2} - {"SHARED"} | {"ROOT"}


def toolchain(root: str) -> str | None:
    p = os.path.join(root, "lean-toolchain")
    if not os.path.isfile(p):
        return None
    return open(p, encoding="utf-8").read().strip().rsplit(":", 1)[-1]


def locked(root: str) -> dict[str, set[str]]:
    p = os.path.join(root, "Cargo.lock")
    if not os.path.isfile(p):
        return {}
    out: dict[str, set[str]] = {}
    with open(p, "rb") as f:
        for pkg in tomllib.load(f).get("package", []):
            out.setdefault(pkg["name"], set()).add(pkg["version"])
    return out


def native_decide_theorems(root: str) -> set[str]:
    out = set()
    for r in _tsv(os.path.join(root, "gates", "axioms-allow.tsv")):
        if len(r) >= 2 and (r[1] in NATIVE_AXIOMS or NATIVE_AUX.search(r[1])):
            out.add(NATIVE_AUX.sub("", r[0]))
    return out


def check(root: str) -> list[str]:
    red: list[str] = []
    rows: dict[str, list[str]] = {}
    known = layers(root)
    p = os.path.join(root, TABLE)
    if not os.path.isfile(p):
        return [f"{TABLE} is missing"]
    for n, line in enumerate(open(p, encoding="utf-8"), 1):
        if not line.strip() or line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) != 6 or not all(x.strip() for x in f):
            red.append(f"{TABLE}:{n}: need component, pin, kind, owner, trusted for, lift condition: {line.rstrip()[:80]!r}")
            continue
        comp, _pin, kind, owner = f[0], f[1], f[2], f[3]
        if kind not in KINDS:
            red.append(f"{TABLE}:{n}: {comp}: kind {kind!r} is not one of {', '.join(sorted(KINDS))}")
        if owner not in known:
            red.append(f"{TABLE}:{n}: {comp}: owner {owner!r} is not a layer in gates/OWNERS")
        if comp in rows:
            red.append(f"{TABLE}:{n}: second row for {comp}")
        rows[comp] = f

    def pins(comp: str) -> set[str]:
        return {x.strip() for x in rows[comp][1].split(",")}

    lock = locked(root)
    for crate in sorted(c for c in lock if matches(c)):
        want = lock[crate]
        if crate not in rows:
            red.append(f"crate {crate} {', '.join(sorted(want))} is in Cargo.lock with no {TABLE} row")
        elif pins(crate) != want:
            red.append(f"crate {crate}: {TABLE} pin {rows[crate][1]} but Cargo.lock has {', '.join(sorted(want))}")
    for comp in sorted(c for c in rows if matches(c) and c not in lock):
        red.append(f"stale {TABLE} row: crate {comp} is not in Cargo.lock")

    tc = toolchain(root)
    if "lean4" not in rows:
        red.append(f"no lean4 row in {TABLE} (the toolchain is {tc})")
    elif pins("lean4") != {tc}:
        red.append(f"lean4: {TABLE} pin {rows['lean4'][1]} but lean-toolchain is {tc}")

    nd = native_decide_theorems(root)
    for thm in sorted(nd):
        c = f"native_decide:{thm}"
        if c not in rows:
            red.append(f"native_decide allow row for {thm} with no {TABLE} row {c}")
        elif pins(c) != {tc}:
            red.append(f"{c}: {TABLE} pin {rows[c][1]} but lean-toolchain is {tc}")
    for c in sorted(r for r in rows if r.startswith("native_decide:") and r[len("native_decide:"):] not in nd):
        red.append(f"stale {TABLE} row {c}: no native_decide row in gates/axioms-allow.tsv")

    ext = {r[0] for r in _tsv(os.path.join(root, "gates", "native-allow.tsv")) if r}
    for m in sorted(ext):
        if f"extern:{m}" not in rows:
            red.append(f"native-allow module {m} (trusted C) with no {TABLE} row extern:{m}")
    for c in sorted(r for r in rows if r.startswith("extern:") and r[len("extern:"):] not in ext):
        red.append(f"stale {TABLE} row {c}: no such module in gates/native-allow.tsv")

    mp = os.path.join(root, "lake-manifest.json")
    if os.path.isfile(mp):
        for pkg in json.load(open(mp, encoding="utf-8")).get("packages", []):
            name = pkg.get("name", "?")
            if name not in rows:
                red.append(f"lake package {name} with no {TABLE} row")
    return red
