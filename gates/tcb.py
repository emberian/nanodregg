#!/usr/bin/env python3
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
  - a lake-manifest.json package with no row whose component is its name;
  - a PINNED FILE that is not what its row says (GATES-20y): a row whose component names a host in
    parentheses (`cc (hbox)`, `sandbox-exec (macOS)`) and whose pin holds `<absolute path> … sha256 <hex>` is
    compared on that host (the hostname, or `macOS` on Darwin): the file's sha256 must be the pin's, and the
    file must exist; on another host the row is not this host's to compare (the judge on hbox compares hbox's).
    A path relative to the tree before a `sha256` pins the tree's own copy (the AppArmor profile's source).
    A `sha256` pin in a row that names no host is red: nothing would ever compare it.

`gates/tcb.py --plants FRESH [--harness-control]` (a gates/runs.tsv script row): a copy of the table and its
inputs in FRESH, mutated, must read each refusal by name: the rustix row removed (an unsafe holder unrowed), a
host row pinning a file of FRESH with a wrong sha256, the same pin right (GREEN), and a sha256 pin with no host.
Last line `TCB PLANTS GREEN`.
"""
from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import shutil
import socket
import sys
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
# CLIENT-30): signal dispositions (sigaction) for nd-supervise SIGTERM; and the syscall layer every
# forbid-unsafe crate's fs/process/net IO goes through (GATES-20y; READ-LEDGER-CENSUS-GATES D7): rustix (a
# direct dependency of client, sandbox, launcher) and its backends, linux-raw-sys (Linux), libc (elsewhere, and
# under errno, cpufeatures, getrandom, ring), errno, windows-sys (Windows; locked, built on no host we build on).
UNSAFE_HOLDERS = {"signal-hook", "signal-hook-registry", "rustix", "linux-raw-sys", "libc", "errno", "windows-sys"}
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


HOST = re.compile(r"\(([^()]+)\)\s*$")
# a path at a token's start (absolute, or relative to the tree: a pin of the tree's own copy), or a sha256 pin
PIN_TOKEN = re.compile(r"(?<![\w./-])(/[^\s,;()]+|[\w.-]+(?:/[\w.-]+)+)|\bsha256\s+([0-9a-f]{64})")


def this_host(label: str) -> bool:
    return label == socket.gethostname() or (label == "macOS" and platform.system() == "Darwin")


def file_pins(pin: str) -> list[tuple[str, str]]:
    """(path, sha256) for every `sha256 HEX` of a pin, paired with the path before it (absolute, or relative to the
    tree)."""
    out, last = [], None
    for m in PIN_TOKEN.finditer(pin):
        if m.group(1):
            last = m.group(1).rstrip(":.")
        elif last:
            out.append((last, m.group(2)))
    return out


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def pinned_files(root: str, rows: dict[str, list[str]]) -> list[str]:
    red = []
    for comp, f in sorted(rows.items()):
        pins = file_pins(f[1])
        host = HOST.search(comp)
        if "sha256" in f[1] and not host:
            red.append(f"{comp}: a sha256 pin and no host in the component name: nothing compares it")
            continue
        if not host or not this_host(host.group(1)):
            continue
        for p, want in pins:
            path = p if p.startswith("/") else os.path.join(root, p)
            if not os.path.isfile(path):
                red.append(f"{comp}: pinned file {path} is absent on {host.group(1)}")
            elif (got := sha256_of(path)) != want:
                red.append(f"{comp}: {path} has sha256 {got}, the row pins {want}")
    return red


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
    red += pinned_files(root, rows)
    return red


def plants(fresh: str, control: bool) -> int:
    """Each mutation of a copy of the tree's table must read its refusal by name (the plants of tcb.check)."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    inputs = ["Cargo.lock", "lean-toolchain", "lake-manifest.json", os.path.join("gates", "OWNERS"),
              os.path.join("gates", "axioms-allow.tsv"), os.path.join("gates", "native-allow.tsv"), TABLE]
    inputs += sorted({p for r in _tsv(os.path.join(root, TABLE)) if len(r) > 1 for p, _ in file_pins(r[1])
                      if not p.startswith("/")})    # the tree's own pinned copies
    here = socket.gethostname()
    target = os.path.join(fresh, "pinned.bin")
    os.makedirs(fresh, exist_ok=True)
    with open(target, "wb") as fh:
        fh.write(b"gates/tcb.py plant\n")
    good = hashlib.sha256(b"gates/tcb.py plant\n").hexdigest()
    row = lambda comp, pin: f"{comp}\t{pin}\ttrusted-unverified\tGATES\tthe plant\tnone\n"

    def table(name: str, edit) -> str:
        d = os.path.join(fresh, name)
        for p in inputs:
            if os.path.exists(os.path.join(root, p)):
                os.makedirs(os.path.dirname(os.path.join(d, p)) or d, exist_ok=True)
                shutil.copyfile(os.path.join(root, p), os.path.join(d, p))
        t = os.path.join(d, TABLE)
        text = open(t, encoding="utf-8").read()
        new = edit(text)
        if new == text:
            raise SystemExit(f"TCB PLANTS RED: the mutation {name} changed nothing")
        open(t, "w", encoding="utf-8").write(new)
        return d
    drop = lambda c: lambda text: "".join(l for l in text.splitlines(True) if not l.startswith(c + "\t"))
    cases = [
        ("control", lambda text: text + "# the plant\n", None),
        ("rustix-unrowed", drop("rustix"), "crate rustix 1.1.2 is in Cargo.lock with no gates/tcb.tsv row"),
        ("pin-wrong", lambda text: text + row(f"plant-file ({here})", f"{target} sha256 {'0' * 64}"),
         f"plant-file ({here}): {target} has sha256 {good}, the row pins {'0' * 64}"),
        ("pin-right", lambda text: text + row(f"plant-file ({here})", f"{target} sha256 {good}"), None),
        ("pin-absent", lambda text: text + row(f"plant-file ({here})", f"{target}.gone sha256 {good}"),
         f"pinned file {target}.gone is absent on {here}"),
        ("pin-no-host", lambda text: text + row("plant-file", f"{target} sha256 {good}"),
         "plant-file: a sha256 pin and no host in the component name"),
    ]
    if control:
        cases.append(("harness-control", lambda text: text + "# nothing\n", "harness-control: nothing reads this"))
    bad = []
    for name, edit, want in cases:
        reds = check(table(name, edit))
        ok = (not reds) if want is None else any(want in r for r in reds)
        print(f"  {name}: {'ok' if ok else 'FAIL'} (want {want or 'GREEN'}){'' if ok else ': ' + '; '.join(reds)[:400]}")
        if not ok:
            bad.append(name)
    print(f"TCB PLANTS {'GREEN' if not bad else 'RED (' + str(len(bad)) + '): ' + ' '.join(bad)}")
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "--plants":
        sys.exit(plants(os.path.abspath(sys.argv[2]), "--harness-control" in sys.argv))
    r = check(sys.argv[1] if len(sys.argv) > 1 else ".")
    for x in r:
        print(x)
    print(f"tcb: {'RED' if r else 'ok'}")
    sys.exit(1 if r else 0)
