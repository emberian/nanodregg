"""gates/owners.py — a commit stays inside its layer (ROOT ruling 2026-10-16, after two commits
from stale private indexes silently reverted another layer's files).

The layer is the commit subject's prefix (`kernel: …`); every changed path must be owned by
that layer (gates/OWNERS, longest prefix) or be SHARED. Red otherwise, naming each foreign path
and its owner, unless the message carries `CROSS-LAYER: <reason>` (the reason is the record).
A path no OWNERS row covers belongs to ROOT.
"""
import os
import re

SUBJECT = {"kernel": "KERNEL", "codec": "CODEC", "emit": "CODEC", "host": "HOST", "protocol": "PROTOCOL",
           "rows": "PROTOCOL", "client": "CLIENT", "sandbox": "CLIENT", "lang": "LANG",
           "gates": "GATES", "build": "GATES", "charter": "ROOT", "root": "ROOT"}


def table(root: str) -> list[tuple[str, str]]:
    rows = []
    for line in open(os.path.join(root, "gates", "OWNERS"), encoding="utf-8"):
        if line.strip() and not line.startswith("#"):
            prefix, layer = line.rstrip("\n").split("\t")
            rows.append((prefix, layer))
    return sorted(rows, key=lambda r: -len(r[0]))


def owner(rows, path: str) -> str:
    for prefix, layer in rows:
        if path == prefix or (prefix.endswith("/") and path.startswith(prefix)):
            return layer
    return "ROOT"


def check(root: str, changed: list[str], message: str) -> list[str]:
    subject = message.strip().splitlines()[0] if message.strip() else ""
    m = re.match(r"([a-z]+)(?:\([^)]*\))?!?:", subject)
    if not m or m.group(1) not in SUBJECT:
        return [f"subject must start with a layer prefix ({', '.join(sorted(SUBJECT))}): {subject!r}"]
    layer = SUBJECT[m.group(1)]
    rows = table(root)
    foreign = [(p, owner(rows, p)) for p in changed if owner(rows, p) not in (layer, "SHARED")]
    if not foreign or re.search(r"(?m)^CROSS-LAYER:\s*\S", message):
        return []
    return [f"{layer} commit touches {p}, owned by {o}" for p, o in foreign] + [
        "split the commit, or add 'CROSS-LAYER: <reason>' to the message"]
