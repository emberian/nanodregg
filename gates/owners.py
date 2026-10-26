"""gates/owners.py — a commit stays inside its layer (ROOT ruling 2026-10-16, after two commits
from stale private indexes silently reverted another layer's files).

The layer is the commit subject's prefix (`kernel: …`); every changed path must be owned by
that layer (gates/OWNERS, longest prefix) or be SHARED. Red otherwise, naming each foreign path
and its owner, unless the message's `CROSS-LAYER: <reason>` lines name that owner (GATES-18): the
layer's name as a word, alone or as a lane (`HOST`, `HOST-13 agreed`, `ROOT for HOST`). A reason
that names only other layers no longer covers a path it does not name (c18e028 changed
gates/waste.tsv under a reason naming HOST and PROTOCOL only). A path no OWNERS row covers belongs
to ROOT, so its reason names ROOT.
"""
import os
import re

# subject prefix -> the layers whose paths it may change. LEDGER has its own prefix `ledger:` (ROOT
# 10-17, replacing the `kernel:`-owns-LEDGER mapping of 5be0d98). SPEC (`Spec/`, the top-level claims) has `spec:` (ROOT 10-26).
SUBJECT = {"kernel": {"KERNEL"}, "ledger": {"LEDGER"}, "codec": {"CODEC"}, "emit": {"CODEC"}, "host": {"HOST"},
           "protocol": {"PROTOCOL"}, "rows": {"PROTOCOL"}, "client": {"CLIENT"}, "sandbox": {"CLIENT"},
           "lang": {"LANG"}, "hosting": {"HOSTING"}, "ops": {"OPS"}, "perf": {"PERF"},
           "transport": {"TRANSPORT"}, "spec": {"SPEC"}, "gates": {"GATES"}, "build": {"GATES"}, "charter": {"ROOT"},
           "root": {"ROOT"}}


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
    layers = SUBJECT[m.group(1)]
    rows = table(root)
    foreign = [(p, owner(rows, p)) for p in changed if owner(rows, p) not in layers | {"SHARED"}]
    if not foreign:
        return []
    reasons = "\n".join(re.findall(r"(?m)^CROSS-LAYER:\s*(\S.*)$", message))
    who = "/".join(sorted(layers))
    if not reasons:
        return [f"{who} commit touches {p}, owned by {o}" for p, o in foreign] + [
            "split the commit, or add 'CROSS-LAYER: <reason>' naming each owner to the message"]
    unnamed = [(p, o) for p, o in foreign if not named(reasons, o)]
    return [f"{who} commit touches {p}, owned by {o}, and no CROSS-LAYER line names {o}" for p, o in unnamed] + (
        [f"name each owner in a CROSS-LAYER line ('{o}-N agreed …', or 'ROOT for {o}' when no {o} lane is live)"
         for o in sorted({o for _, o in unnamed})])


def named(reasons: str, layer: str) -> bool:
    """The layer's name as a whole word, alone or as a lane (`HOST-13`): `HOST` is not named by
    `HOSTING`, nor `CODEC` by `codec` (layer names are upper case in OWNERS and in lane names); `_`
    and `/` separate words (`ROOT_for_HOSTING/LEDGER` names HOSTING and LEDGER)."""
    return re.search(rf"(?<![A-Za-z0-9]){re.escape(layer)}(?:-\d+)?(?![A-Za-z0-9])", reasons) is not None
