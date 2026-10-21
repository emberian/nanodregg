"""Shadow obligation journal; finite receipt authorization is Census.JournalRun.
This module validates/records evidence and maintains a derived index. It never runs a judge
to infer theorem truth, or treats an unavailable export as an empty obligation set.
"""
from __future__ import annotations
import hashlib
import argparse
import fcntl
import os
import json
from pathlib import Path

ROOTS = [
    "Nanodregg.Kernel.chain_binds", "Nanodregg.Kernel.chain_binds_sep",
    "Nanodregg.Kernel.Trie.inclusion_sound", "Nanodregg.Kernel.Trie.exclusion_sound",
    "Nanodregg.Kernel.Receive.receive_ok_with", "Nanodregg.Kernel.Receive.receive_congr",
    "Nanodregg.Kernel.Receive.submit_frame", "Nanodregg.Kernel.Receive.call_frame",
]
MODULES = ["Kernel.Proofs.Fold", "Kernel.Proofs.Trie", "Kernel.Proofs.Receive",
           "Kernel.Proofs.Logic.Triple"]
REFS = {"app": ("f", "a"), "lam": ("ty", "body"), "forallE": ("ty", "body"),
        "letE": ("ty", "value", "body"), "proj": ("value",), "metadata": ("value",),
        "bvar": (), "sort": (), "const": (), "natLit": (), "strLit": ()}


class Incomplete(ValueError):
    pass


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(x):
    return hashlib.sha256(canonical(x).encode()).hexdigest()


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def name_of(n):
    if n == "anonymous":
        return ""
    tag, d = next(iter(n.items()))
    if tag == "anonymous":
        return ""
    parent = name_of(d["parent"])
    part = d["s"] if tag == "str" else str(d["n"])
    return parent + ("." if parent else "") + part


class Export:
    def __init__(self, path, roots=ROOTS):
        self.path = Path(path)
        try:
            self.raw = json.loads(self.path.read_text())
            if self.raw["schema"] != 1 or self.raw["complete"] is not True:
                raise Incomplete("schema or completeness marker")
            if self.raw["roots"] != roots:
                raise Incomplete("root inventory mismatch")
            ds = self.raw["declarations"]
            self.decls = {d["name"]: d for d in ds}
            if len(self.decls) != len(ds) or any(n not in self.decls for n in roots):
                raise Incomplete("duplicate or missing obligation")
            self.nodes = self.raw["nodes"]
            self.node_count = len(self.nodes)
            self.node_hashes = {}
            self.visiting = set()
            # Validate every node, not only the ones a successful root happened to reach.
            for i in range(len(self.nodes)):
                self.expr_hash(i)
            for n, d in self.decls.items():
                for key in ("typeDeps", "valueDeps", "shapeDeps"):
                    if any(x not in self.decls for x in d[key]):
                        raise Incomplete(f"missing {key} dependency of {n}")
                self.expr_hash(d["type"])
                if set(d["typeDeps"]) != self.expression_dependencies(d["type"]):
                    raise Incomplete(f"omitted or invented type edge of {n}")
                if d["value"] is not None:
                    self.expr_hash(d["value"])
                    if set(d["valueDeps"]) != self.expression_dependencies(d["value"]):
                        raise Incomplete(f"omitted or invented proof/value edge of {n}")
                elif d["valueDeps"]:
                    raise Incomplete(f"value edges without a value for {n}")
                for i in d["localApplications"]:
                    self.expr_hash(i)
                shape = d["shape"]
                if isinstance(shape, dict) and "rules" in shape:
                    for rule in shape["rules"]:
                        self.expr_hash(rule["rhs"])
                        if not self.expression_dependencies(rule["rhs"]) <= set(d["shapeDeps"]):
                            raise Incomplete(f"omitted recursor rule edge of {n}")
            saved = {name_of(s["name"]) for s in self.raw["saved"]}
            expected = {n for n, d in self.decls.items() if d["kind"] == "theorem"}
            if saved != expected or len(saved) != len(self.raw["saved"]):
                raise Incomplete("retained theorem inventory mismatch")
            for artifact in self.raw["saved"]:
                declaration = self.decls[name_of(artifact["name"])]
                if any(artifact[k] != declaration[k] for k in ("type", "value", "levels")):
                    raise Incomplete("retained artifact differs from exported declaration")
            self.versions = {n: self.decl_hash(n) for n in self.decls}
            self.nodes = []
            self.raw = None
        except (OSError, KeyError, TypeError, IndexError, RecursionError,
                json.JSONDecodeError, ValueError) as exc:
            raise Incomplete(f"INCOMPLETE COVERAGE: {exc}") from exc

    def expr_hash(self, i):
        if type(i) is not int or not 0 <= i < self.node_count:
            raise Incomplete("invalid expression reference")
        if i in self.node_hashes:
            return self.node_hashes[i]
        if i in self.visiting:
            raise Incomplete("cyclic expression graph")
        self.visiting.add(i)
        raw = self.nodes[i]
        if not isinstance(raw, dict) or len(raw) != 1:
            raise Incomplete("invalid expression node")
        tag, fields = next(iter(raw.items()))
        if tag not in REFS or not isinstance(fields, dict):
            raise Incomplete("unknown expression tag")
        data = dict(fields)
        for k in REFS[tag]:
            data[k] = self.expr_hash(data[k])
        h = data["value"] if tag == "metadata" else digest([tag, data])
        self.visiting.remove(i)
        self.node_hashes[i] = h
        return h

    def expression_dependencies(self, root):
        todo, seen, names = [root], set(), set()
        while todo:
            i = todo.pop()
            if i in seen:
                continue
            seen.add(i)
            tag, fields = next(iter(self.nodes[i].items()))
            if tag in ("const", "proj"):
                names.add(name_of(fields["name"]))
            todo.extend(fields[k] for k in REFS[tag])
        return names

    def decl_hash(self, n, contract=False):
        d = self.decls[n]
        value = d["value"]
        if contract and d["kind"] == "theorem":
            value = None
        shape = d["shape"]
        if isinstance(shape, dict) and "rules" in shape:
            shape = dict(shape, rules=[dict(r, rhs=self.expr_hash(r["rhs"]))
                                      for r in shape["rules"]])
        return digest([d["kind"], d["levels"], self.expr_hash(d["type"]),
                       None if value is None else self.expr_hash(value), shape,
                       d["shapeDeps"], d["axioms"]])

    def closure(self, root, contract=False):
        todo, seen = [root], set()
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            if n not in self.decls:
                raise Incomplete(f"INCOMPLETE COVERAGE: missing dependency {n}")
            seen.add(n)
            d = self.decls[n]
            todo.extend(d["typeDeps"] + d["shapeDeps"])
            if not contract or d["kind"] != "theorem":
                todo.extend(d["valueDeps"])
        return seen

    def revision(self, root, toolchain):
        ds = sorted(self.closure(root, contract=True))
        return dict(claim=root, target=self.expr_hash(self.decls[root]["type"]),
                    context=digest(self.decls[root]["levels"]),
                    definitions=digest([(n, self.decl_hash(n, True)) for n in ds]),
                    instanceId="Kernel-generic-contract;deployment-audit-separate",
                    toolchain=toolchain)

    def inputs(self, root):
        return [(f"decl:{n}", self.versions[n]) for n in sorted(self.closure(root))]


class Index:
    def __init__(self, supports):
        self.supports = supports
        self.postings = {}
        self.maintenance = 0
        for candidate, keys in supports.items():
            for key in keys:
                self.postings.setdefault(key, set()).add(candidate)
                self.maintenance += 1

    def affected(self, changed):
        found, scans = set(), 0
        for key in changed:
            posting = self.postings.get(key, ())
            found.update(posting)
            scans += len(posting)
        return sorted(found), dict(lookups=len(changed), posting_scans=scans)

    def oracle(self, changed):
        changed = set(changed)
        found, scans = [], 0
        for candidate, keys in self.supports.items():
            touched = False
            for key in keys:
                scans += 1
                touched |= key in changed
            if touched:
                found.append(candidate)
        return sorted(found), scans


def read_events(text):
    previous, events = "genesis", []
    for line in text.splitlines():
        record = json.loads(line)
        if record["previous"] != previous or record["hash"] != digest(
                [record["previous"], record["event"]]):
            raise Incomplete("INCOMPLETE COVERAGE: corrupt journal history")
        previous = record["hash"]
        events.append(record)
    return previous, events


def append_event(path, event):
    """One atomic, durable append under a local writer lock; old evidence is never overwritten."""
    path = Path(path)
    with path.open("a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.seek(0)
        previous, _ = read_events(f.read())
        record = dict(previous=previous, event=event, hash=digest([previous, event]))
        f.write(canonical(record) + "\n")
        f.flush()
        os.fsync(f.fileno())
    return record["hash"]


def inspect_journal(path):
    head, records = read_events(Path(path).read_text())
    seeds = [r["event"] for r in records if r["event"]["kind"] == "seed"]
    obligations = seeds[0].get("roots", seeds[0].get("obligations", [])) if seeds else []
    branches = {}
    for record in records:
        e = record["event"]
        if e["kind"] == "edit":
            branches[e["edit"]] = {k:e[k] for k in ("candidate_set", "A", "B", "C", "residual", "alternatives")}
            branches[e["edit"]]["changed_keys"] = e.get("changed_keys", [])
            branches[e["edit"]]["owed_obligations"] = [
                root for root,count in e["alternatives"].items() if count == 0]
    return dict(head=head, persistent_obligations=obligations, branches=branches,
                incomplete=[r["event"] for r in records if r["event"]["kind"] == "incomplete"])


def delta(before, after):
    return sorted("decl:" + n for n in before.keys() | after.keys()
                  if before.get(n) != after.get(n))


def read_recheck(path, export):
    rows = json.loads(Path(path).read_text())
    expected = {n for n, d in export.decls.items() if d["kind"] == "theorem"}
    checks = {r["name"]: r for r in rows}
    if set(checks) != expected or len(rows) != len(checks):
        raise Incomplete("INCOMPLETE COVERAGE: kernel check inventory")
    return checks

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("inspect", "export"))
    parser.add_argument("path", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "inspect":
            print(canonical(inspect_journal(args.path)))
        else:
            exported = Export(args.path)
            print(canonical(dict(complete=True, roots=ROOTS, declarations=len(exported.decls))))
    except (Incomplete, OSError, ValueError, KeyError) as exc:
        print("INCOMPLETE COVERAGE:", exc)
        raise SystemExit(2)
