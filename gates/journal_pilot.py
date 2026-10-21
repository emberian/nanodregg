#!/usr/bin/env python3
"""Reproducible PE1 scratch experiment. Writes only an explicitly supplied lane scratch.
Invoke under SWARM_MEM_MAX=6G LEAN_NUM_THREADS=2 swarm-build. No tree Kernel edits.
"""
from __future__ import annotations
import argparse
import copy
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from journal import (ROOTS, MODULES, Export, Index, Incomplete, append_event, canonical,
                     delta, digest, file_hash, read_recheck)

HERE = Path(__file__).resolve().parents[1]
FOLD, TRIE, RECEIVE, TRIPLE = [Path(m.replace(".", "/") + ".lean") for m in MODULES]
ROOT_MODULE = [FOLD, FOLD, TRIE, TRIE, RECEIVE, RECEIVE, TRIPLE, TRIPLE]
CASES = ["unrelated", "support-proof", "definition-body", "required-hypothesis",
         "unused-hypothesis", "global-collision", "hidden-projection", "simp-input",
         "withdraw-reissue", "exhausted", "pruning-withdrawal", "cost-evidence", "partial-audit"]
IMPORTS = "\n".join("import " + m for m in MODULES)
PREAMBLE = {
    FOLD: "namespace Nanodregg.Kernel\nvariable {D : Type}\n",
    TRIE: """namespace Nanodregg.Kernel.Trie
variable {K V D : Type} (S : Spec K V D) [DecidableEq K] [DecidableEq D]
variable (hL : ∀ x y, leafBody S x = leafBody S y → x = y)
  (hN : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e)
include hL hN
""",
    RECEIVE: "namespace Nanodregg.Kernel.Receive\nopen Nanodregg.Kernel\nvariable {D : Type} [Ord D] [DecidableEq D]\n",
    TRIPLE: "namespace Nanodregg.Kernel.Receive\nopen Nanodregg.Kernel\nvariable {D : Type} [Ord D] [DecidableEq D]\n",
}


def block(source, name):
    start = re.search(r"(?m)^theorem " + re.escape(name) + r"\b", source).start()
    tail = source[start:]
    end = re.search(r"\n(?:/--|/-!|end |omit |namespace |variable )", tail)
    return tail[:end.start() if end else len(tail)].rstrip() + "\n"


def split_recipe(text):
    m = re.search(r":=|\n  \|", text)
    return text[:m.start()], text[m.start():]


def source_variants(case, sources):
    changed = {}
    if case == "unrelated":
        changed[RECEIVE] = sources[RECEIVE] + "\ntheorem pe1Unrelated : (0 : Nat) = 0 := rfl\n"
    elif case in ("support-proof", "hidden-projection"):
        old = block(sources[TRIPLE], "call_frame")
        sig, body = split_recipe(old)
        term = body.removeprefix(":=").strip()
        if case == "support-proof":
            new = sig + ":= id (" + term + ")\n"
            changed[TRIPLE] = sources[TRIPLE].replace(old, new)
        else:
            helper = """structure JournalWrapper (P : Prop) : Prop where
  evidence : P
"""
            new = sig + ":= JournalWrapper.evidence ⟨(" + term + ")⟩\n"
            changed[TRIPLE] = sources[TRIPLE].replace(old, helper + new)
    elif case == "definition-body":
        old = "  ∀ w t w', P w → receive X w c = .ok t → World.admit X.env w t = .ok w' → Q w t w'"
        assert old in sources[TRIPLE]
        changed[TRIPLE] = sources[TRIPLE].replace(old, "  id (" + old.strip() + ")", 1)
    elif case in ("required-hypothesis", "unused-hypothesis"):
        old = block(sources[RECEIVE], "receive_ok_with")
        sig, body = split_recipe(old)
        target = "(h : receive X w c = .ok t)"
        extra = ("(audit : Bool) (newPremise : audit = true) " if case == "required-hypothesis"
                 else "(_unused : True) ")
        new_sig = sig.replace(target, extra + target)
        if case == "required-hypothesis":
            binders, conclusion = new_sig.rsplit(" :\n", 1)
            new_sig = binders + " :\n    (" + conclusion.strip() + ") ∧ audit = true "
            body = body.replace("exact ⟨hw, h⟩", "exact ⟨⟨hw, h⟩, newPremise⟩")
        new = new_sig + body
        alias = re.sub(r"\breceive_ok_with\b", "journalOriginalReceiveOk", old)
        text = re.sub(r"\breceive_ok_with\b", "journalOriginalReceiveOk", sources[RECEIVE])
        changed[RECEIVE] = text.replace(alias, alias + "\n" + new)
    elif case == "global-collision":
        old = block(sources[FOLD], "chain_binds")
        sig, _ = split_recipe(old)
        # Retain the genuine bounded result for the unchanged sep consumer.
        original = re.sub(r"\bchain_binds\b", "journalOriginalChainBinds", old)
        new_sig = sig.replace("[Ord D]", "").replace("Env D", "Env Bool").replace("{c : D}", "{c : Bool}").replace("Step D × D", "Step Bool × Bool")
        new_sig = new_sig.replace("CollidesAmong E.hash (chainPres E c l₁ ++ chainPres E c l₂)",
          '∃ a b : ByteArray, a ≠ b ∧ E.hash "" a = E.hash "" b')
        # Three distinct inputs, two possible hash results: the escape follows from the instance.
        helper = """
theorem journalPigeonhole (E : Env Bool) :
    ∃ a b : ByteArray, a ≠ b ∧ E.hash "" a = E.hash "" b := by
  let a := ByteArray.mk #[0]
  let b := ByteArray.mk #[1]
  let c := ByteArray.mk #[2]
  cases ha : E.hash "" a <;> cases hb : E.hash "" b <;> cases hc : E.hash "" c <;>
    first
    | exact ⟨a, b, by decide, ha.trans hb.symm⟩
    | exact ⟨a, c, by decide, ha.trans hc.symm⟩
    | exact ⟨b, c, by decide, hb.trans hc.symm⟩
"""
        new = new_sig + ":= by\n  intro _ _ _ _ _ _ _ _\n  exact Or.inr (journalPigeonhole E)\n"
        text = re.sub(r"\bchain_binds\b", "journalOriginalChainBinds", sources[FOLD])
        text = text.replace(original, original + helper + new)
        changed[FOLD] = text
    return changed


def execute(cmd, log, env=None):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with Path(log).open("w") as f:
        p = subprocess.run(["/usr/bin/time", "-f",
            '{"peak_rss_kib":%M,"user_seconds":%U,"system_seconds":%S}',
            "-o", str(log) + ".measure", *cmd], cwd=HERE, env=env, stdout=f, stderr=subprocess.STDOUT)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    text = Path(log).read_text()
    metrics = json.loads(Path(str(log) + ".measure").read_text().splitlines()[-1])
    record = dict(command=cmd, exit=p.returncode, output=str(log), output_sha256=file_hash(log),
                  peak_child_rss_kib=metrics["peak_rss_kib"],
                  user_seconds=after.ru_utime-before.ru_utime,
                  system_seconds=after.ru_stime-before.ru_stime)
    # Whole output retained, with accidental harness errors explicitly separated.
    record["harness_errors"] = [line for line in text.splitlines() if re.search(
        r"Traceback|unbound variable|No such file|no such file", line)]
    print(canonical(record), flush=True)
    return record


def lean(file, log, search, output=None, heartbeat=800000):
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(str(p) for p in search)
    env["LEAN_NUM_THREADS"] = "2"
    env["CARGO_TARGET_DIR"] = str(HERE / "target")
    args = ["lean", f"-DmaxHeartbeats={heartbeat}", "-DmaxRecDepth=4096", str(file)]
    if output:
        Path(output).parent.mkdir(parents=True, exist_ok=True)
        relative = Path(output).relative_to(search[0])
        root = Path(file).parents[len(relative.parts) - 1]
        args += ["--root=" + str(root), "-o", str(output)]
    return execute(args, log, env)


def write(path, text):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(text)


def run_recipes(folder, sources, changed, attributes, search, heartbeat=800000):
    records = []
    cresults = {}
    for root, rel in zip(ROOTS, ROOT_MODULE):
        name = root.rsplit(".", 1)[1]
        old = block(sources[rel], name)
        current = block(changed.get(rel, sources[rel]), name)
        current_sig, _ = split_recipe(current)
        _, old_body = split_recipe(old)
        recipe = re.sub(r"\b" + name + r"\b", name + "_journalRecipe", current_sig + old_body)
        path = folder / ("Recipe-" + name + ".lean")
        write(path, IMPORTS + "\n" + attributes + PREAMBLE[rel] + recipe + "\nend " + root.rsplit(".", 1)[0] + "\n")
        receipt = lean(path, folder / ("recipe-" + name + ".log"), search,
                       heartbeat=heartbeat)
        records.append(receipt)
        cresults[root] = receipt["exit"] == 0
    return cresults, records

def recipe_inventory(changed=None, attributes=""):
    changed = changed or {}
    todo = list(ROOT_MODULE)
    seen = {}
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        src = changed.get(path, (HERE / path).read_text())
        seen[path] = digest(src)
        for module in re.findall(r"(?m)^import ([A-Za-z0-9_.]+)", src):
            dep = Path(module.replace(".", "/") + ".lean")
            if (HERE / dep).exists():
                todo.append(dep)
    return sorted((str(k),v) for k,v in seen.items()) + [
        ("lean-toolchain", file_hash(HERE / "lean-toolchain")),
        ("lakefile.lean", file_hash(HERE / "lakefile.lean")),
        ("environment-attributes", digest(attributes))]

def overlay(destination, modules):
    """Read-only links to this lane's warm artifacts; never copies or writes through .lake.
    Lean resolves a package root before an individual module, so a sparse LEAN_PATH is insufficient.
    Only the explicitly mutated module's artifact family is absent and writable in the overlay.
    """
    base = HERE / ".lake/build/lib/lean"
    def visit(src, dst):
        dst.mkdir(parents=True, exist_ok=True)
        for entry in src.iterdir():
            rel = str(entry.relative_to(base))
            exact = any(rel.startswith(m + ".") for m in modules)
            below = any(m.startswith(rel + "/") for m in modules)
            target = dst / entry.name
            if exact:
                continue
            if below and entry.is_dir():
                visit(entry, target)
            else:
                target.symlink_to(entry, target_is_directory=entry.is_dir())
    visit(base, destination)

def get_case(out, case, base, sources, toolchain):
    folder = out / case
    folder.mkdir()
    changed = source_variants(case, sources)
    overlay(folder / "lib", [str(p.with_suffix("")) for p in changed])
    search = [folder / "lib", HERE / ".lake/build/lib/lean"]
    records = []
    for rel, text in changed.items():
        path = folder / rel
        write(path, text)
        record = lean(path, folder / (rel.stem + "-environment.log"), search,
                      folder / "lib" / rel.with_suffix(".olean"))
        records.append(record)
        if record["exit"]:
            raise Incomplete(f"{case}: mutation environment did not compile; {record['output']}")
    if case == "simp-input":
        attributes = "attribute [-simp] List.mem_cons\n"
    else:
        attributes = ""
    # Export and independent B. Same exact original artifact set in every B comparison.
    run = folder / "Export.lean"
    write(run, "import Census.JournalRun\n" + IMPORTS + "\n" + attributes +
          f'#journal_export "{folder / "export.json"}" ' + " ".join(ROOTS) + "\n" +
          f'#journal_recheck "{out / "base/export.json"}" "{folder / "recheck.json"}" '
          + ("1" if case == "exhausted" else "800000") + "\n" +
          f'#journal_audit "{folder / "audit.json"}" ' + " ".join(ROOTS) + "\n")
    records.append(lean(run, folder / "export-recheck.log", search))
    if records[-1]["exit"]:
        raise Incomplete(f"{case}: incomplete export/recheck; {records[-1]['output']}")
    export = Export(folder / "export.json")
    checks = read_recheck(folder / "recheck.json", base)
    cresults, recipe_records = run_recipes(folder, sources, changed, attributes, search,
                                            1 if case == "exhausted" else 800000)
    records += recipe_records
    export.recipe_environment = digest(recipe_inventory(changed, attributes))
    write(folder / "process-receipts.json", canonical(records) + "\n")
    return export, checks, cresults, records


def requests(base, current, checks, toolchain, case, folder=None, initial=False):
    rows = []
    audits = ({r["name"]: r["globalCollisionEscape"] for r in
               json.loads((folder / "audit.json").read_text())} if folder else {})
    if case == "global-collision":
        assert audits.get(ROOTS[0]), "global collision escape went undetected"
    for root in ROOTS:
      for route, receipt_token in (("retained", 1), ("recipe", 5)):
        rev = base.revision(root, toolchain)
        receipt = dict(revision=rev, artifact=base.expr_hash(base.decls[root]["value"]),
                       recipe=base.recipe_ids[root], result="checked", inputs=base.inputs(root) +
                       ([("recipe-env", base.recipe_environment)] if route == "recipe" else []), complete=True)
        live = [[1, 0], [2, 0], [3, 0], [4, 0], [5, 0]]
        blockers = [[9, 0]]
        if route == "recipe" and case == "pruning-withdrawal":
            blockers.append([6, 0])
            if initial:
                live.append([6, 0])
        if not initial:
            if case == "withdraw-reissue":
                live.remove([1, 0])
                live.append([1, 1])
            if case == "exhausted":
                live.remove([1, 0]); live.remove([5, 0])
            if case == "partial-audit":
                live.remove([2, 0])
            if case == "cost-evidence":
                live.remove([3, 0])
            if audits.get(root):
                live.append([9, 0])
        rows.append(dict(id=root + "/" + route, root=root, route=route,
                         revision=current.revision(root, toolchain), receipt=receipt,
                         world=[(f"decl:{n}", v) for n, v in current.versions.items()] +
                         [("recipe-env", current.recipe_environment)],
                         live=live, supports=[[receipt_token, 0], [2, 0], [3, 0], [4, 0]],
                         blockers=blockers, cost=1, budget=100))
    return rows


def judge(folder, label, rows, search):
    original_label = label
    version = 1
    while (folder / (label + ".json")).exists():
        label = original_label + "-repeat" + str(version)
        version += 1
    inp, dest = folder / (label + ".json"), folder / (label + "-out.json")
    write(inp, canonical(dict(world=rows[0]["world"] if rows else [],
                              requests=[{k:v for k,v in r.items() if k not in ("world", "root", "route")} for r in rows])))
    run = folder / (label + ".lean")
    write(run, f'import Census.JournalRun\n#journal_judge "{inp}" "{dest}"\n')
    receipt = lean(run, folder / (label + ".log"), search)
    if receipt["exit"]:
        raise Incomplete(f"INCOMPLETE COVERAGE: finite receipt judgment {receipt['output']}")
    return {r["id"]: r for r in json.loads(dest.read_text())}, receipt


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--cases", nargs="*", default=CASES)
    p.add_argument("--resume", action="store_true")
    args = p.parse_args()
    out = args.out.resolve()
    if out.exists() and not args.resume:
        raise SystemExit("scratch destination already exists; preserve receipts and choose a new run")
    out.mkdir(parents=True, exist_ok=args.resume)
    sources = {rel: (HERE / rel).read_text() for rel in (FOLD, TRIE, RECEIVE, TRIPLE)}
    toolchain = (HERE / "lean-toolchain").read_text().strip()
    source_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=HERE, text=True).strip()
    base_dir = out / "base"
    base_dir.mkdir(exist_ok=args.resume)
    search = [HERE / ".lake/build/lib/lean"]
    if args.resume:
        seed = json.loads((out / "events.jsonl").read_text().splitlines()[0])["event"]
        if seed["source_revision"] != source_revision or seed["recipe_inputs"] != [list(x) for x in recipe_inventory()]:
            raise Incomplete("resume source/recipe input mismatch")
        receipt = seed["receipt"]
        baseline_c_records = seed["recipe_receipts"]
        for recorded in [receipt] + baseline_c_records:
            if file_hash(recorded["output"]) != recorded["output_sha256"] or recorded["exit"]:
                raise Incomplete("resume receipt mismatch")
    else:
        run = base_dir / "Export.lean"
        write(run, "import Census.JournalRun\n" + IMPORTS + "\n" +
              f'#journal_export "{base_dir / "export.json"}" ' + " ".join(ROOTS) + "\n" +
              f'#journal_recheck "{base_dir / "export.json"}" "{base_dir / "recheck.json"}" 800000\n')
        search = [HERE / ".lake/build/lib/lean"]
        receipt = lean(run, base_dir / "export-recheck.log", search)
        if receipt["exit"]:
            raise Incomplete("base export unavailable")
    base = Export(base_dir / "export.json")
    base_checks = read_recheck(base_dir / "recheck.json", base)
    if not all(r["ok"] for r in base_checks.values()):
        bad = [r for r in base_checks.values() if not r["ok"]]
        write(base_dir / "failed-checks.json", canonical(bad))
        raise Incomplete("base retained check incomplete; see failed-checks.json")
    if not args.resume:
        baseline_c, baseline_c_records = run_recipes(base_dir, sources, {}, "", search)
        if not all(baseline_c.values()):
            raise Incomplete("baseline recipe unavailable; no recipe receipt authorized")
    base.recipe_environment = digest(recipe_inventory())
    base.recipe_ids = {r: digest(block(sources[rel], r.rsplit(".", 1)[1]))
                       for r,rel in zip(ROOTS,ROOT_MODULE)}
    journal = out / "events.jsonl"
    if not args.resume:
        append_event(journal, dict(kind="seed", source_revision=source_revision,
                                  export=file_hash(base_dir / "export.json"), roots=ROOTS,
                                  obligations=[base.revision(r, toolchain) for r in ROOTS],
                                  receipt=receipt, recipe_receipts=baseline_c_records,
                                  recipe_inputs=recipe_inventory(),
                                  tool_sources={str(path.relative_to(HERE)):file_hash(path)
                                                for path in [Path(__file__),HERE/"gates/journal.py"]}))
    candidate_ids = [r + "/" + route for r in ROOTS for route in ("retained", "recipe")]
    candidates = digest([(r, base.expr_hash(base.decls[r.split("/")[0]]["value"]),
                         base.recipe_ids[r.split("/")[0]]) for r in candidate_ids])
    base_rows = requests(base, base, base_checks, toolchain, "base")
    cached, jreceipt = judge(base_dir, "judge", base_rows, search)
    if any(v["status"] != "verified" for v in cached.values()):
        raise AssertionError("baseline receipt authority")
    supports = {r: [k for k, _ in base.inputs(r.split("/")[0])] +
                ["revision:" + r.split("/")[0], "receipt:" + r, "policy:" + r] +
                (["recipe-env"] if r.endswith("/recipe") else [])
                for r in candidate_ids}
    index = Index(supports)
    comparison = []
    for case in args.cases:
        prior = out / case
        if args.resume and (prior / "process-receipts.json").exists():
            records = json.loads((prior / "process-receipts.json").read_text())
            for recorded in records:
                if file_hash(recorded["output"]) != recorded["output_sha256"]:
                    raise Incomplete("resume external output mismatch")
            changed_sources = source_variants(case, sources)
            for rel, text in changed_sources.items():
                if (prior / rel).read_text() != text:
                    raise Incomplete("resume scratch source mismatch")
            current = Export(prior / "export.json")
            checks = read_recheck(prior / "recheck.json", base)
            cresults = {r: next(x["exit"] == 0 for x in records
                         if x["output"].endswith("recipe-" + r.rsplit(".",1)[1] + ".log")) for r in ROOTS}
            current.recipe_environment = digest(recipe_inventory(changed_sources,
                "attribute [-simp] List.mem_cons\n" if case == "simp-input" else ""))
        else:
            current, checks, cresults, records = get_case(out, case, base, sources, toolchain)
        rows = requests(base, current, checks, toolchain, case, out / case)
        folder = out / case
        full, fullreceipt = judge(folder, "oracle-status", rows, search)
        changed = delta(base.versions, current.versions)
        if base.recipe_environment != current.recipe_environment:
            changed.append("recipe-env")
        for root in ROOTS:
            if base.revision(root, toolchain) != current.revision(root, toolchain):
                changed.append("revision:" + root)
        if case in ("withdraw-reissue", "exhausted", "partial-audit", "cost-evidence",
                    "pruning-withdrawal", "global-collision"):
            changed += ["policy:" + r for r in candidate_ids]
        touched, counts = index.affected(changed)
        oracle, scans = index.oracle(changed)
        assert touched == oracle, "index affected set disagrees with list oracle"
        if case == "pruning-withdrawal":
            cached, _ = judge(folder, "initial-status",
                requests(base, base, base_checks, toolchain, case, folder, initial=True), search)
        else:
            cached, _ = judge(folder, "initial-status", base_rows, search)
        partial_rows = [r for r in rows if r["id"] in touched]
        subset, subreceipt = judge(folder, "indexed-status", partial_rows, search)
        incremental = dict(cached, **subset)
        assert incremental == full, "indexed status disagrees with full Census receipt check"
        residual = [r for r in candidate_ids if full[r]["status"] != "verified"]
        assert residual == [r for r in candidate_ids if incremental[r]["status"] != "verified"]
        bresults = {r: all(checks[n]["ok"] for n in base.closure(r) if n in checks) for r in ROOTS}
        # Identity includes the entire archived candidate, not only its human-facing ID.
        initial_rows = requests(base, base, base_checks, toolchain, case, folder, initial=True)
        candidate_data = lambda rs: [{k: r[k] for k in
          ("id", "receipt", "supports", "blockers", "cost")} for r in rs]
        assert candidate_data(initial_rows) == candidate_data(rows)
        candidates = digest(candidate_data(rows))
        row = dict(edit=case, candidate_set=candidates, candidate_count=len(candidate_ids),
                   same_candidates=True, A={r: full[r]["status"] for r in candidate_ids},
                   B=bresults, C=cresults, residual=residual, affected=touched,
                   index_maintenance_initial=index.maintenance, index_maintenance_edit=0,
                   oracle_support_scans=scans,
                   index=counts, receipt_judgments_full=len(candidate_ids), receipt_judgments_indexed=len(touched),
                   kernel_checks=sum(r.get("invoked", True) for r in checks.values()),
                   retained_artifacts=len(checks), recipe_checks=len(ROOTS),
                   alternatives={r: sum(full[r + "/" + route]["status"] == "verified"
                       for route in ("retained", "recipe")) for r in ROOTS},
                   peak_child_rss_kib=max(r["peak_child_rss_kib"] for r in records),
                   export_sha256=file_hash(folder / "export.json"))
        row["changed_keys"] = changed
        row["owed_obligations"] = [r for r, count in row["alternatives"].items() if count == 0]
        comparison.append(row)
        write(folder / "comparison.json", canonical(row) + "\n")
        append_event(journal, dict(kind="edit", **row, receipts=records + [fullreceipt, subreceipt]))
        print("CASE COMPLETE " + case, flush=True)
    write(out / "comparison.json", canonical(comparison) + "\n")
    print("PILOT COMPLETE " + str(out), flush=True)


if __name__ == "__main__":
    try:
        main()
    except Incomplete as exc:
        print("INCOMPLETE COVERAGE:", exc, flush=True)
        if "--out" in sys.argv:
            out = Path(sys.argv[sys.argv.index("--out") + 1])
            if out.exists():
                append_event(out / "events.jsonl",
                    dict(kind="incomplete", owed=ROOTS, diagnostic=str(exc)))
        raise SystemExit(2)
