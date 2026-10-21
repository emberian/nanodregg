"""Finalize PE1 receipt-schema validation without rewriting historical evidence."""
import argparse, copy, json
from pathlib import Path
from journal import ROOTS, Export, canonical, digest, append_event, read_events, Incomplete, file_hash
from journal_pilot import HERE, IMPORTS, overlay, lean, judge, write

def migration(run,out):
    search=[HERE/".lake/build/lib/lean"]
    comparisons=json.loads((run/"comparison.json").read_text())
    receipts=[]
    for folder in [run/"base"]+[run/r["edit"] for r in comparisons]:
        labels=["judge"] if folder.name=="base" else ["oracle-status","initial-status","indexed-status"]
        migrated={}
        dest=out/folder.name;dest.mkdir()
        for label in labels:
            candidates=[p for p in folder.glob(label+"*.json") if not p.stem.endswith("-out")]
            src=max(candidates,key=lambda p:p.stat().st_mtime_ns)
            payload=json.loads(src.read_text())
            for r in payload["requests"]:
                assert r["receipt"].get("result","checked")=="checked"
                r["receipt"]["result"]="checked";r["world"]=payload["world"]
            observed,record=judge(dest,label,payload["requests"],search);receipts.append(record)
            old=json.loads(src.with_name(src.stem+"-out.json").read_text())
            assert {k:v["status"] for k,v in observed.items()}=={r["id"]:r["status"] for r in old}
            # Census verdict constructors replace the excluded calculus; compare named statuses,
            # never claim the old Closure representation is the new record type.
            migrated[label]=payload
        if folder.name!="base":
            row=next(r for r in comparisons if r["edit"]==folder.name)
            fields=("id","receipt","supports","blockers","cost")
            ident=lambda rs:digest([{k:r[k] for k in fields} for r in rs])
            assert ident(migrated["oracle-status"]["requests"])==ident(migrated["initial-status"]["requests"])
            row["legacy_candidate_set"]=row["candidate_set"]
            row["candidate_set"]=ident(migrated["oracle-status"]["requests"])
            row["receipt_result_explicit"]=True
            row["owed_obligations"]=[r for r,n in row["alternatives"].items() if n==0]
            before=migrated["initial-status"];after=migrated["oracle-status"]
            bw=dict(before["world"]);aw=dict(after["world"])
            keys=sorted(k for k in bw.keys()|aw.keys() if bw.get(k)!=aw.get(k))
            br={r["id"]:r for r in before["requests"]}
            revised=set()
            policy=[]
            for r in after["requests"]:
                if r["revision"]!=br[r["id"]]["revision"]:revised.add("revision:"+r["id"].split("/")[0])
                if r["live"]!=br[r["id"]]["live"]:policy.append(r["id"])
            keys+=sorted(revised)
            if row["edit"] in ("withdraw-reissue","exhausted","partial-audit","cost-evidence",
                    "cycle-grounding","alternative-worlds","pruning-withdrawal","global-collision"):
                keys+=["policy:"+r["id"] for r in after["requests"]]
            assert len(keys)==row["index"]["lookups"]
            row["changed_keys"]=keys
            row["changed_policy_candidates"]=policy
            append_event(run/"events.jsonl",dict(kind="edit",**row,migration_receipts=receipts[-3:],
                adapter_sources={str(p.relative_to(HERE)):file_hash(p) for p in
                [HERE/"Census/JournalRun.lean",HERE/"gates/journal.py"]}))
    write(out/"comparison.json",canonical(comparisons)+"\n")
    write(out/"receipts.json",canonical(receipts)+"\n")
    print("EXPLICIT RESULT MIGRATION GREEN",len(receipts),flush=True)

def result_tooth(seed,out):
    payload=json.loads(seed.read_text())
    row=copy.deepcopy(payload["requests"][0]);row["world"]=payload["world"]
    row["receipt"]["result"]="exhausted"
    enabled,receipt=judge(out,"exhausted-enabled",[row],[HERE/".lake/build/lib/lean"])
    assert next(iter(enabled.values()))["status"]=="receiptMismatch"
    source=(HERE/"Census/JournalRun.lean").read_text()
    old='    result, ← field j "complete" Bool⟩'
    assert source.count(old)==1
    source=source.replace(old,'    .checked, ← field j "complete" Bool⟩')
    overlay(out/"lib",["Census/JournalRun"]);write(out/"Census/JournalRun.lean",source)
    search=[out/"lib",HERE/".lake/build/lib/lean"]
    build=lean(out/"Census/JournalRun.lean",out/"adapter-build.log",search,out/"lib/Census/JournalRun.olean")
    assert build["exit"]==0
    disabled,mutant=judge(out,"exhausted-disabled",[row],search)
    assert next(iter(disabled.values()))["status"]=="verified"
    write(out/"receipts.json",canonical([receipt,build,mutant])+"\n")
    print("RECEIPT RESULT TOOTH GREEN: enabled receiptMismatch; disabled verified",flush=True)

def audit_tooth(run,out):
    current=run/"global-collision"
    overlay(out/"lib",["Census/Journal","Kernel/Proofs/Fold"])
    (out/"lib/Kernel/Proofs/Fold.olean").symlink_to(current/"lib/Kernel/Proofs/Fold.olean")
    source=(HERE/"Census/Journal.lean").read_text()
    old='if b.getAppFn.isConstOf '+chr(96)*2+'Exists && hasHash && !bounded then bad := true'
    assert source.count(old)==1
    write(out/"Census/Journal.lean",source.replace(old,old.replace("bad := true","bad := false")))
    search=[out/"lib",HERE/".lake/build/lib/lean"]
    build=lean(out/"Census/Journal.lean",out/"audit-build.log",search,out/"lib/Census/Journal.olean")
    assert build["exit"]==0
    write(out/"Audit.lean","import Census.Journal\n"+IMPORTS+"\n"+
          f'#journal_audit "{out / "disabled.json"}" '+" ".join(ROOTS)+"\n")
    receipt=lean(out/"Audit.lean",out/"disabled.log",search)
    assert receipt["exit"]==0
    enabled=json.loads((current/"audit.json").read_text())
    disabled=json.loads((out/"disabled.json").read_text())
    assert enabled[0]["globalCollisionEscape"] and not disabled[0]["globalCollisionEscape"]
    write(out/"receipts.json",canonical([build,receipt])+"\n")
    print("GLOBAL COLLISION AUDIT TOOTH GREEN: enabled finding true; disabled false",flush=True)

def history_tooth(run,out):
    _,records=read_events((run/"events.jsonl").read_text())
    records[0]["event"]["source_revision"]="tampered"
    malformed="\n".join(canonical(r) for r in records)+"\n"
    write(out/"mutated.jsonl",malformed)
    try: read_events(malformed)
    except Incomplete as exc: write(out/"enabled.log",str(exc)+"\n")
    else: raise AssertionError("tampered history accepted")
    source=(HERE/"gates/journal.py").read_text()
    old='if record["previous"] != previous or record["hash"] != digest(\n                [record["previous"], record["event"]]):'
    assert source.count(old)==1
    source=source.replace(old,"if False:")
    namespace={"__name__":"journal_mutant"}
    exec(compile(source,str(out/"journal-disabled.py"),"exec"),namespace)
    write(out/"journal-disabled.py",source)
    _,accepted=namespace["read_events"](malformed)
    assert len(accepted)==len(records)
    write(out/"disabled.log",f"ACCEPTED {len(accepted)} corrupted records with history check disabled\n")
    print("HISTORY TOOTH GREEN: corrupt journal refused; disabled accepted",flush=True)

def literal(run,out):
    current=Export(run/"global-collision/export.json")
    toolchain=(HERE/"lean-toolchain").read_text().strip()
    rev=current.revision(ROOTS[0],toolchain)
    rec=dict(revision=rev,artifact=current.expr_hash(current.decls[ROOTS[0]]["value"]),
             recipe="global-collision/Kernel/Proofs/Fold.lean",result="checked",
             inputs=current.inputs(ROOTS[0]),complete=True)
    row=dict(id=ROOTS[0]+"/new-literal",revision=rev,receipt=rec,
             world=[("decl:"+n,v) for n,v in current.versions.items()],
             live=[[1,0],[2,0],[3,0],[4,0],[9,0]],supports=[[1,0],[2,0],[3,0],[4,0]],
             blockers=[[9,0]],cost=1,budget=100)
    result,a=judge(out,"literal-audited",[row],[HERE/".lake/build/lib/lean"])
    assert next(iter(result.values()))["status"]=="pruned"
    row["live"].remove([9,0])
    result,b=judge(out,"literal-audit-withdrawn",[row],[HERE/".lake/build/lib/lean"])
    assert next(iter(result.values()))["status"]=="verified"
    write(out/"receipts.json",canonical([a,b])+"\n")
    print("LITERAL/OBLIGATION DISTINCTION GREEN: new literal checked; binding obligation pruned",flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument("--run",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True);a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=False);migration(a.run,a.out)
    for name,fn in [("result",lambda d:result_tooth(a.out/"base/judge.json",d)),
                    ("audit",lambda d:audit_tooth(a.run,d)),
                    ("history",lambda d:history_tooth(a.run,d)),
                    ("literal",lambda d:literal(a.run,d))]:
        folder=a.out/name;folder.mkdir();fn(folder)
    print("FINAL RECEIPT AND AUDIT VALIDATION GREEN",flush=True)
if __name__=="__main__":main()

