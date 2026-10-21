"""Composition and derived-index check on the actual exported Kernel receipt candidates."""
import argparse
import copy
import json
from pathlib import Path
from journal import Index, canonical, digest, append_event
from journal_pilot import HERE, judge, write

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--seed",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=False)
    seed=json.loads(a.seed.read_text())
    initial=[]
    for r in seed["requests"]:
        r=copy.deepcopy(r);r["world"]=seed["world"]
        if r["id"].endswith("/recipe"):r["blockers"].append([6,0])
        r["live"].append([6,0]);initial.append(r)
    after1=copy.deepcopy(initial)
    for r in after1:r["live"].remove([1,0])
    after2=copy.deepcopy(after1)
    for r in after2:r["live"].remove([6,0])
    identity=lambda rs:digest([{k:r[k] for k in ("id","receipt","supports","blockers","cost")} for r in rs])
    assert identity(initial)==identity(after1)==identity(after2)
    supports={r["id"]:[f"token:{n}:{v}" for n,v in r["supports"]+r["blockers"]] for r in initial}
    index=Index(supports);search=[HERE/".lake/build/lib/lean"]
    cache,control=judge(a.out,"initial",initial,search)
    receipts=[control];steps=[]
    for stage,rows,changed in [("withdraw",after1,["token:1:0"]),("reopen",after2,["token:6:0"])]:
        affected,counts=index.affected(changed);oracle,scans=index.oracle(changed)
        assert affected==oracle
        subset,receipt=judge(a.out,stage+"-indexed",[r for r in rows if r["id"] in affected],search)
        full,fullreceipt=judge(a.out,stage+"-oracle",rows,search)
        cache.update(subset)
        assert cache==full
        assert sorted(k for k,v in cache.items() if v["status"]!="verified")==sorted(
            k for k,v in full.items() if v["status"]!="verified")
        steps.append(dict(stage=stage,affected=affected,index=counts,oracle_scans=scans,
                          checked=len(affected),full_checked=len(rows)))
        receipts += [receipt,fullreceipt]
    batch,receipt=judge(a.out,"batch",after2,search);receipts.append(receipt)
    assert cache==batch
    result=dict(candidate_set=identity(initial),sequential_equals_batch=True,
                residual=[k for k,v in cache.items() if v["status"]!="verified"],
                index_maintenance=index.maintenance,steps=steps,receipts=receipts)
    write(a.out/"comparison.json",canonical(result)+"\n")
    print("COMPOSITION AND INDEX GREEN",canonical(result),flush=True)

if __name__=="__main__":main()
