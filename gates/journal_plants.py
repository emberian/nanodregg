"""Disable each finite Census receipt check against real exported receipt data."""
import argparse
import copy
import json
from pathlib import Path
from journal_pilot import HERE, lean, write, overlay, judge
from journal import canonical

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--seed",type=Path,required=True)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=False)
    payload=json.loads(a.seed.read_text())
    row=copy.deepcopy(payload["requests"][0]);row["world"]=payload["world"]
    source=(HERE/"Census/JournalRun.lean").read_text()
    search=[HERE/".lake/build/lib/lean"]
    control,control_receipt=judge(a.out,"control",[row],search)
    assert next(iter(control.values()))["status"]=="verified"
    changes={
        "revision": ("decide (r.revision = rev)", "true", "receiptMismatch"),
        "successful": ("decide (r.result = .checked)", "true", "receiptMismatch"),
        "complete": ("&& r.complete", "&& true", "receiptMismatch"),
        "inputs": ("r.inputs.all fun p => decide (w p.1 = some p.2)", "true", "inputMismatch"),
    }
    receipts=[]
    for name,(old,new,expected) in changes.items():
        folder=a.out/name;folder.mkdir()
        malformed=copy.deepcopy(row)
        if name=="revision":malformed["revision"]["target"]="changed"
        if name=="successful":malformed["receipt"]["result"]="exhausted"
        if name=="complete":malformed["receipt"]["complete"]=False
        if name=="inputs":malformed["world"]=[]
        enabled,observed=judge(folder,"enabled",[malformed],search)
        assert next(iter(enabled.values()))["status"]==expected
        rel=Path("Census/JournalRun.lean")
        assert source.count(old)==1
        write(folder/rel,source.replace(old,new))
        overlay(folder/"lib", [str(rel.with_suffix(""))])
        mutant_search=[folder/"lib",HERE/".lake/build/lib/lean"]
        built=lean(folder/rel,folder/"build.log",mutant_search,folder/"lib"/rel.with_suffix(".olean"))
        assert built["exit"]==0 and not built["harness_errors"]
        disabled,broken=judge(folder,"disabled",[malformed],mutant_search)
        assert next(iter(disabled.values()))["status"]=="verified"
        line=f"PLANT RED: {name} disabled accepted real receipt mutation; enabled {expected}"
        write(folder/"tooth.log",line+"\n")
        receipt=dict(check=name,control=control_receipt,enabled=observed,build=built,
                     disabled=broken,enabled_verdict=enabled,disabled_verdict=disabled,
                     real_expected_output=str(folder/"enabled-out.json"),real_expected_line=1)
        receipts.append(receipt);print(canonical(receipt),flush=True);print(line,flush=True)
    write(a.out/"receipts.json",canonical(receipts)+"\n")
    print("FOUR CENSUS RECEIPT-CHECK PLANTS GREEN",flush=True)

if __name__=="__main__":main()
