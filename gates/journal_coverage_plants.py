"""Coverage plants derived from an actual Lean export. All malformed payloads stay in scratch."""
import argparse
import importlib.util
import json
from pathlib import Path
from journal import Export, Incomplete, ROOTS, canonical, append_event, file_hash, inspect_journal
from journal_pilot import HERE, write, lean

def mutant_class(folder, source):
    path=folder/"mutant.py";write(path,source)
    spec=importlib.util.spec_from_file_location("pe1_mutant",path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module.Export

def missing_import(folder, source, export_path):
    folder.mkdir()
    run=folder/"Missing.lean";output=folder/"absent.json"
    write(run,'import Census.Journal\nimport Kernel.Proofs.JournalMissingImport\n'+
          f'#journal_export "{output}" '+" ".join(ROOTS)+"\n")
    process=lean(run,folder/"lean.log",[HERE/".lake/build/lib/lean"])
    assert process["exit"] and not output.exists()
    try:Export(output)
    except Incomplete as e:diagnostic=str(e)
    else:raise AssertionError("missing-import environment authorized")
    write(folder/"adapter.log",diagnostic+"\n")
    history=folder/"events.jsonl"
    append_event(history,dict(kind="seed",obligations=ROOTS,export=str(export_path)))
    append_event(history,dict(kind="incomplete",owed=ROOTS,process=process,diagnostic=diagnostic))
    enabled=inspect_journal(history)
    assert enabled["persistent_obligations"]==ROOTS and enabled["incomplete"][-1]["owed"]==ROOTS
    # Disable only the missing-file refusal in a scratch copy of the real validator.
    # Reuse the actual absent output from the failed Lean import, never a fabricated diagnostic.
    old='            raise Incomplete(f"INCOMPLETE COVERAGE: {exc}") from exc'
    new=('            if isinstance(exc, FileNotFoundError):\n'
         '                self.decls = {}\n'
         '                self.versions = {}\n'
         '                return\n'+old)
    assert source.count(old)==1
    cls=mutant_class(folder,source.replace(old,new,1))
    accepted=cls(output)
    disabled=dict(complete=True,obligations=sorted(n for n in accepted.decls if n in ROOTS))
    write(folder/"disabled.json",canonical(disabled)+"\n")
    try:
        assert disabled["complete"] is False and disabled["obligations"]==ROOTS, (
            f'missing-import coverage lied: complete={disabled["complete"]}, '
            f'obligations={len(disabled["obligations"])}, expected INCOMPLETE with {len(ROOTS)} owed')
    except AssertionError as exc:
        failure=str(exc)
    else:raise AssertionError("missing-import disabling tooth did not turn red")
    write(folder/"disabled.log","PLANT RED: "+failure+"\n")
    receipt=dict(check="missing-import",process=process,expected_log=str(folder/"adapter.log"),
                 expected_line=1,actual_diagnostic=diagnostic,disabled_log=str(folder/"disabled.log"),
                 obligation_inventory=enabled["persistent_obligations"],
                 disabled_complete=disabled["complete"],disabled_obligations=disabled["obligations"])
    print("MISSING IMPORT",diagnostic,"owed",len(ROOTS),flush=True)
    print("PLANT RED:",failure,flush=True)
    return receipt

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--export",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--cases",nargs="*")
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=False)
    source=(HERE/"gates/journal.py").read_text()
    original=json.loads(a.export.read_text())
    good=Export(a.export)
    print("CONTROL COMPLETE",len(good.decls),len(ROOTS),flush=True)
    del good
    plans=[
      ("complete", 'if self.raw["schema"] != 1 or self.raw["complete"] is not True:', 'if False:'),
      ("roots", 'if self.raw["roots"] != roots:', 'if False:'),
      ("dependency", 'if any(x not in self.decls for x in d[key]):', 'if False:'),
      ("edge", 'if set(d["valueDeps"]) != self.expression_dependencies(d["value"]):', 'if False:'),
      ("saved", 'if saved != expected or len(saved) != len(self.raw["saved"]):', 'if False:'),
      ("cycle", 'raise Incomplete("cyclic expression graph")', 'return digest("disabled-cycle-check")'),
      ("artifact", 'if any(artifact[k] != declaration[k] for k in ("type", "value", "levels")):', 'if False:'),
      ("recursor", 'if not self.expression_dependencies(rule["rhs"]) <= set(d["shapeDeps"]):', 'if False:'),
    ]
    receipts=[]
    for name,old,new in plans:
        if a.cases is not None and name not in a.cases:continue
        folder=a.out/name;folder.mkdir()
        data=json.loads(a.export.read_text())
        if name=="complete":data["complete"]=False
        if name=="roots":data["roots"].pop()
        if name=="dependency":
            victim=next(d["name"] for d in data["declarations"] if d["kind"]=="definition")
            data["declarations"]=[d for d in data["declarations"] if d["name"]!=victim]
        if name=="edge":
            victim=next(d for d in data["declarations"] if d["name"]==ROOTS[4])
            assert victim["valueDeps"];victim["valueDeps"].pop()
        if name=="saved":data["saved"].pop()
        if name=="cycle":data["nodes"].append({"metadata":{"value":len(data["nodes"])}})
        if name=="artifact":data["saved"][0]["value"]=data["saved"][1]["value"]
        if name=="recursor":
            victim=next(d for d in data["declarations"] if isinstance(d["shape"],dict)
                        and d["shape"].get("rules") and d["shapeDeps"])
            victim["shapeDeps"]=[]
        path=folder/"input.json";write(path,canonical(data));del data
        try:
            Export(path)
        except Incomplete as e:
            diagnostic=str(e)
        else:
            raise AssertionError("malformed export accepted: "+name)
        write(folder/"enabled.log",diagnostic+"\n")
        print(name,diagnostic,flush=True)
        assert old in source
        cls=mutant_class(folder,source.replace(old,new,1))
        cls(path)
        write(folder/"disabled.log","PLANT RED: disabled "+name+" check accepted the real mutated export\n")
        receipt=dict(check=name,input=str(path),input_hash=file_hash(path),
                     expected_log=str(folder/"enabled.log"),expected_line=1,
                     actual_diagnostic=diagnostic,disabled_log=str(folder/"disabled.log"),
                     obligation_inventory=ROOTS)
        receipts.append(receipt)
        print(canonical(receipt),flush=True)
    if a.cases is None or "missing-import" in a.cases:
        receipts.append(missing_import(a.out/"missing-import",source,a.export))
    write(a.out/"receipts.json",canonical(receipts)+"\n")
    if a.cases is not None:
        print("SCOPED COVERAGE PLANTS GREEN",flush=True)
        return
    print("COVERAGE PLANTS GREEN",flush=True)

if __name__=="__main__":main()
