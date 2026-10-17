/-
# Lang.Law — the one law runner

`runLaw lib t o n r` runs the law `t` (a term of type `lawTy S` under the closure `lib`, e.g.
`get (ref g) ℓ` for the receiver, or a closed stdlib term for a test) on old state `o`, new state
`n` and request `r`, under the consensus budget `lawTicks`, and extracts its verdict under what
is left of it. The receiver (`Lang.Program.judgeOne`) and every test call THIS function, so what
a test measures of a law is what the receiver decides with it (law 1). Its meaning is
`Lang.Proofs.Std.runLaw_ok_bigStep`: an admitted law's application has an `ok` meaning.
-/
import Lang.Package
import Lang.Data

namespace Nanodregg.Lang

/-- The tick budget of one law. A consensus constant: the invoker cannot buy more of it. -/
def lawTicks : Nat := 100000

/-- Apply `t` to the values bound as `var 2, var 1, var 0` (old/state, new/argument, request). -/
def applyAt (t : Term) : Term := .app (.app (.app t (.var 2)) (.var 1)) (.var 0)

/-- Run law `t` on `o → n` under request `r`: a machine fault (`ticks` for an exhausted budget),
or the verdict: `ok`, or `refused` with the author's reason bytes. A value of another shape is
`stuck`. For a loaded package's law the machine run inside is the one `law_never_stuck`
(Lang.Proofs.Invoke) is about (`applyAt (.get (.ref g) ℓ)` is `apply3 g ℓ`), so it never ends
`stuck`, and neither does the extraction: `Lang.Proofs.LawRun.runLaw_never_stuck`. -/
def runLaw (lib : List Term) (t : Term) (o n r : Data) : Except Fault (Except ByteArray Unit) :=
  match run lib Bounds.stackMax lawTicks 0 (State.init (applyAt t) [r.toVal, n.toVal, o.toVal]) with
  | .fault f _ => .error f
  | .value v used =>
    match (Machine.mk lib).extract verdictTy (lawTicks - used) v with
    | .ok (.inj "ok" _, _) => .ok (.ok ())
    | .ok (.inj "refused" (.bytes why), _) => .ok (.error why)
    | .ok _ => .error .stuck
    | .error f => .error f

end Nanodregg.Lang
