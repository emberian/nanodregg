/-
# Hosting.Proofs.Package — the generated package computes the lifecycle

Each theorem is the kernel evaluating LANG's machine (`Lang.eval`) on a field of the package BODY,
applied the way `Lang.Program` applies it (`apply3`, the values `Data.toVal` makes of decoded state),
over every phase and every `last` tag. Because `phase` and `last` are sums of empty records, a
decoded state holds one of exactly these values, so the case split is exhaustive by the type.

The `owner` law reads byte strings, which the kernel cannot range over: it is pinned on two distinct
strings here, and by `hosting-sim`'s run through KERNEL's receivers and the plant that deletes it.
(The vacuity read of 10-17 moved these from the closed `checkTerm`/`targetTerm` to the body: a
`phaseLaw` with `old` and `new` swapped type-checks and passed every closed-term theorem.)
-/
import Hosting.Package
import Hosting.Text
import Hosting.Proofs.Lifecycle
import Lang.Read
import Lang.Eval

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Lang
open Nanodregg.Hosting
open Nanodregg.Hosting.Grain

/-- The fuel every evaluation below is given; each needs far less. -/
private def fuel : Nat := 400

/-- The outcome is the verdict `ok` (`true`) or `refused` with a reason (`false`), and nothing else:
a fault or a value of another shape is neither. -/
private def verdictIs (b : Bool) : Outcome → Bool
  | .value (.inj "ok" (.record [])) _ => b
  | .value (.inj "refused" (.bytes _)) _ => !b
  | _ => false

private def injIs (ℓ : String) : Outcome → Bool
  | .value (.inj m (.record [])) _ => m == ℓ
  | _ => false

theorem lastAll_complete (o : Option Event) : o ∈ lastAll := by
  rcases o with _ | e
  · decide
  · cases e <;> decide

/-! The runtime's own shape: `Lang.Program.judgeOne`/`runMethod` apply a field of the package BODY to
`[req, new, old]` (or `[req, args, state]`) as `Data.toVal` values (`apply3`). So do these. -/

/-- A state value: entry, kind and owner fixed (the phase law and the methods' phase and `last`
never read them), tag `o`, phase `p`. -/
private def stD (o : Option Event) (p : Phase) (owner : ByteArray := .empty) : Data :=
  .record [("entry", .bytes .empty), ("kind", .inj Kind.app.label unitD),
    ("last", .inj (lastLabel o) unitD), ("owner", .bytes owner), ("phase", .inj p.label unitD)]

private def rqD (principal : ByteArray := .empty) : Data :=
  .record [("agent", .bytes .empty), ("notBefore", .nat 0), ("principal", .bytes principal),
    ("validUntil", .nat 0)]

/-- Field `ℓ` of the package body applied to the three bound values. -/
private def bodyAt (ℓ : Label) : Term :=
  .app (.app (.app (.get lifecycle.body ℓ) (.var 2)) (.var 1)) (.var 0)

/-- The `phase` law, as the judge runs it, decides `admits` on `old.phase`, `new.last`, `new.phase`,
whatever `old.last` is, and never faults. -/
theorem phase_law_decides :
    ∀ p ∈ Phase.all, ∀ o' ∈ lastAll, ∀ o ∈ lastAll, ∀ q ∈ Phase.all,
      verdictIs (admits p o q)
        (eval [] fuel (bodyAt "phase") [(rqD).toVal, (stD o q).toVal, (stD o' p).toVal]) = true := by
  decide +kernel

theorem phase_law_iff (p : Phase) (o' o : Option Event) (q : Phase) :
    verdictIs (admits p o q)
      (eval [] fuel (bodyAt "phase") [(rqD).toVal, (stD o q).toVal, (stD o' p).toVal]) = true :=
  phase_law_decides p (Phase.mem_all p) o' (lastAll_complete o') o (lastAll_complete o) q
    (Phase.mem_all q)

/-- Method `e`, as `runMethod` runs it, writes `phase := target p e` and `last := e`. -/
theorem method_writes :
    ∀ p ∈ Phase.all, ∀ o ∈ lastAll, ∀ e ∈ Event.all,
      (injIs (target p e).label
          (eval [] fuel (.get (bodyAt e.label) "phase") [(rqD).toVal, unitD.toVal, (stD o p).toVal]) &&
       injIs (lastLabel (some e))
          (eval [] fuel (.get (bodyAt e.label) "last") [(rqD).toVal, unitD.toVal, (stD o p).toVal]) &&
       injIs Kind.app.label
          (eval [] fuel (.get (bodyAt e.label) "kind") [(rqD).toVal, unitD.toVal, (stD o p).toVal]))
        = true := by
  decide +kernel

/-- Method and law together: the state method `e` writes from phase `p` is admitted by the `phase`
law exactly when `(p, e)` is an edge. -/
theorem method_iff_step :
    ∀ p ∈ Phase.all, ∀ o ∈ lastAll, ∀ e ∈ Event.all,
      verdictIs (step p e).isSome
        (eval [] fuel (bodyAt "phase")
          [(rqD).toVal, (stD (some e) (target p e)).toVal, (stD o p).toVal]) = true := by
  decide +kernel

/-! The `owner` law on concrete byte strings `a ≠ b` (the kernel cannot range over all of them; the
sim's P2 plant deletes the law and must see a stranger admitted). -/

private def bA : ByteArray := "a".toUTF8
private def bB : ByteArray := "b".toUTF8

private def ownerVerdict (o : Option Event) (oldOwner newOwner principal : ByteArray) : Outcome :=
  eval [] fuel (bodyAt "owner")
    [(rqD principal).toVal, (stD o .running newOwner).toVal, (stD o .running oldOwner).toVal]

/-- Born: admitted iff the state's owner is the principal (the creator). -/
theorem owner_born :
    (verdictIs true (ownerVerdict none bA bA bA) && verdictIs false (ownerVerdict none bA bA bB))
      = true := by
  decide +kernel

/-- After birth, for every event tag: the owner may act; another principal may not; the owner may
not change. -/
theorem owner_live :
    ∀ e ∈ Event.all,
      (verdictIs true (ownerVerdict (some e) bA bA bA) &&
       verdictIs false (ownerVerdict (some e) bA bA bB) &&
       verdictIs false (ownerVerdict (some e) bA bB bA)) = true := by
  decide +kernel

/-- Both laws are in force (the judge runs exactly `lifecycle.laws`). -/
theorem laws_in_force : lifecycle.laws = ["phase", "owner"] := rfl

/-- The package passes LANG's install check with no imports. -/
theorem lifecycle_checks : (lifecycle.checkWith [] matches .ok ()) = true := by decide +kernel

/-- Method `n` is the event of index `n`. -/
theorem lifecycle_method_index (e : Event) : lifecycle.methods[e.index]? = some e.label := by
  cases e <;> rfl

/-- The text a member installs reads, by `Lang.Read`, to the package's own bytes. The kernel
cannot reach it: evaluating the printer alone (11 KB of `String` appends) did not finish in 200 s
(measured 10-17), so this is the compiler's evaluation, recorded in gates/axioms-allow.tsv. -/
theorem lifecycle_text_reads :
    ((Text.package lifecycle).bind fun t =>
      (Read.readPackage t).toOption.bind Wire.encodePackage) = Wire.encodePackage lifecycle ∧
    (Wire.encodePackage lifecycle).isSome := by
  native_decide

end Nanodregg.Hosting.Proofs
