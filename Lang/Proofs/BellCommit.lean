/-
# Lang.Proofs.BellCommit — the World that commits an answer holds the answered ring (HOSTING-44)

`Lang.Proofs.Bell.answer_run` states the run: a returned `answer` writes exactly the upsert of
`rings` at the ring's key to `answeredVal x y` and the retract of `pending` there. This module states
what the World holds after the kernel commits such a call:

* `answer_commits`: a signed call invoking a Bell's `answer` (its object's live cell names a package
  read as a Bell at the call's pins), derived by `receive` and admitted by `World.admit` from
  canonical rows: the World it leaves holds at `rings` of the object, at the ring's key, the row
  `answeredVal x y` (amount 0, some version), and no `pending` row there.

The join: the signed invoke is the walk's root (`dispatched_of_signed`), its row acts are touches of
the sealed Turn (`dispatched_invoke_rows`), and an admitted upsert or retract decides its slot
(`Kernel.admit_upsert_row`, `Kernel.admit_retract_row`).
-/
import Lang.Proofs.Bell
import Lang.Proofs.DispatchRows

namespace Nanodregg.Lang.Bell

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- **The World that commits an answer holds the answered ring** (HOSTING-44's World grain; cv
01a16821-5828). A signed call invoking method `m` of object `o`, where `o`'s live cell names package
`P`, `P` reads as a Bell `pk` at the call's pins and labels `m` `answer`, which `receive` turns into
`t` and `World.admit` admits from canonical rows to `w'`: its arguments decode to
`answerData nb x k y`, and `w'` holds at `rings` (relation 1) of `o`, at the ring's key `(k, nb)`,
the row with value `answeredVal x y` (`answered (some (ask y))`, captured `ask {text := x}`; amount
0, some version), and no `pending` row (relation 0) at that key. -/
theorem answer_commits {rc : Lang.ReceiptCheck} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {o P : D} {pk : Package} {m : Nat} {sg : Sig} {args : ByteArray} {b : Nat} {via : Option D}
    (hX : X.program = Lang.program X.env.bytes X.digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke o m args b via)
    (ho : ∃ cl, w.live X.env o = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes P))
    (hid : X.digestOf (X.env.bytes P) = some P)
    (hp : readPackage (pinned X.env w c.unsigned.pins) P = .ok pk) (hs : shapeOk pk = true)
    (hres : resolveMethod (D := D) pk m = .ok ("answer", sg))
    (ha : World.admit X.env w t = .ok w') (hr : w.RowsCanon X.env) :
    ∃ nb x k y kb vb ver, Wire.decodeData answerArg args = .ok (answerData nb x k y) ∧
      keyBytes rings (keyData nb k) = some kb ∧ Wire.encodeData rings.val (answeredVal x y) = some vb ∧
      rowAt X.env w'.rows (.row ⟨o, 1, kb⟩) = some (.row 0 vb ver) ∧
      rowAt X.env w'.rows (.row ⟨o, 0, kb⟩) = none := by
  obtain ⟨cell, p, rq, new, calls, rows, used, hir, hrun, -, hcov⟩ :=
    dispatched_invoke_rows hc (dispatched_of_signed (X := X) (w := w) hb)
  obtain rfl := invokeRun_pkg hir ho hid
  rw [hX] at hrun
  obtain ⟨nb, x, k, y, kb, vb, hdec, -, -, -, -, hkb, -, hvb, hrows⟩ :=
    answer_run X.env.bytes X.digestOf hid hp hs hres hrun
  obtain ⟨hself, -, -⟩ := invokeRun_req hir
  rw [hself] at hrows
  subst hrows
  obtain ⟨τ1, h1, hs1, ha1⟩ := hcov (.row ⟨o, 1, kb⟩, .upsert 0 vb) (by simp)
  obtain ⟨τ0, h0, hs0, ha0⟩ := hcov (.row ⟨o, 0, kb⟩, .retract) (by simp)
  obtain ⟨ver, hv⟩ := admit_upsert_row hr ha h1 hs1 ha1
  exact ⟨nb, x, k, y, kb, vb, ver, hdec, hkb, hvb, hv, admit_retract_row hr ha h0 hs0 ha0⟩

end Nanodregg.Lang.Bell
