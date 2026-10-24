/-
# Lang.Proofs.BellCommit — the World that commits an answer holds the answered ring (HOSTING-44)

`Lang.Proofs.Bell.answer_run` states the run: a returned `answer` writes exactly the upsert of
`rings` at the ring's key to `answeredVal x y` and the retract of `pending` there. This module states
what the World holds after the kernel commits such a call:

* `answer_commits`: a signed call invoking a Bell's `answer` (its object's live cell names a package
  whose live cell reads as a Bell), derived by `receive` and admitted by `World.admit` from
  canonical rows: the World it leaves holds at `rings` of the object, at the ring's key, the row
  `answeredVal x y` (amount 0, some version), and no `pending` row there.

* `program_run_reads`, `pinned_read_live`: the run read its package through the call's pins, so
  the pinned read is the live cell's and is the package the caller read on its own look.

The join: the signed invoke is the walk's root (`dispatched_of_signed`), its row acts are touches of
the sealed Turn (`dispatched_invoke_rows`), and an admitted upsert or retract decides its slot
(`Kernel.admit_upsert_row`, `Kernel.admit_retract_row`).
-/
import Lang.Proofs.Bell
import Lang.Proofs.DispatchRows

namespace Nanodregg.Lang.Bell

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## What a returned run read -/

section
variable {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : ReceiptCheck}

omit [Ord D] [DecidableEq D] in
/-- The live loader reads the package it is handed (at an id that is a digest) through the look. -/
theorem loadLive_reads {rv : RowView D} {self : D} {look : Pinned D} {fuel : Nat} {idb : ByteArray}
    {id : D} {x : Loaded × Nat} (hid : digestOf idb = some id)
    (h : loadLive digestOf rv self look fuel idb ⟨[], [], []⟩ = .ok x) : ∃ p, readPackage look id = .ok p := by
  unfold loadLive loadUsing at h
  cases fuel with
  | zero => simp [indexIn] at h
  | succ n =>
    simp only [indexIn, idOf, hid] at h
    split at h
    · cases h
    · exact ⟨_, ‹_›⟩

omit [Ord D] [DecidableEq D] in
/-- **A returned run read its package through its look**: the deployed program's run of `pkg` (an
id that is a digest) returns only after `readPackage look pkg` succeeds (the live loader's first read). -/
theorem program_run_reads {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat}
    {res : Slots × List (Body D) × List (RowSlot D × RowAct) × Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (h : (program bytesOf digestOf rc).run look rv pkg state method args r budget = .ok res) :
    ∃ p, readPackage look pkg = .ok p := by
  cases hm : runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget with
  | error e => simp [program, hm, Except.map] at h
  | ok x =>
    unfold runMeasuredLive runMeasuredWith at hm
    simp only [bind, Except.bind] at hm
    split at hm
    · cases hm
    · rename_i S hS
      unfold runSetupLive runSetupWith at hS
      simp only [bind, Except.bind, pure, Except.pure] at hS
      repeat' split at hS
      all_goals first | (simp at hS; done) | skip
      all_goals exact loadLive_reads hid ‹_›

end

omit [Ord D] [DecidableEq D] in
/-- A package read depends on the look only at the package's id. -/
theorem readPackage_look {look look' : Pinned D} {P : D} (h : look P = look' P) :
    readPackage look P = readPackage look' P := by
  simp only [readPackage, readKind, h]

/-- A package read through the pins that succeeds read the World's live cell (the id was pinned). -/
theorem pinned_read_live {E : Kernel.Env D} {w : World D} {pins : List (D × D)} {P : D} {p : Package}
    (h : readPackage (pinned E w pins) P = .ok p) : pinned E w pins P = .ok (w.live E P) := by
  unfold pinned at h ⊢
  by_cases hp : (pins.any fun q => decide (q.1 = P)) = true
  · rw [if_pos hp]
  · simp [readPackage, readKind, hp, bind, Except.bind] at h

/-- **The World that commits an answer holds the answered ring** (HOSTING-44's World grain; cv
01a16821-5828). A signed call invoking method `m` of object `o`, where `o`'s live cell names package
`P` (`packageOf`), `P`'s live cell reads as a Bell `pk` (through any look that reads `P`'s cell on
`w`: follow's `worldLook`, the call's pins) and labels `m` `answer`, which `receive` turns into
`t` and `World.admit` admits from canonical rows to `w'`: its arguments decode to
`answerData nb x k y`, and `w'` holds at `rings` (relation 1) of `o`, at the ring's key `(k, nb)`,
the row with value `answeredVal x y` (`answered (some (ask y))`, captured `ask {text := x}`; amount
0, some version), and no `pending` row (relation 0) at that key. The run read `P` through the call's
pins (`program_run_reads`), so that read is the live cell's (`pinned_read_live`) and is `pk`. -/
theorem answer_commits {rc : Lang.ReceiptCheck} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {o P : D} {pk : Package} {m : Nat} {sg : Sig} {args : ByteArray} {b : Nat} {via : Option D}
    {look : Pinned D}
    (hX : X.program = Lang.program X.env.bytes X.digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke o m args b via)
    (ho : ∃ cl, w.live X.env o = some cl ∧ packageOf X o cl = .ok (some P))
    (hid : X.digestOf (X.env.bytes P) = some P)
    (hlook : look P = .ok (w.live X.env P)) (hp : readPackage look P = .ok pk) (hs : shapeOk pk = true)
    (hres : resolveMethod (D := D) pk m = .ok ("answer", sg))
    (ha : World.admit X.env w t = .ok w') (hr : w.RowsCanon X.env) :
    ∃ nb x k y kb vb ver, Wire.decodeData answerArg args = .ok (answerData nb x k y) ∧
      keyBytes rings (keyData nb k) = some kb ∧ Wire.encodeData rings.val (answeredVal x y) = some vb ∧
      rowAt X.env w'.rows (.row ⟨o, 1, kb⟩) = some (.row 0 vb ver) ∧
      rowAt X.env w'.rows (.row ⟨o, 0, kb⟩) = none := by
  obtain ⟨cell, p, rq, new, calls, rows, used, hir, hrun, -, hcov⟩ :=
    dispatched_invoke_rows hc (dispatched_of_signed (X := X) (w := w) hb)
  obtain ⟨hrk, hpk, -⟩ := invokeRun_ok hir
  obtain ⟨cl, hcl, hpo⟩ := ho
  rw [(readKind_pinned hrk).1] at hcl
  cases hcl
  rw [hpo] at hpk
  cases hpk
  rw [hX] at hrun
  obtain ⟨p', hp'⟩ := program_run_reads hid hrun
  have hpin : readPackage (pinned X.env w c.unsigned.pins) P = .ok pk := by
    rw [readPackage_look ((pinned_read_live hp').trans hlook.symm), hp]
  obtain ⟨nb, x, k, y, kb, vb, hdec, -, -, -, -, hkb, -, hvb, hrows⟩ :=
    answer_run X.env.bytes X.digestOf hid hpin hs hres hrun
  obtain ⟨hself, -, -⟩ := invokeRun_req hir
  rw [hself] at hrows
  subst hrows
  obtain ⟨τ1, h1, hs1, ha1⟩ := hcov (.row ⟨o, 1, kb⟩, .upsert 0 vb) (by simp)
  obtain ⟨τ0, h0, hs0, ha0⟩ := hcov (.row ⟨o, 0, kb⟩, .retract) (by simp)
  obtain ⟨ver, hv⟩ := admit_upsert_row hr ha h1 hs1 ha1
  exact ⟨nb, x, k, y, kb, vb, ver, hdec, hkb, hvb, hv, admit_retract_row hr ha h0 hs0 ha0⟩

end Nanodregg.Lang.Bell
