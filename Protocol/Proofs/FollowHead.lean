/-
# Protocol.Proofs.FollowHead — follow's World keeps a live object's head and its ROM, across every frame

Follow's World moves only by the steps its own machine takes (`Command.step`, on ANY frame: any
connection's continuation, any result): a step keeps follow's World, or absorbs a log page (each
event re-derived on follow's World, `absorbStep`: a Turn by `Receive.submit`, a refusal by
`Receive.judge` or `Receive.cancel`), or adopts a base, which it does only while follow's World holds
nothing (`atGenesis`, checked at the step that adopts, HOSTING-43).

- `absorbStep_object_head`: one re-derived event keeps a live object live, an object, with its
  `packageOf` (KERNEL-64's `submit_object_head`; a refusal changes no cell, `refuse_live`).
- `absorbStep_rom`: one re-derived event keeps a live ROM cell, identical (`Frame.admit_rom`).
- `step_keeps`: any property of follow's World that every re-derived event keeps, and that holding
  nothing refutes, is kept by every step of follow's machine.
- `PackageAt`/`step_packageAt`: the instance HOSTING's member socket reads (HOSTING-42 trigger (ii)):
  a live object with package `P`, whose package cell is live and ROM, stays so, the same cell, across
  every step follow takes.

What is not claimed: anything over a bare `World.fold` (KERNEL-64: a hand-made Turn may write slot
0), nor across a process restart (follow reopens its Store by the writer's own fold, HOST-22: the
World it persisted, which these steps produced).
-/
import Protocol.Proofs.Command
import Kernel.Proofs.ObjectHead
import Kernel.Proofs.Frame

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- A World that holds nothing (`atGenesis`) has no live cell. -/
theorem atGenesis_live {E : Env D} {w : World D} (h : atGenesis w = true) (c : D) : w.live E c = none := by
  unfold atGenesis at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, ht⟩ := h
  unfold World.live World.entry
  split at ht
  · rename_i he
    simp [he, Trie.T.get, Trie.getAt]
  · cases ht

/-- **One re-derived event keeps a live object's package** (KERNEL-64 at follow's step). -/
theorem absorbStep_object_head [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D}
    {e : ByteArray} {s : Kernel.Step D} {obj : D} {cell : Cell}
    (h : absorbStep X w e = .ok (s, w')) (hl : w.live X.env obj = some cell) (hk : cell.kind = kindObject) :
    ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
      packageOf X obj cell' = packageOf X obj cell := by
  unfold absorbStep at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try (obtain ⟨rfl, rfl⟩ := h))
  all_goals first
    | (exact ⟨cell, (refuse_live (cancel_recorded ‹_›).2.2.2 obj).trans hl, hk, rfl⟩)
    | (exact ⟨cell, (refuse_live (judge_recorded ‹_›).2.2.2 obj).trans hl, hk, rfl⟩)
    | (obtain ⟨cell', hl', hk', hlo, -⟩ := submit_object_head ‹_› hl hk
       have hp := hlo slotPackage (by simp [slotPackage, lawBase])
       exact ⟨cell', hl', hk', by unfold packageOf; rw [hp]⟩)

/-- **One re-derived event keeps a live ROM cell** (`Frame.admit_rom`; a refusal changes no cell). -/
theorem absorbStep_rom {X : Ctx D} {w w' : World D} {e : ByteArray} {s : Kernel.Step D} {c : D}
    {cell : Cell} (h : absorbStep X w e = .ok (s, w')) (hl : w.live X.env c = some cell)
    (hrom : cell.discipline = .rom) : w'.live X.env c = some cell :=
  fold_rom hrom (fold_cons_ok (rest := []).mpr ⟨w', absorbStep_step h, rfl⟩) hl

section keeps
variable {X : Ctx D} {P : World D → Prop}

theorem absorb_keeps (hA : ∀ {w w' e s}, P w → absorbStep X w e = .ok (s, w') → P w') :
    ∀ (evs : List ByteArray) {w w' : World D} {acc ts : Array (Kernel.Step D × D)},
      absorb X w acc evs = .ok (w', ts) → P w → P w'
  | [], w, w', acc, ts, h, hp => by
    simp only [absorb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp
  | e :: es, w, w', acc, ts, h, hp => by
    unfold absorb at h
    split at h
    · rename_i s w₁ hs
      exact absorb_keeps hA es h (hA hp hs)
    · cases h

theorem absorbPage_keeps (hA : ∀ {w w' e s}, P w → absorbStep X w e = .ok (s, w') → P w')
    {w w' : World D} {evs : List ByteArray} {steps base : Nat} {chain : ByteArray}
    {ts : List (Kernel.Step D × D)} {wb? : Option (World D)}
    (h : absorbPage X w evs steps chain base = .ok (w', ts, wb?)) (hp : P w) : P w' := by
  obtain ⟨wb, tb, ts', h₁, h₂, -, -, -⟩ := absorbPage_ok h
  exact absorb_keeps hA _ h₂ (absorb_keeps hA _ h₁ hp)

/-- **Every step of follow's machine keeps what re-derivation keeps and holding nothing refutes.**
Any frame, any continuation, any result: the step leaves follow's World as it was, or moves it to
a World `absorbPage` reached (every event re-derived), or adopts a base, which it does only from a
World that holds nothing (`atGenesis`). -/
theorem step_keeps {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D} {f f' : Follow D}
    {p : Persist D} {kb result : ByteArray} {r : Reply}
    (hA : ∀ {w w' e s}, P w → absorbStep X w e = .ok (s, w') → P w')
    (hG : ∀ {w}, P w → atGenesis w = false)
    (h : step X dc B me f kb result = (f', p, r)) (hp : P f.world) : P f'.world := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (try (obtain ⟨rfl, -, -⟩ := h))
  all_goals first
    | exact hp
    | exact absorbPage_keeps hA ‹_› hp
    | (exfalso; rename_i hg _; rw [hG hp] at hg; exact hg rfl)

end keeps

/-- A live object with package `P`, whose package cell `pc` is live and ROM: what a description and
an invoke of the object both read (`describe`, `invokedPackage`, `Lang.readPackage`). -/
def PackageAt (X : Ctx D) (w : World D) (obj P : D) (pc : Cell) : Prop :=
  (∃ cell, w.live X.env obj = some cell ∧ cell.kind = kindObject ∧ packageOf X obj cell = .ok (some P)) ∧
    w.live X.env P = some pc ∧ pc.discipline = .rom

/-- **Follow's World keeps an object's package, and the package's ROM cell, across every step it
takes** (HOSTING-42 trigger (ii), at follow's own machine). -/
theorem step_packageAt [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {dc : Codec.Stream D}
    {B : Thin.Base (World D)} {me : Self D} {f f' : Follow D} {p : Persist D} {kb result : ByteArray}
    {r : Reply} {obj P : D} {pc : Cell}
    (h : step X dc B me f kb result = (f', p, r)) (hp : PackageAt X f.world obj P pc) :
    PackageAt X f'.world obj P pc := by
  refine step_keeps (P := fun w => PackageAt X w obj P pc) ?_ ?_ h hp
  · rintro w w' e s ⟨⟨cell, hl, hk, hpk⟩, hpl, hrom⟩ hs
    obtain ⟨cell', hl', hk', hpk'⟩ := absorbStep_object_head hs hl hk
    exact ⟨⟨cell', hl', hk', hpk'.trans hpk⟩, absorbStep_rom hs hpl hrom, hrom⟩
  · rintro w ⟨⟨cell, hl, -, -⟩, -, -⟩
    cases hg : atGenesis w
    · rfl
    · rw [atGenesis_live hg] at hl; cases hl

end Nanodregg.Protocol.Command
