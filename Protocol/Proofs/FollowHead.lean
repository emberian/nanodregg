/-
# Protocol.Proofs.FollowHead — follow's World keeps a live object's head and its ROM, across every frame

Follow's World moves only by the steps its own machine takes (`Command.step`, on ANY frame: any
connection's continuation, any result): a step keeps follow's World, or absorbs a log page (each
event re-derived on follow's World, `absorbStep`: a Turn by `Receive.submit`, a refusal by
`Receive.judge` or `Receive.cancel`), or adopts a base, which it does only while follow's World is one
a genesis builds (`atGenesis`, checked at the step that adopts, HOSTING-43, PROTOCOL-67).

- `genesisWorld_atGenesis`: every genesis World is one adopt may replace (the honest joiner's,
  before its adopt); `atGenesis_object`: such a World holds no live object.

- `absorbStep_object_head`: one re-derived event keeps a live object live, an object, with its
  `packageOf` (KERNEL-64's `submit_object_head`; a refusal changes no cell, `refuse_live`).
- `absorbStep_rom`: one re-derived event keeps a live ROM cell, identical (`Frame.admit_rom`).
- `step_keeps`: any property of follow's World that every re-derived event keeps, and that
  `atGenesis` refutes, is kept by every step of follow's machine.
- `PackageAt`/`step_packageAt`: the instance HOSTING's member socket reads (HOSTING-42 trigger (ii)):
  a live object with package `P`, whose package cell is live and ROM, stays so, the same cell, across
  every step follow takes (`absorbStep_packageAt` per event, `packageAt_atGenesis` for the adopt).

What is not claimed: anything over a bare `World.fold` (KERNEL-64: a hand-made Turn may write slot
0), nor across a process restart (follow reopens its Store by the writer's own fold, HOST-22: the
World it persisted, which these steps produced).
-/
import Protocol.Proofs.Command
import Kernel.Proofs.ObjectHead
import Kernel.Proofs.Frame
import Kernel.Proofs.Rooted

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- A World adopt may replace (`atGenesis`) holds no live object: each of its cells is a founder's
member cell or root grant. -/
theorem atGenesis_object {E : Env D} {w : World D} (h : atGenesis w = true) {c : D} {cell : Cell}
    (hl : w.live E c = some cell) : cell.kind ≠ kindObject := by
  unfold atGenesis at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨-, hall⟩ := h
  unfold World.live World.entry at hl
  cases hg : w.trie.get (trieSpec E) (.cell c) with
  | none => simp [hg] at hl
  | some l =>
    cases l with
    | spent => simp [hg] at hl
    | entry e =>
      cases e with
      | tomb => simp [hg] at hl
      | live cell' v =>
        simp only [hg, Option.some.injEq] at hl
        subst hl
        have hk := hall _ (Trie.mem_of_getAt (trieSpec E) 0 w.trie _ _ hg)
        simp only [genesisLeaf, Bool.or_eq_true, beq_iff_eq] at hk
        rcases hk with hk | hk <;> rw [hk] <;> decide

omit [Ord D] in
/-- What `insertAll` lists is what the map listed or one of the inserted entries. -/
theorem insertAll_toList {E : Env D} {Q : Slot D × Leaf → Prop} :
    ∀ {m : Cells D} (ps : List (D × Entry)), (∀ p ∈ ps, Q (.cell p.1, .entry p.2)) →
      (∀ q ∈ m.toList, Q q) → ∀ q ∈ (insertAll E m ps).toList, Q q
  | _, [], _, h => h
  | m, p :: rest, hp, h => by
      unfold insertAll
      exact insertAll_toList (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest
        (fun q hq => hp q (List.mem_cons_of_mem _ hq))
        (fun q hq => by
          rcases Trie.keys_insAt (trieSpec E) _ _ 0 m q hq with hq | rfl
          · exact h q hq
          · exact hp p List.mem_cons_self)

/-- **A genesis World is one adopt may replace** (the floor `atGenesis` is satisfiable): no step, and
only the founders' member cells and root grants. A joiner's follow holds exactly this World until it
adopts (`nd --join`, then `nd adopt`). -/
theorem genesisWorld_atGenesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) :
    atGenesis (Receive.genesisWorld X name nonce allowance founders) = true := by
  unfold atGenesis Receive.genesisWorld
  simp only [World.genesis, Bool.and_eq_true, beq_self_eq_true, true_and, List.all_eq_true]
  refine insertAll_toList (Q := fun q => genesisLeaf q.2 = true) _ ?_ (by simp [Trie.T.toList])
  rintro ⟨id, e⟩ hq
  obtain ⟨p, -, ⟨-, he⟩ | ⟨-, he⟩⟩ := Receive.mem_founderEntries hq <;> subst he <;>
    simp [genesisLeaf, Receive.founderMember, Receive.founderRoot]

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
World a genesis builds (`atGenesis`). -/
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

/-- One re-derived event keeps `PackageAt` (`absorbStep_object_head`, `absorbStep_rom`). -/
theorem absorbStep_packageAt [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D}
    {e : ByteArray} {s : Kernel.Step D} {obj P : D} {pc : Cell} (hp : PackageAt X w obj P pc)
    (hs : absorbStep X w e = .ok (s, w')) : PackageAt X w' obj P pc := by
  obtain ⟨⟨cell, hl, hk, hpk⟩, hpl, hrom⟩ := hp
  obtain ⟨cell', hl', hk', hpk'⟩ := absorbStep_object_head hs hl hk
  exact ⟨⟨cell', hl', hk', hpk'.trans hpk⟩, absorbStep_rom hs hpl hrom, hrom⟩

/-- A World holding a live object is not one adopt may replace. -/
theorem packageAt_atGenesis {X : Ctx D} {w : World D} {obj P : D} {pc : Cell}
    (hp : PackageAt X w obj P pc) : atGenesis w = false := by
  obtain ⟨⟨cell, hl, hk, -⟩, -, -⟩ := hp
  cases hg : atGenesis w
  · rfl
  · exact absurd hk (atGenesis_object hg hl)

/-- **Follow's World keeps an object's package, and the package's ROM cell, across every step it
takes** (HOSTING-42 trigger (ii), at follow's own machine). -/
theorem step_packageAt [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {dc : Codec.Stream D}
    {B : Thin.Base (World D)} {me : Self D} {f f' : Follow D} {p : Persist D} {kb result : ByteArray}
    {r : Reply} {obj P : D} {pc : Cell}
    (h : step X dc B me f kb result = (f', p, r)) (hp : PackageAt X f.world obj P pc) :
    PackageAt X f'.world obj P pc :=
  step_keeps (P := fun w => PackageAt X w obj P pc) absorbStep_packageAt packageAt_atGenesis h hp

end Nanodregg.Protocol.Command
