/-
# Ledger.Proofs.GrantCap — a grant moves at most what it had left, over every honest history

KERNEL-60's `Right.transfer (cap)` is spent per transfer from the grant's ledger, and KERNEL-30's
`LedgerContiguous` makes a spend READ BACK (`spend_reads_back_dispatched`, `grant_turn_ledger`). This
module lifts that to a history, as an instance of LANG's ONE chain scheme (`Std.Chain`, its state a
`World` and its request a log `Step`):

* `honest_grant_chain`: an honest folded log (every log the follower takes,
  `Kernel.Proofs.Rederive.rederiveLog_sound`) from a World whose cells are canonical, whose grants'
  ledgers are contiguous, and where `g` is a live grant, is a `Std.Chain (GrantStep X g)`: each step
  a kernel step that is honest (`World.step`, `Honest X o [s]`), from a World where those three hold
  (or `g` is already a tombstone).
* `grant_moves_le_cap` (`Std.chain_sum`, through the private scheme `spends_le_left`; its credit twin
  `grant_credits_le_cap` counts credit lines on the credit ledger): along such a log, the amounts of the transfers dispatched
  through `g` (signed, or called by an object's run at any depth), at most one per step, sum to at
  most what `g`'s transfer ledger had left at the start (its cap, for a grant no spend has touched
  yet: `grant` writes the cap as the ledger's one entry). The potential is
  `2^64 - left`; each step's weight (what it took off `left`) is paid by its rise, because what is
  left never rises (`left_falls`: a turn keeps, retires, or lowers one ledger by what it spent; a
  retired grant is a tombstone for ever, so no birth reuses its id), and a transfer through `g`
  weighs exactly its amount (`move_weight`, from the read-back).

Tooth (`Ledger.Proofs.GrantCapTooth.grant_cap_needs_contiguous`, kernel-evaluated): with every
other premise met (canonical cells, a live grant with 10 left, an honest folded log whose steps each
dispatched a transfer of 10 through it), a World whose grant's ledger has a gap moves 20: the bound
fails exactly where `LedgerContiguous` does.
-/
import Kernel.Proofs.LedgerNext
import Kernel.Proofs.Rederive
import Kernel.Proofs.Versions
import Lang.Proofs.Chain

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Kernel Nanodregg.Kernel.Receive

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- `g` is a live grant at `w`, or a tombstone. -/
def GrantOrTomb (E : Env D) (g : D) (w : World D) : Prop :=
  (∃ cell, w.live E g = some cell ∧ cell.kind = kindGrant) ∨ w.entry E g = some .tomb

/-- One honest step of a log around grant `g`, from a World `o` the read-back holds at: a kernel
step that is what its own event is decided to (`Honest X o [s]`), over canonical cells and
contiguous ledgers, with `g` a live grant or a tombstone. -/
def GrantStep (X : Ctx D) (g : D) (s : Step D) (n o : World D) : Prop :=
  (World.step X.env o s = .ok n ∧ Honest X o [s]) ∧ CellsCanon X.env o ∧ LedgerContiguous X.env o ∧
    GrantOrTomb X.env g o

/-- Step `s` from `o` dispatched a transfer of `a` through grant `g`: the turn's call (the one its
event decodes to) has, somewhere in its tree, `transfer src dst a (some g) once`. -/
def MovesThrough (X : Ctx D) (g : D) (o : World D) (s : Step D) (a : Nat) : Prop :=
  ∃ t c n wk actor src dst once, s = .turn t ∧ X.decodeCall t.event = some c ∧
    Dispatched X o c n wk actor (.transfer src dst a (some g) once)

/-- Step `s` from `o` extended a credit line of `a` through grant `g` (the credit twin of
`MovesThrough`): the turn's call has `credit well acct a (some g)` anywhere in its tree. -/
def CreditsThrough (X : Ctx D) (g : D) (o : World D) (s : Step D) (a : Nat) : Prop :=
  ∃ t c n wk actor well acct, s = .turn t ∧ X.decodeCall t.event = some c ∧
    Dispatched X o c n wk actor (.credit well acct a (some g))

/-- What `g`'s ledger at `base` has left at `w` (0 when `g` is not live or has no such ledger). -/
private def leftAt (base : Nat) (E : Env D) (g : D) (w : World D) : Nat :=
  match w.live E g with
  | some c => match ledgerLeft base g c with
    | .ok p => p.2
    | .error _ => 0
  | none => 0

private theorem leftAt_of {base : Nat} {E : Env D} {g : D} {w : World D} {c : Cell} {i l : Nat}
    (h1 : w.live E g = some c) (h2 : ledgerLeft base g c = .ok (i, l)) : leftAt base E g w = l := by
  simp [leftAt, h1, h2]

private theorem leftAt_none {base : Nat} {E : Env D} {g : D} {w : World D} (h : w.live E g = none) : leftAt base E g w = 0 := by
  simp [leftAt, h]

private theorem leftAt_lt {base : Nat} {E : Env D} {g : D} {w : World D} : leftAt base E g w < 2 ^ 64 := by
  unfold leftAt
  split
  · split
    · rename_i p hp
      exact (ledgerLeft_ok (i := p.1) (left := p.2) hp).2
    · decide
  · decide

private theorem leftAt_same {base : Nat} {E : Env D} {g : D} {w w' : World D} {c c' : Cell}
    (h1 : w.live E g = some c) (h2 : w'.live E g = some c')
    (he : ledgerLeft base g c' = ledgerLeft base g c) : leftAt base E g w' = leftAt base E g w := by
  simp [leftAt, h1, h2, he]

/-- One admitted turn keeps `g`'s entry or moves it strictly forward. -/
private theorem admit_estep {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') (g : D) :
    EStep (w.entry E g) (w'.entry E g) :=
  fold_entryStep g (l := [.turn t]) (fold_cons_ok.mpr ⟨w', h, rfl⟩)

private theorem tomb_stays {a b : Option Entry} (ha : a = some .tomb) (h : EStep a b) : b = some .tomb := by
  rcases h with rfl | h
  · exact ha
  · subst ha; rcases b with _ | (⟨_, _⟩ | _) <;> simp [EAdv] at h

private theorem live_none_tomb {E : Env D} {w w' : World D} {g : D} {c : Cell} (hl : w.live E g = some c)
    (hn : w'.live E g = none) (h : EStep (w.entry E g) (w'.entry E g)) : w'.entry E g = some .tomb := by
  unfold World.live at hl hn
  cases he : w.entry E g with
  | none => rw [he] at hl; cases hl
  | some e =>
    cases e with
    | tomb => rw [he] at hl; cases hl
    | live c0 v =>
      rw [he] at h
      cases he' : w'.entry E g with
      | none => rw [he'] at h; rcases h with h | h <;> simp [EAdv] at h
      | some e' =>
        cases e' with
        | tomb => rfl
        | live c1 v1 => rw [he'] at hn; cases hn

section Lawful
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **The invariants carry over an honest step.** -/
private theorem grant_step_keeps {X : Ctx D} {g : D} {s : Step D} {o n : World D}
    (h : GrantStep X g s n o) :
    CellsCanon X.env n ∧ LedgerContiguous X.env n ∧ GrantOrTomb X.env g n := by
  obtain ⟨hs, hcan, hlc, hinv⟩ := h
  cases s with
  | refusal r =>
      obtain ⟨hst, -⟩ := hs
      have hrf : World.refuse X.env o r = .ok n := hst
      refine ⟨fun id cell hl => hcan id cell ((refuse_live hrf id).symm.trans hl),
        fun id cell hl => hlc id cell ((refuse_live hrf id).symm.trans hl), ?_⟩
      rcases hinv with ⟨cell, hl, hk⟩ | ht
      · exact .inl ⟨cell, (refuse_live hrf g).trans hl, hk⟩
      · exact .inr ((refuse_entry hrf g).trans ht)
  | turn t =>
      obtain ⟨hst, c, -, hr, -⟩ := hs
      have ha : World.admit X.env o t = .ok n := hst
      refine ⟨admit_cellsCanon hcan ha, step_ledgerContiguous hcan hlc hr ha, ?_⟩
      rcases hinv with ⟨cell, hl, hk⟩ | ht
      · rcases grant_turn_ledger hr ha hcan hlc hl hk with hn | ⟨cell', hl', hk', -⟩
        · exact .inr (live_none_tomb hl hn (admit_estep ha g))
        · exact .inl ⟨cell', hl', hk'⟩
      · exact .inr (tomb_stays ht (admit_estep ha g))

/-- **An honest folded log is a `Std.Chain` of `GrantStep`s**, from a World where the read-back holds
and `g` is a live grant (or a tombstone). -/
theorem honest_grant_chain {X : Ctx D} {g : D} :
    ∀ {w w' : World D} {l : List (Step D)}, CellsCanon X.env w → LedgerContiguous X.env w →
      GrantOrTomb X.env g w → World.fold X.env w l = .ok w' → Honest X w l →
      ∃ steps : List (Step D × World D), steps.map Prod.fst = l ∧ Nanodregg.Lang.Std.Chain (GrantStep X g) w steps
  | w, w', [], _, _, _, _, _ => ⟨[], rfl, .nil w⟩
  | w, w', s :: rest, hcan, hlc, hinv, hf, hh => by
      obtain ⟨w₁, hs, h1, hfr, hhr⟩ := fold_honest_cons hf hh
      have hst : GrantStep X g s w₁ w := ⟨⟨hs, h1⟩, hcan, hlc, hinv⟩
      obtain ⟨hcan₁, hlc₁, hinv₁⟩ := grant_step_keeps hst
      obtain ⟨steps, hmap, hc⟩ := honest_grant_chain hcan₁ hlc₁ hinv₁ hfr hhr
      exact ⟨(s, w₁) :: steps, by simp [hmap], .cons hst hc⟩

/-- What is left at `g` never rises along a step. -/
private theorem left_falls {base : Nat} (hb0 : LedgerBase base) {X : Ctx D} {g : D} {s : Step D} {o n : World D}
    (h : GrantStep X g s n o) :
    leftAt base X.env g n ≤ leftAt base X.env g o := by
  obtain ⟨hs, hcan, hlc, hinv⟩ := h
  cases s with
  | refusal r =>
      obtain ⟨hst, -⟩ := hs
      have hrf : World.refuse X.env o r = .ok n := hst
      exact (show leftAt base X.env g n = leftAt base X.env g o by unfold leftAt; rw [refuse_live hrf g]) ▸ Nat.le_refl _
  | turn t =>
      obtain ⟨hst, c, -, hr, -⟩ := hs
      have ha : World.admit X.env o t = .ok n := hst
      rcases hinv with ⟨cell, hl, hk⟩ | ht
      · rcases grant_turn_ledger hr ha hcan hlc hl hk with hn | ⟨cell', hl', -, hkeep | ⟨b', i, left, u, hb, hll, -, hu, hll', hother⟩⟩
        · rw [leftAt_none hn]; exact Nat.zero_le _
        · exact Nat.le_of_eq (leftAt_same hl hl' (hkeep base hb0))
        · by_cases hbt : b' = base
          · subst hbt
            rw [leftAt_of hl hll, leftAt_of hl' hll']
            omega
          · exact Nat.le_of_eq (leftAt_same hl hl' (hother base hb0 (Ne.symm hbt)))
      · have hn := tomb_stays ht (admit_estep ha g)
        have : n.live X.env g = none := by unfold World.live; rw [hn]
        rw [leftAt_none this]; exact Nat.zero_le _

/-- A transfer through `g` weighs exactly its amount: what the step took off `g`'s transfer ledger. -/
private theorem move_weight {X : Ctx D} {g : D} {s : Step D} {o n : World D} {a : Nat}
    (h : GrantStep X g s n o) (hm : MovesThrough X g o s a) :
    a = leftAt transferBase X.env g o - leftAt transferBase X.env g n := by
  obtain ⟨hs, hcan, hlc, -⟩ := h
  obtain ⟨t, c, k, wk, actor, src, dst, once, rfl, hdec, hd⟩ := hm
  obtain ⟨hst, c', hdec', hr, -⟩ := hs
  have ha : World.admit X.env o t = .ok n := hst
  rw [hdec] at hdec'
  cases hdec'
  obtain ⟨gc, gc', i, left, hl, hll, hu, hl', hll'⟩ := spend_reads_back_dispatched hr ha hcan hlc hd
  rw [leftAt_of hl hll, leftAt_of hl' hll']
  omega

/-- A credit line through `g` weighs exactly its amount: what the step took off `g`'s credit ledger. -/
private theorem credit_weight {X : Ctx D} {g : D} {s : Step D} {o n : World D} {a : Nat}
    (h : GrantStep X g s n o) (hm : CreditsThrough X g o s a) :
    a = leftAt creditBase X.env g o - leftAt creditBase X.env g n := by
  obtain ⟨hs, hcan, hlc, -⟩ := h
  obtain ⟨t, c, k, wk, actor, well, acct, rfl, hdec, hd⟩ := hm
  obtain ⟨hst, c', hdec', hr, -⟩ := hs
  have ha : World.admit X.env o t = .ok n := hst
  rw [hdec] at hdec'
  cases hdec'
  obtain ⟨gc, gc', i, left, hl, hll, hu, hl', hll'⟩ := credit_reads_back_dispatched hr ha hcan hlc hd
  rw [leftAt_of hl hll, leftAt_of hl' hll']
  omega

private theorem sum_map_le {α : Type} {a f : α → Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, a x ≤ f x) → (xs.map a).sum ≤ (xs.map f).sum
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
      simp only [List.sum_cons, List.map_cons]
      exact Nat.add_le_add (h x (List.mem_cons_self ..)) (sum_map_le fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The scheme both bounds instantiate: along a `GrantStep` chain, amounts each 0 or a step's weight
on the ledger at `base` sum to at most what that ledger had left at the start (`Std.chain_sum`). -/
private theorem spends_le_left {base : Nat} (hb0 : LedgerBase base) {X : Ctx D} {g : D} {w : World D}
    {steps : List (Step D × World D)} (hc : Nanodregg.Lang.Std.Chain (GrantStep X g) w steps)
    (Moves : World D → Step D → Nat → Prop)
    (hw : ∀ s n o a, GrantStep X g s n o → Moves o s a → a = leftAt base X.env g o - leftAt base X.env g n)
    (amt : World D × Step D × World D → Nat)
    (hf : ∀ x ∈ (w :: steps.map Prod.snd).zip steps, amt x = 0 ∨ Moves x.1 x.2.1 (amt x)) :
    (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ leftAt base X.env g w := by
  have hsum := Nanodregg.Lang.Std.chain_sum (fun v => 2 ^ 64 - leftAt base X.env g v)
    (fun _ n o => leftAt base X.env g o - leftAt base X.env g n) (2 ^ 64) hc
    (fun _ n o hs _ => by
      have := left_falls hb0 hs
      have := leftAt_lt (base := base) (E := X.env) (g := g) (w := o)
      dsimp only
      omega)
    (fun _ _ => Nat.sub_le _ _) (Nat.sub_le _ _)
  have hstep : ∀ x ∈ (w :: steps.map Prod.snd).zip steps, GrantStep X g x.2.1 x.2.2 x.1 :=
    fun x hx => Nanodregg.Lang.Std.chain_always (fun rq n o => GrantStep X g rq n o) (fun _ _ _ hs => hs) hc
      x.1 x.2.1 x.2.2 hx
  have h1 := sum_map_le (a := amt) (f := fun x => leftAt base X.env g x.1 - leftAt base X.env g x.2.2)
    (xs := (w :: steps.map Prod.snd).zip steps) (fun x hx => by
      rcases hf x hx with h0 | hm
      · rw [h0]; exact Nat.zero_le _
      · exact Nat.le_of_eq (hw _ _ _ _ (hstep x hx) hm))
  simp only [] at hsum
  have := leftAt_lt (base := base) (E := X.env) (g := g) (w := w)
  omega

/-- **A grant moves at most what it had left, over every honest history** (`Std.chain_sum`). From a
World whose cells are canonical and whose grants' ledgers are contiguous (every World a follower
reaches from genesis: `genesis_cellsCanon`, `genesis_ledgerContiguous`, `honest_ledgerContiguous`),
where `g` is a live grant whose transfer ledger has `left` left, every honest folded log is a chain of
`GrantStep`s, and any choice `amt` of an amount per step, each either 0 or the amount of a transfer
the step dispatched through `g` (signed, or called by an object's run at any depth), sums to at most
`left`: what was left, never more, whatever the log. -/
theorem grant_moves_le_cap {X : Ctx D} {g : D} {w w' : World D} {l : List (Step D)} {cell : Cell}
    {i left : Nat} (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hl : w.live X.env g = some cell) (hk : cell.kind = kindGrant)
    (hleft : ledgerLeft transferBase g cell = .ok (i, left)) (hf : World.fold X.env w l = .ok w')
    (hh : Honest X w l) :
    ∃ steps : List (Step D × World D), steps.map Prod.fst = l ∧
      Nanodregg.Lang.Std.Chain (GrantStep X g) w steps ∧
      ∀ amt : World D × Step D × World D → Nat,
        (∀ x ∈ (w :: steps.map Prod.snd).zip steps, amt x = 0 ∨ MovesThrough X g x.1 x.2.1 (amt x)) →
        (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ left := by
  obtain ⟨steps, hmap, hc⟩ := honest_grant_chain hcan hlc (.inl ⟨cell, hl, hk⟩) hf hh
  refine ⟨steps, hmap, hc, fun amt hf => ?_⟩
  have := spends_le_left (.inr (.inl rfl)) hc (MovesThrough X g) (fun _ _ _ _ hs hm => move_weight hs hm) amt hf
  rwa [leftAt_of hl hleft] at this

/-- **A grant extends at most the credit it had left, over every honest history**: the credit twin
of `grant_moves_le_cap`, on the grant's credit ledger, counting the credit lines dispatched through
`g` (`CreditsThrough`). -/
theorem grant_credits_le_cap {X : Ctx D} {g : D} {w w' : World D} {l : List (Step D)} {cell : Cell}
    {i left : Nat} (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hl : w.live X.env g = some cell) (hk : cell.kind = kindGrant)
    (hleft : ledgerLeft creditBase g cell = .ok (i, left)) (hf : World.fold X.env w l = .ok w')
    (hh : Honest X w l) :
    ∃ steps : List (Step D × World D), steps.map Prod.fst = l ∧
      Nanodregg.Lang.Std.Chain (GrantStep X g) w steps ∧
      ∀ amt : World D × Step D × World D → Nat,
        (∀ x ∈ (w :: steps.map Prod.snd).zip steps, amt x = 0 ∨ CreditsThrough X g x.1 x.2.1 (amt x)) →
        (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ left := by
  obtain ⟨steps, hmap, hc⟩ := honest_grant_chain hcan hlc (.inl ⟨cell, hl, hk⟩) hf hh
  refine ⟨steps, hmap, hc, fun amt hf => ?_⟩
  have := spends_le_left (.inr (.inr rfl)) hc (CreditsThrough X g) (fun _ _ _ _ hs hm => credit_weight hs hm) amt hf
  rwa [leftAt_of hl hleft] at this

end Lawful

end

end Nanodregg.Ledger.Proofs
