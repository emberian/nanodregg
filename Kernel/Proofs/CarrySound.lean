/-
# Kernel.Proofs.CarrySound — what a carried World is (KERNEL-79)

A carry is the only upgrade path (law 1). It re-geneses the World from its exported state under an
authority the operator STATES. What the new World is, stated over the carried state as `host import`
decodes it (a canonical trie whose slots hold the leaves of their kinds, CODEC's `kernel/leaf-fit` and
`kernel/trie-order`):

* `carry_sound`: the stated authority passes genesis's own check (`checkAuthority`, the clause of
  `checkGenesis` that judges an authority); the World is canonical and slotted, its one authority
  cell is the stated one (`AuthorityOnly`) and `authorityOf` reads it; every entry of the carried trie
  but a live authority cell is at its slot unchanged (cells, tombstones, spent nullifiers), and nothing
  else is in it; its rows, journal, allowance and height are the carried ones; its origin commits to
  the carry (`carryOriginOf`: the four roots as exported, so the OLD authority cell is in the new
  origin's input as provenance, and the stated authority whole) and its chain starts there;
* `carry_tomb`: a retired id stays retired;
* `carry_meter`, `carry_meterAt`, `carry_ticksUsed`: the meter is carried, leaf for leaf, and no
  refusal record or count is (they are the old log's, keyed by its origin): a member's ticks in the
  current window are what they were before the export, so a carry grants nobody a second budget;
* `carry_refusalsOk`: the carried window trie keeps the window invariant;
* `authorityOf_honest_fold_carry`: every World an honest fold reaches from the carried World bears
  the stated authority (KERNEL-69.2's honest-carrier theorem, for a carried lineage), and
  `deployed_carry_authority`: from a genesis, through an honest fold, a carry and an honest fold again,
  the authority is the one the carry stated, not the genesis's.
-/
import Kernel.Proofs.Budget
import Kernel.Proofs.AuthorityOf
import Kernel.Proofs.Refusals
import Kernel.Proofs.RefusalsCounted

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

section Trie

/-- **A carry keeps every entry of the carried trie but a live authority cell**, at its slot. -/
theorem carry_keeps {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {auth : Authority}
    {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (h : carry X name nonce fromOrigin c auth = .ok w') {s : Slot D} {l : Leaf}
    (hg : c.trie.get (trieSpec X.env) s = some l) (hl : liveAuthority s l = false) :
    w'.trie.get (trieSpec X.env) s = some l := by
  obtain ⟨⟨-, -, -, hfree, -⟩, rfl⟩ := carry_ok.mp h
  show (reauthor X c.trie auth).get (trieSpec X.env) s = some l
  rw [reauthor_get hc]
  split
  · rename_i he
    subst he
    simp [authorityFree, hg, hl] at hfree
  · rw [hg]
    simp [Option.filter, hl]

/-- **Nothing else is in the carried World's trie** but the stated authority cell. -/
theorem carry_only {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {auth : Authority}
    {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (h : carry X name nonce fromOrigin c auth = .ok w') {s : Slot D} {l : Leaf}
    (hg : w'.trie.get (trieSpec X.env) s = some l) :
    c.trie.get (trieSpec X.env) s = some l ∨
      (s = .cell (authorityId X auth) ∧ l = .entry (.live (authorityCell auth) 0)) := by
  obtain ⟨-, rfl⟩ := carry_ok.mp h
  change (reauthor X c.trie auth).get (trieSpec X.env) s = some l at hg
  rw [reauthor_get hc] at hg
  split at hg
  · exact .inr ⟨‹_›, (Option.some.inj hg).symm⟩
  · exact .inl (Option.filter_eq_some_iff.mp hg).1

/-- **A retired id stays retired** across a carry (KERNEL-70's tombstone, carried). -/
theorem carry_tomb {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {auth : Authority}
    {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (h : carry X name nonce fromOrigin c auth = .ok w') {k : D}
    (ht : c.trie.get (trieSpec X.env) (.cell k) = some (.entry .tomb)) :
    w'.trie.get (trieSpec X.env) (.cell k) = some (.entry .tomb) :=
  carry_keeps hc h ht rfl

/-- The stated authority cell is live in the carried World, at its content id. -/
theorem carry_authority_live {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (h : carry X name nonce fromOrigin c auth = .ok w') :
    w'.live X.env (authorityId X auth) = some (authorityCell auth) := by
  obtain ⟨-, rfl⟩ := carry_ok.mp h
  refine get_live (v := 0) ?_
  show (reauthor X c.trie auth).get (trieSpec X.env) _ = _
  rw [reauthor_get hc, if_pos rfl]

omit [DecidableEq D] in
theorem authority_counts {auth : Authority} (ha : auth.Fits) :
    auth.threshold < 2 ^ 64 ∧ auth.certifiers.length < 2 ^ 64 := by
  obtain ⟨hlen, -, -, hthr, -⟩ := ha
  have : Bounds.slotsPerCellMax = 1024 := rfl
  omega

/-- **The carried World's one authority cell is the stated one** (`AuthorityOnly`), given the
carried trie's nullifier slots hold `spent` (CODEC's `kernel/leaf-fit`). -/
theorem carry_authorityOnly {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (hs : ∀ s l, c.trie.get (trieSpec X.env) s = some l → Leaf.fits s l = true)
    (h : carry X name nonce fromOrigin c auth = .ok w') : AuthorityOnly X auth w' := by
  refine ⟨fun id cell hl hk => ?_, fun n l hg => ?_⟩
  · obtain ⟨v, hg⟩ := live_get hl
    obtain ⟨-, rfl⟩ := carry_ok.mp h
    change (reauthor X c.trie auth).get (trieSpec X.env) (.cell id) = _ at hg
    rw [reauthor_get hc] at hg
    split at hg
    · rename_i he
      obtain rfl := Slot.cell.inj he
      simp only [Option.some.injEq, Leaf.entry.injEq, Entry.live.injEq] at hg
      exact ⟨rfl, hg.1.symm⟩
    · obtain ⟨-, hp⟩ := Option.filter_eq_some_iff.mp hg
      simp [liveAuthority, hk] at hp
  · rcases carry_only hc h hg with hg' | ⟨he, -⟩
    · have := hs _ _ hg'
      cases l <;> simp_all [Leaf.fits]
    · cases he

end Trie

/-- **A carry is sound** (KERNEL-79). The carried World, from a carried state as `host import`
decodes it (canonical, every slot holding the leaf of its kind):

* its stated authority passes genesis's own authority check, and the World bears it: one live
  authority cell, the stated one at its content id, which `authorityOf` reads;
* it is canonical and slotted, as a genesis World is;
* every entry of the carried trie but a live authority cell (every cell, tombstone and spent
  nullifier) is at its slot unchanged, and nothing else is in it;
* its rows, journal, allowance and height are the carried ones; its origin is the carry's
  (`carryOriginOf`: the four roots as exported, the OLD authority in them, and the stated authority
  whole), and its chain starts at that origin. -/
theorem carry_sound {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {auth : Authority}
    {w' : World D} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (hs : ∀ s l, c.trie.get (trieSpec X.env) s = some l → Leaf.fits s l = true)
    (h : carry X name nonce fromOrigin c auth = .ok w') :
    checkAuthority auth = .ok () ∧
    AuthorityOnly X auth w' ∧ w'.live X.env (authorityId X auth) = some (authorityCell auth) ∧
      authorityOf w' = some auth ∧
    w'.Canon X.env ∧ w'.Slotted X.env ∧
    (∀ s l, c.trie.get (trieSpec X.env) s = some l → liveAuthority s l = false →
      w'.trie.get (trieSpec X.env) s = some l) ∧
    (∀ s l, w'.trie.get (trieSpec X.env) s = some l →
      c.trie.get (trieSpec X.env) s = some l ∨
        (s = .cell (authorityId X auth) ∧ l = .entry (.live (authorityCell auth) 0))) ∧
    w'.rows = c.rows ∧ w'.journal = c.journal ∧ w'.allowance = c.allowance ∧ w'.height = c.height ∧
    w'.origin = carryOriginOf X name nonce fromOrigin c auth ∧ w'.chain = World.genesisChain X.env w'.origin := by
  have ha : auth.Fits := (carry_ok.mp h).1.2.2.1
  have hcan : w'.Canon X.env := by
    obtain ⟨-, rfl⟩ := carry_ok.mp h
    exact reauthor_canon hc auth
  have hon := carry_authorityOnly hc hs h
  have hlv := carry_authority_live hc h
  refine ⟨checkAuthority_ok.mpr ha, hon, hlv,
    authorityOf_of_only hcan hon hlv (authority_counts ha).1 (authority_counts ha).2, hcan, ?_,
    fun _ _ hg hl => carry_keeps hc h hg hl, fun _ _ hg => carry_only hc h hg, ?_⟩
  · intro s l hg
    rcases carry_only hc h hg with hg' | ⟨rfl, rfl⟩
    · exact hs s l hg'
    · rfl
  · obtain ⟨-, rfl⟩ := carry_ok.mp h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The meter -/

/-- **The meter is carried, and nothing else of the window trie** (KERNEL-79): at every meter key
the carried World holds the exported window trie's leaf; at every refusal-window key it holds
nothing; its height and step counter are the carried height. -/
theorem carry_meter {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {auth : Authority}
    {w' : World D} (hr : Trie.Canon (refusalSpec X.env) 0 c.refusals)
    (h : carry X name nonce fromOrigin c auth = .ok w') :
    (∀ k : MeterSlot D, w'.refusals.get (refusalSpec X.env) (.meter k) = c.refusals.get (refusalSpec X.env) (.meter k)) ∧
    (∀ k : RefusalSlot D, w'.refusalAt X.env k = none) ∧ w'.height = c.height ∧ w'.steps = c.height := by
  obtain ⟨-, rfl⟩ := carry_ok.mp h
  refine ⟨fun k => ?_, fun k => ?_, rfl, rfl⟩
  · show (meterOnly X.env c.refusals).get (refusalSpec X.env) (.meter k) = _
    rw [meterOnly_get hr]
    cases c.refusals.get (refusalSpec X.env) (.meter k) <;> rfl
  · show (meterOnly X.env c.refusals).get (refusalSpec X.env) (.refusal k) = none
    rw [meterOnly_get hr]
    cases c.refusals.get (refusalSpec X.env) (.refusal k) <;> rfl

/-- **Export, then carry: every member's meter reads as before.** -/
theorem carry_meterAt {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (hr : w.RefusalsCanon X.env) (h : carry X name nonce w.origin w.carried auth = .ok w') (k : MeterSlot D) :
    w'.meterAt X.env k = w.meterAt X.env k := by
  unfold World.meterAt
  rw [(carry_meter (c := w.carried) hr h).1 k]
  rfl

/-- **A carry grants nobody a second budget**: the ticks a member has spent in the window its next
Turn lands in are what they were before the export (`checkTicks` reads them). -/
theorem carry_ticksUsed {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (hr : w.RefusalsCanon X.env) (h : carry X name nonce w.origin w.carried auth = .ok w') (m : D) :
    ticksUsed X.env w' m = ticksUsed X.env w m := by
  have hh : w'.height = w.height := (carry_meter (c := w.carried) hr h).2.2.1
  unfold ticksUsed
  rw [hh, carry_meterAt hr h]

/-- The carried window trie keeps the window invariant (`RefusalsOk`): canonical, every leaf fitting
the carried height. -/
theorem carry_refusalsOk {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (ho : w.RefusalsOk X.env) (h : carry X name nonce w.origin w.carried auth = .ok w') : w'.RefusalsOk X.env := by
  obtain ⟨-, rfl⟩ := carry_ok.mp h
  refine ⟨meterOnly_canon ho.1, fun k l hk => ?_⟩
  change (meterOnly X.env w.refusals).get (refusalSpec X.env) k = some l at hk
  rw [meterOnly_get ho.1] at hk
  exact ho.2 k l (Option.filter_eq_some_iff.mp hk).1

omit [Ord D] [DecidableEq D] in
theorem sum_map_zero {α : Type} {g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, g x = 0) → (l.map g).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_map_zero (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [Ord D] [DecidableEq D] in
theorem sum_map_filter_le {α : Type} (p : α → Bool) (g : α → Nat) :
    ∀ (l : List α), ((l.filter p).map g).sum ≤ (l.map g).sum
  | [] => by simp
  | a :: l => by
    have := sum_map_filter_le p g l
    rw [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

omit [Ord D] [DecidableEq D] in
/-- The carried meter lists the carried window trie's meter entries, in order. -/
theorem meterOnly_toList {E : Env D} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r) :
    (meterOnly E r).toList = r.toList.filter fun p => isMeter p.1 p.2 :=
  Trie.toList_retainAt _ _ [] 0 r hr.1 (under_nil (q := isMeter) _)

/-- **The carried World's counts are its records'** (`CountedOk`, KERNEL-50): it holds no record,
count or total, and its meter leaves are no more than the carried window held, which the carried
codec bounds (`carriedWindowFits`) as `refusalsCounted` bounds a World's. -/
theorem carry_countedOk {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' : World D} (hr : Trie.Canon (refusalSpec X.env) 0 c.refusals)
    (hm : (c.refusals.toList.map meterKeyOne).sum ≤ c.height % Bounds.windowMax + 1)
    (h : carry X name nonce fromOrigin c auth = .ok w') : w'.CountedOk X.env := by
  obtain ⟨-, hnone, hh, hs⟩ := carry_meter hr h
  have hl : w'.refusals.toList = c.refusals.toList.filter fun p => isMeter p.1 p.2 := by
    obtain ⟨-, rfl⟩ := carry_ok.mp h
    exact meterOnly_toList hr
  have hz : ∀ g : WindowSlot D × RefusalLeaf D → Nat, (∀ k v, g (.meter k, v) = 0) →
      (w'.refusals.toList.map g).sum = 0 := by
    intro g hg
    rw [hl]
    refine sum_map_zero fun x hx => ?_
    obtain ⟨-, hx2⟩ := List.mem_filter.mp hx
    obtain ⟨k, v⟩ := x
    cases k with
    | refusal k => simp [isMeter] at hx2
    | meter k => exact hg k v
  refine ⟨?_, fun m => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hz refusedOne (fun _ _ => rfl), hh, hs]; omega
  · unfold refusalCount
    rw [hnone, hz _ (fun _ _ => rfl)]
  · unfold refusalTotal
    rw [hnone, hz _ (fun _ _ => rfl)]
  · rw [hz _ (fun _ _ => rfl)]; exact Nat.zero_le _
  · rw [hz _ (fun _ _ => rfl)]; exact Nat.zero_le _
  · intro o win v hg
    rw [hnone] at hg
    cases hg
  · rw [hl, hh]
    exact Nat.le_trans (sum_map_filter_le _ _ _) hm

/-- The carried World holds no refused transaction id (`RefusalsDisjoint`): it holds no record. -/
theorem carry_refusalsDisjoint {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' : World D} (hr : Trie.Canon (refusalSpec X.env) 0 c.refusals)
    (h : carry X name nonce fromOrigin c auth = .ok w') : w'.RefusalsDisjoint X.env := by
  intro id hh code mb hg
  rw [(carry_meter hr h).2.1] at hg
  cases hg

/-- The carried World keeps the window invariant when the carried window trie is canonical and
every leaf fits the carried height (what the carried codec's `kernel/carried-window` checks). -/
theorem carry_refusalsOk_of {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' : World D} (hr : Trie.Canon (refusalSpec X.env) 0 c.refusals)
    (hf : ∀ k l, c.refusals.get (refusalSpec X.env) k = some l → refusalFits c.height k l = true)
    (h : carry X name nonce fromOrigin c auth = .ok w') : w'.RefusalsOk X.env := by
  obtain ⟨-, rfl⟩ := carry_ok.mp h
  refine ⟨meterOnly_canon hr, fun k l hk => ?_⟩
  change (meterOnly X.env c.refusals).get (refusalSpec X.env) k = some l at hk
  rw [meterOnly_get hr] at hk
  exact hf k l (Option.filter_eq_some_iff.mp hk).1

/-! ## The authority along the carried lineage -/

/-- **Every World an honest fold reaches from a carried World bears the stated authority**
(KERNEL-69.2 for a carried lineage): no honest step bears an authority cell, so the stated cell stays
the only one. -/
theorem authorityOf_honest_fold_carry {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w' w'' : World D} {l : List (Step D)} (hc : Trie.Canon (trieSpec X.env) 0 c.trie)
    (hs : ∀ s l, c.trie.get (trieSpec X.env) s = some l → Leaf.fits s l = true)
    (h : carry X name nonce fromOrigin c auth = .ok w') (hf : World.fold X.env w' l = .ok w'')
    (hh : Honest X w' l) : authorityOf w'' = some auth := by
  obtain ⟨ha, hon, hlv, -, hcan, -⟩ := carry_sound hc hs h
  have ha' := checkAuthority_ok.mp ha
  exact authorityOf_of_only (fold_canon hcan hf) (honest_authorityOnly hon hf hh) (fold_rom rfl hf hlv)
    (authority_counts ha').1 (authority_counts ha').2

/-- **The authority of a carried lineage is the one the carry stated, never the genesis's.** From a
checked genesis under `auth`, along an honest log, carried under `auth'`, and along an honest log
again: `authorityOf` answers `auth'`. -/
theorem deployed_carry_authority {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth auth' : Authority} {name' nonce' : ByteArray}
    {g w w' w'' : World D} {l l' : List (Step D)}
    (hg : genesis X name nonce allowance founders auth = .ok g) (hf : World.fold X.env g l = .ok w)
    (hc : carry X name' nonce' w.origin w.carried auth' = .ok w') (hf' : World.fold X.env w' l' = .ok w'')
    (hh' : Honest X w' l') : authorityOf w'' = some auth' := by
  obtain ⟨-, rfl⟩ := genesis_ok.mp hg
  have hcan : w.Canon X.env := fold_canon (receive_genesis_canon X name nonce allowance founders auth) hf
  have hsl : w.Slotted X.env := fold_slotted (receive_genesis_slotted X name nonce allowance founders auth) hf
  exact authorityOf_honest_fold_carry (c := w.carried) hcan hsl hc hf' hh'

end Nanodregg.Kernel.Receive
