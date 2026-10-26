/-
The authority a genesis World carries reads back as the authority it was made from (KERNEL-69's
honest-carrier theorem; cv 01a177f3-2293; DESIGN-TRUST T3b). `authorityOf` finds the one live
`kindAuthority` cell and decodes it; this file proves that on every genesis World it finds exactly
the authority cell and decodes exactly the genesis authority, and that every World a fold reaches
from it still holds that cell (ROM is forever).
-/
import Kernel.Proofs.Rooted
import Kernel.Proofs.LedgerNext
import Kernel.Proofs.Origin

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

section Lists

/-- A filterMap that keeps exactly one element of a list with distinct keys, and keeps it once. -/
theorem filterMap_eq_singleton {α β κ : Type} [DecidableEq κ] {key : α → κ} {F : α → Option β}
    {x : α} {c : β} :
    ∀ {L : List α}, (L.map key).Nodup → x ∈ L → F x = some c → (∀ p ∈ L, ∀ c', F p = some c' → p = x) →
      L.filterMap F = [c]
  | [], _, hx, _, _ => absurd hx (by simp)
  | q :: rest, hn, hx, hF, hall => by
      rw [List.map_cons, List.nodup_cons] at hn
      by_cases hq : q = x
      · subst hq
        rw [List.filterMap_cons_some hF, List.filterMap_eq_nil_iff.mpr]
        intro p hp
        cases hFp : F p with
        | none => rfl
        | some c' =>
          have := hall p (List.mem_cons_of_mem _ hp) c' hFp
          subst this
          exact absurd (List.mem_map_of_mem hp) hn.1
      · have hx' : x ∈ rest := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h.symm hq
          · exact h
        have hFq : F q = none := by
          cases hFq : F q with
          | none => rfl
          | some c' => exact absurd (hall q List.mem_cons_self c' hFq) hq
        rw [List.filterMap_cons_none hFq]
        exact filterMap_eq_singleton hn.2 hx' hF fun p hp => hall p (List.mem_cons_of_mem _ hp)

/-- In a list with distinct keys, the entries at a listed key are that one entry. -/
theorem filter_key_singleton {β : Type} {k : Nat} {v : β} :
    ∀ {ps : List (Nat × β)}, (ps.map Prod.fst).Nodup → (k, v) ∈ ps → (ps.filter fun p => p.1 == k) = [(k, v)]
  | [], _, h => absurd h (by simp)
  | q :: rest, hn, h => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.mpr]
        intro p hp hk
        exact hn.1 (by simpa [(beq_iff_eq.mp hk)] using List.mem_map_of_mem (f := Prod.fst) hp)
      · have hq : (q.1 == k) = false := by
          rw [beq_eq_false_iff_ne]
          intro hqk
          exact hn.1 (hqk ▸ List.mem_map_of_mem (f := Prod.fst) h)
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact filter_key_singleton hn.2 h

omit [Ord D] [DecidableEq D] in
/-- A slot listed once in `slotsOf` reads back as its value. -/
theorem slotsOf_get_of_mem {ps : List (Nat × ByteArray)} {k : Nat} {v : ByteArray}
    (hn : (ps.map Prod.fst).Nodup) (h : (k, v) ∈ ps) : (slotsOf ps).get k = some v := by
  rw [slotsOf_get, filter_key_singleton hn h]
  rfl

/-- `mapM` over consecutive indices, each read as the list's element there, rebuilds the list. -/
theorem mapM_range'_get {β : Type} {f : Nat → Option β} :
    ∀ (l : List β) (s : Nat), (∀ i (h : i < l.length), f (s + i) = some l[i]) →
      (List.range' s l.length).mapM f = some l
  | [], _, _ => rfl
  | a :: l, s, h => by
      rw [List.length_cons, List.range'_succ, List.mapM_cons]
      have h0 : f s = some a := by simpa using h 0 (by simp)
      have ih := mapM_range'_get l (s + 1) fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      simp [h0, ih]

/-- Shifted indices of `zipIdx` are a `range'`. -/
theorem zipIdx_map_add {β : Type} (b : Nat) :
    ∀ (l : List β) (s : Nat), (l.zipIdx s).map (fun p => b + p.2) = List.range' (b + s) l.length
  | [], _ => rfl
  | x :: l, s => by
      rw [List.zipIdx_cons, List.map_cons, zipIdx_map_add b l (s + 1), List.length_cons, List.range'_succ]
      simp [Nat.add_assoc]

end Lists

section Cell

omit [Ord D] [DecidableEq D] in
/-- **The authority cell decodes as the authority it was made from**, for every authority whose
counts fit a `u64` (every `Authority.Fits` one). -/
theorem authorityOfCell_authorityCell {a : Authority} (ht : a.threshold < 2 ^ 64)
    (hn : a.certifiers.length < 2 ^ 64) : authorityOfCell (authorityCell a) = some a := by
  have hz : a.certifiers.zipIdx.map (fun p : ByteArray × Nat => certifierBase + p.2) =
      List.range' certifierBase a.certifiers.length := by
    simpa using zipIdx_map_add certifierBase a.certifiers 0
  have hkeys : ((([(slotThreshold, countBytes a.threshold), (slotCertifierCount, countBytes a.certifiers.length)] ++
      a.certifiers.zipIdx.map fun p => (certifierBase + p.2, p.1)) : List (Nat × ByteArray)).map Prod.fst).Nodup := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def]
    rw [hz]
    simp [List.nodup_range', List.mem_range', slotThreshold, slotCertifierCount, certifierBase]
    exact ⟨fun _ _ => by omega, fun _ _ => by omega⟩
  have hc : (authorityCell a).slots.get slotCertifierCount = some (countBytes a.certifiers.length) :=
    slotsOf_get_of_mem hkeys (by simp)
  have htg : (authorityCell a).slots.get slotThreshold = some (countBytes a.threshold) :=
    slotsOf_get_of_mem hkeys (by simp)
  have hks : (List.range a.certifiers.length).mapM (fun i => (authorityCell a).slots.get (certifierBase + i)) =
      some a.certifiers := by
    rw [List.range_eq_range']
    refine mapM_range'_get (f := fun i => (authorityCell a).slots.get (certifierBase + i)) a.certifiers 0
      fun i hi => ?_
    refine slotsOf_get_of_mem hkeys (List.mem_append_right _ (List.mem_map.mpr ⟨(a.certifiers[i], i), ?_, by simp⟩))
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])
  unfold authorityOfCell
  simp [htg, hc, countOf_countBytes, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hn, hks]

end Cell

section Genesis

omit [Ord D] in
theorem insertAll_routed {E : Env D} : ∀ {m : Cells D} (ps : List (D × Entry)),
    Trie.Routed (trieSpec E) 0 m → Trie.Routed (trieSpec E) 0 (insertAll E m ps)
  | _, [], h => h
  | m, p :: rest, h => insertAll_routed (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest
      (Trie.routed_insert (trieSpec E) _ _ h)

omit [Ord D] in
/-- What `insertAll` holds at any slot: an entry it wrote at a cell slot, or what it held before. -/
theorem insertAll_get_slot {E : Env D} {s : Slot D} {l : Leaf} :
    ∀ {m : Cells D} {ps : List (D × Entry)}, (insertAll E m ps).get (trieSpec E) s = some l →
      (∃ k e, s = .cell k ∧ l = .entry e ∧ (k, e) ∈ ps) ∨ m.get (trieSpec E) s = some l
  | m, [], h => .inr h
  | m, p :: rest, h => by
      rcases insertAll_get_slot (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) (ps := rest) h
        with ⟨k, e, hs, hl, hm⟩ | hm
      · exact .inl ⟨k, e, hs, hl, List.mem_cons_of_mem _ hm⟩
      · rw [Trie.get_insert] at hm
        split at hm
        · rename_i hs
          simp only [Option.some.injEq] at hm
          exact .inl ⟨p.1, p.2, hs, hm.symm, by simp⟩
        · exact .inr hm

omit [Ord D] in
/-- The last entry `insertAll` writes is what its slot holds. -/
theorem insertAll_append_get {E : Env D} (m : Cells D) (ps : List (D × Entry)) (k : D) (e : Entry) :
    (insertAll E m (ps ++ [(k, e)])).get (trieSpec E) (.cell k) = some (.entry e) := by
  unfold insertAll
  rw [List.foldl_append]
  simp [Trie.get_insert]

/-- **The authority a genesis World carries is its genesis authority** (KERNEL-69): `authorityOf`
finds exactly one live `kindAuthority` cell in every genesis World, the authority cell at its
content id, and decodes the authority the genesis was made from. Premise: the authority's counts fit
a `u64` (`Authority.Fits` gives it: `authorityOf_genesis`). No hash premise: the authority is
written last, so a founder id equal to its content id is overwritten by it, not the reverse. -/
theorem authorityOf_genesisWorld (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) {auth : Authority} (ht : auth.threshold < 2 ^ 64)
    (hn : auth.certifiers.length < 2 ^ 64) :
    authorityOf (genesisWorld X name nonce allowance founders auth) = some auth := by
  let o := originOf X name nonce allowance founders auth
  let w := genesisWorld X name nonce allowance founders auth
  have hr : Trie.Routed (trieSpec X.env) 0 w.trie := insertAll_routed _ trivial
  let F : Slot D × Leaf → Option Cell := fun p => match p.2 with
    | .entry (.live c _) => if c.kind = kindAuthority then some c else none
    | _ => none
  let x : Slot D × Leaf := (.cell (authorityId X auth), .entry (.live (authorityCell auth) 0))
  have hx : x ∈ w.trie.toList := by
    refine (Trie.mem_toList (trieSpec X.env) 0 w.trie hr _ _).mpr ?_
    exact insertAll_append_get _ (founderEntries X o founders) _ _
  have hFx : F x = some (authorityCell auth) := by simp [F, x, authorityCell]
  have hall : ∀ p ∈ w.trie.toList, ∀ c', F p = some c' → p = x := by
    rintro ⟨s, l⟩ hp c' hF
    have hg := (Trie.mem_toList (trieSpec X.env) 0 w.trie hr s l).mp hp
    rcases insertAll_get_slot (m := Trie.T.empty) (ps := genesisEntries X o founders auth) hg with
      ⟨k, e, rfl, rfl, hm⟩ | hm
    · rcases mem_genesisEntries hm with hm | ⟨rfl, rfl⟩
      · exfalso
        obtain ⟨p, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := mem_founderEntries hm
        · simp [F, founderMember, kindMember, kindAuthority] at hF
        · simp [F, founderRoot, kindGrant, kindAuthority] at hF
      · rfl
    · exact absurd (hm.symm.trans (Trie.get_empty _ _)) (by simp)
  have hf : w.trie.toList.filterMap F = [authorityCell auth] :=
    filterMap_eq_singleton (key := Prod.fst) (Trie.toList_nodup (trieSpec X.env) 0 w.trie hr) hx hFx hall
  show (match w.trie.toList.filterMap F with
    | [c] => authorityOfCell c
    | _ => none) = some auth
  rw [hf]
  exact authorityOfCell_authorityCell ht hn

/-- **Every checked genesis carries its authority** (`GenesisFits`, the premise `genesis` checks). -/
theorem authorityOf_genesis {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} (hf : GenesisFits X name nonce allowance founders auth) :
    authorityOf (genesisWorld X name nonce allowance founders auth) = some auth := by
  obtain ⟨-, -, -, -, ⟨hlen, -, -, hthr, -⟩, -⟩ := hf
  have : Bounds.slotsPerCellMax = 1024 := rfl
  exact authorityOf_genesisWorld X name nonce allowance founders (by omega) (by omega)

/-- **The authority cell outlives every turn**: every World a fold reaches from a genesis World
holds the genesis authority cell, live and unchanged, at its content id (`fold_rom`: ROM is
forever). What it does not yet say: that no turn births a second `kindAuthority` cell, which
`authorityOf` would read as `none` (no receiver names the kind; not yet a theorem). -/
theorem fold_genesis_authority {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} {l : List (Step D)} {w' : World D}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders auth) l = .ok w') :
    w'.live X.env (authorityId X auth) = some (authorityCell auth) := by
  have hg : (genesisWorld X name nonce allowance founders auth).trie.get (trieSpec X.env)
      (.cell (authorityId X auth)) = some (.entry (.live (authorityCell auth) 0)) :=
    insertAll_append_get _ _ _ _
  have hl : (genesisWorld X name nonce allowance founders auth).live X.env (authorityId X auth) =
      some (authorityCell auth) := by
    unfold World.live World.entry
    rw [hg]
  exact fold_rom rfl h hl

end Genesis

end Nanodregg.Kernel.Receive
