/-
The authority a World carries is the authority its genesis was made from, on every World an honest
fold reaches (KERNEL-69's honest-carrier theorem; KERNEL-69.1, KERNEL-69.2; cv 01a177f3-2293,
01a179ea-85e3; DESIGN-TRUST T3b). `authorityOf` finds the one live `kindAuthority` cell and decodes
it. No receiver bears a cell of that kind (`derive_born_not_authority`), no write reaches a ROM cell,
so the genesis authority cell stays the only one (`AuthorityOnly`, kept by every honest step) and
`authorityOf` answers it (`authorityOf_honest_fold`).
-/
import Kernel.Proofs.Rooted
import Kernel.Proofs.Cells
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


section Births

omit [Ord D] in
/-- **No receiver bears an authority cell**, anywhere in a call's tree: `enroll` bears a member,
`install` a package, `create` an object, `grant` a grant, `issue` and `account` an account; the rest
bear nothing. -/
theorem derive_born_not_authority {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {d : Draft D}
    (h : derive X look rv c = .ok d) : ∀ p ∈ d.creates, p.2.kind ≠ kindAuthority := by
  have one : ∀ (cell : Cell) (base : Nat), cell.kind ≠ kindAuthority →
      ∀ p ∈ bornAt X c base [cell], p.2.kind ≠ kindAuthority := by
    intro cell base hk p hp
    have := mem_bornAt_cell hp
    simp only [List.mem_singleton] at this
    rw [this]; exact hk
  refine derive_all (P := fun d => ∀ p ∈ d.creates, p.2.kind ≠ kindAuthority) ?_ ?_ ?_ h
  · intro a b ha hb p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp
    · exact hb p hp
  · intro _ _ _ _ p hp; simp at hp
  · intro sub wk actor b r hb h
    cases b with
    | invoke => simp [Body.isInvoke] at hb
    | enroll key next origin join via =>
        have hd := stepped_draft h
        simp only [enroll, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        simp [kindMember, kindAuthority]
    | rotate key next =>
        have hd := stepped_draft h
        simp only [rotate, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | install pkg =>
        have hd := stepped_draft h
        simp only [install, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨⟨⟩, _, hr⟩ := hd
        rw [← hr]
        exact one _ _ (by simp [kindPackage, kindAuthority])
    | create pkg laws state =>
        have hd := stepped_draft h
        simp only [create, except_bind_ok, pure, Except.pure] at hd
        obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hr⟩ := hd
        have hc : r.1.creates = bornAt X c wk.born [objectCell X actor pkg laws state] := by
          cases pkg <;>
          · simp only [except_bind_ok, Except.ok.injEq] at hr
            obtain ⟨_, _, hr⟩ := hr
            rw [← hr]
        rw [hc]
        exact one _ _ (by simp [objectCell, kindObject, kindAuthority])
    | write obj edits via =>
        have hd := stepped_draft h
        simp only [write, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | law obj laws via =>
        have hd := stepped_draft h
        simp only [law, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | grant target grantee rights parent =>
        have hd := stepped_draft h
        simp only [grant, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        exact one _ _ (by simp [kindGrant, kindAuthority])
    | retire x =>
        have hd := stepped_draft h
        simp only [retire, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, hr⟩ := hd
        rw [← hr]
        simp
    | issue cap =>
        have hd := stepped_draft h
        simp only [issue, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨⟨⟩, _, hr⟩ := hd
        rw [← hr]
        exact one _ _ (by simp [accountCell, kindAccount, kindAuthority])
    | account asset owner =>
        have hd := stepped_draft h
        simp only [account, pure, Except.pure, Except.ok.injEq] at hd
        rw [← hd]
        intro p hp
        simp only [List.mem_singleton] at hp
        rw [hp]
        simp [accountCell, kindAccount, kindAuthority]
    | transfer src dst amount via once =>
        have hd := stepped_draft h
        simp only [transfer, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        simp
    | credit well acct amount via =>
        have hd := stepped_draft h
        simp only [credit, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        simp

/-- What a derived Turn bears is never an authority cell. -/
theorem receive_born_not_authority {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (hr : receive X w c = .ok t) : ∀ cell ∈ t.born, cell.kind ≠ kindAuthority := by
  obtain ⟨d, hd, hc⟩ := receiveWith_born (receive_ok_with hr).2
  intro cell hcell
  rw [Turn.born, hc] at hcell
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcell
  exact derive_born_not_authority hd p hp

/-- Every live `kindAuthority` cell of the World is the authority cell of `auth` at its content id,
and every nullifier slot holds `spent`: with the cell live, `authorityOf` reads exactly `auth`
(`authorityOf_of_only`). -/
def AuthorityOnly (X : Ctx D) (auth : Authority) (w : World D) : Prop :=
  (∀ id cell, w.live X.env id = some cell → cell.kind = kindAuthority →
    id = authorityId X auth ∧ cell = authorityCell auth) ∧
  ∀ n l, w.trie.get (trieSpec X.env) (.nullifier n) = some l → l = .spent

/-- An admitted Turn that bears no authority cell keeps `AuthorityOnly`: what it leaves live it
bore, kept, or wrote, and a write of the authority cell is refused (ROM). -/
theorem admit_authorityOnly {X : Ctx D} {auth : Authority} {w w' : World D} {t : Turn D}
    (hw : AuthorityOnly X auth w) (hb : ∀ c ∈ t.born, c.kind ≠ kindAuthority)
    (h : World.admit X.env w t = .ok w') : AuthorityOnly X auth w' := by
  refine ⟨fun id c' hl hk => ?_, fun n l hg => ?_⟩
  · rcases admit_live h hl with hc | ⟨cell, hold, rfl | ⟨ops, hp⟩⟩
    · exact absurd hk (hb c' (List.mem_map_of_mem (f := Prod.snd) hc))
    · exact hw.1 id _ hold hk
    · obtain ⟨hkind, -, -⟩ := postWrite_keeps hp
      obtain ⟨-, rfl⟩ := hw.1 id cell hold (hkind ▸ hk)
      have hd : (authorityCell auth).discipline = .rom := rfl
      unfold postWrite at hp
      rw [hd] at hp
      cases hp
  · obtain ⟨posts, _, rfl⟩ := admit_ok h
    rw [show (commit X.env w t posts).trie = commitTrie X.env w t posts from rfl, commitTrie_nul] at hg
    split at hg
    · exact (Option.some.inj hg).symm
    · exact hw.2 n l hg

theorem refuse_authorityOnly {X : Ctx D} {auth : Authority} {w w' : World D} {r : Refused D}
    (hw : AuthorityOnly X auth w) (h : World.refuse X.env w r = .ok w') : AuthorityOnly X auth w' :=
  ⟨fun id cell hl => hw.1 id cell ((refuse_live h id).symm.trans hl),
    fun n l hg => hw.2 n l (by rw [refuse_trie h] at hg; exact hg)⟩

/-- **Every honest folded log keeps `AuthorityOnly`**: no honest step bears an authority cell. -/
theorem honest_authorityOnly {X : Ctx D} {auth : Authority} :
    ∀ {w w' : World D} {l : List (Step D)}, AuthorityOnly X auth w → World.fold X.env w l = .ok w' →
      Honest X w l → AuthorityOnly X auth w'
  | w, w', [], hw, hf, _ => by simp only [World.fold, Except.ok.injEq] at hf; subst hf; exact hw
  | w, w', .refusal r :: rest, hw, hf, hh => by
      obtain ⟨w₁, hs, -, hfr, hhr⟩ := fold_honest_cons hf hh
      have hrf : World.refuse X.env w r = .ok w₁ := hs
      exact honest_authorityOnly (refuse_authorityOnly hw hrf) hfr hhr
  | w, w', .turn t :: rest, hw, hf, hh => by
      obtain ⟨w₁, hs, ⟨c, -, hr, -⟩, hfr, hhr⟩ := fold_honest_cons hf hh
      exact honest_authorityOnly (admit_authorityOnly hw (receive_born_not_authority hr) hs) hfr hhr

/-- **`authorityOf` reads the one authority cell**: on a canonical World where the authority cell
of `auth` is live and is the only live cell of its kind, `authorityOf` answers `auth`. -/
theorem authorityOf_of_only {X : Ctx D} {auth : Authority} {w : World D} (hc : w.Canon X.env)
    (ho : AuthorityOnly X auth w) (hl : w.live X.env (authorityId X auth) = some (authorityCell auth))
    (ht : auth.threshold < 2 ^ 64) (hn : auth.certifiers.length < 2 ^ 64) : authorityOf w = some auth := by
  have hr : Trie.Routed (trieSpec X.env) 0 w.trie := hc.1
  obtain ⟨v, hg⟩ := live_get hl
  let F : Slot D × Leaf → Option Cell := fun p => match p.2 with
    | .entry (.live c _) => if c.kind = kindAuthority then some c else none
    | _ => none
  let x : Slot D × Leaf := (.cell (authorityId X auth), .entry (.live (authorityCell auth) v))
  have hx : x ∈ w.trie.toList := (Trie.mem_toList (trieSpec X.env) 0 w.trie hr _ _).mpr hg
  have hFx : F x = some (authorityCell auth) := by simp [F, x, authorityCell]
  have hall : ∀ p ∈ w.trie.toList, ∀ c', F p = some c' → p = x := by
    rintro ⟨s, l⟩ hp c' hF
    have hg' := (Trie.mem_toList (trieSpec X.env) 0 w.trie hr s l).mp hp
    cases l with
    | spent => simp [F] at hF
    | entry e =>
      cases e with
      | tomb => simp [F] at hF
      | live c'' v' =>
        have hk : c''.kind = kindAuthority := by
          by_cases hne : c''.kind = kindAuthority
          · exact hne
          · simp [F, hne] at hF
        have hg' : w.trie.get (trieSpec X.env) s = some (.entry (.live c'' v')) := hg'
        cases s with
        | nullifier n => exact absurd (ho.2 n _ hg') (by simp)
        | cell k =>
          obtain ⟨rfl, rfl⟩ := ho.1 k c'' (get_live hg') hk
          rw [hg] at hg'
          simp only [Option.some.injEq, Leaf.entry.injEq, Entry.live.injEq, true_and] at hg'
          simp [x, hg']
  have hf : w.trie.toList.filterMap F = [authorityCell auth] :=
    filterMap_eq_singleton (key := Prod.fst) (Trie.toList_nodup (trieSpec X.env) 0 w.trie hr) hx hFx hall
  show (match w.trie.toList.filterMap F with
    | [c] => authorityOfCell c
    | _ => none) = some auth
  rw [hf]
  exact authorityOfCell_authorityCell ht hn

end Births

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

/-- A genesis World holds one `kindAuthority` cell, the authority's, and no nullifier. -/
theorem genesis_authorityOnly (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Authority) :
    AuthorityOnly X auth (genesisWorld X name nonce allowance founders auth) := by
  let o := originOf X name nonce allowance founders auth
  refine ⟨fun id cell hl hk => ?_, fun n l hg => ?_⟩
  · obtain ⟨v, hg⟩ := live_get hl
    rcases insertAll_get_slot (m := Trie.T.empty) (ps := genesisEntries X o founders auth) hg with
      ⟨k, e, hs, he, hm⟩ | hm
    · simp only [Slot.cell.injEq, Leaf.entry.injEq] at hs he
      subst hs he
      rcases mem_genesisEntries hm with hm | ⟨rfl, he⟩
      · exfalso
        obtain ⟨p, _, ⟨_, h⟩ | ⟨_, h⟩⟩ := mem_founderEntries hm
        · simp only [Entry.live.injEq] at h
          rw [h.1] at hk
          simp [founderMember, kindMember, kindAuthority] at hk
        · simp only [Entry.live.injEq] at h
          rw [h.1] at hk
          simp [founderRoot, kindGrant, kindAuthority] at hk
      · simp only [Entry.live.injEq] at he
        exact ⟨rfl, he.1⟩
    · exact absurd (hm.symm.trans (Trie.get_empty _ _)) (by simp)
  · rcases insertAll_get_slot (m := Trie.T.empty) (ps := genesisEntries X o founders auth) hg with
      ⟨k, e, hs, -, -⟩ | hm
    · cases hs
    · exact absurd (hm.symm.trans (Trie.get_empty _ _)) (by simp)

/-- The authority cell is live in the genesis World, at its content id. -/
theorem genesis_authority_live (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Authority) :
    (genesisWorld X name nonce allowance founders auth).live X.env (authorityId X auth) =
      some (authorityCell auth) :=
  get_live (insertAll_append_get _ (founderEntries X _ founders) _ _)

/-- **The authority a genesis World carries is its genesis authority** (KERNEL-69): `authorityOf`
finds exactly one live `kindAuthority` cell in every genesis World, the authority cell at its
content id, and decodes the authority the genesis was made from. Premise: the authority's counts fit
a `u64` (`Authority.Fits` gives it: `authorityOf_genesis`). No hash premise: the authority is
written last, so a founder id equal to its content id is overwritten by it, not the reverse. -/
theorem authorityOf_genesisWorld (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) {auth : Authority} (ht : auth.threshold < 2 ^ 64)
    (hn : auth.certifiers.length < 2 ^ 64) :
    authorityOf (genesisWorld X name nonce allowance founders auth) = some auth :=
  authorityOf_of_only (receive_genesis_canon X name nonce allowance founders auth)
    (genesis_authorityOnly X name nonce allowance founders auth)
    (genesis_authority_live X name nonce allowance founders auth) ht hn

/-- **Every checked genesis carries its authority** (`GenesisFits`, the premise `genesis` checks). -/
theorem authorityOf_genesis {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} (hf : GenesisFits X name nonce allowance founders auth) :
    authorityOf (genesisWorld X name nonce allowance founders auth) = some auth := by
  obtain ⟨-, -, -, -, ⟨hlen, -, -, hthr, -⟩, -⟩ := hf
  have : Bounds.slotsPerCellMax = 1024 := rfl
  exact authorityOf_genesisWorld X name nonce allowance founders (by omega) (by omega)

/-- **The authority cell outlives every turn**: every World a fold reaches from a genesis World
holds the genesis authority cell, live and unchanged, at its content id (`fold_rom`: ROM is
forever), honest or not. -/
theorem fold_genesis_authority {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} {l : List (Step D)} {w' : World D}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders auth) l = .ok w') :
    w'.live X.env (authorityId X auth) = some (authorityCell auth) :=
  fold_rom rfl h (genesis_authority_live X name nonce allowance founders auth)

/-- **Every World an honest fold reaches carries the genesis authority** (KERNEL-69.2; cv
01a179ea-85e3): from a checked genesis, along any honest log (every Turn what `receive` derives,
every refusal what its re-judge records: the follower's and the writer's Worlds), `authorityOf`
answers the authority the genesis was made from. No receiver bears a `kindAuthority` cell, so the
genesis cell stays the only one. -/
theorem authorityOf_honest_fold {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} {l : List (Step D)} {w' : World D}
    (hf : GenesisFits X name nonce allowance founders auth)
    (h : World.fold X.env (genesisWorld X name nonce allowance founders auth) l = .ok w')
    (hh : Honest X (genesisWorld X name nonce allowance founders auth) l) :
    authorityOf w' = some auth := by
  obtain ⟨-, -, -, -, ⟨hlen, -, -, hthr, -⟩, -⟩ := hf
  have : Bounds.slotsPerCellMax = 1024 := rfl
  exact authorityOf_of_only (fold_canon (receive_genesis_canon X name nonce allowance founders auth) h)
    (honest_authorityOnly (genesis_authorityOnly X name nonce allowance founders auth) h hh)
    (fold_genesis_authority h) (by omega) (by omega)

end Genesis

end Nanodregg.Kernel.Receive
