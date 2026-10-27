/-
The authority a World carries is its genesis authority, or a rotation of it, on every World an
honest fold reaches (KERNEL-69's honest-carrier theorem; KERNEL-69.1, KERNEL-69.2; KERNEL-79; cv
01a177f3-2293, 01a179ea-85e3, 01a17a5c-fa4c; DESIGN-TRUST T3b, §4.4c). `authorityOf` finds the one
live `kindAuthority` cell and decodes it. No receiver bears a cell of that kind
(`derive_born_not_authority`), and the one receiver that writes it is a certifier's rotation to the
successor key it committed, signed by that key (`effect_at_authority`, `authority_turn`), so the
cell at `authorityId` stays the only one and decodes as a rotation of the genesis authority
(`AuthorityOnly`, kept by every honest step), and `authorityOf` answers it (`authorityOf_honest_fold`).
After a rotation only the new key certifies at its index (`rotate_retires`,
`rotateCertifier_authorityOf`).
-/
import Kernel.Proofs.Rooted
import Kernel.Proofs.Cells
import Kernel.Proofs.LedgerNext
import Kernel.Proofs.Origin
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.InvokeNext

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
/-- A `mapM` over consecutive indices that answers reads every index: its result has one element
per index, the element at `j` what the function answers at `s + j`. -/
theorem mapM_range'_some {β : Type} {f : Nat → Option β} :
    ∀ (n s : Nat) {r : List β}, (List.range' s n).mapM f = some r →
      r.length = n ∧ ∀ j, j < n → f (s + j) = r[j]?
  | 0, _, r, h => by
      simp only [List.range'_zero, List.mapM_nil, pure, Option.some.injEq] at h
      subst h; exact ⟨rfl, fun j hj => absurd hj (by omega)⟩
  | n + 1, s, r, h => by
      rw [List.range'_succ, List.mapM_cons] at h
      cases hf : f s with
      | none => simp [hf] at h
      | some b =>
        cases hm : (List.range' (s + 1) n).mapM f with
        | none => simp [hf, hm] at h
        | some bs =>
          simp only [hf, hm, Option.bind_some, pure, Option.some.injEq, bind] at h
          subst h
          obtain ⟨hl, hg⟩ := mapM_range'_some n (s + 1) hm
          refine ⟨by simp [hl], fun j hj => ?_⟩
          cases j with
          | zero => simpa using hf
          | succ j =>
            have := hg j (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

omit [Ord D] [DecidableEq D] in
/-- **The authority cell decodes as the authority it was made from**, for every authority whose
counts fit a `u64`, whose keys stay below `nextBase`, and which commits one next-key digest per
certifier (every `Authority.Fits` one). -/
theorem authorityOfCell_authorityCell {a : Authority} (ht : a.threshold < 2 ^ 64)
    (hn : a.certifiers.length < 2 ^ 64) (hb : a.certifiers.length + certifierBase ≤ nextBase)
    (hx : a.next.length = a.certifiers.length) : authorityOfCell (authorityCell a) = some a := by
  have hz : a.certifiers.zipIdx.map (fun p : ByteArray × Nat => certifierBase + p.2) =
      List.range' certifierBase a.certifiers.length := by
    simpa using zipIdx_map_add certifierBase a.certifiers 0
  have hz' : a.next.zipIdx.map (fun p : ByteArray × Nat => nextBase + p.2) =
      List.range' nextBase a.certifiers.length := by
    simpa [hx] using zipIdx_map_add nextBase a.next 0
  have hkeys : ((([(slotThreshold, countBytes a.threshold), (slotCertifierCount, countBytes a.certifiers.length)] ++
      a.certifiers.zipIdx.map (fun p => (certifierBase + p.2, p.1)) ++
      a.next.zipIdx.map fun p => (nextBase + p.2, p.1)) : List (Nat × ByteArray)).map Prod.fst).Nodup := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def]
    rw [hz, hz']
    have hb' : certifierBase = 2 := rfl
    have hn' : nextBase = 513 := rfl
    rw [hb', hn'] at hb ⊢
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨by decide, List.nodup_range', ?_⟩, List.nodup_range', ?_⟩
    · intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, slotThreshold, slotCertifierCount] at hx
      rw [List.mem_range'_1] at hy
      omega
    · intro x hx y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, slotThreshold,
        slotCertifierCount, List.mem_range'_1] at hx
      rw [List.mem_range'_1] at hy
      omega
  have hc : (authorityCell a).slots.get slotCertifierCount = some (countBytes a.certifiers.length) :=
    slotsOf_get_of_mem hkeys (by simp)
  have htg : (authorityCell a).slots.get slotThreshold = some (countBytes a.threshold) :=
    slotsOf_get_of_mem hkeys (by simp)
  have hks : (List.range a.certifiers.length).mapM (fun i => (authorityCell a).slots.get (certifierBase + i)) =
      some a.certifiers := by
    rw [List.range_eq_range']
    refine mapM_range'_get (f := fun i => (authorityCell a).slots.get (certifierBase + i)) a.certifiers 0
      fun i hi => ?_
    refine slotsOf_get_of_mem hkeys (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨(a.certifiers[i], i), ?_, by simp⟩)))
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])
  have hns : (List.range a.certifiers.length).mapM (fun i => (authorityCell a).slots.get (nextBase + i)) =
      some a.next := by
    rw [List.range_eq_range', ← hx]
    refine mapM_range'_get (f := fun i => (authorityCell a).slots.get (nextBase + i)) a.next 0
      fun i hi => ?_
    refine slotsOf_get_of_mem hkeys (List.mem_append_right _
      (List.mem_map.mpr ⟨(a.next[i], i), ?_, by simp⟩))
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hi])
  unfold authorityOfCell
  simp [htg, hc, countOf_countBytes, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hn, hks, hns]

omit [Ord D] [DecidableEq D] in
/-- What a certifier rotation's two writes leave at each slot. -/
theorem rotation_get {s : Slots} {i : Nat} {key nb : ByteArray} (k : Nat) :
    (applyOps s [.set (certifierBase + i) key, .set (nextBase + i) nb]).get k =
      if k = nextBase + i then some nb else if k = certifierBase + i then some key else s.get k := by
  simp only [applyOps, List.foldl, applyOp]
  by_cases h1 : k = nextBase + i
  · subst h1; simp [slots_get_set_eq]
  · rw [slots_get_set_ne _ h1]
    by_cases h2 : k = certifierBase + i
    · subst h2; rw [if_neg h1, if_pos rfl, slots_get_set_eq]
    · rw [slots_get_set_ne _ h2]; simp [h1, h2]

omit [Ord D] [DecidableEq D] in
/-- **A rotated authority cell decodes as the rotated authority** (KERNEL-79): writing certifier `i`'s
key and next commitment into a cell that decodes as `a` (keys below `nextBase`) leaves a cell that
decodes as `a.rotate i key nb`. -/
theorem authorityOfCell_rotate {cell : Cell} {a : Authority} {i : Nat} {key nb : ByteArray}
    (h : authorityOfCell cell = some a) (hi : i < a.certifiers.length)
    (hb : a.certifiers.length + certifierBase ≤ nextBase) :
    authorityOfCell { cell with slots := applyOps cell.slots [.set (certifierBase + i) key, .set (nextBase + i) nb] } =
      some (a.rotate i key nb) := by
  unfold authorityOfCell at h ⊢
  cases ht : cell.slots.get slotThreshold with
  | none => simp [ht] at h
  | some tb =>
  cases htc : countOf tb with
  | none => simp [ht, htc] at h
  | some t =>
  cases hcb : cell.slots.get slotCertifierCount with
  | none => simp [ht, hcb] at h
  | some nb0 =>
  cases hn : countOf nb0 with
  | none => simp [ht, hcb, hn] at h
  | some n =>
  cases hks : (List.range n).mapM fun j => cell.slots.get (certifierBase + j) with
  | none => simp [ht, hcb, hn, hks] at h
  | some ks =>
  cases hns : (List.range n).mapM fun j => cell.slots.get (nextBase + j) with
  | none => simp [ht, hcb, hn, hks, hns] at h
  | some ns =>
  simp [ht, htc, hcb, hn, hks, hns] at h
  subst h
  rw [List.range_eq_range'] at hks hns
  obtain ⟨hkl, hkg⟩ := mapM_range'_some n 0 hks
  obtain ⟨hnl, hng⟩ := mapM_range'_some n 0 hns
  simp only at hi hb
  have hb' : certifierBase = 2 := rfl
  have hn' : nextBase = 513 := rfl
  have g0 : (applyOps cell.slots [.set (certifierBase + i) key, .set (nextBase + i) nb]).get slotThreshold =
      some tb := by
    rw [rotation_get, if_neg (show slotThreshold ≠ nextBase + i by rw [hn']; unfold slotThreshold; omega),
      if_neg (show slotThreshold ≠ certifierBase + i by rw [hb']; unfold slotThreshold; omega)]
    exact ht
  have g1 : (applyOps cell.slots [.set (certifierBase + i) key, .set (nextBase + i) nb]).get slotCertifierCount =
      some nb0 := by
    rw [rotation_get, if_neg (show slotCertifierCount ≠ nextBase + i by rw [hn']; unfold slotCertifierCount; omega),
      if_neg (show slotCertifierCount ≠ certifierBase + i by rw [hb']; unfold slotCertifierCount; omega)]
    exact hcb
  have gk : (List.range n).mapM (fun j =>
      (applyOps cell.slots [.set (certifierBase + i) key, .set (nextBase + i) nb]).get (certifierBase + j)) =
      some (ks.set i key) := by
    rw [List.range_eq_range']
    have hl : (ks.set i key).length = n := by simp [hkl]
    rw [← hl]
    refine mapM_range'_get _ 0 fun j hj => ?_
    rw [hl] at hj
    rw [rotation_get, List.getElem_set]
    have hne : ¬ certifierBase + (0 + j) = nextBase + i := by rw [hb', hn']; omega
    simp only [hne, if_false]
    by_cases hji : i = j
    · subst hji; simp
    · have hne' : ¬ certifierBase + (0 + j) = certifierBase + i := by omega
      simp only [hne', if_false, hji]
      have := hkg j hj
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  have gn : (List.range n).mapM (fun j =>
      (applyOps cell.slots [.set (certifierBase + i) key, .set (nextBase + i) nb]).get (nextBase + j)) =
      some (ns.set i nb) := by
    rw [List.range_eq_range']
    have hl : (ns.set i nb).length = n := by simp [hnl]
    rw [← hl]
    refine mapM_range'_get _ 0 fun j hj => ?_
    rw [hl] at hj
    rw [rotation_get, List.getElem_set]
    by_cases hji : i = j
    · subst hji; simp
    · have hne : ¬ nextBase + (0 + j) = nextBase + i := by omega
      have hne' : ¬ nextBase + (0 + j) = certifierBase + i := by rw [hb', hn']; omega
      simp only [hne, hne', if_false, hji]
      have := hng j hj
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  simp [g0, g1, htc, hn, gk, gn, Authority.rotate]

end Cell

section Births

omit [Ord D] in
/-- **No receiver bears an authority cell**, anywhere in a call's tree: `enroll` bears a member,
`install` a package, `create` an object, `createOf` an object and perhaps a package, `grant` a grant,
`issue` and `account` an account; the rest
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
  · intro sub wk actor _caller b r hb h
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
    | rotateCertifier index key next =>
        obtain ⟨-, -, -, -, -, -, hr⟩ := rotateCertifier_ok (stepped_draft h)
        rw [hr]
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
    | createOf pkg laws state =>
        have hd := stepped_draft h
        intro x hx hk
        rcases createOf_kind hd x hx with h' | h' <;> rw [h'] at hk <;>
          simp [kindObject, kindPackage, kindAuthority] at hk
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


/-! ## Rotation (KERNEL-79) -/

/-- One certifier rotation: certifier `i` moved to its committed successor `key`, committing `nb`
(digest bytes) for the key after it. -/
def Rotated (X : Ctx D) (a b : Authority) : Prop :=
  ∃ i key nb, a.preRotated X i key = true ∧ b = a.rotate i key nb

/-- A run of certifier rotations from `a` to `b`: the authority is `a`, or a rotation of a rotation
of it. -/
inductive Rotations (X : Ctx D) : Authority → Authority → Prop
  | refl (a : Authority) : Rotations X a a
  | step {a b c : Authority} : Rotations X a b → Rotated X b c → Rotations X a c

omit [Ord D] [DecidableEq D] in
theorem preRotated_iff {X : Ctx D} {a : Authority} {i : Nat} {key : ByteArray} :
    a.preRotated X i key = true ↔ i < a.certifiers.length ∧
      a.next[i]? = some (X.env.bytes (certifyNextDigest X key)) ∧ key ∉ a.certifiers := by
  simp only [Authority.preRotated, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun hk => h3 key hk rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun k hk he => h3 (he ▸ hk)⟩

omit [Ord D] [DecidableEq D] in
/-- A rotation changes neither the counts nor the threshold. -/
theorem rotations_shape {X : Ctx D} {a b : Authority} (h : Rotations X a b) :
    b.certifiers.length = a.certifiers.length ∧ b.next.length = a.next.length ∧ b.threshold = a.threshold := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step _ hr ih =>
      obtain ⟨i, key, nb, -, rfl⟩ := hr
      simpa [Authority.rotate] using ih

theorem nodup_set {α : Type} {x : α} : ∀ {l : List α} {i : Nat}, l.Nodup → x ∉ l → (l.set i x).Nodup
  | [], _, _, _ => by simp
  | a :: l, 0, hn, hx => by
      rw [List.nodup_cons] at hn
      simp only [List.set_cons_zero, List.nodup_cons]
      exact ⟨fun h => hx (List.mem_cons_of_mem _ h), hn.2⟩
  | a :: l, i + 1, hn, hx => by
      rw [List.nodup_cons] at hn
      simp only [List.set_cons_succ, List.nodup_cons]
      refine ⟨fun h => ?_, nodup_set hn.2 (fun h => hx (List.mem_cons_of_mem _ h))⟩
      rcases List.mem_or_eq_of_mem_set h with h | h
      · exact hn.1 h
      · exact hx (h ▸ List.mem_cons_self)

theorem not_mem_set_old {α : Type} {x : α} : ∀ {l : List α} {i : Nat} (hi : i < l.length), l.Nodup →
    x ≠ l[i] → l[i] ∉ l.set i x
  | [], _, hi, _, _ => absurd hi (by simp)
  | a :: l, 0, _, hn, hx => by
      rw [List.nodup_cons] at hn
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.mem_cons, not_or]
      exact ⟨fun h => hx h.symm, hn.1⟩
  | a :: l, i + 1, hi, hn, hx => by
      rw [List.nodup_cons] at hn
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.mem_cons, not_or]
      simp only [List.length_cons] at hi
      exact ⟨fun h => hn.1 (h ▸ List.getElem_mem _), not_mem_set_old (by omega) hn.2 hx⟩

omit [Ord D] [DecidableEq D] in
/-- **After a rotation only the new key certifies at its index** (KERNEL-79): rotating certifier `i`
to its committed successor `key` lists `key` at `i`, keeps the keys distinct, and lists certifier
`i`'s old key nowhere, so no signer of a certificate under the rotated authority verifies under it
(`Protocol.Proofs.Head.holds_rotated`). -/
theorem rotate_retires {X : Ctx D} {a : Authority} {i : Nat} {key nb : ByteArray}
    (hp : a.preRotated X i key = true) (hn : a.certifiers.Nodup) :
    (a.rotate i key nb).certifiers[i]? = some key ∧ (a.rotate i key nb).certifiers.Nodup ∧
      ∀ old, a.certifiers[i]? = some old → old ∉ (a.rotate i key nb).certifiers := by
  obtain ⟨hi, -, hk⟩ := preRotated_iff.mp hp
  refine ⟨by simp [Authority.rotate, hi], nodup_set hn hk, fun old ho => ?_⟩
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at ho
  subst ho
  exact not_mem_set_old hi hn (fun he => hk (he ▸ List.getElem_mem _))

omit [Ord D] [DecidableEq D] in
/-- Every rotation of an authority with distinct keys has distinct keys. -/
theorem rotations_nodup {X : Ctx D} {a b : Authority} (h : Rotations X a b) (hn : a.certifiers.Nodup) :
    b.certifiers.Nodup := by
  induction h with
  | refl => exact hn
  | step _ hr ih =>
      obtain ⟨i, key, nb, hp, rfl⟩ := hr
      exact (rotate_retires hp ih).2.1

/-! ## The invariant, and what keeps it -/

/-- Every live `kindAuthority` cell of the World is at `authorityId` and decodes as a rotation of
`auth`; one is live; every nullifier slot holds `spent`. With these, `authorityOf` reads that
rotation (`authorityOf_eq`). -/
def AuthorityOnly (X : Ctx D) (auth : Authority) (w : World D) : Prop :=
  (∀ id cell, w.live X.env id = some cell → cell.kind = kindAuthority →
    id = authorityId X ∧ ∃ a, Rotations X auth a ∧ authorityOfCell cell = some a) ∧
  (∃ cell, w.live X.env (authorityId X) = some cell ∧ cell.kind = kindAuthority) ∧
  ∀ n l, w.trie.get (trieSpec X.env) (.nullifier n) = some l → l = .spent

/-- **What one admitted turn does to the authority cell** (KERNEL-79): on a World whose authority
cell is the only one, it is unchanged and the call is no certifier rotation, or the call is
`rotateCertifier i key next`, its member the authority cell, signed by `key`, `key` certifier `i`'s
committed successor in the authority the cell decodes as, and the cell left is the rotation's write
of it. Every other receiver writes no authority cell (`effect_at_authority`). -/
theorem authority_turn {X : Ctx D} {auth : Authority} {w w' : World D} {c : Call D} {t : Turn D}
    (hw : AuthorityOnly X auth w) (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    (w'.live X.env (authorityId X) = w.live X.env (authorityId X) ∧
        ∀ i key next, c.unsigned.body ≠ .rotateCertifier i key next) ∨
      ∃ cell a i key next, w.live X.env (authorityId X) = some cell ∧ authorityOfCell cell = some a ∧
        c.unsigned.body = .rotateCertifier i key next ∧ c.unsigned.member = authorityId X ∧
        c.unsigned.key = key ∧ a.preRotated X i key = true ∧
        w'.live X.env (authorityId X) = some { cell with slots := applyOps cell.slots (rotationOps X i key next) } := by
  obtain ⟨-, hwith⟩ := receive_ok_with hr
  obtain ⟨-, d, _k, hd, hs⟩ := receiveWith_sealed hwith
  replace hd := derive_of_withTicks hd
  rw [derive_eq] at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok R =>
  rw [hR] at hd
  simp only [Except.map, Except.ok.injEq] at hd
  subst hd
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  obtain ⟨cell₀, hl₀, hk₀⟩ := hw.2.1
  have readAt : ∀ x, (c.unsigned.pins.any fun p => decide (p.1 = x)) = true →
      ∀ cl, w.live X.env x = some cl → cl.kind = kindAuthority →
        readKind (pinned X.env w c.unsigned.pins) x kindAuthority = .ok cl := by
    intro x hany cl hl hk
    simp [readKind, pinned, hany, hl, hk]
  by_cases hex : ∃ e ∈ R.1.effects, e.1 = authorityId X
  · right
    obtain ⟨e, he, hid⟩ := hex
    obtain ⟨q, hq, hqe⟩ := hpins e he
    have hany : (c.unsigned.pins.any fun p => decide (p.1 = e.1)) = true :=
      List.any_eq_true.mpr ⟨q, hq, by simpa using hqe⟩
    have hrk := readAt e.1 hany cell₀ (hid ▸ hl₀) hk₀
    obtain ⟨i, key, next, hbody, rfl⟩ := effect_at_authority hR he hrk
    simp only at hid hrk hany
    have hR' := hR
    rw [hbody] at hR'
    obtain ⟨cl, a, hka, hdec, hkey, hpre, hdr⟩ := rotateCertifier_ok (stepped_draft hR')
    rw [hrk] at hka
    cases hka
    have heff : R.1.effects = [(c.unsigned.member, .write (rotationOps X i key next))] := by rw [hdr]
    refine ⟨cell₀, a, i, key, next, hl₀, hdec, hbody, hid, hkey, hpre, ?_⟩
    have hx : ∃ x ∈ t.touches, x.cell = authorityId X := by
      rw [htouch]
      exact ⟨_, List.mem_map_of_mem hq, by simp only; rw [← hid]; simpa using hqe⟩
    have hall : ∀ x ∈ t.touches, x.cell = authorityId X → x.act = .write (rotationOps X i key next) := by
      intro x hx hxc
      rw [htouch] at hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc, heff, ← hid]
      simp [actFor]
    exact (admit_live_write ha hl₀ hx hall).1
  · left
    have hkeep : ∀ x ∈ t.touches, x.cell = authorityId X → x.act = .keep := by
      intro x hx hxc
      rw [htouch] at hx
      obtain ⟨q', -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc]
      exact actFor_none (fun e he he' => hex ⟨e, he, he'⟩)
    have hnc : authorityId X ∉ createdIds t := by
      obtain ⟨posts, hk', -⟩ := admit_ok ha
      exact live_not_created hk' hl₀
    refine ⟨by unfold World.live; rw [admit_frame ha hkeep hnc], fun i key next hbody => ?_⟩
    have hR' := hR
    rw [hbody] at hR'
    obtain ⟨cl, a, hka, -, -, -, hdr⟩ := rotateCertifier_ok (stepped_draft hR')
    obtain ⟨hlook, hkind⟩ := readKind_ok hka
    have hlive : w.live X.env c.unsigned.member = some cl := by
      unfold pinned at hlook
      split at hlook
      · exact Except.ok.inj hlook
      · cases hlook
    obtain ⟨hid, -⟩ := hw.1 _ cl hlive hkind
    exact hex ⟨(c.unsigned.member, .write (rotationOps X i key next)), by rw [hdr]; simp, hid⟩

/-- **An admitted turn keeps `AuthorityOnly`**: it bears no authority cell
(`receive_born_not_authority`), and it leaves the one authority cell as it was or rotated by one
pre-rotated certifier (`authority_turn`). -/
theorem admit_authorityOnly {X : Ctx D} {auth : Authority} {w w' : World D} {c : Call D} {t : Turn D}
    (hw : AuthorityOnly X auth w) (hb : auth.certifiers.length + certifierBase ≤ nextBase)
    (hr : receive X w c = .ok t) (h : World.admit X.env w t = .ok w') : AuthorityOnly X auth w' := by
  have hstep := authority_turn hw hr h
  refine ⟨fun id c' hl hk => ?_, ?_, fun n l hg => ?_⟩
  · rcases admit_live h hl with hc | ⟨cell, hold, hsame | ⟨ops, hp⟩⟩
    · exact absurd hk (receive_born_not_authority hr c' (List.mem_map_of_mem (f := Prod.snd) hc))
    · subst hsame; exact hw.1 id _ hold hk
    · have hkc : cell.kind = kindAuthority := (postWrite_keeps hp).1 ▸ hk
      obtain ⟨rfl, a, hra, hdec⟩ := hw.1 id cell hold hkc
      refine ⟨rfl, ?_⟩
      rcases hstep with ⟨hsame, -⟩ | ⟨cell', a', i, key, next, hl', hdec', -, -, -, hpre, hl''⟩
      · rw [hsame, hold] at hl; cases hl; exact ⟨a, hra, hdec⟩
      · rw [hold] at hl'; cases hl'
        rw [hdec] at hdec'; cases hdec'
        rw [hl] at hl''; cases hl''
        refine ⟨a.rotate i key (X.env.bytes next), .step hra ⟨i, key, X.env.bytes next, hpre, rfl⟩, ?_⟩
        have hlen := (rotations_shape hra).1
        exact authorityOfCell_rotate hdec (preRotated_iff.mp hpre).1 (by rw [hlen]; exact hb)
  · rcases hstep with ⟨hsame, -⟩ | ⟨cell', a', i, key, next, hl', -, -, -, -, -, hl''⟩
    · obtain ⟨cell, hl, hk⟩ := hw.2.1; exact ⟨cell, hsame ▸ hl, hk⟩
    · obtain ⟨cell, hl, hk⟩ := hw.2.1
      rw [hl] at hl'; cases hl'
      exact ⟨_, hl'', hk⟩
  · obtain ⟨posts, _, rfl⟩ := admit_ok h
    rw [show (commit X.env w t posts).trie = commitTrie X.env w t posts from rfl, commitTrie_nul] at hg
    split at hg
    · exact (Option.some.inj hg).symm
    · exact hw.2.2 n l hg

theorem refuse_authorityOnly {X : Ctx D} {auth : Authority} {w w' : World D} {r : Refused D}
    (hw : AuthorityOnly X auth w) (h : World.refuse X.env w r = .ok w') : AuthorityOnly X auth w' :=
  ⟨fun id cell hl => hw.1 id cell ((refuse_live h id).symm.trans hl),
    by obtain ⟨cell, hl, hk⟩ := hw.2.1; exact ⟨cell, (refuse_live h _).trans hl, hk⟩,
    fun n l hg => hw.2.2 n l (by rw [refuse_trie h] at hg; exact hg)⟩

/-- **Every honest folded log keeps `AuthorityOnly`**: no honest step bears an authority cell, and
the only honest write of one is a pre-rotated certifier's rotation. -/
theorem honest_authorityOnly {X : Ctx D} {auth : Authority} (hb : auth.certifiers.length + certifierBase ≤ nextBase) :
    ∀ {w w' : World D} {l : List (Step D)}, AuthorityOnly X auth w → World.fold X.env w l = .ok w' →
      Honest X w l → AuthorityOnly X auth w'
  | w, w', [], hw, hf, _ => by simp only [World.fold, Except.ok.injEq] at hf; subst hf; exact hw
  | w, w', .refusal r :: rest, hw, hf, hh => by
      obtain ⟨w₁, hs, -, hfr, hhr⟩ := fold_honest_cons hf hh
      have hrf : World.refuse X.env w r = .ok w₁ := hs
      exact honest_authorityOnly hb (refuse_authorityOnly hw hrf) hfr hhr
  | w, w', .turn t :: rest, hw, hf, hh => by
      obtain ⟨w₁, hs, ⟨c, -, hr, -⟩, hfr, hhr⟩ := fold_honest_cons hf hh
      exact honest_authorityOnly hb (admit_authorityOnly hw hb hr hs) hfr hhr

/-- **`authorityOf` reads the one authority cell**: on a canonical World whose authority cell is the
only one, `authorityOf` answers what that cell decodes as. -/
theorem authorityOf_eq {X : Ctx D} {auth : Authority} {w : World D} {cell : Cell} {a : Authority}
    (hc : w.Canon X.env) (ho : AuthorityOnly X auth w) (hl : w.live X.env (authorityId X) = some cell)
    (hdec : authorityOfCell cell = some a) : authorityOf w = some a := by
  have hr : Trie.Routed (trieSpec X.env) 0 w.trie := hc.1
  obtain ⟨v, hg⟩ := live_get hl
  have hk : cell.kind = kindAuthority := by
    obtain ⟨cell₀, hl₀, hk₀⟩ := ho.2.1
    rw [hl] at hl₀; cases hl₀; exact hk₀
  let F : Slot D × Leaf → Option Cell := fun p => match p.2 with
    | .entry (.live c _) => if c.kind = kindAuthority then some c else none
    | _ => none
  let x : Slot D × Leaf := (.cell (authorityId X), .entry (.live cell v))
  have hx : x ∈ w.trie.toList := (Trie.mem_toList (trieSpec X.env) 0 w.trie hr _ _).mpr hg
  have hFx : F x = some cell := by simp [F, x, hk]
  have hall : ∀ p ∈ w.trie.toList, ∀ c', F p = some c' → p = x := by
    rintro ⟨s, l⟩ hp c' hF
    have hg' := (Trie.mem_toList (trieSpec X.env) 0 w.trie hr s l).mp hp
    cases l with
    | spent => simp [F] at hF
    | entry e =>
      cases e with
      | tomb => simp [F] at hF
      | live c'' v' =>
        have hk' : c''.kind = kindAuthority := by
          by_cases hne : c''.kind = kindAuthority
          · exact hne
          · simp [F, hne] at hF
        have hg' : w.trie.get (trieSpec X.env) s = some (.entry (.live c'' v')) := hg'
        cases s with
        | nullifier n => exact absurd (ho.2.2 n _ hg') (by simp)
        | cell k =>
          obtain ⟨rfl, -⟩ := ho.1 k c'' (get_live hg') hk'
          rw [hg] at hg'
          simp only [Option.some.injEq, Leaf.entry.injEq, Entry.live.injEq] at hg'
          obtain ⟨rfl, rfl⟩ := hg'
          rfl
  have hf : w.trie.toList.filterMap F = [cell] :=
    filterMap_eq_singleton (key := Prod.fst) (Trie.toList_nodup (trieSpec X.env) 0 w.trie hr) hx hFx hall
  show (match w.trie.toList.filterMap F with
    | [c] => authorityOfCell c
    | _ => none) = some a
  rw [hf]
  exact hdec

/-- `authorityOf` answers a rotation of `auth` on every canonical World whose authority cell is the
only one. -/
theorem authorityOf_of_only {X : Ctx D} {auth : Authority} {w : World D} (hc : w.Canon X.env)
    (ho : AuthorityOnly X auth w) : ∃ a, Rotations X auth a ∧ authorityOf w = some a := by
  obtain ⟨cell, hl, hk⟩ := ho.2.1
  obtain ⟨-, a, hra, hdec⟩ := ho.1 _ cell hl hk
  exact ⟨a, hra, authorityOf_eq hc ho hl hdec⟩

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

/-- The authority cell is live in the genesis World, at `authorityId`. -/
theorem genesis_authority_live (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Authority) :
    (genesisWorld X name nonce allowance founders auth).live X.env (authorityId X) =
      some (authorityCell auth) :=
  get_live (insertAll_append_get _ (founderEntries X _ founders) _ _)

/-- A checked genesis World holds one `kindAuthority` cell, the authority's, decoding as its
genesis authority, and no nullifier. -/
theorem genesis_authorityOnly {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} (hf : GenesisFits X name nonce allowance founders auth) :
    AuthorityOnly X auth (genesisWorld X name nonce allowance founders auth) := by
  obtain ⟨-, -, -, -, ⟨hlen, -, -, ⟨hthr, -⟩, hnx, -⟩, -⟩ := hf
  have h2 : certifierBase = 2 := rfl
  have h5 : nextBase = 513 := rfl
  have hdec : authorityOfCell (authorityCell auth) = some auth :=
    authorityOfCell_authorityCell (by omega) (by omega) hlen hnx
  let o := originOf X name nonce allowance founders auth
  refine ⟨fun id cell hl hk => ?_, ⟨_, genesis_authority_live X name nonce allowance founders auth, rfl⟩,
    fun n l hg => ?_⟩
  · have hl' := genesis_authority_live X name nonce allowance founders auth
    by_cases hid : id = authorityId X
    · subst hid
      rw [hl'] at hl; cases hl
      exact ⟨rfl, auth, .refl auth, hdec⟩
    · obtain ⟨v, hg⟩ := live_get hl
      rcases insertAll_get_slot (m := Trie.T.empty) (ps := genesisEntries X o founders auth) hg with
        ⟨k, e, hs, he, hm⟩ | hm
      · simp only [Slot.cell.injEq, Leaf.entry.injEq] at hs he
        subst hs he
        rcases mem_genesisEntries hm with hm | ⟨hid', -⟩
        · exfalso
          obtain ⟨p, _, ⟨_, h⟩ | ⟨_, h⟩⟩ := mem_founderEntries hm
          · simp only [Entry.live.injEq] at h
            rw [h.1] at hk
            simp [founderMember, kindMember, kindAuthority] at hk
          · simp only [Entry.live.injEq] at h
            rw [h.1] at hk
            simp [founderRoot, kindGrant, kindAuthority] at hk
        · exact absurd hid' hid
      · exact absurd (hm.symm.trans (Trie.get_empty _ _)) (by simp)
  · rcases insertAll_get_slot (m := Trie.T.empty) (ps := genesisEntries X o founders auth) hg with
      ⟨k, e, hs, -, -⟩ | hm
    · cases hs
    · exact absurd (hm.symm.trans (Trie.get_empty _ _)) (by simp)

/-- **Every checked genesis carries its authority** (`GenesisFits`, the premise `genesis` checks). -/
theorem authorityOf_genesis {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} (hf : GenesisFits X name nonce allowance founders auth) :
    authorityOf (genesisWorld X name nonce allowance founders auth) = some auth := by
  have hf' := hf
  obtain ⟨-, -, -, -, ⟨hlen, -, -, ⟨hthr, -⟩, hnx, -⟩, -⟩ := hf'
  have h2 : certifierBase = 2 := rfl
  have h5 : nextBase = 513 := rfl
  exact authorityOf_eq (receive_genesis_canon X name nonce allowance founders auth) (genesis_authorityOnly hf)
    (genesis_authority_live X name nonce allowance founders auth)
    (authorityOfCell_authorityCell (by omega) (by omega) hlen hnx)

/-- **Every World an honest fold reaches carries a rotation of the genesis authority** (KERNEL-69.2,
KERNEL-79): from a checked genesis, along any honest log (every Turn what `receive` derives, every
refusal what its re-judge records: the follower's and the writer's Worlds), `authorityOf` answers
the genesis authority with some of its certifiers moved, each to the successor key its predecessor
committed, by a call that key signed. The threshold and the counts are the genesis's. -/
theorem authorityOf_honest_fold {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} {l : List (Step D)} {w' : World D}
    (hf : GenesisFits X name nonce allowance founders auth)
    (h : World.fold X.env (genesisWorld X name nonce allowance founders auth) l = .ok w')
    (hh : Honest X (genesisWorld X name nonce allowance founders auth) l) :
    ∃ a, Rotations X auth a ∧ authorityOf w' = some a := by
  have hf' := hf
  obtain ⟨-, -, -, -, ⟨hlen, -⟩, -⟩ := hf'
  exact authorityOf_of_only (fold_canon (receive_genesis_canon X name nonce allowance founders auth) h)
    (honest_authorityOnly hlen (genesis_authorityOnly hf) h hh)

/-- **A certifier rotation, at the World** (KERNEL-79): on a canonical World whose authority cell is
the only one (every World an honest fold from a checked genesis reaches), an admitted
`rotateCertifier i key next` moves `authorityOf` from `a` to `a.rotate i key next`, where `key` was
certifier `i`'s committed successor in `a` and signed the call; with `a`'s keys distinct, certifier
`i`'s old key is then listed nowhere (`rotate_retires`). -/
theorem rotateCertifier_authorityOf {X : Ctx D} {auth : Authority} {w w' : World D} {c : Call D} {t : Turn D}
    {i : Nat} {key : ByteArray} {next : D} (hc : w.Canon X.env) (hw : AuthorityOnly X auth w)
    (hb : auth.certifiers.length + certifierBase ≤ nextBase)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hbody : c.unsigned.body = .rotateCertifier i key next) :
    ∃ a, authorityOf w = some a ∧ c.unsigned.key = key ∧ a.preRotated X i key = true ∧
      authorityOf w' = some (a.rotate i key (X.env.bytes next)) := by
  rcases authority_turn hw hr ha with ⟨-, hno⟩ | ⟨cell, a, i', key', next', hl, hdec, hbody', -, hkey, hpre, hl'⟩
  · exact absurd hbody (hno i key next)
  · rw [hbody] at hbody'
    cases hbody'
    have hw' := admit_authorityOnly hw hb hr ha
    have hk : cell.kind = kindAuthority := by
      obtain ⟨c₀, h₀, hk₀⟩ := hw.2.1; rw [hl] at h₀; cases h₀; exact hk₀
    obtain ⟨-, a₀, hra, hdec₀⟩ := hw.1 _ cell hl hk
    rw [hdec] at hdec₀; cases hdec₀
    have hlen := (rotations_shape hra).1
    refine ⟨a, authorityOf_eq hc hw hl hdec, hkey, hpre, authorityOf_eq (admit_canon hc ha) hw' hl' ?_⟩
    exact authorityOfCell_rotate hdec (preRotated_iff.mp hpre).1 (by rw [hlen]; exact hb)

end Genesis

end Nanodregg.Kernel.Receive
