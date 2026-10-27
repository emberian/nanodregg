/-
# Kernel.Proofs.Carry — a carry moves exactly the carried state into a new World (KERNEL-29, KERNEL-79)

`Receive.carry` re-geneses a World from a `Carried` state under an authority the operator STATES
(law 1: state crosses a flag day by re-genesis, never by a migration; KERNEL-79: the authority is
re-stated, never inherited). It is checked like genesis (`carry_ok`: refused by name outside
`CarryFits`, the stated authority by genesis's own `checkAuthority`) and

* `carry_carried`, `carry_of_carried`: the new World carries what it was given, its trie
  re-authored (`reauthor`) and its window trie cut to the meter (`meterOnly`);
* `reauthor_get`: the re-authored trie holds the stated authority cell at its content id and every
  other entry of the carried trie but a live authority cell, unchanged;
* `meterOnly_get`: the carried window trie's meter leaves, and nothing else;
* `carry_origin_ne_genesis`: a carry's origin equal to a genesis's is a collision between the
  two origin inputs (tagged apart, `originInput`); its tooth `carry_origin_ne_genesis_sep`;
* `carryOriginOfStart_inj`, `carry_inj`: a carry's origin commits to its whole start (name, nonce,
  the exported World's origin, the four roots as exported, the allowance, the height and the stated
  authority), or the two carry inputs collide (teeth `carryOriginOfStart_inj_sep`, `carry_inj_sep`);
* `carry_canon`, `carry_cellsFit`, `carry_journalOk`: the new World keeps every invariant the read
  and journal theorems rest on;
* `carry_replayed`: a call the exported World journaled is answered `replayed` at its height by
  the new World — answered, never re-run (PROTOCOL-29).

What the carried World IS — the stated authority's, the source's cells, tombstones, rows and meter
under the new origin — is `Kernel.Proofs.CarrySound`.
-/
import Kernel.Proofs.Lawful
import Kernel.Proofs.Origin
import Kernel.Proofs.Journal
import Kernel.Proofs.CellsFit
import Kernel.Proofs.TrieRetain

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

/-- A carry input within the raw codec's bounds, under an authority genesis would take, whose
stated authority's content id holds no entry of another kind, and whose allowance plus the carried
World's cells' and rows' storage is below 2^64 (so the allowance is, and every World folded from
the carry keeps the sum below it: `Budget.carry_fold_budget_lt`). `carry` refuses by name outside it. -/
def CarryFits [DecidableEq D] (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    Prop :=
  name.size ≤ Bounds.eventBytesMax ∧ nonce.size ≤ Bounds.eventBytesMax ∧ auth.Fits ∧
    authorityFree X c.trie auth = true ∧ rowsParented X.env (reauthor X c.trie auth) c.rows = true ∧
    cellsWeight (reauthor X c.trie auth) + rowsWeight c.rows + c.allowance < 2 ^ 64 ∧
    c.height < 2 ^ 64 ∧
    (X.env.bytes fromOrigin).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.trie.hashOf (trieSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.rows.hashOf (rowSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.journal.hashOf (journalSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.refusals.hashOf (refusalSpec X.env))).size ≤ Bounds.eventBytesMax

omit [Ord D] in
theorem checkCarryAuthority_ok {auth : Authority} : checkCarryAuthority auth = .ok () ↔ auth.Fits := by
  rw [← checkAuthority_ok]
  unfold checkCarryAuthority
  cases checkAuthority auth with
  | ok u => simp
  | error r => simp

/-- **The carry check is `CarryFits`**, clause by clause. -/
theorem checkCarry_ok [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} :
    checkCarry X name nonce fromOrigin c auth = .ok () ↔ CarryFits X name nonce fromOrigin c auth := by
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  simp only [checkCarry, req_bind_ok, decide_eq_true_eq, hc]
  rw [except_bind_ok]
  simp only [req_bind_ok, req_ok, decide_eq_true_eq, Bool.and_eq_true]
  unfold CarryFits
  constructor
  · rintro ⟨h1, h2, ⟨⟩, ha, hf, hp, hw, hh, ⟨⟨⟨⟨h6, h7⟩, h8⟩, h9⟩, h10⟩⟩
    exact ⟨h1, h2, checkCarryAuthority_ok.mp ha, hf, hp, hw, hh, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, ha, hf, hp, hw, hh, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, (), checkCarryAuthority_ok.mpr ha, hf, hp, hw, hh, ⟨⟨⟨⟨h6, h7⟩, h8⟩, h9⟩, h10⟩⟩

/-- **Carry is checked**: it returns a World exactly on a `CarryFits` input, and that World is
`carryWorld`. -/
theorem carry_ok [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w : World D} :
    carry X name nonce fromOrigin c auth = .ok w ↔
      CarryFits X name nonce fromOrigin c auth ∧ w = carryWorld X name nonce fromOrigin c auth := by
  unfold carry
  rw [except_bind_ok]
  constructor
  · rintro ⟨⟨⟩, hc, hw⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hw
    exact ⟨checkCarry_ok.mp hc, hw.symm⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨(), checkCarry_ok.mpr hf, rfl⟩

/-- **A carry carries what it was given**, its trie re-authored and its window trie cut to the meter. -/
theorem carry_carried [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    {auth : Authority} {w : World D} (h : carry X name nonce fromOrigin c auth = .ok w) :
    w.carried = { c with trie := reauthor X c.trie auth, refusals := meterOnly X.env c.refusals } := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  rfl

/-- **Export, then carry: the same state under the stated authority.** The new World holds the
exported World's allowance, height, journal and rows, its trie re-authored and its window trie cut
to the meter; its chain and origin are its own. -/
theorem carry_of_carried [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (h : carry X name nonce w.origin w.carried auth = .ok w') :
    w'.trie = reauthor X w.trie auth ∧ w'.allowance = w.allowance ∧ w'.height = w.height ∧
      w'.journal = w.journal ∧ w'.rows = w.rows ∧ w'.refusals = meterOnly X.env w.refusals ∧
      w'.chain = World.genesisChain X.env w'.origin := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The re-authored trie and the carried meter -/

omit [Ord D] in
theorem under_nil {K V : Type} (S : Trie.Spec K V D) {t : Trie.T K V D} {q : K → V → Bool} :
    ∀ p ∈ t.toList, q p.1 p.2 = false → Trie.Under S 0 [] p.1 :=
  fun _ _ _ _ _ _ hb => by simp at hb

omit [Ord D] in
/-- **What the re-authored trie holds** (KERNEL-79): the stated authority's cell at its content id,
and at every other slot the carried trie's entry unless it is a live authority cell. -/
theorem reauthor_get [DecidableEq D] {X : Ctx D} {t : Cells D} (ht : Trie.Canon (trieSpec X.env) 0 t)
    (auth : Authority) (s : Slot D) :
    (reauthor X t auth).get (trieSpec X.env) s =
      if s = .cell (authorityId X auth) then some (.entry (.live (authorityCell auth) 0))
      else (t.get (trieSpec X.env) s).filter (fun l => !liveAuthority s l) := by
  unfold reauthor
  rw [Trie.get_insert, Trie.get_retainAt _ _ _ ht (under_nil (q := fun s l => !liveAuthority s l) _)]

omit [Ord D] in
/-- The re-authored trie is canonical when the carried one is. -/
theorem reauthor_canon [DecidableEq D] {X : Ctx D} {t : Cells D} (ht : Trie.Canon (trieSpec X.env) 0 t)
    (auth : Authority) : Trie.Canon (trieSpec X.env) 0 (reauthor X t auth) :=
  Trie.canon_insert _ _ _ (Trie.canon_retainAt _ _ [] 0 t ht (under_nil (q := fun s l => !liveAuthority s l) _))

omit [Ord D] in
/-- **What the carried meter holds**: the carried window trie's entry at a meter key, nothing at a
refusal-window key. -/
theorem meterOnly_get [DecidableEq D] {E : Env D} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r)
    (k : WindowSlot D) : (meterOnly E r).get (refusalSpec E) k = (r.get (refusalSpec E) k).filter (isMeter k) :=
  Trie.get_retainAt _ _ _ hr (under_nil (q := isMeter) _) k

omit [Ord D] in
/-- The carried meter is canonical when the carried window trie is. -/
theorem meterOnly_canon [DecidableEq D] {E : Env D} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r) :
    Trie.Canon (refusalSpec E) 0 (meterOnly E r) :=
  Trie.canon_retainAt _ _ [] 0 r hr (under_nil (q := isMeter) _)

/-! ## The origin -/

/-- The carry input's domain, as the raw codec's product reads it. -/
theorem carryInput_lawfulOn :
    LawfulOn (fun v : CarryInput => v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.2.2.2.1 < 2 ^ 64 ∧
        ((v.2.2.2.2.2.2.2.2.2.1.length ≤ Bounds.eventBytesMax ∧
          ∀ x ∈ v.2.2.2.2.2.2.2.2.2.1, x.size ≤ Bounds.eventBytesMax) ∧
        v.2.2.2.2.2.2.2.2.2.2 < 2 ^ 64)))))))))) carryInput :=
  product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
    (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
        (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn nat64_lawfulOn
          (product_lawfulOn nat64_lawfulOn
            (product_lawfulOn (rawList_lawfulOn (rawBytes_lawfulOn _ (by decide)) _ (by decide))
              nat64_lawfulOn)))))))))

/-- A carry start within the raw codec's bounds under an authority genesis would take. -/
def CarryStart.Fits (X : Ctx D) (s : CarryStart D) : Prop :=
  s.name.size ≤ Bounds.eventBytesMax ∧ s.nonce.size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes s.fromOrigin).size ≤ Bounds.eventBytesMax ∧ (X.env.bytes s.trieRoot).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes s.rowsRoot).size ≤ Bounds.eventBytesMax ∧ (X.env.bytes s.journalRoot).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes s.windowRoot).size ≤ Bounds.eventBytesMax ∧ s.allowance < 2 ^ 64 ∧ s.height < 2 ^ 64 ∧ s.auth.Fits

omit [Ord D] in
theorem carryStart_fits_input {X : Ctx D} {s : CarryStart D} (h : s.Fits X) :
    let v := carryInputOfStart X s
    v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.2.2.2.1 < 2 ^ 64 ∧
        ((v.2.2.2.2.2.2.2.2.2.1.length ≤ Bounds.eventBytesMax ∧
          ∀ x ∈ v.2.2.2.2.2.2.2.2.2.1, x.size ≤ Bounds.eventBytesMax) ∧
        v.2.2.2.2.2.2.2.2.2.2 < 2 ^ 64))))))))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨ha1, ha2, -, ha4, -⟩⟩ := h
  have hs1 : Bounds.slotsPerCellMax = 1024 := rfl
  have hs2 : Bounds.eventBytesMax = 65536 := rfl
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨by simp only [carryInputOfStart]; omega, ha2⟩,
    by simp only [carryInputOfStart]; omega⟩

/-- The start of a fitting carry fits. -/
theorem carryStartOf_fits [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {f : D} {c : Carried D} {auth : Authority}
    (h : CarryFits X name nonce f c auth) : (carryStartOf X name nonce f c auth).Fits X := by
  obtain ⟨h1, h2, ha, -, -, hw, hh, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h6, h7, h8, h9, h10, by simp only [carryStartOf]; omega, hh, ha⟩

omit [Ord D] in
/-- **A carry's origin is never a genesis's** but by a collision between the two origin inputs:
they are the two cases of one tagged codec, so their bytes differ in the first byte. -/
theorem carry_origin_ne_genesis [Ord D] [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D}
    {c : Carried D} {auth' : Authority} {name' nonce' : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {auth : Authority}
    (h : carryOriginOf X name nonce fromOrigin c auth' = originOf X name' nonce' allowance founders auth) :
    CollidesAmong X.env.hash
      [carryOriginPre X name nonce fromOrigin c auth', originPre X name' nonce' allowance founders auth] :=
  .pair (fun he => (sum_inl_ne_inr genesisInput_lawfulOn carryInput_lawfulOn _ _).symm (congrArg Prod.snd he)) h

omit [Ord D] in
/-- **Tooth of `carry_origin_ne_genesis`**: where the hash separates the two origin inputs, a carry's
origin is not a genesis's. -/
theorem carry_origin_ne_genesis_sep [Ord D] [DecidableEq D] {X : Ctx D} {name nonce : ByteArray}
    {fromOrigin : D} {c : Carried D} {auth' : Authority} {name' nonce' : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority}
    (hs : Separates X.env.hash
      [carryOriginPre X name nonce fromOrigin c auth', originPre X name' nonce' allowance founders auth]) :
    carryOriginOf X name nonce fromOrigin c auth' ≠ originOf X name' nonce' allowance founders auth :=
  fun h => hs.not_collides (carry_origin_ne_genesis h)

/-- What `carryOriginOfStart` hashes. -/
def carryStartPre (X : Ctx D) (s : CarryStart D) : String × ByteArray :=
  (domOrigin, originInput.bytes (.inr (carryInputOfStart X s)))

/-- **A carried World's origin commits to its whole start** (KERNEL-79): two fitting starts with one
origin are one start — name, nonce, exported origin, the four roots, allowance, height and the
stated authority — or their two carry inputs collide. -/
theorem carryOriginOfStart_inj {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {s s' : CarryStart D}
    (hf : s.Fits X) (hf' : s'.Fits X) (h : carryOriginOfStart X s = carryOriginOfStart X s') :
    s = s' ∨ CollidesAmong X.env.hash [carryStartPre X s, carryStartPre X s'] := by
  by_cases hbytes : originInput.bytes (.inr (carryInputOfStart X s)) =
      originInput.bytes (.inr (carryInputOfStart X s'))
  · left
    unfold originInput at hbytes
    rw [sum_bytes_inr_on carryInput_lawfulOn, sum_bytes_inr_on carryInput_lawfulOn] at hbytes
    have he := carryInput_lawfulOn.bytes_injective (carryStart_fits_input hf) (carryStart_fits_input hf')
      (ba_append_cancel _ _ _ hbytes)
    rcases s with ⟨n1, o1, f1, t1, r1, j1, w1, a1, ht1, ⟨c1, th1⟩⟩
    rcases s' with ⟨n2, o2, f2, t2, r2, j2, w2, a2, ht2, ⟨c2, th2⟩⟩
    simp only [carryInputOfStart, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, h3, h4, h5, h6, h7, rfl, rfl, rfl, rfl⟩ := he
    rw [hE.bytes_eq h3, hE.bytes_eq h4, hE.bytes_eq h5, hE.bytes_eq h6, hE.bytes_eq h7]
  · right
    exact .pair (fun he => hbytes (congrArg Prod.snd he)) h

/-- **Tooth of `carryOriginOfStart_inj`**: where the hash separates the two carry inputs, equal
origins are equal starts. -/
theorem carryOriginOfStart_inj_sep {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {s s' : CarryStart D}
    (hf : s.Fits X) (hf' : s'.Fits X) (hs : Separates X.env.hash [carryStartPre X s, carryStartPre X s'])
    (h : carryOriginOfStart X s = carryOriginOfStart X s') : s = s' :=
  hs.elim (carryOriginOfStart_inj hE hf hf' h)

/-- **A carry commits to everything it was made from**: two fitting carries with one origin had
the same start (name, nonce, exported origin, the four roots as exported, allowance, height, stated
authority), or the two carry inputs collide. -/
theorem carry_inj [DecidableEq D] {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D} {auth auth' : Authority}
    (hf : CarryFits X name nonce f c auth) (hf' : CarryFits X name' nonce' f' c' auth')
    (h : carryOriginOf X name nonce f c auth = carryOriginOf X name' nonce' f' c' auth') :
    carryStartOf X name nonce f c auth = carryStartOf X name' nonce' f' c' auth' ∨
      CollidesAmong X.env.hash [carryOriginPre X name nonce f c auth, carryOriginPre X name' nonce' f' c' auth'] :=
  carryOriginOfStart_inj hE (carryStartOf_fits hf) (carryStartOf_fits hf') h

/-- **Tooth of `carry_inj`**: where the hash separates the two carry inputs, equal origins are equal
carry starts. -/
theorem carry_inj_sep [DecidableEq D] {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D} {auth auth' : Authority}
    (hf : CarryFits X name nonce f c auth) (hf' : CarryFits X name' nonce' f' c' auth')
    (hs : Separates X.env.hash [carryOriginPre X name nonce f c auth, carryOriginPre X name' nonce' f' c' auth'])
    (h : carryOriginOf X name nonce f c auth = carryOriginOf X name' nonce' f' c' auth') :
    carryStartOf X name nonce f c auth = carryStartOf X name' nonce' f' c' auth' :=
  hs.elim (carry_inj hE hf hf' h)

/-! ## Invariants -/

/-- A carried World is canonical when the exported one was. -/
theorem carry_canon [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (hc : w.Canon X.env) (h : carry X name nonce w.origin w.carried auth = .ok w') : w'.Canon X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact reauthor_canon hc auth

/-- A carried World's cells fit when the exported one's did and the stated authority's cell does. -/
theorem carry_cellsFit [DecidableEq D] {X : Ctx D} {F : Cell → Prop} {name nonce : ByteArray} {auth : Authority}
    {w w' : World D} (hcn : w.Canon X.env) (hc : w.CellsFit F X.env)
    (ha : (Leaf.entry (.live (authorityCell auth) 0)).CellFit F)
    (h : carry X name nonce w.origin w.carried auth = .ok w') : w'.CellsFit F X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  intro s l hg
  simp only [carryWorld, World.carried] at hg
  rw [reauthor_get hcn] at hg
  split at hg
  · cases hg; exact ha
  · obtain ⟨hl, -⟩ := Option.filter_eq_some_iff.mp hg
    exact hc s l hl

/-- A carried World's journal is bounded when the exported one's was (same entries, same height). -/
theorem carry_journalOk [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority}
    {w w' : World D} (hj : w.JournalOk X.env) (h : carry X name nonce w.origin w.carried auth = .ok w') :
    w'.JournalOk X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hj

/-- **Carry, then fold: still bounded.** Every World folded from a carry of a `JournalOk` World
holds fewer than `3 * windowMax` journal entries, so its export is within the wire's bound too. -/
theorem carry_fold_journal_bounded [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority}
    {w w' w'' : World D} {l : List (Step D)} (hj : w.JournalOk X.env)
    (h : carry X name nonce w.origin w.carried auth = .ok w') (hf : World.fold X.env w' l = .ok w'') :
    w''.journal.toList.length < 3 * Bounds.windowMax :=
  journal_bounded (fold_journalOk (carry_journalOk hj h) hf)

/-- **Answered, never re-run** (PROTOCOL-29). A call the exported World journaled is `replayed` at
its original height by the carried World: a call committed just before the export, its reply
lost, settles as committed. -/
theorem carry_replayed [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    {c : Call D} {hh : Nat} {d : D}
    (h : carry X name nonce w.origin w.carried auth = .ok w') (hj : w.journalAt X.env (txIdOf X c) = some (hh, d)) :
    submit X w' c = .error (.rejected (.replayed hh)) := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact submit_replayed hj

/-! ## Ids are names: a carry changes no authority (KERNEL-40)

A carried World keeps its members' ids, derived at the lineage's genesis from the FIRST origin
(KERNEL-24). That is sound because nothing reads an origin out of an id: `receive` reads the
World's origin only in its first check (`wrongWorld`), and admission never reads it. -/

/-- **`receive` reads the World's origin and chain only in the `wrongWorld` check.** Give a World
any new origin and chain: a call naming the new origin is derived from the OLD World's pinned
state (`pinned` reads only the trie), whatever the origin and chain were. -/
theorem receive_reorigin [DecidableEq D] {X : Ctx D} {w : World D} {c : Call D} {o ch : D}
    {rf : Refusals D} {st : Nat} (hc : c.unsigned.world = o)
    (hj : c.unsigned.body.joinOrigin.all (· = o) = true) :
    receive X { w with origin := o, chain := ch, refusals := rf, steps := st } c =
      receiveWith X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c := by
  unfold receive receiveWith
  simp only [req, decide_eq_true hc, if_true, hj]
  rfl

/-- A call that names its World is derived from the World's pinned state alone. -/
theorem receive_named [DecidableEq D] {X : Ctx D} {w : World D} {c : Call D}
    (hc : c.unsigned.world = w.origin) (hj : c.unsigned.body.joinOrigin.all (· = w.origin) = true) :
    receive X w c = receiveWith X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c := by
  unfold receive receiveWith
  simp only [req, decide_eq_true hc, if_true, hj]
  rfl

/-- **A carry changes no member's rights.** The carried World derives every call that names it
exactly as the exported World's own state does past the World check, with the World's authority
cell the stated one (`reauthor`, KERNEL-79; no receiver reads a `kindAuthority` cell): through the
same pinned view of every member, key, grant and cell at the same ids, so the members keep their ids
and their rights. (On the old World the same call is `wrongWorld`: it names the new origin.) An
enrolment is the one call that also names the World in its body: its join must name the carried
World (PROTOCOL-79: a carried World's join is a new join). -/
theorem carry_receive [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (h : carry X name nonce w.origin w.carried auth = .ok w') {c : Call D} (hc : c.unsigned.world = w'.origin)
    (hj : c.unsigned.body.joinOrigin.all (· = w'.origin) = true) :
    receive X w' c =
      receiveWith X (pinned X.env { w with trie := reauthor X w.trie auth } c.unsigned.pins)
        (rowView X.env { w with trie := reauthor X w.trie auth } c.unsigned) c := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact receive_reorigin (w := { w with trie := reauthor X w.trie auth }) hc hj

/-! ### The call's own world field (KERNEL-40)

`receive_reorigin` is about the World's origin. The call's own `Unsigned.world` is, after a carry,
the NEW origin, so a derivation that recomputed an id from it (`founderId X c.unsigned.world i`)
would still pass `carry_receive`, whose two sides take the same call. Past the `wrongWorld` check,
the derivation reads the call's world only through the call's two encodings: `callBytes` (the
transaction id, so the births' ids, the event and its weight) and `unsignedBytes` (the signed
message). Fix those two values to the call's own and give the call any other world: the result is
the same, refusal or Turn. The tooth `receiveWith_world_sep` is the hazard: a key rule that reads
the signer's id as `founderId X c.unsigned.world 0` makes the same statement false. -/

omit [Ord D] in
private theorem dispatch_world [DecidableEq D] (X : Ctx D) (U : Unsigned D → ByteArray) (look : Pinned D)
    (rv : RowView D) (c : Call D) (o : D) (sub : Sub D) :
    dispatch X look rv c sub =
      dispatch { X with callBytes := fun _ => X.callBytes c, unsignedBytes := U } look rv
        { c with unsigned := { c.unsigned with world := o } } sub := by
  funext wk a b
  cases b <;> rfl

omit [Ord D] in
private theorem tree_world [DecidableEq D] (X : Ctx D) (U : Unsigned D → ByteArray) (look : Pinned D)
    (rv : RowView D) (c : Call D) (o : D) (n : Nat) :
    tree X look rv c n =
      tree { X with callBytes := fun _ => X.callBytes c, unsignedBytes := U } look rv
        { c with unsigned := { c.unsigned with world := o } } n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext wk obj b
    simp only [tree]
    rw [ih, dispatch_world X U look rv c o]

private theorem deriveTurn_world' [DecidableEq D] (X : Ctx D) (U : Unsigned D → ByteArray) (look : Pinned D)
    (rv : RowView D) (c : Call D) (o : D) :
    deriveTurn X look rv c =
      deriveTurn { X with callBytes := fun _ => X.callBytes c, unsignedBytes := U } look rv
        { c with unsigned := { c.unsigned with world := o } } := by
  unfold deriveTurn deriveWithTicks
  rw [tree_world X U look rv c o, dispatch_world X U look rv c o]
  rfl

/-- **The derived Turn reads the call's world only through `callBytes`.** With `callBytes` fixed to
the call's own bytes, the call given any other world derives the same Turn or the same refusal:
no receiver of the call's tree reads `c.unsigned.world`. -/
theorem deriveTurn_world [DecidableEq D] (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (o : D) :
    deriveTurn X look rv c =
      deriveTurn { X with callBytes := fun _ => X.callBytes c } look rv
        { c with unsigned := { c.unsigned with world := o } } :=
  deriveTurn_world' X X.unsignedBytes look rv c o

/-- **`receiveWith` reads the call's world only through the call's two encodings.** With
`callBytes` and `unsignedBytes` fixed to the call's own, the call given any other world is derived
the same, signature check, key rule and tree: `receiveWith`'s own body reads the world only in
the bytes the signature covers and the transaction id hashes. (The views `receive` hands it are
`rowView_world`'s and `carry_receive_world`'s.) -/
theorem receiveWith_world [DecidableEq D] (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (o : D) :
    receiveWith X look rv c =
      receiveWith
        { X with
          callBytes := fun _ => X.callBytes c
          unsignedBytes := fun _ => X.unsignedBytes c.unsigned }
        look rv { c with unsigned := { c.unsigned with world := o } } := by
  unfold receiveWith
  rw [deriveTurn_world' X (fun _ => X.unsignedBytes c.unsigned) look rv c o]
  rfl

/-- **The row view is blind to the call's world**: `rowView` reads the caller's row pins and
ranges, never `Unsigned.world` (`pinned` reads only the pins, which a world update keeps). -/
theorem rowView_world [DecidableEq D] (E : Env D) (w : World D) (u : Unsigned D) (o : D) :
    rowView E w { u with world := o } = rowView E w u := rfl

/-- **A carry changes no derivation but the call's bytes** (KERNEL-40, end to end). The carried
World derives a call naming its new origin exactly as the exported World derives the same call
naming the OLD origin, with the call's two encodings fixed to the new call's own. So nothing on the
receive path, the pinned view and the row view included, reads the world the call names but the
`wrongWorld` check and the bytes. Not an enrolment: its join names the World too (PROTOCOL-79), so
the old World refuses the carried World's join `otherWorld` and the carried World the old one's. -/
theorem carry_receive_world [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority}
    {w w' : World D}
    (h : carry X name nonce w.origin w.carried auth = .ok w') {c : Call D} (hc : c.unsigned.world = w'.origin)
    (hj : c.unsigned.body.joinOrigin = none) :
    receive X w' c =
      receive
        { X with
          callBytes := fun _ => X.callBytes c
          unsignedBytes := fun _ => X.unsignedBytes c.unsigned }
        { w with trie := reauthor X w.trie auth } { c with unsigned := { c.unsigned with world := w.origin } } := by
  rw [carry_receive h hc (by simp [hj]), receiveWith_world X _ _ c w.origin,
    receive_named rfl (by simp [hj]), rowView_world]
  rfl

/-! #### Tooth: a derivation that recomputes an id from the call's world

`leakyReceiveWith` is `receiveWith` with the hazard: its key rule looks the signer up at
`founderId X c.unsigned.world 0`. On one toy context (a byte-sum hash, no pins, every signature
verifying) its two sides refuse `unpinned` at the founder ids of worlds 0 and 1, which differ, so
`receiveWith_world`'s statement is false for it. Toy parameters only. -/

private def leakyKeyRule [DecidableEq D] (X : Ctx D) (look : Pinned D) (u : Unsigned D) : Except (Refusal D) Unit :=
  match u.body with
  | .rotate _ _ => .ok ()
  | _ => checkKey look { u with member := founderId X u.world 0 }

private def leakyReceiveWith [DecidableEq D] (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) :
    Except (Refusal D) (Turn D) := do
  checkSignature X c
  leakyKeyRule X look c.unsigned
  deriveTurn X look rv c

private def wCtx : Ctx UInt8 where
  env :=
    { hash := fun d b => UInt8.ofNat (d.length + b.size + (b.data.toList.map UInt8.toNat).sum)
      bytes := fun d => ⟨#[d]⟩
      turnBytes := fun _ => ByteArray.empty
      cellBytes := fun _ => ByteArray.empty }
  unsignedBytes _ := ByteArray.empty
  callBytes _ := ByteArray.empty
  decodeCall _ := none
  digestOf _ := none
  verify _ _ _ := true
  program :=
    { checkInstall := fun _ _ => .ok ()
      judge := fun _ _ _ _ _ _ => .ok ()
      run := fun _ _ _ s _ _ _ _ => .ok (s, [], [], 0)
      rels := fun _ _ _ => .ok [] }

private def wLook : Pinned UInt8 := fun i => .error (.unpinned i)

private def wRv : RowView UInt8 := ⟨fun _ _ => [], fun _ _ => .ok []⟩

private def wCall : Call UInt8 :=
  { unsigned :=
      { world := 0, member := 9, key := ByteArray.empty, notBefore := 0, validUntil := 1, pins := [],
        maxCharge := 0, body := .retire 3 }
    signature := ByteArray.empty }

private def unpinnedAt : Except (Refusal UInt8) (Turn UInt8) → Option UInt8
  | .error (.unpinned i) => some i
  | _ => none

private theorem leaky_sides :
    unpinnedAt (leakyReceiveWith wCtx wLook wRv wCall) = some (founderId wCtx 0 0) ∧
      unpinnedAt (leakyReceiveWith
        { wCtx with
          callBytes := fun _ => wCtx.callBytes wCall
          unsignedBytes := fun _ => wCtx.unsignedBytes wCall.unsigned }
        wLook wRv { wCall with unsigned := { wCall.unsigned with world := 1 } }) =
        some (founderId wCtx 1 0) ∧
      founderId wCtx 0 0 ≠ founderId wCtx 1 0 := by
  decide +kernel

/-- **Tooth of `receiveWith_world`**: the statement is false for a derivation whose key rule reads
the signer's id as `founderId X c.unsigned.world 0`. -/
theorem receiveWith_world_sep :
    ¬ ∀ (X : Ctx UInt8) (look : Pinned UInt8) (rv : RowView UInt8) (c : Call UInt8) (o : UInt8),
      leakyReceiveWith X look rv c =
        leakyReceiveWith
          { X with
            callBytes := fun _ => X.callBytes c
            unsignedBytes := fun _ => X.unsignedBytes c.unsigned }
          look rv { c with unsigned := { c.unsigned with world := o } } := by
  intro h
  obtain ⟨h0, h1, hne⟩ := leaky_sides
  have := congrArg unpinnedAt (h wCtx wLook wRv wCall 1)
  rw [h0, h1] at this
  exact hne (Option.some.inj this)

/-- `deriveTurn` with the hazard in the tree's half: it first reads the member cell at
`founderId X c.unsigned.world 0`. -/
private def leakyDeriveTurn [DecidableEq D] (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) :
    Except (Refusal D) (Turn D) := do
  let _ ← readKind look (founderId X c.unsigned.world 0) kindMember
  deriveTurn X look rv c

private theorem leakyDerive_sides :
    unpinnedAt (leakyDeriveTurn wCtx wLook wRv wCall) = some (founderId wCtx 0 0) ∧
      unpinnedAt (leakyDeriveTurn { wCtx with callBytes := fun _ => wCtx.callBytes wCall } wLook wRv
        { wCall with unsigned := { wCall.unsigned with world := 1 } }) = some (founderId wCtx 1 0) ∧
      founderId wCtx 0 0 ≠ founderId wCtx 1 0 := by
  decide +kernel

/-- **Tooth of `deriveTurn_world`**: the statement is false for a derivation that reads a cell at
`founderId X c.unsigned.world 0`. -/
theorem deriveTurn_world_sep :
    ¬ ∀ (X : Ctx UInt8) (look : Pinned UInt8) (rv : RowView UInt8) (c : Call UInt8) (o : UInt8),
      leakyDeriveTurn X look rv c =
        leakyDeriveTurn { X with callBytes := fun _ => X.callBytes c } look rv
          { c with unsigned := { c.unsigned with world := o } } := by
  intro h
  obtain ⟨h0, h1, hne⟩ := leakyDerive_sides
  have := congrArg unpinnedAt (h wCtx wLook wRv wCall 1)
  rw [h0, h1] at this
  exact hne (Option.some.inj this)

/-- **Admission is blind to the origin and the chain.** -/
theorem check_origin_blind [DecidableEq D] {E : Env D} {w : World D} {t : Turn D} {o ch : D} :
    check E { w with origin := o, chain := ch } t = check E w t := rfl

/-- **A carry changes no admission but the authority it re-states and the refusals it forgets**:
the carried World checks every turn as the exported one would with its authority cell the stated
one, its window trie cut to the meter (KERNEL-79: a member's ticks this window still count; a
refusal record is the old log's, and a call refused in the old World is `wrongWorld` in the new,
KERNEL-24) and its step counter restarted at its height. -/
theorem carry_check [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (h : carry X name nonce w.origin w.carried auth = .ok w') (t : Turn D) :
    check X.env w' t =
      check X.env
        { w with trie := reauthor X w.trie auth, refusals := meterOnly X.env w.refusals, steps := w.height } t := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  rfl

end Nanodregg.Kernel.Receive
