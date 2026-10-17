/-
# Kernel.Proofs.Carry — a carry moves exactly the carried state into a new World (KERNEL-29)

`Receive.carry` re-geneses a World from a `Carried` state (law 1: state crosses a flag day by
re-genesis, never by a migration). It is checked like genesis (`carry_ok`: refused by name outside
`CarryFits`) and

* `carry_carried`: the new World carries exactly what it was given — byte equality of the
  carried state is HOST's import check (HOST-28), and this is what makes it the right one;
* `carry_origin_ne_genesis`: a carry's origin is never a genesis's origin, or the origin hash has
  a collision (the two inputs are tagged apart, `originInput`);
* `carry_inj`: a carry's origin commits to its name, nonce, the exported World's origin, the
  trie's root, the allowance, the height and the journal (up to `Equiv`), or a collision;
* `carry_canon`, `carry_cellsFit`, `carry_journalOk`: the new World keeps every invariant the
  read and journal theorems rest on (true by construction: the fields are copied);
  `carry_journal_fits`, `carry_fold_journal_bounded`: a reached World always fits a carry, and
  so does every World folded from a carry;
* `carry_replayed`: a call the exported World journaled is answered `replayed` at its height by
  the new World — answered, never re-run (PROTOCOL-29).
-/
import Kernel.Proofs.Lawful
import Kernel.Proofs.Origin
import Kernel.Proofs.Journal
import Kernel.Proofs.CellsFit

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

/-- A carry input within the raw codec's bounds. `carry` refuses by name outside it. -/
def CarryFits (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : Prop :=
  name.size ≤ Bounds.eventBytesMax ∧ nonce.size ≤ Bounds.eventBytesMax ∧ c.allowance < 2 ^ 64 ∧
    c.height < 2 ^ 64 ∧ c.journal.size ≤ Bounds.journalMax ∧
    (X.env.bytes fromOrigin).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.trie.hashOf (trieSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    ∀ p ∈ c.journal.toList, (X.env.bytes p.1).size ≤ Bounds.eventBytesMax ∧ p.2.1 < 2 ^ 64 ∧
      (X.env.bytes p.2.2).size ≤ Bounds.eventBytesMax

/-- **The carry check is `CarryFits`**, clause by clause. -/
theorem checkCarry_ok {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} :
    checkCarry X name nonce fromOrigin c = .ok () ↔ CarryFits X name nonce fromOrigin c := by
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  simp only [checkCarry, req_bind_ok, req_ok, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, hc]
  unfold CarryFits
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, ⟨⟨h6, h7⟩, h8⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun p hp => ⟨(h8 p hp).1.1, (h8 p hp).1.2, (h8 p hp).2⟩⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, ⟨⟨h6, h7⟩, fun p hp => ⟨⟨(h8 p hp).1, (h8 p hp).2.1⟩, (h8 p hp).2.2⟩⟩⟩

/-- **Carry is checked**: it returns a World exactly on a `CarryFits` input, and that World is
`carryWorld`. -/
theorem carry_ok {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {w : World D} :
    carry X name nonce fromOrigin c = .ok w ↔
      CarryFits X name nonce fromOrigin c ∧ w = carryWorld X name nonce fromOrigin c := by
  unfold carry
  rw [except_bind_ok]
  constructor
  · rintro ⟨⟨⟩, hc, hw⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hw
    exact ⟨checkCarry_ok.mp hc, hw.symm⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨(), checkCarry_ok.mpr hf, rfl⟩

/-- **A carry carries exactly what it was given.** -/
theorem carry_carried {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} {w : World D}
    (h : carry X name nonce fromOrigin c = .ok w) : w.carried = c := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  rfl

/-- **Export, then carry: the same state.** The new World holds the exported World's trie,
allowance, height and journal; only its chain and origin are its own. -/
theorem carry_of_carried {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') :
    w'.trie = w.trie ∧ w'.allowance = w.allowance ∧ w'.height = w.height ∧ w'.journal = w.journal ∧
      w'.chain = World.genesisChain X.env w'.origin := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem carryInput_lawfulOn :
    LawfulOn (fun v : CarryInput => v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.2.2.2.length ≤ Bounds.journalMax ∧
          ∀ x ∈ v.2.2.2.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧
            (x.2.1 < 2 ^ 64 ∧ x.2.2.size ≤ Bounds.eventBytesMax)))))))) carryInput :=
  product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
    (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
        (rawList_lawfulOn (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
          (product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide)))) _ (by decide)))))))

omit [Ord D] in
/-- **A carry's origin is never a genesis's**, or the origin hash has a collision: the two inputs
are the two cases of one tagged codec, so their bytes differ in the first byte. -/
theorem carry_origin_ne_genesis [Ord D] [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D}
    {c : Carried D} {name' nonce' : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    (h : carryOriginOf X name nonce fromOrigin c = originOf X name' nonce' allowance founders) :
    HashColl X.env domOrigin :=
  ⟨_, _, (sum_inl_ne_inr genesisInput_lawfulOn carryInput_lawfulOn _ _).symm, h⟩

theorem carry_fits_input {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    (h : CarryFits X name nonce fromOrigin c) :
    let v := carryInputOf X name nonce fromOrigin c
    v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.2.2.2.length ≤ Bounds.journalMax ∧
          ∀ x ∈ v.2.2.2.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧
            (x.2.1 < 2 ^ 64 ∧ x.2.2.size ≤ Bounds.eventBytesMax))))))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h6, h7, h3, h4, ?_, ?_⟩
  · simp only [carryInputOf, List.length_map, Std.TreeMap.length_toList]; exact h5
  · intro x hx
    simp only [carryInputOf, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact h8 p hp

/-- **A carry commits to everything it was made from**: two carries with one origin had the same
name, nonce, exported origin, trie root, allowance, height and journal (up to `Equiv`), or the
origin hash has a collision. -/
theorem carry_inj [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D}
    {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D}
    (hf : CarryFits X name nonce f c) (hf' : CarryFits X name' nonce' f' c')
    (h : carryOriginOf X name nonce f c = carryOriginOf X name' nonce' f' c') :
    (name = name' ∧ nonce = nonce' ∧ f = f' ∧
      c.trie.hashOf (trieSpec X.env) = c'.trie.hashOf (trieSpec X.env) ∧ c.allowance = c'.allowance ∧
      c.height = c'.height ∧ c.journal.Equiv c'.journal) ∨ HashColl X.env domOrigin := by
  by_cases hbytes : originInput.bytes (.inr (carryInputOf X name nonce f c)) =
      originInput.bytes (.inr (carryInputOf X name' nonce' f' c'))
  · left
    unfold originInput at hbytes
    rw [sum_bytes_inr_on carryInput_lawfulOn, sum_bytes_inr_on carryInput_lawfulOn] at hbytes
    have he := carryInput_lawfulOn.bytes_injective (carry_fits_input hf) (carry_fits_input hf')
      (ba_append_cancel _ _ _ hbytes)
    simp only [carryInputOf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, hfo, hr, ha, hh, hl⟩ := he
    refine ⟨rfl, rfl, hE.bytes_eq hfo, hE.bytes_eq hr, ha, hh, ?_⟩
    have hinj : Function.Injective (fun p : D × Nat × D => (X.env.bytes p.1, p.2.1, X.env.bytes p.2.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (hE.bytes_eq hab.1) (Prod.ext hab.2.1 (hE.bytes_eq hab.2.2))
    exact Std.TreeMap.equiv_iff_toList_eq.mpr (map_inj hinj hl)
  · right
    exact ⟨_, _, hbytes, h⟩

/-- A carried World is canonical when the exported one was: the trie is the same. -/
theorem carry_canon {X : Ctx D} {name nonce : ByteArray} {w w' : World D} (hc : w.Canon X.env)
    (h : carry X name nonce w.origin w.carried = .ok w') : w'.Canon X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hc

/-- A carried World's cells fit when the exported one's did. -/
theorem carry_cellsFit [DecidableEq D] {X : Ctx D} {F : Cell → Prop} {name nonce : ByteArray} {w w' : World D}
    (hc : w.CellsFit F X.env) (h : carry X name nonce w.origin w.carried = .ok w') : w'.CellsFit F X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hc

/-- A carried World's journal is bounded when the exported one's was (same entries, same height). -/
theorem carry_journalOk [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {name nonce : ByteArray}
    {w w' : World D} (hj : w.JournalOk) (h : carry X name nonce w.origin w.carried = .ok w') :
    w'.JournalOk := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hj

/-- **A reached World's journal always fits a carry**: `journalTooLong` never fires on a World
whose journal is `JournalOk` (every World a genesis or a carry reaches). -/
theorem carry_journal_fits [Std.TransOrd D] [Std.LawfulEqOrd D] {w : World D} (hj : w.JournalOk) :
    w.carried.journal.size ≤ Bounds.journalMax :=
  Nat.le_of_lt (journal_bounded hj)

/-- **Carry, then fold: still bounded.** Every World folded from a carry of a `JournalOk` World
holds fewer than `3 * windowMax` journal entries, so a second carry passes `journalTooLong` too. -/
theorem carry_fold_journal_bounded [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] {X : Ctx D}
    {name nonce : ByteArray} {w w' w'' : World D} {l : List (Turn D)} (hj : w.JournalOk)
    (h : carry X name nonce w.origin w.carried = .ok w') (hf : World.fold X.env w' l = .ok w'') :
    w''.journal.size < 3 * Bounds.windowMax :=
  journal_bounded (fold_journalOk (carry_journalOk hj h) hf)

/-- **Answered, never re-run** (PROTOCOL-29). A call the exported World journaled is `replayed` at
its original height by the carried World: a call committed just before the export, its reply
lost, settles as committed. -/
theorem carry_replayed [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D} {c : Call D} {hh : Nat} {d : D}
    (h : carry X name nonce w.origin w.carried = .ok w') (hj : w.journal[txIdOf X c]? = some (hh, d)) :
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
    (hc : c.unsigned.world = o) :
    receive X { w with origin := o, chain := ch } c = receiveWith X (pinned X.env w c.unsigned.pins) c := by
  unfold receive
  simp only [req, decide_eq_true hc, if_true]
  rfl

/-- A call that names its World is derived from the World's pinned state alone. -/
theorem receive_named [DecidableEq D] {X : Ctx D} {w : World D} {c : Call D}
    (hc : c.unsigned.world = w.origin) :
    receive X w c = receiveWith X (pinned X.env w c.unsigned.pins) c := by
  unfold receive
  simp only [req, decide_eq_true hc, if_true]
  rfl

/-- **A carry changes no authority.** The carried World derives every call that names it exactly
as the exported World's own state does past the World check: through the same pinned view (the
same members, keys, grants and cells at the same ids), so the members keep their ids and their
rights. (On the old World the same call is `wrongWorld`: it names the new origin.) -/
theorem carry_receive [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') {c : Call D} (hc : c.unsigned.world = w'.origin) :
    receive X w' c = receiveWith X (pinned X.env w c.unsigned.pins) c := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact receive_reorigin (w := w) hc

/-- **Admission is blind to the origin and the chain.** -/
theorem check_origin_blind [DecidableEq D] {E : Env D} {w : World D} {t : Turn D} {o ch : D} :
    check E { w with origin := o, chain := ch } t = check E w t := rfl

/-- **A carry changes no admission**: the carried World checks every turn as the exported one. -/
theorem carry_check [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') (t : Turn D) :
    check X.env w' t = check X.env w t := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact check_origin_blind

end Nanodregg.Kernel.Receive
