/-
# Kernel.Proofs.Carry — a carry moves exactly the carried state into a new World (KERNEL-29)

`Receive.carry` re-geneses a World from a `Carried` state (law 1: state crosses a flag day by
re-genesis, never by a migration). It is checked like genesis (`carry_ok`: refused by name outside
`CarryFits`) and

* `carry_carried`: the new World carries exactly what it was given — byte equality of the
  carried state is HOST's import check (HOST-28), and this is what makes it the right one;
* `carry_origin_ne_genesis`: a carry's origin equal to a genesis's is a collision between the
  two origin inputs (tagged apart, `originInput`); its tooth `carry_origin_ne_genesis_sep`;
* `carry_inj`: a carry's origin commits to its name, nonce, the exported World's origin, the
  trie's root, the rows' root, the allowance, the height and the journal's listing, or the two
  carry inputs collide (with both journals canonical, the journal itself: `carry_inj_canon`; teeth
  `carry_inj_sep`, `carry_inj_canon_sep`);
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

/-- A carry input within the raw codec's bounds, whose allowance plus the carried cells' and rows'
storage is
below 2^64 (so the allowance is, and every World folded from the carry keeps the sum below it:
`Budget.carry_fold_budget_lt`). `carry` refuses by name outside it. -/
def CarryFits (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : Prop :=
  name.size ≤ Bounds.eventBytesMax ∧ nonce.size ≤ Bounds.eventBytesMax ∧
    cellsWeight c.trie + rowsWeight c.rows + c.allowance < 2 ^ 64 ∧
    c.height < 2 ^ 64 ∧ c.journal.toList.length ≤ Bounds.journalMax ∧
    (X.env.bytes fromOrigin).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.trie.hashOf (trieSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    (X.env.bytes (c.rows.hashOf (rowSpec X.env))).size ≤ Bounds.eventBytesMax ∧
    ∀ p ∈ c.journal.toList, (X.env.bytes p.1).size ≤ Bounds.eventBytesMax ∧ p.2.1 < 2 ^ 64 ∧
      (X.env.bytes p.2.2).size ≤ Bounds.eventBytesMax

/-- **The carry check is `CarryFits`**, clause by clause. -/
theorem checkCarry_ok {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D} :
    checkCarry X name nonce fromOrigin c = .ok () ↔ CarryFits X name nonce fromOrigin c := by
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  simp only [checkCarry, req_bind_ok, req_ok, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, hc]
  unfold CarryFits
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, ⟨⟨⟨h6, h7⟩, h7'⟩, h8⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h7', fun p hp => ⟨(h8 p hp).1.1, (h8 p hp).1.2, (h8 p hp).2⟩⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h7', h8⟩
    exact ⟨h1, h2, h3, h4, h5, ⟨⟨⟨h6, h7⟩, h7'⟩, fun p hp => ⟨⟨(h8 p hp).1, (h8 p hp).2.1⟩, (h8 p hp).2.2⟩⟩⟩

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
allowance, height, journal and rows; only its chain and origin are its own. -/
theorem carry_of_carried {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') :
    w'.trie = w.trie ∧ w'.allowance = w.allowance ∧ w'.height = w.height ∧ w'.journal = w.journal ∧
      w'.rows = w.rows ∧ w'.chain = World.genesisChain X.env w'.origin := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem carryInput_lawfulOn :
    LawfulOn (fun v : CarryInput => v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.2.2.2.2.length ≤ Bounds.journalMax ∧
          ∀ x ∈ v.2.2.2.2.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧
            (x.2.1 < 2 ^ 64 ∧ x.2.2.size ≤ Bounds.eventBytesMax))))))))) carryInput :=
  product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
    (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
        (rawList_lawfulOn (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
          (product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide)))) _ (by decide))))))))

omit [Ord D] in
/-- **A carry's origin is never a genesis's** but by a collision between the two origin inputs:
they are the two cases of one tagged codec, so their bytes differ in the first byte. -/
theorem carry_origin_ne_genesis [Ord D] [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D}
    {c : Carried D} {name' nonce' : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    (h : carryOriginOf X name nonce fromOrigin c = originOf X name' nonce' allowance founders) :
    CollidesAmong X.env.hash [carryOriginPre X name nonce fromOrigin c, originPre X name' nonce' allowance founders] :=
  .pair (fun he => (sum_inl_ne_inr genesisInput_lawfulOn carryInput_lawfulOn _ _).symm (congrArg Prod.snd he)) h

omit [Ord D] in
/-- **Tooth of `carry_origin_ne_genesis`**: where the hash separates the two origin inputs, a carry's
origin is not a genesis's. -/
theorem carry_origin_ne_genesis_sep [Ord D] [DecidableEq D] {X : Ctx D} {name nonce : ByteArray}
    {fromOrigin : D} {c : Carried D} {name' nonce' : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)}
    (hs : Separates X.env.hash
      [carryOriginPre X name nonce fromOrigin c, originPre X name' nonce' allowance founders]) :
    carryOriginOf X name nonce fromOrigin c ≠ originOf X name' nonce' allowance founders :=
  fun h => hs.not_collides (carry_origin_ne_genesis h)

theorem carry_fits_input {X : Ctx D} {name nonce : ByteArray} {fromOrigin : D} {c : Carried D}
    (h : CarryFits X name nonce fromOrigin c) :
    let v := carryInputOf X name nonce fromOrigin c
    v.1.size ≤ Bounds.eventBytesMax ∧ (v.2.1.size ≤ Bounds.eventBytesMax ∧
      (v.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.1.size ≤ Bounds.eventBytesMax ∧
        (v.2.2.2.2.1.size ≤ Bounds.eventBytesMax ∧ (v.2.2.2.2.2.1 < 2 ^ 64 ∧
        (v.2.2.2.2.2.2.1 < 2 ^ 64 ∧ (v.2.2.2.2.2.2.2.length ≤ Bounds.journalMax ∧
          ∀ x ∈ v.2.2.2.2.2.2.2, x.1.size ≤ Bounds.eventBytesMax ∧
            (x.2.1 < 2 ^ 64 ∧ x.2.2.size ≤ Bounds.eventBytesMax)))))))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h7', h8⟩ := h
  refine ⟨h1, h2, h6, h7, h7', by simp only [carryInputOf]; omega, h4, ?_, ?_⟩
  · simp only [carryInputOf, List.length_map]; exact h5
  · intro x hx
    simp only [carryInputOf, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact h8 p hp

/-- **A carry commits to everything it was made from**: two carries with one origin had the same
name, nonce, exported origin, trie root, rows root, allowance, height and journal listing, or the
two carry inputs collide. -/
theorem carry_inj {X : Ctx D}
    {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D}
    (hf : CarryFits X name nonce f c) (hf' : CarryFits X name' nonce' f' c')
    (h : carryOriginOf X name nonce f c = carryOriginOf X name' nonce' f' c') :
    (name = name' ∧ nonce = nonce' ∧ f = f' ∧
      c.trie.hashOf (trieSpec X.env) = c'.trie.hashOf (trieSpec X.env) ∧
      c.rows.hashOf (rowSpec X.env) = c'.rows.hashOf (rowSpec X.env) ∧ c.allowance = c'.allowance ∧
      c.height = c'.height ∧ c.journal.toList = c'.journal.toList) ∨
        CollidesAmong X.env.hash [carryOriginPre X name nonce f c, carryOriginPre X name' nonce' f' c'] := by
  by_cases hbytes : originInput.bytes (.inr (carryInputOf X name nonce f c)) =
      originInput.bytes (.inr (carryInputOf X name' nonce' f' c'))
  · left
    unfold originInput at hbytes
    rw [sum_bytes_inr_on carryInput_lawfulOn, sum_bytes_inr_on carryInput_lawfulOn] at hbytes
    have he := carryInput_lawfulOn.bytes_injective (carry_fits_input hf) (carry_fits_input hf')
      (ba_append_cancel _ _ _ hbytes)
    simp only [carryInputOf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, hfo, hr, hrr, ha, hh, hl⟩ := he
    refine ⟨rfl, rfl, hE.bytes_eq hfo, hE.bytes_eq hr, hE.bytes_eq hrr, ha, hh, ?_⟩
    have hinj : Function.Injective (fun p : D × Nat × D => (X.env.bytes p.1, p.2.1, X.env.bytes p.2.2)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (hE.bytes_eq hab.1) (Prod.ext hab.2.1 (hE.bytes_eq hab.2.2))
    exact map_inj hinj hl
  · right
    exact .pair (fun he => hbytes (congrArg Prod.snd he)) h

/-- **With canonical journals, a carry's origin commits to the journal itself** (`carry_inj` and
`Trie.eq_of_toList_eq`: a canonical trie is a function of its listing). -/
theorem carry_inj_canon [DecidableEq D] {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D}
    (hj : Trie.Canon (journalSpec X.env) 0 c.journal) (hj' : Trie.Canon (journalSpec X.env) 0 c'.journal)
    (hf : CarryFits X name nonce f c) (hf' : CarryFits X name' nonce' f' c')
    (h : carryOriginOf X name nonce f c = carryOriginOf X name' nonce' f' c') :
    (name = name' ∧ nonce = nonce' ∧ f = f' ∧
      c.trie.hashOf (trieSpec X.env) = c'.trie.hashOf (trieSpec X.env) ∧
      c.rows.hashOf (rowSpec X.env) = c'.rows.hashOf (rowSpec X.env) ∧ c.allowance = c'.allowance ∧
      c.height = c'.height ∧ c.journal = c'.journal) ∨
        CollidesAmong X.env.hash [carryOriginPre X name nonce f c, carryOriginPre X name' nonce' f' c'] := by
  rcases carry_inj hE hf hf' h with ⟨h1, h2, h3, h4, h4', h5, h6, h7⟩ | hc
  · exact .inl ⟨h1, h2, h3, h4, h4', h5, h6, Trie.eq_of_toList_eq (journalSpec X.env) hj hj' h7⟩
  · exact .inr hc

/-- **Tooth of `carry_inj`**: where the hash separates the two carry inputs, equal origins are equal
carry inputs. -/
theorem carry_inj_sep {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D}
    (hf : CarryFits X name nonce f c) (hf' : CarryFits X name' nonce' f' c')
    (hs : Separates X.env.hash [carryOriginPre X name nonce f c, carryOriginPre X name' nonce' f' c'])
    (h : carryOriginOf X name nonce f c = carryOriginOf X name' nonce' f' c') :
    name = name' ∧ nonce = nonce' ∧ f = f' ∧
      c.trie.hashOf (trieSpec X.env) = c'.trie.hashOf (trieSpec X.env) ∧
      c.rows.hashOf (rowSpec X.env) = c'.rows.hashOf (rowSpec X.env) ∧ c.allowance = c'.allowance ∧
      c.height = c'.height ∧ c.journal.toList = c'.journal.toList :=
  hs.elim (carry_inj hE hf hf' h)

/-- **Tooth of `carry_inj_canon`**: where the hash separates the two carry inputs, equal origins of
canonical carries are equal journals. -/
theorem carry_inj_canon_sep [DecidableEq D] {X : Ctx D} {n : Nat} (hE : X.env.Lawful n)
    {name nonce name' nonce' : ByteArray} {f f' : D} {c c' : Carried D}
    (hj : Trie.Canon (journalSpec X.env) 0 c.journal) (hj' : Trie.Canon (journalSpec X.env) 0 c'.journal)
    (hf : CarryFits X name nonce f c) (hf' : CarryFits X name' nonce' f' c')
    (hs : Separates X.env.hash [carryOriginPre X name nonce f c, carryOriginPre X name' nonce' f' c'])
    (h : carryOriginOf X name nonce f c = carryOriginOf X name' nonce' f' c') :
    name = name' ∧ nonce = nonce' ∧ f = f' ∧
      c.trie.hashOf (trieSpec X.env) = c'.trie.hashOf (trieSpec X.env) ∧
      c.rows.hashOf (rowSpec X.env) = c'.rows.hashOf (rowSpec X.env) ∧ c.allowance = c'.allowance ∧
      c.height = c'.height ∧ c.journal = c'.journal :=
  hs.elim (carry_inj_canon hE hj hj' hf hf' h)

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
theorem carry_journalOk [DecidableEq D] {X : Ctx D} {name nonce : ByteArray}
    {w w' : World D} (hj : w.JournalOk X.env) (h : carry X name nonce w.origin w.carried = .ok w') :
    w'.JournalOk X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hj

/-- **A reached World's journal always fits a carry**: `journalTooLong` never fires on a World
whose journal is `JournalOk` (every World a genesis or a carry reaches). -/
theorem carry_journal_fits [DecidableEq D] {E : Env D} {w : World D} (hj : w.JournalOk E) :
    w.carried.journal.toList.length ≤ Bounds.journalMax :=
  Nat.le_of_lt (journal_bounded hj)

/-- **Carry, then fold: still bounded.** Every World folded from a carry of a `JournalOk` World
holds fewer than `3 * windowMax` journal entries, so a second carry passes `journalTooLong` too. -/
theorem carry_fold_journal_bounded [DecidableEq D] {X : Ctx D}
    {name nonce : ByteArray} {w w' w'' : World D} {l : List (Step D)} (hj : w.JournalOk X.env)
    (h : carry X name nonce w.origin w.carried = .ok w') (hf : World.fold X.env w' l = .ok w'') :
    w''.journal.toList.length < 3 * Bounds.windowMax :=
  journal_bounded (fold_journalOk (carry_journalOk hj h) hf)

/-- **Answered, never re-run** (PROTOCOL-29). A call the exported World journaled is `replayed` at
its original height by the carried World: a call committed just before the export, its reply
lost, settles as committed. -/
theorem carry_replayed [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D} {c : Call D} {hh : Nat} {d : D}
    (h : carry X name nonce w.origin w.carried = .ok w') (hj : w.journalAt X.env (txIdOf X c) = some (hh, d)) :
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
    {rf : Refusals D} {st : Nat} (hc : c.unsigned.world = o) :
    receive X { w with origin := o, chain := ch, refusals := rf, steps := st } c =
      receiveWith X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c := by
  unfold receive
  simp only [req, decide_eq_true hc, if_true]
  rfl

/-- A call that names its World is derived from the World's pinned state alone. -/
theorem receive_named [DecidableEq D] {X : Ctx D} {w : World D} {c : Call D}
    (hc : c.unsigned.world = w.origin) :
    receive X w c = receiveWith X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c := by
  unfold receive
  simp only [req, decide_eq_true hc, if_true]
  rfl

/-- **A carry changes no authority.** The carried World derives every call that names it exactly
as the exported World's own state does past the World check: through the same pinned view (the
same members, keys, grants and cells at the same ids), so the members keep their ids and their
rights. (On the old World the same call is `wrongWorld`: it names the new origin.) -/
theorem carry_receive [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') {c : Call D} (hc : c.unsigned.world = w'.origin) :
    receive X w' c = receiveWith X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact receive_reorigin (w := w) hc

/-- **Admission is blind to the origin and the chain.** -/
theorem check_origin_blind [DecidableEq D] {E : Env D} {w : World D} {t : Turn D} {o ch : D} :
    check E { w with origin := o, chain := ch } t = check E w t := rfl

/-- **A carry changes no admission but the refusals it forgets**: the carried World checks every
turn as the exported one would with its recorded refusals dropped and its step counter restarted at
its height (KERNEL-44: a carry carries no refusals; a call refused in the old World is `wrongWorld`
in the new, KERNEL-24). -/
theorem carry_check [DecidableEq D] {X : Ctx D} {name nonce : ByteArray} {w w' : World D}
    (h : carry X name nonce w.origin w.carried = .ok w') (t : Turn D) :
    check X.env w' t = check X.env { w with refusals := .empty, steps := w.height } t := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  rfl

end Nanodregg.Kernel.Receive
