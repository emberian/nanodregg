import Codec.Proofs.World

/-!
# The carried codec (CODEC-22, KERNEL-41): canonical, both tries read back exactly

* `carried_lawfulOn`: the carried codec `trie ‖ allowance ‖ height ‖ journal ‖ rows` is lawful on
  `Carried.CodecFits`, so `decode b = .ok c ↔ b = bytes c` exactly (`carried_decode_iff`): with the
  journal a trie (KERNEL-41), the `CarriedEquiv` of CODEC-22 is gone.
* `carried_decode_journalFits`: a decoded carried journal is the window's at the carried height
  (`kernel/carried-journal`; `carried_decode_wire_refused` is the refusal).
* `carried_decode_canon`: a decoded cells trie is canonical and every slot holds the leaf of its kind;
  `carried_decode_journalCanon`: a decoded journal trie is canonical.
* `carried_decode_rows`: a decoded carried state's rows fit and every head counts its rows
  (`kernel/carried-rows`, `kernel/carried-rows-headed`; KERNEL-48 carries the rows).
* `carried_decode_window`: a decoded carried window trie is canonical and every leaf fits the carried
  height (`kernel/carried-window`; KERNEL-79 carries the meter);
* `carried_fits`: the carried state of a fitting World is in the codec's domain.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D] [DecidableEq D]

/-- The wire's domain, as the product of its parts. -/
def CarriedWireFits (E : Env D) (PD : D → Prop) (x : CarriedWire D) : Prop :=
  CellsFits E PD x.1 ∧ x.2.1 < 2 ^ 64 ∧ x.2.2.1 < 2 ^ 64 ∧ JournalTrieFits E PD x.2.2.2.1 ∧
    RowsTrieFits E PD x.2.2.2.2.1 ∧ RefusalsTrieFits E PD x.2.2.2.2.2

/-- A carried state in the codec's domain: a canonical cells trie whose slots hold the leaves of their
kinds, counters below 2^64, a canonical journal trie of at most `Bounds.journalMax` entries, every
digest in the digest codec's domain, a journal that is the window's at the carried height, and rows
that fit with every head counting its rows (KERNEL-48). Named fields, one per site. -/
structure Carried.CodecFits (E : Env D) (PD : D → Prop) (c : Carried D) : Prop where
  /-- kernel/leaf-fit, kernel/trie-order -/
  cells : CellsFits E PD c.trie
  allowance : c.allowance < 2 ^ 64
  height : c.height < 2 ^ 64
  /-- kernel/journal-order -/
  journal : JournalTrieFits E PD c.journal
  /-- kernel/carried-journal -/
  journalFits : journalFits c.height c.journal.toList = true
  /-- kernel/row-order, kernel/carried-rows, kernel/carried-rows-headed, kernel/carried-rows-parented -/
  rows : RowsCodecFits E PD c.trie c.rows
  /-- kernel/refusal-order (KERNEL-79: the window trie, its meter carried) -/
  window : RefusalsTrieFits E PD c.refusals
  /-- kernel/carried-window -/
  windowFits : carriedWindowFits c.height c.refusals.toList = true

omit [Ord D] in
theorem carriedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CarriedWireFits E PD) (carriedWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn (journalTrie_lawfulOn E hd)
        (product_lawfulOn (rowsTrie_lawfulOn E hd) (refusalsTrie_lawfulOn E hd)))))).mono
    (fun _ h => h) (fun _ h => h)

/-- **`kernel/carried-journal` is lawful on exactly the journals `journalFits` admits at the carried
height.** -/
theorem carriedJournalWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => CarriedWireFits E PD x ∧
      journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true) (carriedJournalWire E dc) :=
  refineIf_lawfulOn (carriedWire_lawfulOn E hd) "kernel/carried-journal"
    (fun x => journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true)

/-- **`kernel/carried-rows` is lawful on exactly the carried rows `rowsFits` admits.** -/
theorem carriedRowsWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => (CarriedWireFits E PD x ∧
      journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true) ∧
      rowsFits E (carriedOfWire x).rows.toList = true) (carriedRowsWire E dc) :=
  refineIf_lawfulOn (carriedJournalWire_lawfulOn E hd) "kernel/carried-rows"
    (fun x => rowsFits E (carriedOfWire x).rows.toList = true)

/-- **`kernel/carried-rows-headed` is lawful on exactly the carried rows `rowsHeaded` admits.** -/
theorem carriedHeadedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => ((CarriedWireFits E PD x ∧
      journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true) ∧
      rowsFits E (carriedOfWire x).rows.toList = true) ∧ rowsHeaded (carriedOfWire x).rows.toList = true)
      (carriedHeadedWire E dc) :=
  refineIf_lawfulOn (carriedRowsWire_lawfulOn E hd) "kernel/carried-rows-headed"
    (fun x => rowsHeaded (carriedOfWire x).rows.toList = true)

/-- **`kernel/carried-rows-parented` is lawful on exactly the carried relations whose parents are live.** -/
theorem carriedParentedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => (((CarriedWireFits E PD x ∧
      journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true) ∧
      rowsFits E (carriedOfWire x).rows.toList = true) ∧ rowsHeaded (carriedOfWire x).rows.toList = true) ∧
      rowsParented E (carriedOfWire x).trie (carriedOfWire x).rows = true)
      (carriedParentedWire E dc) :=
  refineIf_lawfulOn (carriedHeadedWire_lawfulOn E hd) "kernel/carried-rows-parented"
    (fun x => rowsParented E (carriedOfWire x).trie (carriedOfWire x).rows = true)

/-- **`kernel/carried-window` is lawful on exactly the carried window tries `refusalsFits` admits at the
carried height.** -/
theorem carriedWindowWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun x => ((((CarriedWireFits E PD x ∧
      journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true) ∧
      rowsFits E (carriedOfWire x).rows.toList = true) ∧ rowsHeaded (carriedOfWire x).rows.toList = true) ∧
      rowsParented E (carriedOfWire x).trie (carriedOfWire x).rows = true) ∧
      carriedWindowFits (carriedOfWire x).height (carriedOfWire x).refusals.toList = true)
      (carriedWindowWire E dc) :=
  refineIf_lawfulOn (carriedParentedWire_lawfulOn E hd) "kernel/carried-window"
    (fun x => carriedWindowFits (carriedOfWire x).height (carriedOfWire x).refusals.toList = true)

/-- **The carried codec is lawful on `Carried.CodecFits`.** -/
theorem carried_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Carried.CodecFits E PD) (carried E dc) := by
  unfold carried
  refine (refine_lawfulOn (carriedWindowWire_lawfulOn E hd) "kernel/carried" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; cases h; rfl
  · intro c ⟨⟨⟨⟨⟨⟨hc, ha, hh, hj, hr, hw⟩, hjf⟩, hrf⟩, hrh⟩, hrp⟩, hwf⟩
    exact ⟨hc, ha, hh, hj, hjf, ⟨hr, hrf, hrh, hrp⟩, hw, hwf⟩
  · intro c h
    exact ⟨⟨⟨⟨⟨⟨h.cells, h.allowance, h.height, h.journal, h.rows.listing, h.window⟩, h.journalFits⟩,
      h.rows.fits⟩, h.rows.headed⟩, h.rows.parented⟩, h.windowFits⟩

theorem carried_bytes (E : Env D) (dc : Stream D) (c : Carried D) :
    (carried E dc).bytes c = (carriedWire E dc).bytes (carriedToWire c) := rfl

/-- A fitting carried state reads back from its bytes, exactly. -/
theorem carried_decode_bytes {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {c : Carried D} (hc : Carried.CodecFits E PD c) : (carried E dc).decode ((carried E dc).bytes c) = .ok c :=
  (carried_lawfulOn E hd).decode_bytes hc

/-- Whatever decodes to `c` is exactly `c`'s bytes. -/
theorem eq_bytes_of_carried_decode {E : Env D} {PD : D → Prop} {dc : Stream D}
    (hd : LawfulOn PD dc) {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    b = (carried E dc).bytes c :=
  ((carried_lawfulOn E hd).eq_bytes_of_decode h).2

/-- **Canonicity, exactly**: for a fitting `c`, `b` decodes to `c` iff `b` is `c`'s bytes. -/
theorem carried_decode_iff {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (hc : Carried.CodecFits E PD c) :
    (carried E dc).decode b = .ok c ↔ b = (carried E dc).bytes c :=
  ⟨eq_bytes_of_carried_decode hd, fun h => h ▸ carried_decode_bytes hd hc⟩

theorem carried_decode_fits {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) : Carried.CodecFits E PD c :=
  ((carried_lawfulOn E hd).eq_bytes_of_decode h).1

/-- **A decoded carried state's journal is the window's at its height** (HOST-11's find): an import
never genesis-writes a Store whose base the World codec would then refuse `kernel/journal`. -/
theorem carried_decode_journalFits {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    journalFits c.height c.journal.toList = true :=
  (carried_decode_fits hd h).journalFits

/-- **A decoded carried state's rows fit and every head counts its rows** (KERNEL-48): an import never
genesis-writes a Store whose base the World codec would then refuse `kernel/rows` or
`kernel/rows-headed`. -/
theorem carried_decode_rows {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) : RowsCodecFits E PD c.trie c.rows :=
  (carried_decode_fits hd h).rows

omit [Ord D] in
private theorem carried_decode_wire {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x) :
    (carriedWire E dc).get ((carriedWire E dc).bytes x) 0 = .ok (x, ((carriedWire E dc).bytes x).size) := by
  simpa using (carriedWire_lawfulOn E hd).get_of_occurs x ((carriedWire E dc).bytes x) 0 hx (occursAt_self _)

/-- **The refusal**: a carried wire value whose journal is not the window's at its height is refused
`kernel/carried-journal` by name, at offset 0. -/
theorem carried_decode_wire_refused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x)
    (hj : journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = false) :
    (carried E dc).decode ((carriedWire E dc).bytes x) = .error (.rejected 0 "kernel/carried-journal") := by
  have hg := carried_decode_wire hd hx
  simp only [carried, decode, carriedWindowWire, carriedParentedWire, carriedHeadedWire, carriedRowsWire, carriedJournalWire, refine, hg, hj]
  rfl

/-- **The rows refusal**: a carried wire value whose journal is the window's but whose rows do not fit
is refused `kernel/carried-rows` by name, at offset 0. -/
theorem carried_decode_wire_rowsRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x)
    (hj : journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true)
    (hr : rowsFits E (carriedOfWire x).rows.toList = false) :
    (carried E dc).decode ((carriedWire E dc).bytes x) = .error (.rejected 0 "kernel/carried-rows") := by
  have hg := carried_decode_wire hd hx
  simp only [carried, decode, carriedWindowWire, carriedParentedWire, carriedHeadedWire, carriedRowsWire, carriedJournalWire, refine, hg, hj, hr, ite_true]
  rfl

/-- **The heads refusal**: a carried wire value whose rows fit but a head does not count its rows is
refused `kernel/carried-rows-headed` by name, at offset 0. -/
theorem carried_decode_wire_headedRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x)
    (hj : journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true)
    (hr : rowsFits E (carriedOfWire x).rows.toList = true) (hh : rowsHeaded (carriedOfWire x).rows.toList = false) :
    (carried E dc).decode ((carriedWire E dc).bytes x) = .error (.rejected 0 "kernel/carried-rows-headed") := by
  have hg := carried_decode_wire hd hx
  simp only [carried, decode, carriedWindowWire, carriedParentedWire, carriedHeadedWire, carriedRowsWire, carriedJournalWire, refine, hg, hj, hr, hh,
    ite_true]
  rfl

/-- **The parents refusal**: a carried wire value whose relations fit and count their rows, but one of
whose parents is not a live carried cell, is refused `kernel/carried-rows-parented` by name, at offset 0. -/
theorem carried_decode_wire_parentedRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : CarriedWire D} (hx : CarriedWireFits E PD x)
    (hj : journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList = true)
    (hr : rowsFits E (carriedOfWire x).rows.toList = true) (hh : rowsHeaded (carriedOfWire x).rows.toList = true)
    (hp : rowsParented E (carriedOfWire x).trie (carriedOfWire x).rows = false) :
    (carried E dc).decode ((carriedWire E dc).bytes x) = .error (.rejected 0 "kernel/carried-rows-parented") := by
  have hg := carried_decode_wire hd hx
  simp only [carried, decode, carriedWindowWire, carriedParentedWire, carriedHeadedWire, carriedRowsWire, carriedJournalWire, refine, hg,
    hj, hr, hh, hp, ite_true]
  rfl

/-- A decoded cells trie is canonical (the kernel's `Trie.Canon`) and every slot holds the leaf of its kind. -/
theorem carried_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (trieSpec E) 0 c.trie ∧ ∀ p ∈ c.trie.toList, Leaf.fits p.1 p.2 = true :=
  let hf := carried_decode_fits hd h
  ⟨hf.cells.2, hf.cells.1.2⟩

/-- **A decoded carried window trie is canonical, every leaf fitting the carried height** (KERNEL-79:
the meter the carry keeps is the current window's and bounded). -/
theorem carried_decode_window {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (refusalSpec E) 0 c.refusals ∧ carriedWindowFits c.height c.refusals.toList = true :=
  ⟨(carried_decode_fits hd h).window.2, (carried_decode_fits hd h).windowFits⟩

/-- A decoded journal trie is canonical. -/
theorem carried_decode_journalCanon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {c : Carried D} (h : (carried E dc).decode b = .ok c) :
    Trie.Canon (journalSpec E) 0 c.journal :=
  (carried_decode_fits hd h).journal.2

/-- The carried state of a fitting World is in the codec's domain (the rows as the World holds them). -/
theorem carried_fits {E : Env D} {PD : D → Prop} {w : World D} (hw : World.CodecFits E PD w) :
    Carried.CodecFits E PD w.carried :=
  ⟨hw.cells, Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hw.budget, hw.height, hw.journal, hw.journalFits, hw.rows,
    hw.refusals, by
      have hc := hw.refusalsCounted
      unfold refusalsCounted at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [carriedWindowFits, World.carried, hw.refusalsFits, Bool.true_and, decide_eq_true_eq]
      exact hc.2⟩

end Nanodregg.Codec.Kernel
