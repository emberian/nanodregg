/-
# Lang.Proofs.PeerRead — what a declared peer read reads (PROT-6)

`methodReads` with declared peer reads `ps ≠ []`: the peer is the OTHER member of the argument's
`pair` (`peerOf_party`); every point of the `peer` field is read under the peer, never under the
reader (`peerReads_parent`); the peer is a live object cell whose package slot holds this package's
id (`peerReads_package`); an unpinned peer cell is the pinned view's own refusal, by name
(`peerReads_unpinned`); with no peer reads the rows are exactly the reader's own (`methodReads_no_peer`).
-/
import Lang.Program

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- `==` on byte strings is equality (`ByteArray`'s `BEq` compares the arrays). -/
private instance : LawfulBEq ByteArray where
  rfl := by
    intro ⟨a⟩
    show (a == a) = true
    exact beq_self_eq_true a
  eq_of_beq := by
    intro ⟨a⟩ ⟨b⟩ h
    have : (a == b) = true := h
    rw [eq_of_beq this]

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) {rc : ReceiptCheck}

private theorem readsData_record {look : Pinned D} {rels : List (Label × RelDecl)} {rv : RowView D}
    {self : D} {rs : List (Label × RelRead)} {args : Data} {d : Data}
    (h : readsData digestOf rc look rels rv self rs args = .ok d) : ∃ fs, d = .record fs := by
  unfold readsData at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl⟩

/-- The peer is the OTHER member of the pair: the pair names the reader once and a distinct peer.
Falsified by dropping the `samePeer` check (a pair `(self, self)` yields `self`), or by returning
the pair's `a` always. -/
theorem peerOf_party {self q : D} {args : Data}
    (h : peerOf bytesOf digestOf self args = .ok q) :
    ∃ a b, args.field "pair" = some (.record [("a", .digest a), ("b", .digest b)]) ∧ a ≠ b ∧
      ((a = bytesOf self ∧ digestOf b = some q) ∨ (b = bytesOf self ∧ digestOf a = some q)) := by
  unfold peerOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i a b hp
    refine ⟨a, b, hp, ?_⟩
    by_cases hab : (a == b) = true
    · simp [hab] at h
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
      have hne : a ≠ b := fun e => hab (by simp [e])
      refine ⟨hne, ?_⟩
      by_cases ha : (a == bytesOf self) = true
      · simp only [ha, ↓reduceIte] at h
        split at h
        · cases h; exact .inl ⟨by simpa using ha, by assumption⟩
        · cases h
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hb : (b == bytesOf self) = true
        · simp only [hb, ↓reduceIte] at h
          split at h
          · cases h; exact .inr ⟨by simpa using hb, by assumption⟩
          · cases h
        · simp [hb] at h
  · cases h

/-- Every point of the peer part is read under the PEER: the rows are the reader's own record
(under `self`) and, at `peer`, `readsData` under `peerOf`. Falsified by reading the peer part
under `self` (P6). -/
theorem peerReads_parent {look : Pinned D} {pkg : D} {rels : List (Label × RelDecl)}
    {rv : RowView D} {self : D} {args : Data} {rs ps : List (Label × RelRead)} {wd : Data}
    (h : methodReads bytesOf digestOf rc look pkg rels rv self args rs ps = .ok wd) (hps : ps ≠ []) :
    ∃ peer fs pd, peerOf bytesOf digestOf self args = .ok peer ∧
      readsData digestOf rc look rels rv self rs args = .ok (.record fs) ∧
      readsData digestOf rc look rels rv peer ps args = .ok pd ∧
      wd = .record (Row.sort (fs ++ [(peerLabel, pd)])) := by
  unfold methodReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i own hown
    obtain ⟨fs, rfl⟩ := readsData_record digestOf hown
    have he : ps.isEmpty = false := by cases ps <;> simp_all
    simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    cases hpo : peerOf bytesOf digestOf self args with
    | error e => rw [hpo] at h; cases h
    | ok peer =>
      rw [hpo] at h
      simp only at h
      cases hk : readKind look peer kindObject with
      | error e => rw [hk] at h; cases h
      | ok cell =>
        rw [hk] at h
        simp only at h
        by_cases hc : (cell.slots.get slotPackage == some (bytesOf pkg)) = true
        · simp only [hc, ↓reduceIte] at h
          cases hpd : readsData digestOf rc look rels rv peer ps args with
          | error e => rw [hpd] at h; cases h
          | ok pd =>
            rw [hpd] at h
            cases h
            exact ⟨peer, fs, pd, rfl, hown, hpd, rfl⟩
        · simp [hc] at h

/-- The peer is a live object of THIS package: its pinned cell is of kind `kindObject` and its
package slot holds `bytesOf pkg`. Falsified by dropping the package check (P7). -/
theorem peerReads_package {look : Pinned D} {pkg : D} {rels : List (Label × RelDecl)}
    {rv : RowView D} {self : D} {args : Data} {rs ps : List (Label × RelRead)} {wd : Data}
    (h : methodReads bytesOf digestOf rc look pkg rels rv self args rs ps = .ok wd) (hps : ps ≠ []) :
    ∃ peer cell, peerOf bytesOf digestOf self args = .ok peer ∧
      readKind look peer kindObject = .ok cell ∧ cell.slots.get slotPackage = some (bytesOf pkg) := by
  unfold methodReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · have he : ps.isEmpty = false := by cases ps <;> simp_all
    simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    cases hpo : peerOf bytesOf digestOf self args with
    | error e => rw [hpo] at h; cases h
    | ok peer =>
      rw [hpo] at h
      simp only at h
      cases hk : readKind look peer kindObject with
      | error e => rw [hk] at h; cases h
      | ok cell =>
        rw [hk] at h
        simp only at h
        by_cases hc : (cell.slots.get slotPackage == some (bytesOf pkg)) = true
        · exact ⟨peer, cell, rfl, hk, by simpa using hc⟩
        · simp [hc] at h

/-- An unpinned (or otherwise refused) peer cell is the pinned view's own refusal, by name — never
an absent peer. Falsified by reading a refused peer as absent. -/
theorem peerReads_unpinned {look : Pinned D} {pkg : D} {rels : List (Label × RelDecl)}
    {rv : RowView D} {self q : D} {args : Data} {rs ps : List (Label × RelRead)} {own : Data}
    {e : Refusal D}
    (hown : readsData digestOf rc look rels rv self rs args = .ok own) (hps : ps ≠ [])
    (hq : peerOf bytesOf digestOf self args = .ok q) (hl : look q = .error e) :
    methodReads bytesOf digestOf rc look pkg rels rv self args rs ps = .error e := by
  have he : ps.isEmpty = false := by cases ps <;> simp_all
  have hk : readKind look q kindObject = .error e := by unfold readKind; rw [hl]
  unfold methodReads
  simp only [bind, Except.bind, pure, Except.pure, hown, he, Bool.false_eq_true, ↓reduceIte, hq, hk]

/-- Control: with no peer reads the rows are exactly the reader's own. -/
theorem methodReads_no_peer {look : Pinned D} {pkg : D} {rels : List (Label × RelDecl)}
    {rv : RowView D} {self : D} {args : Data} {rs : List (Label × RelRead)} :
    methodReads bytesOf digestOf rc look pkg rels rv self args rs [] =
      readsData digestOf rc look rels rv self rs args := by
  unfold methodReads
  simp only [bind, Except.bind, pure, Except.pure, List.isEmpty_nil, ↓reduceIte]
  split <;> simp_all

end

end Nanodregg.Lang
