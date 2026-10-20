/-
# Host.Proofs.Segs — the multi-file reader returns the logical segment (HOST-64's named follow-up)

HOST-64 split the segment into files `seg.<o>.log` = header ‖ the logical bytes from `o`, and proved
the open over ONE logical byte sequence (`segReader`). The files are read by `Host.Store.Segs.read`,
which learns the files (`cover`, `size`: each header verified, each file ending where the next
starts) and reads through `segRead`. This module states what `segRead` returns:

* `segGather_logical` — over files that are slices of one logical sequence `L` (`SlicesOf`: ascending,
  each body `L`'s bytes up to the next file's start, the newest to `L`'s end), the bytes gathered from
  `cur` (at or past the oldest file's start) to `stop` are `L.extract cur stop`;
* `segRead_logical` — `segRead` returns `L.extract off (off + len)` for every `off` from the
  `Log.tagBytes` bytes before the oldest file on, when the oldest file's header tag is those bytes of
  `L` (what the writer puts there: the tag the file's first frame chains from), and that file starts
  at or past `Log.tagBytes` (every file but `seg.0.log` follows the origin frame, which is longer;
  `seg.0.log` itself is `segRead_whole`'s case);
* `segRead_whole` — the retain=∞ identity: a Store keeping every file (`retainedFrom` = 0, the oldest
  file at 0) reads, at every offset, exactly what `segReader` over the logical bytes reads, which is
  what the single `seg.log` held before HOST-64; no header tag is read.
* `slicesOf_two`, `slicesOf_whole` — `SlicesOf` holds at a real file boundary and for the one-file
  layout; the teeth `segGather_gap` (a read before the oldest known file's start gathers nothing)
  and `segGather_short` (a body shorter than its slice: the read stops short of the extract).

What is NOT stated here: that the bytes the IO reads ARE a file's body past its header (the File
layer, `Host/c/file.c`), and that the files on disk satisfy `SlicesOf` for the segment the writer
appended. The headers' contiguity checks (`Segs.cover`, `Segs.size`: each file's start is its
predecessor's start plus its body) pin the starts; the bytes are the MAC chain's (`openWith`).
-/
import Host.Segment
import Host.Open

namespace Nanodregg.Host

open ByteArray

/-- `starts` are files of the logical sequence `L`, `body o` the bytes the file starting at `o`
holds past its header: ascending, each body `L`'s slice up to the next file's start, the newest
`L`'s slice to its end. -/
def SlicesOf (L : ByteArray) (body : Nat → ByteArray) : List Nat → Prop
  | [] => True
  | [o] => o ≤ L.size ∧ body o = L.extract o L.size
  | o :: n :: rest => o ≤ n ∧ body o = L.extract o n ∧ SlicesOf L body (n :: rest)

theorem SlicesOf.le_size {L : ByteArray} {body : Nat → ByteArray} :
    ∀ {o : Nat} {rest : List Nat}, SlicesOf L body (o :: rest) → o ≤ L.size
  | _, [], h => h.1
  | _, _ :: _, h => Nat.le_trans h.1 (SlicesOf.le_size h.2.2)

theorem extract_clamp (L : ByteArray) (i j : Nat) : L.extract i j = L.extract i (min j L.size) := by
  by_cases hj : j ≤ L.size
  · rw [Nat.min_eq_left hj]
  · rw [Nat.min_eq_right (by omega)]
    by_cases hi : i ≤ L.size
    · rw [extract_eq_extract_append_extract L.size hi (by omega)]
      have : L.extract L.size j = ByteArray.empty := by rw [extract_eq_empty_iff]; omega
      rw [this, append_empty]
    · have h1 : L.extract i j = ByteArray.empty := by rw [extract_eq_empty_iff]; omega
      have h2 : L.extract i L.size = ByteArray.empty := by rw [extract_eq_empty_iff]; omega
      rw [h1, h2]

/-- The reader over the files' bodies held in memory. -/
private abbrev bodyReader (body : Nat → ByteArray) : Nat → Nat → Nat → Id ByteArray :=
  fun o p n => pure ((body o).extract p (p + n))

/-- **The files read as the logical sequence they slice.** From any `cur` at or past the oldest
file's start (or with nothing left to read), the bytes gathered to `stop` are `L.extract cur stop`. -/
theorem segGather_logical (L : ByteArray) (body : Nat → ByteArray) :
    ∀ (rest : List Nat) (o cur stop : Nat), SlicesOf L body (o :: rest) → (o ≤ cur ∨ stop ≤ cur) →
      Id.run (segGather (bodyReader body) (o :: rest) cur stop) = L.extract cur stop := by
  intro rest
  induction rest with
  | nil =>
    intro o cur stop hs hc
    have hlo := hs.1
    rw [segGather]
    by_cases hst : stop ≤ cur
    · rw [if_pos (Or.inl hst)]
      show ByteArray.empty = _
      exact (extract_eq_empty_iff.mpr (by omega)).symm
    · rw [if_neg (by omega)]
      show (body o).extract (cur - o) (cur - o + (stop - cur)) = _
      rw [hs.2, extract_extract, extract_clamp L cur stop]
      congr 1 <;> omega
  | cons n more ih =>
    intro o cur stop hs hc
    obtain ⟨hon, hbo, hs'⟩ := hs
    have hn := hs'.le_size
    rw [segGather]
    by_cases hst : stop ≤ cur
    · rw [if_pos (Or.inl hst)]
      show ByteArray.empty = _
      exact (extract_eq_empty_iff.mpr (by omega)).symm
    · rw [if_neg (by omega)]
      simp only [List.head?_cons]
      by_cases hnc : n ≤ cur
      · rw [if_pos hnc]
        exact ih n cur stop hs' (Or.inl hnc)
      · rw [if_neg hnc]
        have hgot : (body o).extract (cur - o) (cur - o + (min stop n - cur)) = L.extract cur (min stop n) := by
          rw [hbo, extract_extract]; congr 1 <;> omega
        have hsz : (L.extract cur (min stop n)).size = min stop n - cur := by
          rw [size_extract]; omega
        show Id.run (do
          let got ← bodyReader body o (cur - o) (min stop n - cur)
          if got.size < min stop n - cur then pure got else
          return got ++ (← segGather (bodyReader body) (n :: more) (cur + got.size) stop)) = _
        simp only [bodyReader, hgot, hsz, Nat.lt_irrefl, if_false, pure_bind, Id.run_bind]
        have hrest := ih n (cur + (min stop n - cur)) stop hs' (by omega)
        show L.extract cur (min stop n) ++
          Id.run (segGather (bodyReader body) (n :: more) (cur + (min stop n - cur)) stop) = _
        rw [hrest, show cur + (min stop n - cur) = min stop n by omega]
        exact (extract_eq_extract_append_extract _ (by omega) (by omega)).symm

/-- **`segRead` returns the logical extract** from every offset at or past the `Log.tagBytes` bytes
before the oldest file, when the oldest file's header tag (`tagAt first`) is those bytes of `L`. -/
theorem segRead_logical {E : Type} (L : ByteArray) (body : Nat → ByteArray) (tag : ByteArray)
    {first : Nat} {rest : List Nat} {off len : Nat} (hs : SlicesOf L body (first :: rest))
    (ht : tag = L.extract (first - Log.tagBytes) first) (hf : Log.tagBytes ≤ first)
    (hoff : first - Log.tagBytes ≤ off) :
    Id.run (segRead (E := E) (fun _ => pure (.ok tag)) (bodyReader body) (first :: rest) off len) =
      .ok (L.extract off (off + len)) := by
  have hl := hs.le_size
  unfold segRead
  by_cases ho : off < first
  · have htb : first - off ≤ Log.tagBytes := by omega
    simp only [ho, htb, if_true]
    have hT : tag.extract (Log.tagBytes - (first - off)) Log.tagBytes = L.extract off first := by
      rw [ht, extract_extract]; congr 1 <;> omega
    have hTs : (L.extract off first).size = first - off := by rw [size_extract]; omega
    have hT2 : (L.extract off first).extract 0 (min (first - off) (off + len - off)) =
        L.extract off (min first (off + len)) := by
      rw [extract_extract]; congr 1 <;> omega
    have hT2s : (L.extract off (min first (off + len))).size = min first (off + len) - off := by
      rw [size_extract]; omega
    simp only [hT, hTs, hT2, hT2s, pure_bind, Id.run_bind]
    show Except.ok (L.extract off (min first (off + len)) ++
      Id.run (segGather (bodyReader body) (first :: rest) (off + (min first (off + len) - off)) (off + len))) = _
    rw [segGather_logical L body rest first _ _ hs (by omega),
      show off + (min first (off + len) - off) = min first (off + len) by omega,
      ← extract_eq_extract_append_extract _ (by omega) (by omega)]
  · simp only [ho, if_false]
    show Except.ok (Id.run (segGather (bodyReader body) (first :: rest) off (off + len))) = _
    rw [segGather_logical L body rest first _ _ hs (by omega)]

/-- **The retain=∞ identity** (HOST-64's claim, as a theorem): a Store keeping every file reads,
at every offset, what `segReader` over the logical bytes reads, which is what the single `seg.log`
held before the split. The oldest file starts at 0, so no header tag is ever read. -/
theorem segRead_whole {E F : Type} (L : ByteArray) (body : Nat → ByteArray)
    (tagAt : Nat → Id (Except E ByteArray)) {rest : List Nat} (hs : SlicesOf L body (0 :: rest))
    (off len : Nat) :
    Id.run (segRead tagAt (bodyReader body) (0 :: rest) off len) = .ok (L.extract off (off + len)) ∧
      Id.run (segReader (F := F) L off len) = .ok (L.extract off (off + len)) := by
  refine ⟨?_, rfl⟩
  unfold segRead
  simp only [Nat.not_lt_zero, if_false]
  show Except.ok (Id.run (segGather (bodyReader body) (0 :: rest) off (off + len))) = _
  rw [segGather_logical L body rest 0 _ _ hs (by omega)]

/-! ## Satisfiable, and teeth -/

/-- **`SlicesOf` holds at a real split**: two files cut at `b` (the boundary a rotation makes) slice
`L`, and `segRead_logical` applies to them. -/
theorem slicesOf_two (L : ByteArray) {a b : Nat} (hab : a < b) (hb : b ≤ L.size) :
    SlicesOf L (fun x => if x = a then L.extract a b else L.extract b L.size) [a, b] :=
  ⟨Nat.le_of_lt hab, by simp, hb, by simp [Nat.ne_of_gt hab]⟩

/-- One file holding the whole of `L` from 0 (the layout before HOST-64) slices it. -/
theorem slicesOf_whole (L : ByteArray) : SlicesOf L (fun _ => L) [0] :=
  ⟨Nat.zero_le _, extract_zero_size.symm⟩

/-- **Tooth: a gap reads nothing.** A read from before the oldest known file's start (a file the
headers did not reach) gathers no bytes: the coverage premise of `segGather_logical` is needed. -/
theorem segGather_gap {m : Type → Type} [Monad m] (rd : Nat → Nat → Nat → m ByteArray)
    {o cur stop : Nat} (rest : List Nat) (h : cur < o) :
    segGather rd (o :: rest) cur stop = pure .empty := by
  rw [segGather, if_pos (Or.inr h)]

/-- **Tooth: a body shorter than its slice is not the logical extract.** Two files over 1 2 3 4 cut
at 2, the first holding only `1`: the read of `[0, 4)` stops at the short body and returns `1`,
not the four bytes, so `SlicesOf`'s body equation is what the conclusion rests on. -/
theorem segGather_short :
    Id.run (segGather (bodyReader (fun x => if x = 0 then ⟨#[1]⟩ else ⟨#[3, 4]⟩)) [0, 2] 0 4) =
        ⟨#[1]⟩ ∧
      (⟨#[1, 2, 3, 4]⟩ : ByteArray).extract 0 4 ≠ ⟨#[1]⟩ := by
  decide

end Nanodregg.Host
