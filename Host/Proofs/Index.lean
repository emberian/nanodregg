/-
# Host.Proofs.Index — the fixed-entry index (HOST-33)

`index.log` is fixed-width entries, entry k at byte k · entryBytes, each tagged over its position.

* `Entry.read_bytes` / `Entry.read_sound` — an entry in the layout reads back at its position as
  itself, and a read that returns an entry was handed exactly that entry's bytes at that position
  (its tag verified there): a read never returns an entry whose tag failed;
* `Entry.read_other` — the same bytes read at any other position are refused when the tags at the
  two positions differ (the tag names the position: an entry cannot be moved);
* `run_extract` / `run_read` — the bytes `Entry.run` writes read back entry by entry, by position;
* `entries_ok` / `entries_entryUnfit` / `entries_indexTooLarge` — what one seal's `Base.entries`
  returns, and its two refusals;
* `seal_at_end` / `seal_indexMoved` — a seal appends exactly at the end of the entries the newest
  base counts, or refuses `indexMoved`;
* `entriesSeq_read` — the `index.log` successive seals write from genesis reads back, every entry
  at its position, and the one check open makes passes on it (no Store this Host writes is refused);
* `indexNamed_none` / `indexNamed_unread` — what the one open check means, and its tooth;
* (`Host.Proofs.Base.openWith_verifies_named`) — an open that succeeds found `index.log` holding every entry the base
  counts, and its last entry reading back at its position with the tag the base names;
* `indexClean_none` / `indexClean_unread` — `host check` reads EVERY entry: when it passes, each
  reads back at its position and names its record's offset.
-/
import Host.Open
import Codec.Proofs.Raw

namespace Nanodregg.Host

open Nanodregg.Host.Log
open Nanodregg.Codec (Stream)

theorem Entry.fits_iff (w : Nat) (e : Entry) :
    e.fits w = true ↔ e.height < 2 ^ 64 ∧ e.offset < 2 ^ 64 ∧ e.chain.size = w := by
  simp [Entry.fits, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem nat64_size (n : Nat) : (Stream.nat64.bytes n).size = 8 :=
  (Codec.Stream.nat64_lawfulOn.size_eq n).symm

theorem Entry.body_size (e : Entry) : e.body.size = 16 + e.chain.size := by
  simp only [Entry.body, ByteArray.size_append, nat64_size]

/-- An entry in the layout is `entryBytes` long. -/
theorem Entry.bytes_size (keys : Keys) (k : Nat) (e : Entry) (he : e.chain.size = keys.chainBytes) :
    (Entry.bytes keys k e).size = entryBytes keys := by
  simp only [Entry.bytes, ByteArray.size_append, Entry.body_size, Codec.Digest.size_eq, entryBytes, he,
    Log.tagBytes]

/-- **An entry reads back at its position as itself** (HOST-33): an entry in the layout
(`Entry.fits` at the Store's chain width) is what `Entry.read` returns from its own bytes. -/
theorem Entry.read_bytes (keys : Keys) (k : Nat) (e : Entry) (he : e.fits keys.chainBytes = true) :
    Entry.read keys k (Entry.bytes keys k e) = some e := by
  obtain ⟨hh, ho, hc⟩ := (Entry.fits_iff _ e).mp he
  have hA := nat64_size e.height
  have hB := nat64_size e.offset
  have e1 : (Entry.bytes keys k e).extract 0 8 = Stream.nat64.bytes e.height := by
    simp only [Entry.bytes, Entry.body, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left hA.symm
  have e2 : (Entry.bytes keys k e).extract 8 16 = Stream.nat64.bytes e.offset := by
    simp only [Entry.bytes, Entry.body, ByteArray.append_assoc]
    rw [show (8 : Nat) = 8 + 0 from rfl, show (16 : Nat) = 8 + 8 from rfl,
      ByteArray.extract_append_size_add' hA.symm]
    exact ByteArray.extract_append_eq_left hB.symm
  have e3 : (Entry.bytes keys k e).extract 16 (16 + keys.chainBytes) = e.chain := by
    simp only [Entry.bytes, Entry.body]
    rw [show (16 : Nat) = 16 + 0 from rfl, ByteArray.append_assoc,
      ByteArray.extract_append_size_add' (by simp only [ByteArray.size_append, hA, hB])]
    exact ByteArray.extract_append_eq_left hc.symm
  unfold Entry.read
  rw [e1, e2, Codec.Stream.nat64_lawfulOn.decode_bytes hh, Codec.Stream.nat64_lawfulOn.decode_bytes ho]
  simp only [e3]
  simp

/-- **A read never returns an entry whose tag failed** (HOST-33): an entry `Entry.read` returns at
position `k` was handed exactly `Entry.bytes keys k` of it, the entry's fields and the tag over
`k` and them. -/
theorem Entry.read_sound {keys : Keys} {k : Nat} {b : ByteArray} {e : Entry}
    (h : Entry.read keys k b = some e) : Entry.bytes keys k e = b := by
  unfold Entry.read at h
  split at h
  · simp only at h
    split at h
    · cases h; assumption
    · cases h
  · cases h

/-- **An entry cannot be moved**: the bytes of entry `k` read at another position `j` are refused,
unless the tags over `j` and over `k` are the same (a collision of the Store's MAC). -/
theorem Entry.read_other (keys : Keys) {j k : Nat} (e : Entry) {e' : Entry}
    (h : Entry.read keys j (Entry.bytes keys k e) = some e') : e'.tag keys j = e.tag keys k := by
  have hs := Entry.read_sound h
  unfold Entry.bytes at hs
  have hl : e'.body.size = e.body.size := by
    have := congrArg ByteArray.size hs
    simp only [ByteArray.size_append, Codec.Digest.size_eq] at this
    omega
  have hb : e'.body = e.body := ByteArray.append_inj_left hs hl
  rw [hb] at hs
  have ht := (ByteArray.append_right_inj _).mp hs
  cases ht' : e'.tag keys j
  cases ht'' : e.tag keys k
  rw [ht', ht''] at ht
  simp only at ht
  subst ht
  rfl

/-! ## What seals write -/

theorem run_append (keys : Keys) : ∀ (k : Nat) (a b : List Entry),
    Entry.run keys k (a ++ b) = Entry.run keys k a ++ Entry.run keys (k + a.length) b
  | k, [], b => by simp [Entry.run]
  | k, e :: a, b => by
    simp only [List.cons_append, Entry.run, List.length_cons]
    rw [run_append keys (k + 1) a b, ByteArray.append_assoc, Nat.add_assoc, Nat.add_comm 1 a.length]

theorem run_size (keys : Keys) : ∀ (k : Nat) (es : List Entry), (∀ e ∈ es, e.chain.size = keys.chainBytes) →
    (Entry.run keys k es).size = es.length * entryBytes keys
  | k, [], _ => by simp [Entry.run]
  | k, e :: es, h => by
    simp only [Entry.run, ByteArray.size_append, List.length_cons]
    rw [Entry.bytes_size keys k e (h e (by simp)), run_size keys (k + 1) es (fun x hx => h x (by simp [hx]))]
    rw [Nat.succ_mul, Nat.add_comm]

/-- **Entry i of the bytes `Entry.run` writes from position k is entry k + i**, at byte
i · entryBytes. -/
theorem run_extract (keys : Keys) : ∀ (k : Nat) (es : List Entry) (i : Nat) (hi : i < es.length),
    (∀ e ∈ es, e.chain.size = keys.chainBytes) →
    (Entry.run keys k es).extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys) =
      Entry.bytes keys (k + i) es[i]
  | k, [], i, hi, _ => absurd hi (by simp)
  | k, e :: es, 0, _, h => by
    simp only [Entry.run, Nat.zero_mul, Nat.zero_add, Nat.add_zero, List.getElem_cons_zero]
    exact ByteArray.extract_append_eq_left (Entry.bytes_size keys k e (h e (by simp))).symm
  | k, e :: es, i + 1, hi, h => by
    simp only [Entry.run, List.getElem_cons_succ]
    have hs := Entry.bytes_size keys k e (h e (by simp))
    rw [show (i + 1) * entryBytes keys = entryBytes keys + i * entryBytes keys by rw [Nat.succ_mul, Nat.add_comm],
      show entryBytes keys + i * entryBytes keys + entryBytes keys
        = entryBytes keys + (i * entryBytes keys + entryBytes keys) by omega,
      ByteArray.extract_append_size_add' hs.symm,
      run_extract keys (k + 1) es i (by simpa using hi) (fun x hx => h x (by simp [hx]))]
    rw [show k + 1 + i = k + (i + 1) by omega]

/-- **The index reads back by position** (HOST-33): every entry `Entry.run` writes from position
k, each in the layout, is what `Entry.read` returns at its position. -/
theorem run_read (keys : Keys) (k : Nat) (es : List Entry) (i : Nat) (hi : i < es.length)
    (h : ∀ e ∈ es, e.fits keys.chainBytes = true) :
    Entry.read keys (k + i) ((Entry.run keys k es).extract (i * entryBytes keys)
      (i * entryBytes keys + entryBytes keys)) = some es[i] := by
  rw [run_extract keys k es i hi (fun e he => ((Entry.fits_iff _ e).mp (h e he)).2.2)]
  exact Entry.read_bytes keys (k + i) es[i] (h _ (List.getElem_mem hi))

/-- What one seal's `Base.entries` returns: every entry in the layout, the count advanced by the
entries, at most `indexMax`, the bytes `Entry.run` writes from the old count; no entries, nothing
changes; otherwise the last tag is the last entry's at its position. -/
theorem entries_ok {keys : Keys} {ix ix' : IndexAt} {es : Array Entry} {p : ByteArray}
    (h : Base.entries keys ix es = .ok (p, ix')) :
    (∀ e ∈ es.toList, e.fits keys.chainBytes = true) ∧ ix'.count = ix.count + es.size ∧
      ix'.count ≤ indexMax ∧ p = Entry.run keys ix.count es.toList ∧
      (es.toList = [] → ix' = ix) ∧
      (∀ e, es.back? = some e → ix'.last = e.tag keys (ix'.count - 1)) := by
  unfold Base.entries at h
  split at h
  · cases h
  · rename_i hn
    rw [List.findIdx?_eq_none_iff] at hn
    have hfit : ∀ e ∈ es.toList, e.fits keys.chainBytes = true := fun e he => by simpa using hn e he
    split at h
    · cases h
    · rename_i hle
      split at h
      · rename_i hb
        cases h
        have he : es = #[] := by simpa using hb
        subst he
        exact ⟨hfit, by simp, by simp at hle; omega, by simp [Entry.run], fun _ => rfl, by simp⟩
      · rename_i e hb
        cases h
        exact ⟨hfit, rfl, show ix.count + es.size ≤ indexMax by omega, rfl, fun hnil => by simp_all, fun e' he' => by
          rw [hb] at he'; cases he'; rfl⟩

/-- **The tooth of `entries_ok`'s fit**: entries holding one outside the layout are refused
`entryUnfit` at the first such entry, before anything is encoded. -/
theorem entries_entryUnfit (keys : Keys) (ix : IndexAt) (es : Array Entry) (i : Nat)
    (hi : es.toList.findIdx? (fun e => !e.fits keys.chainBytes) = some i) :
    Base.entries keys ix es = .error (.entryUnfit i) := by
  unfold Base.entries
  rw [hi]

/-- **The lifetime bound** (HOST-33 condition 4): entries in the layout that would take the index
past `indexMax` are refused `indexTooLarge`, before encoding. -/
theorem entries_indexTooLarge (keys : Keys) (ix : IndexAt) (es : Array Entry)
    (hfit : ∀ e ∈ es.toList, e.fits keys.chainBytes = true) (hb : indexMax < ix.count + es.size) :
    Base.entries keys ix es = .error (.indexTooLarge (ix.count + es.size)) := by
  unfold Base.entries
  have hn : es.toList.findIdx? (fun e => !e.fits keys.chainBytes) = none := by
    rw [List.findIdx?_eq_none_iff]; intro e he; simp [hfit e he]
  rw [hn]
  simp only [hb, if_true]

/-- **A seal appends at the end of the entries the newest base counts** (HOST-31, HOST-33). A seal
that succeeds was handed an `index.log` of exactly `ix.count · entryBytes` bytes, its bytes are
`Base.entries`' after `ix`, and the base it writes counts what `Base.entries` returns. So the
entries a checkpoint appends land at the positions their tags name. What is not stated: that
`File.writeAll` appends exactly its bytes at the end (the FFI's contract, `Host/c/file.c`). -/
theorem seal_at_end {W : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W) (w : W)
    (seg : Position) (ix : IndexAt) (entries : Array Entry) (indexSize : Nat)
    {page file : ByteArray} {ix' : IndexAt}
    (h : Base.seal keys c world w seg ix entries indexSize = .ok (page, ix', file)) :
    indexSize = ix.count * entryBytes keys ∧ Base.entries keys ix entries = .ok (page, ix') ∧
      Base.file keys c world w seg ix' = .ok file := by
  unfold Base.seal at h
  split at h
  · cases h
  · rename_i hsz
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i page' ip hp
        split at h
        · cases h
        · rename_i file' hf
          cases h
          exact ⟨by simpa using hsz, hp, hf⟩

/-- **The tooth of `seal_at_end`**: an `index.log` of any other size than the end of the entries
the newest base counts is refused `indexMoved`, before anything is encoded or written. -/
theorem seal_indexMoved {W : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W) (w : W)
    (seg : Position) (ix : IndexAt) (entries : Array Entry) (indexSize : Nat)
    (hne : indexSize ≠ ix.count * entryBytes keys) :
    Base.seal keys c world w seg ix entries indexSize =
      .error (.indexMoved indexSize (ix.count * entryBytes keys)) := by
  unfold Base.seal
  rw [if_pos hne]

/-! ## The one check open makes, and the whole check `host check` makes -/

/-- What `indexNamed` passing means: at count 0 the base names no last tag; otherwise the bytes
read back as entry `count - 1` at its position, with the tag the base names. -/
theorem indexNamed_none {keys : Keys} {n : Nat} {last : Codec.Digest} {b : ByteArray}
    (h : indexNamed keys n last b = none) :
    (n = 0 ∧ last = Codec.Digest.zero) ∨
      (0 < n ∧ ∃ e, Entry.read keys (n - 1) b = some e ∧ e.tag keys (n - 1) = last) := by
  unfold indexNamed at h
  by_cases hn : n = 0
  · rw [if_pos hn] at h
    by_cases hl : last = Codec.Digest.zero
    · exact Or.inl ⟨hn, hl⟩
    · rw [if_neg hl] at h; cases h
  · rw [if_neg hn] at h
    split at h
    · cases h
    · rename_i e he
      by_cases ht : e.tag keys (n - 1) = last
      · exact Or.inr ⟨by omega, e, he, ht⟩
      · rw [if_neg ht] at h; cases h

/-- **The binding tooth of `indexNamed_none`**: a last entry that reads back, but whose tag is not
the `indexLast` the base names (a correctly-tagged entry of an older or another index), is refused
`indexCorrupt`. -/
theorem indexNamed_otherLast (keys : Keys) {n : Nat} (last : Codec.Digest) {b : ByteArray} {e : Entry}
    (hn : 0 < n) (h : Entry.read keys (n - 1) b = some e) (ht : e.tag keys (n - 1) ≠ last) :
    indexNamed keys n last b = some .indexCorrupt := by
  unfold indexNamed
  rw [if_neg (by omega), h]
  simp only [ht, if_false]

/-- **The tooth of `indexNamed_none`**: a last entry that does not read back at its position is
refused `indexCorrupt`. -/
theorem indexNamed_unread (keys : Keys) {n : Nat} (last : Codec.Digest) {b : ByteArray} (hn : 0 < n)
    (h : Entry.read keys (n - 1) b = none) : indexNamed keys n last b = some .indexCorrupt := by
  unfold indexNamed
  rw [if_neg (by omega), h]

theorem indexClean_go_none (keys : Keys) (bytes : ByteArray) (offs : List Nat) :
    ∀ (k h : Nat), indexClean.go keys bytes k h offs = none → ∀ (i : Nat) (hi : i < offs.length),
      ∃ e, Entry.read keys (k + i) (bytes.extract ((k + i) * entryBytes keys)
        ((k + i) * entryBytes keys + entryBytes keys)) = some e ∧ e.offset = offs[i] := by
  induction offs with
  | nil => intro _ _ _ i hi; exact absurd hi (by simp)
  | cons off rest ih =>
    intro k h hgo i hi
    rw [indexClean.go] at hgo
    cases hr : Entry.read keys k (bytes.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys)) with
    | none => rw [hr] at hgo; cases hgo
    | some e =>
      rw [hr] at hgo
      simp only at hgo
      by_cases hc : e.offset = off ∧ h ≤ e.height
      · rw [if_pos hc] at hgo
        cases i with
        | zero => exact ⟨e, by simpa using hr, by simpa using hc.1⟩
        | succ i =>
          obtain ⟨e', he', ho'⟩ := ih (k + 1) e.height hgo i (by simpa using hi)
          exact ⟨e', by rw [show k + (i + 1) = k + 1 + i by omega]; exact he', by simpa using ho'⟩
      · rw [if_neg hc] at hgo; cases hgo

theorem indexClean_go_rise (keys : Keys) (bytes : ByteArray) (offs : List Nat) :
    ∀ (k h : Nat), indexClean.go keys bytes k h offs = none → ∀ (i : Nat) (_ : i + 1 < offs.length) (e e' : Entry),
      Entry.read keys (k + i) (bytes.extract ((k + i) * entryBytes keys)
        ((k + i) * entryBytes keys + entryBytes keys)) = some e →
      Entry.read keys (k + i + 1) (bytes.extract ((k + i + 1) * entryBytes keys)
        ((k + i + 1) * entryBytes keys + entryBytes keys)) = some e' → e.height ≤ e'.height := by
  induction offs with
  | nil => intro _ _ _ i hi; exact absurd hi (by simp)
  | cons off rest ih =>
    intro k h hgo i hi e e' he he'
    rw [indexClean.go] at hgo
    cases hr : Entry.read keys k (bytes.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys)) with
    | none => rw [hr] at hgo; cases hgo
    | some e₀ =>
      rw [hr] at hgo
      simp only at hgo
      by_cases hc : e₀.offset = off ∧ h ≤ e₀.height
      · rw [if_pos hc] at hgo
        cases i with
        | zero =>
          simp only [Nat.add_zero] at he he'
          rw [hr] at he; cases he
          cases rest with
          | nil => exact absurd hi (by simp)
          | cons off' rest' =>
            rw [indexClean.go] at hgo
            rw [he'] at hgo
            simp only at hgo
            split at hgo
            · rename_i hc'; exact hc'.2
            · cases hgo
        | succ i =>
          exact ih (k + 1) e₀.height hgo i (by simpa using hi) e e'
            (by rw [show k + 1 + i = k + (i + 1) by omega]; exact he)
            (by rw [show k + 1 + i + 1 = k + (i + 1) + 1 by omega]; exact he')
      · rw [if_neg hc] at hgo; cases hgo

/-- **`host check` reads every entry** (HOST-33 condition 1): when `indexClean` passes, the index
holds exactly the `count` entries the base counts, one per record frame before the base, EVERY one
reads back at its position under the Store's keys (its tag verified there) and names that record
frame's offset, and heights never fall from one entry to the next. -/
theorem indexClean_none {keys : Keys} {bytes : ByteArray} {count : Nat} {offsets : List Nat}
    (h : indexClean keys bytes count offsets = none) :
    offsets.length = count ∧ bytes.size = count * entryBytes keys ∧
    (∀ (k : Nat) (hk : k < offsets.length), ∃ e,
      Entry.read keys k (bytes.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys)) = some e ∧
        e.offset = offsets[k]) ∧
    (∀ (k : Nat) (_ : k + 1 < offsets.length) (e e' : Entry),
      Entry.read keys k (bytes.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys)) = some e →
      Entry.read keys (k + 1) (bytes.extract ((k + 1) * entryBytes keys)
        ((k + 1) * entryBytes keys + entryBytes keys)) = some e' → e.height ≤ e'.height) := by
  unfold indexClean at h
  by_cases hc : offsets.length ≠ count ∨ bytes.size ≠ count * entryBytes keys
  · rw [if_pos hc] at h; cases h
  · rw [if_neg hc] at h
    refine ⟨by omega, by omega, fun k hk => by simpa using indexClean_go_none keys bytes offsets 0 0 h k hk,
      fun k hk e e' he he' => indexClean_go_rise keys bytes offsets 0 0 h k hk e e' (by simpa using he)
        (by simpa using he')⟩

/-- **The tooth of `indexClean_none`**: when the sizes agree, a first entry that does not read back
is refused at 0. -/
theorem indexClean_unread (keys : Keys) (bytes : ByteArray) (off : Nat) (rest : List Nat)
    (hs : bytes.size = (rest.length + 1) * entryBytes keys)
    (h : Entry.read keys 0 (bytes.extract 0 (entryBytes keys)) = none) :
    indexClean keys bytes (rest.length + 1) (off :: rest) = some 0 := by
  unfold indexClean
  rw [if_neg (by simp [hs])]
  simp only [indexClean.go, Nat.zero_mul, Nat.zero_add, h]

/-- **The count tooth**: an index of another length than the base's count is refused. -/
theorem indexClean_count (keys : Keys) (bytes : ByteArray) (count : Nat) (offsets : List Nat)
    (h : offsets.length ≠ count) : indexClean keys bytes count offsets = some (min count offsets.length) := by
  unfold indexClean
  rw [if_pos (Or.inl h)]

/-! ## The index successive seals write -/

/-- The bytes open reads for a count `n`: the last entry's, or none. -/
theorem lastAt_read (keys : Keys) (n : Nat) (hn : 0 < n) :
    lastAt keys n = ((n - 1) * entryBytes keys, entryBytes keys) := by
  unfold lastAt; rw [if_neg (by omega)]

/-- The entry open reads lies within the entries the base counts. -/
theorem lastAt_within (keys : Keys) (n : Nat) : (lastAt keys n).1 + (lastAt keys n).2 ≤ n * entryBytes keys := by
  unfold lastAt
  split
  · simp
  · rename_i hn
    show (n - 1) * entryBytes keys + entryBytes keys ≤ n * entryBytes keys
    rw [← Nat.succ_mul, show (n - 1).succ = n by omega]
    exact Nat.le_refl _

/-- One seal keeps the open check passing: if `pre` holds the `ix.count` entries the old base
counts and its last entry reads back with the old last tag, then `pre` with this seal's entries
holds the new count and its last entry reads back with the new last tag. -/
theorem entries_named {keys : Keys} {ix ix' : IndexAt} {es : Array Entry} {p pre : ByteArray}
    (h : Base.entries keys ix es = .ok (p, ix')) (hpre : pre.size = ix.count * entryBytes keys)
    (hn : indexNamed keys ix.count ix.last
      (pre.extract (lastAt keys ix.count).1 ((lastAt keys ix.count).1 + (lastAt keys ix.count).2)) = none) :
    (pre ++ p).size = ix'.count * entryBytes keys ∧
      indexNamed keys ix'.count ix'.last ((pre ++ p).extract (lastAt keys ix'.count).1
        ((lastAt keys ix'.count).1 + (lastAt keys ix'.count).2)) = none := by
  obtain ⟨hfit, hc, _, hp, hnil, hlast⟩ := entries_ok h
  have hsz : ∀ e ∈ es.toList, e.chain.size = keys.chainBytes := fun e he => ((Entry.fits_iff _ e).mp (hfit e he)).2.2
  by_cases he : es.toList = []
  · obtain rfl := hnil he
    rw [hp, he]
    simp only [Entry.run, ByteArray.append_empty]
    exact ⟨hpre, hn⟩
  · have hpos : 0 < es.size := by
      rcases Nat.eq_zero_or_pos es.size with h0 | h0
      · exact absurd (by simpa using Array.eq_empty_of_size_eq_zero h0) he
      · exact h0
    have hb : es.back? = some (es[es.size - 1]'(by omega)) := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem]
    have hrun := run_size keys ix.count es.toList hsz
    refine ⟨by rw [ByteArray.size_append, hpre, hp, hrun, hc, Array.length_toList, Nat.add_mul], ?_⟩
    have hcount : 0 < ix'.count := by omega
    rw [lastAt_read keys _ hcount]
    have hoff : (ix'.count - 1) * entryBytes keys = pre.size + (es.size - 1) * entryBytes keys := by
      rw [hpre, hc, ← Nat.add_mul]; congr 1; omega
    rw [hoff, Nat.add_assoc, ByteArray.extract_append_size_add, hp]
    have hr := run_read keys ix.count es.toList (es.size - 1) (by simp; omega) hfit
    have hk : ix.count + (es.size - 1) = ix'.count - 1 := by omega
    rw [hk] at hr
    unfold indexNamed
    rw [if_neg (by omega), hr]
    have hel : es.toList[es.size - 1]'(by simp; omega) = es[es.size - 1]'(by omega) := by
      simp only [Array.getElem_toList]
    simp only [hel, hlast _ hb, if_true]

theorem entriesSeq_named (keys : Keys) : ∀ (ess : List (Array Entry)) (ix : IndexAt) (pre : ByteArray)
    {bytes : ByteArray} {ix'' : IndexAt}, Base.entriesSeq keys ix ess = .ok (bytes, ix'') →
    pre.size = ix.count * entryBytes keys →
    indexNamed keys ix.count ix.last
      (pre.extract (lastAt keys ix.count).1 ((lastAt keys ix.count).1 + (lastAt keys ix.count).2)) = none →
    (pre ++ bytes).size = ix''.count * entryBytes keys ∧
      indexNamed keys ix''.count ix''.last ((pre ++ bytes).extract (lastAt keys ix''.count).1
        ((lastAt keys ix''.count).1 + (lastAt keys ix''.count).2)) = none
  | [], ix, pre, bytes, ix'', h, hpre, hn => by
    simp only [Base.entriesSeq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ByteArray.append_empty]; exact ⟨hpre, hn⟩
  | es :: ess, ix, pre, bytes, ix'', h, hpre, hn => by
    simp only [Base.entriesSeq] at h
    split at h
    · cases h
    · rename_i p ix' hp
      split at h
      · cases h
      · rename_i ps ix2 hps
        cases h
        obtain ⟨h1, h2⟩ := entries_named hp hpre hn
        have := entriesSeq_named keys ess ix' (pre ++ p) hps h1 h2
        rwa [ByteArray.append_assoc] at this

theorem entriesSeq_run (keys : Keys) : ∀ (ess : List (Array Entry)) (ix : IndexAt)
    {bytes : ByteArray} {ix'' : IndexAt}, Base.entriesSeq keys ix ess = .ok (bytes, ix'') →
    bytes = Entry.run keys ix.count (ess.map Array.toList).flatten ∧
      ix''.count = ix.count + (ess.map Array.toList).flatten.length ∧
      ∀ e ∈ (ess.map Array.toList).flatten, e.fits keys.chainBytes = true
  | [], ix, bytes, ix'', h => by
    simp only [Base.entriesSeq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Entry.run]
  | es :: ess, ix, bytes, ix'', h => by
    simp only [Base.entriesSeq] at h
    split at h
    · cases h
    · rename_i p ix' hp
      split at h
      · cases h
      · rename_i ps ix2 hps
        cases h
        obtain ⟨hfit, hc, _, hpb, _, _⟩ := entries_ok hp
        obtain ⟨hb, hc', hf⟩ := entriesSeq_run keys ess ix' hps
        refine ⟨?_, ?_, ?_⟩
        · rw [hpb, hb, hc, List.map_cons, List.flatten_cons, run_append, Array.length_toList]
        · rw [hc', hc]; simp [Nat.add_assoc]
        · intro e he
          simp only [List.map_cons, List.flatten_cons, List.mem_append] at he
          rcases he with he | he
          · exact hfit e he
          · exact hf e he

/-- **No entry the seals wrote is lost, and no Store this Host writes is refused by the one open
check** (HOST-33; replaces HOST-31's `indexEntries_pages`). The `index.log` successive seals write
from genesis (`Base.entriesSeq` from `indexStart`, one `Base.entries` per seal) is exactly
`entryBytes` per entry; EVERY entry handed to every seal reads back at its own position, in
order (`run_read`); and the check open makes over the last one passes (`indexNamed`). No premise:
`Base.entries` refuses an entry outside the layout (`entryUnfit`). That successive seals are what
the loop's seals append is two facts: each seal appends at the end (`seal_at_end`, `indexMoved`
otherwise), and seal k+1 is handed seal k's returned `IndexAt` (`spawnSeal` passes
`sealed.index`, `settle` stores the returned one, at most one seal pending): read off
Host/Loop.lean (IO), not proved. -/
theorem entriesSeq_read (keys : Keys) (ess : List (Array Entry)) {bytes : ByteArray} {ix : IndexAt}
    (h : Base.entriesSeq keys indexStart ess = .ok (bytes, ix)) :
    bytes.size = ix.count * entryBytes keys ∧ ix.count = (ess.map Array.toList).flatten.length ∧
      (∀ (i : Nat) (hi : i < (ess.map Array.toList).flatten.length),
        Entry.read keys i (bytes.extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys)) =
          some (ess.map Array.toList).flatten[i]) ∧
      indexNamed keys ix.count ix.last
        (bytes.extract (lastAt keys ix.count).1 ((lastAt keys ix.count).1 + (lastAt keys ix.count).2)) = none := by
  obtain ⟨hb, hc, hf⟩ := entriesSeq_run keys ess indexStart h
  have hn := entriesSeq_named keys ess indexStart ByteArray.empty h (by simp [indexStart])
    (by simp [indexNamed, indexStart])
  simp only [ByteArray.empty_append] at hn
  refine ⟨hn.1, by simpa [indexStart] using hc, fun i hi => ?_, hn.2⟩
  rw [hb]
  have := run_read keys indexStart.count _ i hi hf
  simpa [indexStart] using this

end Nanodregg.Host
