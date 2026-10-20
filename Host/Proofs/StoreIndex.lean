/-
# Host.Proofs.StoreIndex — the Store's index is coherent, at every open (cv 01a15180-9499)

`StoreIndexes` is `Host.Proofs.Coherence`'s `Page.Indexes` for a Store, and the theorems that every
Store written at an open has it, and so its deployed pages short of the tip are non-empty. The
module header of `Host.Proofs.Coherence` lists them and what is not proved.

HOST-68 (cv 01a1583d-864c items 3 and 6): the predicate covers a RETAINED Store (`indexFrom` > 0,
HOST-64): the kept run is entries `k0 …` read at their LOGICAL positions `k0 + i` (what
`Page.kept` reads through `Page.entryAt (k0 + k)`), and it begins at the run start `(o₀, s₀)`:
`o₀ = max retainedFrom originEnd` (the oldest kept file's start, or the origin frame's end when the
Store keeps everything) and `s₀`, the first kept entry's step count. `s₀` is a GHOST: no open reads
it; it is pinned at the start (`genesis_indexes`: the genesis World's step count; `import_indexes`:
the import's, its carried height) and carried by every write. `host check` reads it: the first kept
entry's step count must equal the oldest kept header's `steps` (`indexClean`).
-/
import Host.Proofs.Coherence
import Host.Proofs.Seal

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray
open Nanodregg.Host.Page (Indexes frameOf)

/-! ## The Store: every entry the base counts, and every entry since -/

/-- Where a run of entries begins, as (offset, step count): its first entry's, or `at_` (the base's
offset and its World's step count) when it holds none. A Store's run begins at `(o₀, s₀)`, the
oldest kept file's start (the origin frame's end for a Store keeping everything, HOST-65) and the
first kept entry's step count (HOST-68). -/
def RunFrom (L : List Entry) (at_ o : Nat × Nat) : Prop :=
  match L with
  | [] => at_ = o
  | e :: _ => (e.offset, e.steps) = o

/-- Two runs, the second beginning where the first ends, begin where the first does. -/
theorem RunFrom.append {L M : List Entry} {B P O : Nat × Nat} (hL : RunFrom L B O) (hM : RunFrom M P B) :
    RunFrom (L ++ M) P O := by
  cases L with
  | nil => subst hL; exact hM
  | cons e _ => exact hL

/-- A non-empty run begins at its first entry. -/
theorem RunFrom.head {L : List Entry} {P O : Nat × Nat} (h : RunFrom L P O) (hj : 0 < L.length) :
    ((L[0]'hj).offset, (L[0]'hj).steps) = O := by
  cases L with
  | nil => simp at hj
  | cons e rest => exact h

/-- A run of no entries begins at the base. -/
theorem RunFrom.nil {L : List Entry} {P O : Nat × Nat} (h : RunFrom L P O) (hL : L.length = 0) : P = O := by
  cases L with
  | nil => exact h
  | cons e rest => simp at hL

/-- **The Store's index points at its records** (cv 01a15180-9499, HOST-64/68): the base file decodes
to a base `b`; the entries `b.indexFrom … b.indexCount - 1` the base keeps read back at their
LOGICAL positions `b.indexFrom + i` (the index file `index.<k0>.log` holds them from its first byte;
`I` is the logical index, whose bytes below `k0` nobody reads) under the Store's index key as `L`;
`L` is a coherent run over the segment to the base (its offset and its World's step count), the
segment reaching the base; and the run begins at the run start (`RunFrom`): entry `k0` sits at the
oldest kept file's start, `max b.retainedFrom (frameSize (origin b.world))` (the origin frame's end
for a Store keeping everything: entry 0 is the Store's first record, HOST-65; a LOGICAL offset read
from nothing), at the step count `s₀`; or, with no entry, the base sits there. What the deployed
open adds to it is the tail's entries (`openWith_indexes`). Every Store this Host writes has it:
`StoreIndexes.of_open_empty` (genesis, import, adopt: no entry, `s₀` the base World's step count),
`StoreIndexes.append` (records and orphans appended), `StoreIndexes.cut_open` (the writer's
truncation at open), `sealed_indexes` (a seal keeping what the base kept, `sealed_indexes_same`; a
seal that drops, under `KeepNames`: the new `Keep` names the run start, which `keep_of_header`
discharges from the header this writer wrote at the oldest kept file). -/
def StoreIndexes {W D : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) (file I S : ByteArray)
    (s₀ : Nat) : Prop :=
  ∃ (b : Base W) (n : Nat) (d : ByteArray) (L : List Entry), Base.read keys c world file = .ok (b, n, d) ∧
    b.indexFrom + L.length = b.indexCount ∧ b.indexCount * entryBytes keys ≤ I.size ∧ b.offset ≤ S.size ∧
    (∀ (i : Nat) (hi : i < L.length), Entry.read (keys.forStore (origin b.world)) (b.indexFrom + i)
      (I.extract ((b.indexFrom + i) * entryBytes keys) ((b.indexFrom + i) * entryBytes keys + entryBytes keys)) =
        some L[i]) ∧
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1) ∧
    RunFrom L (b.offset, (mark b.world).1) (max b.retainedFrom (frameSize (origin b.world)), s₀)

/-- **A seal's `Keep` names the run start** (HOST-68, the premise of `sealed_indexes`): over the
logical index `I` of a base keeping from `k0` and counting `count` entries, at the base's position
`P` (offset, step count), the kept entries begin at or after `k0`, within the count, and the first
kept entry `keep.indexFrom` reads back as an entry at `(o₀, s₀)`, or, when it is the count, the base
itself sits at `(o₀, s₀)`. `o₀` is `max keep.retainedFrom originEnd` at the use. A seal that keeps
what the base kept has it from the base's own run (`sealed_indexes_same`); a drop's `Keep` comes
from the oldest kept file's header, `(start, indexCount, steps)`, which `keep_of_header` shows
names the run at the base that wrote it and `keepNames_append` / `keepNames_cut` / `keepNames_seal`
carry through every later write. -/
def KeepNames (keys : Keys) (I : ByteArray) (k0 count : Nat) (P : Nat × Nat) (keep : Keep) (o₀ s₀ : Nat) :
    Prop :=
  k0 ≤ keep.indexFrom ∧ keep.indexFrom ≤ count ∧
    (keep.indexFrom < count → ∃ e, Entry.read keys keep.indexFrom
      (I.extract (keep.indexFrom * entryBytes keys) (keep.indexFrom * entryBytes keys + entryBytes keys)) = some e ∧
      (e.offset, e.steps) = (o₀, s₀)) ∧
    (keep.indexFrom = count → P = (o₀, s₀))

variable {W F D : Type}

/-- **The open's entries since the base begin at the base** (the head fact of `indexed_indexes`,
HOST-68): the first entry `Host.indexed` makes is at the base's offset and its World's step count,
or there is none and the open's position is the base's. No coherence of the base's own entries is
needed. -/
theorem openWith_run (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d)) :
    RunFrom o.index.toList (o.pos.offset, (mark o.opened.world).1) (b.offset, (mark b.world).1) := by
  obtain ⟨b', _, _, _, op, _, hb', hlen, hoff, htag, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  obtain ⟨rs, he, hf, _, _, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hesz : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
    rw [← he]; simp only [size_extract]; omega
  have he' : S.extract b.offset (b.offset + (encodeAll keys.segment b.tag.bytes rs).size) =
      encodeAll keys.segment b.tag.bytes rs := by
    rw [hesz, ← he, extract_extract]; congr 1 <;> omega
  have hp : S.extract (b.offset - tagBytes) (b.offset - tagBytes + tagBytes) = b.tag.bytes := by
    rw [show b.offset - tagBytes + tagBytes = b.offset by omega]; exact htag
  obtain ⟨M, hM, -, hhd⟩ := indexed_indexes (dc := dc) (S := S) mark step hstep rs b.world #[] b.offset
    b.tag.bytes hrs hp he' hf
  have hend := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop
  simp only [List.nil_append] at hM
  dsimp only
  rw [hM, ← hend]
  cases M with
  | nil => exact hhd
  | cons e _ => exact hhd

/-- **The open's entries point at their records**: over a Store whose base's entries are a
coherent run to the base, the one open's entries since the base continue it to the open's
position and World (`Host.indexed` makes each from the frame the open verified), when each fold
step decodes its record to steps that move the step count by their number (`hstep`); and they
begin at the base (`openWith_run`). -/
theorem openWith_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d)) {L : List Entry}
    (hL : Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1)) :
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) ∧
    RunFrom o.index.toList (o.pos.offset, (mark o.opened.world).1) (b.offset, (mark b.world).1) := by
  refine ⟨?_, openWith_run keys c world mark origin step hstep file H I S h hb⟩
  obtain ⟨b', _, _, _, op, _, hb', hlen, hoff, htag, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  obtain ⟨rs, he, hf, _, _, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hesz : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
    rw [← he]; simp only [size_extract]; omega
  have he' : S.extract b.offset (b.offset + (encodeAll keys.segment b.tag.bytes rs).size) =
      encodeAll keys.segment b.tag.bytes rs := by
    rw [hesz, ← he, extract_extract]; congr 1 <;> omega
  have hp : S.extract (b.offset - tagBytes) (b.offset - tagBytes + tagBytes) = b.tag.bytes := by
    rw [show b.offset - tagBytes + tagBytes = b.offset by omega]; exact htag
  obtain ⟨M, hM, hI, hhd⟩ := indexed_indexes (dc := dc) (S := S) mark step hstep rs b.world #[] b.offset
    b.tag.bytes hrs hp he' hf
  have hend := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop
  simp only [List.nil_append] at hM
  dsimp only
  rw [hM, ← hend]
  exact Indexes.append L M _ hL hI hhd

/-- The origin frame's end is at or before every base of a coherent Store: the run begins at or
after it and ends before the base, or the base sits at the run start. -/
theorem StoreIndexes.originEnd_le {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    {mark : W → Nat × ByteArray} {origin : W → ByteArray} {dc : Codec.Stream D} {file I S : ByteArray} {s₀ : Nat}
    (h : StoreIndexes keys c world mark origin dc file I S s₀) {b : Base W} {n : Nat} {d : ByteArray}
    (hb : Base.read keys c world file = .ok (b, n, d)) : frameSize (origin b.world) ≤ b.offset := by
  obtain ⟨b', n', d', L, hb', -, -, -, -, hL, hO⟩ := h
  rw [hb] at hb'; cases hb'
  cases L with
  | nil =>
    simp only [RunFrom, Prod.mk.injEq] at hO
    rw [hO.1]; exact Nat.le_max_right _ _
  | cons e rest =>
    simp only [RunFrom, Prod.mk.injEq] at hO
    have h1 : e.offset < b.offset := Indexes.offset_lt rest e hL
    omega

/-- A Store whose base counts no entry has a coherent index: the empty one, from its World's step
count. -/
theorem StoreIndexes.of_count_zero (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) {file I S : ByteArray}
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d))
    (h0 : b.indexCount = 0) (hS : b.offset ≤ S.size) (hO : b.offset = frameSize (origin b.world)) {s₀ : Nat}
    (hs : (mark b.world).1 = s₀) :
    StoreIndexes keys c world mark origin dc file I S s₀ := by
  obtain ⟨hk1, hk2⟩ := Base.read_keep hb
  have hm : max b.retainedFrom (frameSize (origin b.world)) = frameSize (origin b.world) :=
    Nat.max_eq_right (by omega)
  refine ⟨b, n, d, [], hb, by simp only [List.length_nil, Nat.add_zero]; omega, by rw [h0]; simp, hS,
    fun _ hi => absurd hi (by simp), trivial, ?_⟩
  show (b.offset, (mark b.world).1) = _
  rw [hm, hs, hO]

/-- **A Store whose the index file is empty has a coherent index** (genesis, import and a follower's
adopted base all write an empty one): whenever the one open succeeds over it, from the base World's
step count (`o.sealed.steps`). -/
theorem StoreIndexes.of_open_empty (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (dc : Codec.Stream D) (file H S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size ByteArray.empty.size
      (segReader ByteArray.empty) (segReader S)) = .ok o) :
    StoreIndexes keys c world mark origin dc file ByteArray.empty S o.sealed.steps := by
  obtain ⟨b, _, _, _, _, _, hb, hlen, _, _, _, _, _, hi, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world mark origin step file H ByteArray.empty S h
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have heb : 0 < entryBytes keys := by unfold entryBytes; omega
  simp only [ByteArray.size_empty, Nat.le_zero, Nat.mul_eq_zero] at hi
  have h0 : b.indexCount = 0 := hi.resolve_right (by omega)
  exact StoreIndexes.of_count_zero keys c world mark origin dc hb h0 (by omega)
    (openWith_originEnd keys c world mark origin step file H ByteArray.empty S h hb h0) (by rw [ho])

theorem Entry.read_extract_append {keys : Keys} {I x : ByteArray} {k : Nat}
    (hk : (k + 1) * entryBytes keys ≤ I.size) :
    (I ++ x).extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys) =
      I.extract (k * entryBytes keys) (k * entryBytes keys + entryBytes keys) := by
  rw [Nat.succ_mul] at hk
  exact extract_append_le (by omega)

/-- **Appending keeps the index coherent**: records appended to the segment and entries (or
orphans) appended to the index file leave every entry the base keeps, and the run to the base, as
they were. -/
theorem StoreIndexes.append {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    {mark : W → Nat × ByteArray} {origin : W → ByteArray} {dc : Codec.Stream D} {file I S : ByteArray} {s₀ : Nat}
    (x y : ByteArray) (h : StoreIndexes keys c world mark origin dc file I S s₀) :
    StoreIndexes keys c world mark origin dc file (I ++ x) (S ++ y) s₀ := by
  obtain ⟨b, n, d, L, hb, hc, hI, hS, hr, hL, hO⟩ := h
  refine ⟨b, n, d, L, hb, hc, by rw [size_append]; omega, by rw [size_append]; omega,
    fun i hi => by
      have hk : (b.indexFrom + i + 1) * entryBytes keys ≤ I.size :=
        Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hI
      rw [Entry.read_extract_append hk]; exact hr i hi,
    ?_, hO⟩
  exact Indexes.congr (fun i j hj => (extract_append_le (by simp only at hj; omega)).symm) L hL

/-- **The writer's cut keeps the index coherent**: `openWriter` truncates the segment to the open's
valid end and the index file to the entries the base counts (`Host.openWriter`); the cut Store has
the same coherent index. -/
theorem StoreIndexes.cut_open (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {dc : Codec.Stream D} (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    {s₀ : Nat} (hS : StoreIndexes keys c world mark origin dc file I S s₀) :
    StoreIndexes keys c world mark origin dc file (I.extract 0 (o.sealed.index.count * entryBytes keys))
      (S.extract 0 o.pos.offset) s₀ := by
  obtain ⟨b, n, d, L, hb, hc, hI, hSz, hr, hL, hO⟩ := hS
  obtain ⟨b', _, _, _, op, _, hb', hlen, _, _, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  dsimp only
  refine ⟨b, n, d, L, hb, hc, by simp only [size_extract]; omega, by simp only [size_extract]; omega,
    fun i hi => ?_, ?_, hO⟩
  · have : (b.indexFrom + i + 1) * entryBytes keys ≤ b.indexCount * entryBytes keys :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    rw [extract_prefix I (by omega)]; exact hr i hi
  · exact Indexes.congr (fun i j hj => (extract_prefix S (by simp only at hj; omega)).symm) L hL

theorem entryBytes_forStore (keys : Keys) (sid : ByteArray) :
    entryBytes (keys.forStore sid) = entryBytes keys := rfl

/-- **The entries a seal writes read back** (the core of `sealed_reads` and `keepNames_seal`): after
the open with entries `M` since the base and the seal of it, entry `j` of `M` reads back at the
logical position `b.indexCount + j` from the index file with the seal's page appended (`run_read`);
and the seal's origin, counts and sizes. No coherence of the base's own entries is needed. -/
theorem sealed_reads_new (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size keep = .ok (page, ix', file))
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d)) :
    origin o.opened.world = origin b.world ∧ o.sealed.index.count = b.indexCount ∧
    ix'.count = b.indexCount + o.index.size ∧ I.size = b.indexCount * entryBytes keys ∧
    (∀ (j : Nat) (hj : j < o.index.toList.length),
      Entry.read (keys.forStore (origin o.opened.world)) (b.indexCount + j)
        ((I ++ page).extract ((b.indexCount + j) * entryBytes keys) ((b.indexCount + j) * entryBytes keys + entryBytes keys)) =
        some o.index.toList[j]) := by
  obtain ⟨-, -, -, -, -, -, -, -, hI, hcnt, -, -, -, -⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world mark origin step file₀ H I S h
  rw [hb] at hb'; cases hb'
  have hcount : o.sealed.index.count = b.indexCount := by rw [ho]
  obtain ⟨b'', _, _, rs, hb'', hf, -⟩ := openWith_world keys c world mark origin step file₀ H I S h
  rw [hb] at hb''; cases hb''
  have hor : origin o.opened.world = origin b.world := foldlM_origin horigin rs _ _ hf
  obtain ⟨-, hent, -⟩ := seal_at_end _ _ _ _ _ _ _ _ _ hseal
  obtain ⟨hfit, -, -, hp, -, -⟩ := entries_ok hent
  have hes : (sealEntries o.index).toList = o.index.toList := by simp [sealEntries]
  rw [hes] at hp hfit
  refine ⟨hor, hcount, by rw [hcnt, hcount], by rw [hI, hcount], fun j hj => ?_⟩
  rw [← hcount]
  have hpos : (o.sealed.index.count + j) * entryBytes keys = I.size + j * entryBytes keys := by
    rw [hI, Nat.add_mul]
  rw [hpos, show I.size + j * entryBytes keys + entryBytes keys =
      I.size + (j * entryBytes keys + entryBytes keys) by omega, extract_append_size_add' rfl, hp]
  have hr' := run_read (keys.forStore (origin o.opened.world)) o.sealed.index.count o.index.toList j hj hfit
  rw [entryBytes_forStore] at hr'
  exact hr'

/-- **The entries a seal leaves read back**: over a Store whose base keeps `L` (each read back at
`k0 + i`), after the open with entries `M` since the base and the seal of it, every entry of
`L ++ M` reads back at `k0 + i` from the index file with the seal's page appended (the old ones
unchanged, the new ones by `sealed_reads_new`). -/
theorem sealed_reads (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size keep = .ok (page, ix', file))
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d))
    {L : List Entry} (hc : b.indexFrom + L.length = b.indexCount) (hIL : b.indexCount * entryBytes keys ≤ I.size)
    (hr : ∀ (i : Nat) (hi : i < L.length), Entry.read (keys.forStore (origin b.world)) (b.indexFrom + i)
      (I.extract ((b.indexFrom + i) * entryBytes keys) ((b.indexFrom + i) * entryBytes keys + entryBytes keys)) =
        some L[i]) :
    origin o.opened.world = origin b.world ∧ o.sealed.index.count = b.indexCount ∧
    ix'.count = b.indexCount + o.index.size ∧ I.size = b.indexCount * entryBytes keys ∧
    (∀ (i : Nat) (hi : i < (L ++ o.index.toList).length),
      Entry.read (keys.forStore (origin o.opened.world)) (b.indexFrom + i)
        ((I ++ page).extract ((b.indexFrom + i) * entryBytes keys) ((b.indexFrom + i) * entryBytes keys + entryBytes keys)) =
        some (L ++ o.index.toList)[i]) := by
  obtain ⟨hor, hcount, hcnt, hI, hnew⟩ :=
    sealed_reads_new keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal hb
  refine ⟨hor, hcount, hcnt, hI, fun i hi => ?_⟩
  by_cases hiL : i < L.length
  · have hk : (b.indexFrom + i + 1) * entryBytes keys ≤ I.size :=
      Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hIL
    rw [Entry.read_extract_append hk, List.getElem_append_left hiL, hor]
    exact hr i hiL
  · obtain ⟨j, rfl⟩ : ∃ j, i = L.length + j := ⟨i - L.length, by omega⟩
    have hj : j < o.index.toList.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right (by omega), show b.indexFrom + (L.length + j) = b.indexCount + j by omega]
    simp only [Nat.add_sub_cancel_left]
    exact hnew j hj

/-- **A seal keeps the index coherent** (the completeness side, discharged at seal): the seal of
an opened World at the open's position, with the entries since the base (what both checkpoints
write, `Base.seal`), over a Store whose index is coherent, leaves a Store (the new base, the index file
with the seal's entries appended, the segment cut at the open's position) whose index is coherent
from the run start the seal's `Keep` names (`KeepNames`, HOST-68: a seal keeping what the base kept
names the old one, `sealed_indexes_same`; a drop names the oldest kept file's header's, which
`keep_of_header` and the `keepNames_*` steps discharge): the kept entries are the old base's then
the open's (`openWith_indexes`), from `keep.indexFrom` (`Indexes.drop`), each read back at its
logical position (`sealed_reads`). Premises are `sealed_opens`' and `hstep`. -/
theorem sealed_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size keep = .ok (page, ix', file))
    {s₀ : Nat} (hS : StoreIndexes keys c world mark origin dc file₀ I S s₀)
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d)) {s₀' : Nat}
    (hkeep : KeepNames (keys.forStore (origin o.opened.world)) (I ++ page) b.indexFrom ix'.count
      (o.pos.offset, (mark o.opened.world).1) keep (max keep.retainedFrom (frameSize (origin o.opened.world))) s₀') :
    StoreIndexes keys c world mark origin dc file (I ++ page) (S.extract 0 o.pos.offset) s₀' := by
  obtain ⟨-, hrd, -, hle, -, -, -, -, -, -, -, hsz, -, -⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal
  obtain ⟨b', n', d', L, hb', hc, hIL, -, hr, hL, hO⟩ := hS
  rw [hb] at hb'; cases hb'
  obtain ⟨-, -, hcnt, -, hreads⟩ :=
    sealed_reads keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal hb hc hIL hr
  obtain ⟨hL', -⟩ := openWith_indexes keys c world mark origin step hstep file₀ H I S h hb hL
  obtain ⟨hk0, hkc, hke, hkP⟩ := hkeep
  have hlen : (L ++ o.index.toList).length = ix'.count - b.indexFrom := by
    simp only [List.length_append, Array.length_toList]; omega
  have hL'' : Indexes dc keys.segment c.recordBytesMax
      (fun x y => (pure ((S.extract 0 o.pos.offset).extract x (x + y)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) :=
    Indexes.congr (fun i j (hj : j ≤ o.pos.offset) => (extract_prefix S hj).symm) _ hL'
  refine ⟨_, _, _, (L ++ o.index.toList).drop (keep.indexFrom - b.indexFrom), hrd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    simp only [List.length_drop, hlen]; omega
  · dsimp only
    rw [hsz]; exact Nat.le_refl _
  · dsimp only
    simp only [size_extract]; omega
  · intro i hi
    simp only [List.length_drop, hlen] at hi
    have hi' : keep.indexFrom - b.indexFrom + i < (L ++ o.index.toList).length := by rw [hlen]; omega
    have hre := hreads _ hi'
    rw [show b.indexFrom + (keep.indexFrom - b.indexFrom + i) = keep.indexFrom + i by omega] at hre
    rw [List.getElem_drop]
    exact hre
  · exact Indexes.drop _ _ hL''
  · dsimp only
    rcases Nat.lt_or_ge keep.indexFrom ix'.count with hlt | hge
    · obtain ⟨e, he, hoe⟩ := hke hlt
      have hj : keep.indexFrom - b.indexFrom < (L ++ o.index.toList).length := by rw [hlen]; omega
      rw [List.drop_eq_getElem_cons hj]
      have hre := hreads (keep.indexFrom - b.indexFrom) hj
      rw [entryBytes_forStore] at he
      rw [show b.indexFrom + (keep.indexFrom - b.indexFrom) = keep.indexFrom by omega, he] at hre
      have hre' := Option.some.inj hre
      show ((L ++ o.index.toList)[keep.indexFrom - b.indexFrom].offset,
        (L ++ o.index.toList)[keep.indexFrom - b.indexFrom].steps) = _
      rw [← hre']; exact hoe
    · have hj : (L ++ o.index.toList).length ≤ keep.indexFrom - b.indexFrom := by rw [hlen]; omega
      rw [List.drop_of_length_le hj]
      exact hkP (by omega)

/-- **A seal keeping what the base kept keeps the run start** (HOST-68, the default seal: `Keep`
unchanged): its `KeepNames` is the base's own run, so the sealed Store is coherent from the same
`(o₀, s₀)`, with no premise beyond `sealed_indexes`' before HOST-68. -/
theorem sealed_indexes_same (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {page file : ByteArray} {ix' : IndexAt}
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d))
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size ⟨b.retainedFrom, b.indexFrom⟩ = .ok (page, ix', file))
    {s₀ : Nat} (hS : StoreIndexes keys c world mark origin dc file₀ I S s₀) :
    StoreIndexes keys c world mark origin dc file (I ++ page) (S.extract 0 o.pos.offset) s₀ := by
  refine sealed_indexes keys c world mark origin step hw horigin hmono hcap hstep file₀ H I S h hP hseal hS hb ?_
  obtain ⟨b', n', d', L, hb', hc, hIL, -, hr, hL, hO⟩ := hS
  rw [hb] at hb'; cases hb'
  obtain ⟨hor, -, hcnt, -, hreads⟩ :=
    sealed_reads keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal hb hc hIL hr
  have hrun := openWith_run keys c world mark origin step hstep file₀ H I S h hb
  have hOrun := RunFrom.append hO hrun
  rw [hor]
  rw [hor] at hreads
  refine ⟨Nat.le_refl _, ?_, fun hlt => ?_, fun heq => ?_⟩
  · show b.indexFrom ≤ ix'.count; omega
  · have hlt' : b.indexFrom < ix'.count := hlt
    have hj : 0 < (L ++ o.index.toList).length := by
      simp only [List.length_append, Array.length_toList]; omega
    refine ⟨(L ++ o.index.toList)[0]'hj, ?_, RunFrom.head hOrun hj⟩
    have := hreads 0 hj
    rw [Nat.add_zero] at this
    exact this
  · have heq' : b.indexFrom = ix'.count := heq
    exact RunFrom.nil hOrun (by simp only [List.length_append, Array.length_toList]; omega)

/-! ## The drop's `Keep` comes from a header this writer wrote (HOST-68) -/

/-- **The header of a base's own file names the run at that base** (`keep_of_header`): a `Keep`
taken from a header stating `(start, steps, indexCount) = (b.offset, (mark b.world).1, b.indexCount)`
(what `openWith_header` says of the base's own file: `Checkpoint.rotate` wrote it at the seal that
made the base) names the run at the base itself: the first kept entry is the count, and the base
sits at `(start, steps)`. From here `keepNames_append`, `keepNames_cut` and `keepNames_seal` carry it
through every later write to the seal that drops to this file (`keepFrom` reads exactly `start` and
`indexCount`, and `Check.keptClean` reads `steps`). -/
theorem keep_of_header {keys : Keys} {I : ByteArray} {k0 : Nat} {b : Base W} {hd : Header} {origin : W → ByteArray}
    {mark : W → Nat × ByteArray}
    (hstart : hd.start = b.offset) (hsteps : hd.steps = (mark b.world).1) (hcount : hd.indexCount = b.indexCount)
    (hk0 : k0 ≤ b.indexCount) (hrf : frameSize (origin b.world) ≤ b.offset) :
    KeepNames keys I k0 b.indexCount (b.offset, (mark b.world).1) ⟨hd.start, hd.indexCount⟩
      (max hd.start (frameSize (origin b.world))) hd.steps := by
  refine ⟨show k0 ≤ hd.indexCount by omega, show hd.indexCount ≤ b.indexCount by omega,
    fun hlt => absurd hlt (show ¬ hd.indexCount < b.indexCount by omega), fun _ => ?_⟩
  show (b.offset, (mark b.world).1) = (max hd.start (frameSize (origin b.world)), hd.steps)
  rw [hstart, hsteps, Nat.max_eq_left hrf]

/-- A larger first kept entry, at or below the named one, keeps the name. -/
theorem keepNames_mono {keys : Keys} {I : ByteArray} {k0 k0' count : Nat} {P : Nat × Nat} {keep : Keep} {o₀ s₀ : Nat}
    (h : KeepNames keys I k0 count P keep o₀ s₀) (hk : k0' ≤ keep.indexFrom) :
    KeepNames keys I k0' count P keep o₀ s₀ :=
  ⟨hk, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Appending to the index (entries or orphans past the count) keeps the name. -/
theorem keepNames_append {keys : Keys} {I x : ByteArray} {k0 count : Nat} {P : Nat × Nat} {keep : Keep} {o₀ s₀ : Nat}
    (hI : count * entryBytes keys ≤ I.size) (h : KeepNames keys I k0 count P keep o₀ s₀) :
    KeepNames keys (I ++ x) k0 count P keep o₀ s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun hlt => ?_, h4⟩
  obtain ⟨e, he, hoe⟩ := h3 hlt
  have hk : (keep.indexFrom + 1) * entryBytes keys ≤ I.size := Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hI
  exact ⟨e, by rw [Entry.read_extract_append hk]; exact he, hoe⟩

/-- The writer's cut at open (the index to the entries the base counts) keeps the name. -/
theorem keepNames_cut {keys : Keys} {I : ByteArray} {k0 count : Nat} {P : Nat × Nat} {keep : Keep} {o₀ s₀ : Nat}
    (h : KeepNames keys I k0 count P keep o₀ s₀) :
    KeepNames keys (I.extract 0 (count * entryBytes keys)) k0 count P keep o₀ s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun hlt => ?_, h4⟩
  obtain ⟨e, he, hoe⟩ := h3 hlt
  refine ⟨e, ?_, hoe⟩
  have : (keep.indexFrom + 1) * entryBytes keys ≤ count * entryBytes keys := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at this
  rw [extract_prefix I (by omega)]; exact he

/-- **A seal keeps the name** (the induction step of a drop's premise): over a base `b` whose index
`I` names the run at `keep`, the seal after an open of it (entries `M` since the base, the page
appended) names it still: an entry below the old count is unchanged; the entry AT the old count is
the open's first, which sits at the base (`openWith_run`); and when the new count is still the
named one, the open held no entry and its position is the base's. No coherence of the base's own
entries is needed. -/
theorem keepNames_seal (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {keep' : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size keep' = .ok (page, ix', file))
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d))
    {k0 : Nat} {keep : Keep} {o₀ s₀ : Nat}
    (hk : KeepNames (keys.forStore (origin b.world)) I k0 b.indexCount (b.offset, (mark b.world).1) keep o₀ s₀) :
    KeepNames (keys.forStore (origin o.opened.world)) (I ++ page) k0 ix'.count
      (o.pos.offset, (mark o.opened.world).1) keep o₀ s₀ := by
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, hIL, _, _, _, _, _⟩ :=
    openWith_seg_ok keys c world mark origin step file₀ H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hor, -, hcnt, -, hnew⟩ :=
    sealed_reads_new keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal hb
  have hrun := openWith_run keys c world mark origin step hstep file₀ H I S h hb
  obtain ⟨h1, h2, h3, h4⟩ := hk
  rw [hor]
  rw [hor] at hnew
  refine ⟨h1, by omega, fun hlt => ?_, fun heq => ?_⟩
  · rcases Nat.lt_or_ge keep.indexFrom b.indexCount with hold | hnew'
    · obtain ⟨e, he, hoe⟩ := h3 hold
      have hk : (keep.indexFrom + 1) * entryBytes keys ≤ I.size :=
        Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hIL
      rw [entryBytes_forStore] at he ⊢
      exact ⟨e, by rw [Entry.read_extract_append hk]; exact he, hoe⟩
    · have heq : keep.indexFrom = b.indexCount := by omega
      have hj : 0 < o.index.toList.length := by simp only [Array.length_toList]; omega
      refine ⟨o.index.toList[0]'hj, ?_, ?_⟩
      · have := hnew 0 hj
        rw [Nat.add_zero] at this
        rw [heq, entryBytes_forStore]
        exact this
      · rw [← h4 heq]
        exact RunFrom.head hrun hj
  · rw [← h4 (by omega)]
    exact RunFrom.nil hrun (by simp only [Array.length_toList]; omega)

end Nanodregg.Host

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Codec ByteArray

/-- The deployed reopen's step decodes its record to the steps it takes: the step count moves by
their number (`openWith_indexes`' `hstep`). -/
theorem foldStep_decode {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    ∃ ts : List (Step D × D), (Record.codec Codec.Deployed.digestCodec).decode r = .ok ts ∧
      (recorder.mark w').1 = (recorder.mark w).1 + ts.length := by
  obtain ⟨ps, hd, hr⟩ := Record.step_rooted (dc := Codec.Deployed.digestCodec) (admit := World.step X.env)
    (root := World.roots X.env) h
  exact ⟨ps, hd, by rw [recorder_mark, recorder_mark]; exact rooted_steps hr⟩

/-- The deployed index is coherent from the run start `(o₀, s₀)`: what `page_nonempty` assumes, and
every deployed Store write keeps (`genesis_indexes`, `import_indexes`, `StoreIndexes.append`,
`StoreIndexes.cut_open`, `sealed_indexes_deployed`). -/
abbrev Coherent (keys : Keys) (file I S : ByteArray) (s₀ : Nat) : Prop :=
  StoreIndexes keys c world recorder.mark originChain Codec.Deployed.digestCodec file I S s₀

/-- Over a coherent Store at the deployed open, the kept run: the entries from `b.indexFrom` (the
base's own, read through `Page.entryAt (k0 + k)` as `Page.kept` reads them, then the loop's),
coherent to the open's position, beginning at the run start. -/
theorem coherent_reader {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)} {s₀ : Nat}
    (hS : Coherent keys file I S s₀)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d)) :
    ∃ L : List Entry, b.indexFrom + L.length = o.sealed.index.count + o.index.size ∧
      Page.Indexes Codec.Deployed.digestCodec keys.segment c.recordBytesMax
        (fun x y => (pure (S.extract x (x + y)) : Id ByteArray)) L (o.pos.offset, (recorder.mark o.opened.world).1) ∧
      (∀ k e, Page.entryAt (m := Id) (keys.forStore (originChain o.opened.world))
        (fun x y => pure (I.extract x (x + y))) o.sealed.index.count o.index (b.indexFrom + k) = .ok e →
        L[k]? = some e) ∧
      RunFrom L (o.pos.offset, (recorder.mark o.opened.world).1)
        (max b.retainedFrom (frameSize (originChain o.opened.world)), s₀) := by
  obtain ⟨b', n', d', L, hb', hc, -, -, hr, hL, hO⟩ := hS
  rw [hb] at hb'; cases hb'
  obtain ⟨hL', hrun⟩ := openWith_indexes keys c world recorder.mark originChain foldStep
    (fun _ _ _ hs => foldStep_decode hs) file H I S h hb hL
  obtain ⟨b'', _, _, _, _, _, hb'', _, _, _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep file H I S h
  rw [hb] at hb''; cases hb''
  have hcount : o.sealed.index.count = b.indexCount := by rw [ho]
  obtain ⟨b''', _, _, rs, hb''', hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file H I S h
  rw [hb] at hb'''; cases hb'''
  have hor : originChain o.opened.world = originChain b.world :=
    foldlM_origin (fun _ _ _ hs => foldStep_originChain hs) rs _ _ hf
  refine ⟨L ++ o.index.toList, by simp only [List.length_append, Array.length_toList]; omega, hL', ?_,
    by rw [hor]; exact RunFrom.append hO hrun⟩
  intro k e hk
  rcases Page.entryAt_ok (rd := fun x y => I.extract x (x + y)) hk with ⟨hlt, hre⟩ | ⟨hge, hm⟩
  · rw [hcount] at hlt
    have hkL : k < L.length := by omega
    rw [hor, entryBytes_forStore, hr k hkL] at hre
    rw [List.getElem?_append_left hkL, List.getElem?_eq_getElem hkL]
    exact hre
  · rw [List.getElem?_append_right (by omega), Array.getElem?_toList, hcount] at *
    rw [show k - L.length = b.indexFrom + k - b.indexCount by omega]
    exact hm

/-- **A page short of the tip is non-empty, at the deployed instance** (HOST-60's lift, cv
01a15180-9499; HOST-68: over the kept files). Over a Store whose index is coherent (`Coherent`:
every deployed write keeps it), the deployed open's state (the resident a writer or a follower starts
from), and the deployed pager (`Host.Deployed.pageKept`: `Page.kept` from the base's `indexFrom`,
with `Page.entryAt` over the base's entries on disk and the open's since, the durable end, the
World's mark), every page served from a `start` below the World's step count holds at least one
event. -/
theorem page_nonempty (keys : Keys) (file H I S : ByteArray) {o : Opening (World D)} {s₀ : Nat}
    (hS : Coherent keys file I S s₀)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d))
    {start : Nat} (hs : start < o.opened.world.steps) {a : Page.Acc}
    (ha : Id.run (Page.kept X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget b.indexFrom (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index)
      (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start) = .ok a) :
    0 < a.events.size := by
  obtain ⟨L, hlen, hL, hget, -⟩ := coherent_reader hS h hb
  have ha' := Page.kept_ok ha
  rw [show o.sealed.index.count + o.index.size - b.indexFrom = L.length by omega] at ha'
  exact Page.build_nonempty Codec.Deployed.digestCodec_lawful.on Page.budget_fits_event hget hL hs ha'

/-- **A deployed page is refused `beforeLog` only from below the entry its search reads first**
(HOST-61's entry-0 case): the deployed pager over any the index file and any loop entries, when it
holds an entry and reads entry 0 as `e₀`, refuses `beforeLog` only from a `start` below `e₀`'s step
count. Over a coherent Store, entry 0 sits at the run start: `page_beforeLog_origin` (HOST-65/68). -/
theorem page_beforeLog_first (keys : Keys) (I S : ByteArray) (r : Resident (World D)) {start x y : Nat}
    (hc : r.sealed.index.count + r.index.size ≠ 0)
    (ha : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain r.world)) (fun x y => pure (I.extract x (x + y)))
        r.sealed.index.count r.index)
      (r.sealed.index.count + r.index.size) r.pos.offset (recorder.mark r.world) start) =
        .error (.beforeLog x y))
    {e₀ : Entry} (h0 : Page.entryAt (m := Id) (keys.forStore (originChain r.world))
      (fun x y => pure (I.extract x (x + y))) r.sealed.index.count r.index 0 = .ok e₀) :
    start < e₀.steps :=
  Page.build_beforeLog_first hc h0 (fun k x' y' hk => by
    have := Page.entryAt_error (rd := fun x y => I.extract x (x + y)) hk
    cases this) ha

/-- **The first kept entry is the Store's first kept record, at the step count the run began**
(HOST-65 and HOST-68, closing HOST-61's entry-0 case and HOST-65's named gap over a coherent
Store): at the deployed open's state, a deployed page over the kept files (`Page.kept` from the
base's `indexFrom`) refused `beforeLog` (a Store keeping everything) or `checkpointed` (one that
dropped) reads as its first entry `e₀` an entry at the run start: the oldest kept file's start
(`max retainedFrom originEnd`; the origin frame's end, a LOGICAL offset, for a Store keeping
everything, so the segment's first record: no record lies before it, given that [0, that end) is
the origin frame, the open's origin check, HOST-25, HOST-64's header) at the step count `s₀` the
run began at (0 for a Store genesis made, the carried height for an imported one:
`genesis_indexes`, `import_indexes`), and is refused only from a `start` below `s₀`. `Coherent`
is kept by every deployed write (`StoreIndexes.append`, `StoreIndexes.cut_open`,
`sealed_indexes_deployed`); its run start is checked at every open for a base counting none
(`openWith_originEnd`, the count-0 arm of `lastFrameFault`) and at `host check` for every Store
(`indexClean`: the first kept entry's step count is the oldest kept header's). -/
theorem page_beforeLog_origin (keys : Keys) (file H I S : ByteArray) {o : Opening (World D)} {s₀ : Nat}
    (hS : Coherent keys file I S s₀)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d))
    (hc : b.indexFrom < o.sealed.index.count + o.index.size) {start x y : Nat}
    (ha : Id.run (Page.kept X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget b.indexFrom (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index)
      (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start) =
        .error (.beforeLog x y) ∨
      Id.run (Page.kept X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget b.indexFrom (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index)
      (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start) =
        .error (.checkpointed x y))
    {e₀ : Entry} (h0 : Page.entryAt (m := Id) (keys.forStore (originChain o.opened.world))
      (fun x y => pure (I.extract x (x + y))) o.sealed.index.count o.index b.indexFrom = .ok e₀) :
    e₀.offset = max b.retainedFrom (frameSize (originChain o.opened.world)) ∧ e₀.steps = s₀ ∧ start < s₀ := by
  obtain ⟨L, -, -, hget, hrun⟩ := coherent_reader hS h hb
  have hL0 := hget 0 e₀ (by rw [Nat.add_zero]; exact h0)
  have hb' : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (fun k => Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index (b.indexFrom + k))
      (o.sealed.index.count + o.index.size - b.indexFrom) o.pos.offset (recorder.mark o.opened.world) start) =
        .error (.beforeLog x y) := by
    rcases ha with ha | ha
    · exact (Page.kept_beforeLog ha).2
    · exact (Page.kept_checkpointed (fun k x' y' hk => by
        have := Page.entryAt_error (rd := fun x y => I.extract x (x + y)) hk
        cases this) ha).2
  have hlt : start < e₀.steps := Page.build_beforeLog_first (by omega) (by rw [Nat.add_zero]; exact h0)
    (fun k x' y' hk => by
      have := Page.entryAt_error (rd := fun x y => I.extract x (x + y)) hk
      cases this) hb'
  cases L with
  | nil => simp at hL0
  | cons e _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL0
    subst hL0
    simp only [RunFrom, Prod.mk.injEq] at hrun
    exact ⟨hrun.1, hrun.2, hrun.2 ▸ hlt⟩

/-- `sealed_indexes` at the deployed instance: every premise discharged as in
`sealed_opens_deployed`, under the seal's `KeepNames` (HOST-68). -/
theorem sealed_indexes_deployed (keys : Keys) (file₀ H I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size keep = .ok (page, ix', file))
    {s₀ : Nat} (hS : Coherent keys file₀ I S s₀)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d)) {s₀' : Nat}
    (hkeep : KeepNames (keys.forStore (originChain o.opened.world)) (I ++ page) b.indexFrom ix'.count
      (o.pos.offset, (recorder.mark o.opened.world).1) keep
      (max keep.retainedFrom (frameSize (originChain o.opened.world))) s₀') :
    Coherent keys file (I ++ page) (S.extract 0 o.pos.offset) s₀' :=
  sealed_indexes keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide)
    (fun _ _ _ hs => foldStep_decode hs) file₀ H I S h (openWith_codecFits h) hseal hS hb hkeep

/-- `sealed_indexes_same` at the deployed instance: the default seal, keeping what the base kept,
with no premise beyond the open and the seal. -/
theorem sealed_indexes_deployed_same (keys : Keys) (file₀ H I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {page file : ByteArray} {ix' : IndexAt}
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d))
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size ⟨b.retainedFrom, b.indexFrom⟩ = .ok (page, ix', file))
    {s₀ : Nat} (hS : Coherent keys file₀ I S s₀) :
    Coherent keys file (I ++ page) (S.extract 0 o.pos.offset) s₀ :=
  sealed_indexes_same keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide)
    (fun _ _ _ hs => foldStep_decode hs) file₀ H I S h (openWith_codecFits h) hb hseal hS

/-- `keepNames_seal` at the deployed instance. -/
theorem keepNames_seal_deployed (keys : Keys) (file₀ H I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {keep' : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size keep' = .ok (page, ix', file))
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file₀ = .ok (b, n, d))
    {k0 : Nat} {keep : Keep} {o₀ s₀ : Nat}
    (hk : KeepNames (keys.forStore (originChain b.world)) I k0 b.indexCount (b.offset, (recorder.mark b.world).1)
      keep o₀ s₀) :
    KeepNames (keys.forStore (originChain o.opened.world)) (I ++ page) k0 ix'.count
      (o.pos.offset, (recorder.mark o.opened.world).1) keep o₀ s₀ :=
  keepNames_seal keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide)
    (fun _ _ _ hs => foldStep_decode hs) file₀ H I S h (openWith_codecFits h) hseal hb hk

/-- The base `genesisImage` writes reads back as the World it was given. -/
theorem genesisImage_base_read (keys : Keys) {w₀ : World D}
    (hfit : Codec.Kernel.World.CodecFits X.env (fun _ => True) w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    ∃ n d, Base.read keys c world img.base =
      .ok (⟨w₀, (Log.frame keys.segment segmentInitial (recorder.mark w₀).2).size,
        tagDigest keys.segment (segmentInitial ++ (recorder.mark w₀).2), indexStart.count, indexStart.last,
        Keep.all.retainedFrom, Keep.all.indexFrom⟩, n, d) := by
  obtain ⟨file, hf, rfl⟩ := genesisImage_ok h
  obtain ⟨-, hrd⟩ := Base.read_file (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    hf hfit (by decide) (by decide)
  exact ⟨_, _, hrd⟩

/-- **`host genesis`'s Store has a coherent index**: it holds none, and its run begins at the
genesis World's step count. -/
theorem genesis_indexes (keys : Keys) (hkeys : keys.chainBytes = Digest.width) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment w₀.steps := by
  obtain ⟨o, ho, -⟩ := genesis_reopens keys hkeys hg h
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  obtain ⟨n, d, hrd⟩ := genesisImage_base_read keys (genesisWorld_codecFits hf) h
  obtain ⟨file, -, rfl⟩ := genesisImage_ok h
  have hs := StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep
    Codec.Deployed.digestCodec _ _ _ ho
  obtain ⟨b, _, _, _, _, _, hb, _, _, _, _, _, _, _, _, _, _, _, hoo⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep _ _ _ _ ho
  have hsteps : o.sealed.steps = (Receive.genesisWorld X name nonce allowance founders).steps := by
    rw [hoo]
    show (recorder.mark b.world).1 = _
    rw [hb] at hrd; cases hrd
    rw [recorder_mark]
  rw [hsteps] at hs
  exact hs

/-- **`host import`'s Store has a coherent index**: it holds none, and its run begins at the imported
World's step count, its carried height (`importWorld_steps`): a page before it is refused
`beforeLog` (`Page.build_beforeLog_none`), and `page_beforeLog_origin` says from exactly where. -/
theorem import_indexes (keys : Keys) (hkeys : keys.chainBytes = Digest.width) {name nonce : ByteArray} {pin : Carry.Pin D} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (hi : Carry.importWorld X Codec.Deployed.digestCodec name nonce pin f = .ok (w₀, r)) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment w₀.steps := by
  obtain ⟨o, ho, -⟩ := import_reopens keys hkeys hi h
  obtain ⟨n, d, hrd⟩ := genesisImage_base_read keys (importWorld_codecFits hi) h
  obtain ⟨file, -, rfl⟩ := genesisImage_ok h
  have hs := StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep
    Codec.Deployed.digestCodec _ _ _ ho
  obtain ⟨b, _, _, _, _, _, hb, _, _, _, _, _, _, _, _, _, _, _, hoo⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep _ _ _ _ ho
  have hsteps : o.sealed.steps = w₀.steps := by
    rw [hoo]
    show (recorder.mark b.world).1 = _
    rw [hb] at hrd; cases hrd
    rw [recorder_mark]
  rw [hsteps] at hs
  exact hs

end Nanodregg.Host.Deployed
