/-
HOST-71: identity correspondence is preserved by every writer operation. An interrupted
adoption changes neither the previous base, its index, nor any selected file. The open
corollary uses the existing logical open, keeping sealed_opens / seal_facts unchanged.
OS realization assumptions: durable writes preserve other files; base rename is atomic.
-/
import Host.IdentityImage
import Host.Open
import Host.Proofs.Segs

namespace Nanodregg.Host
open Nanodregg.Codec

theorem segmentIdentity_injective {g g' o o' : Nat} (ho : o < 2 ^ 64) (ho' : o' < 2 ^ 64)
    (h : segmentIdentity g o = segmentIdentity g' o') : g = g' ∧ o = o' := by
  unfold segmentIdentity at h
  omega

/-- The runtime reader's accepted header is authenticated under the selected generation
and names exactly the requested logical offset. No physical identity is silently relabelled. -/
theorem physicalHeaderRead_ok {keys : Keys} {generation offset : Nat} {bytes logical : ByteArray}
    {h : Header} (read : physicalHeaderRead keys generation offset bytes = .ok (h, logical)) :
    physicalRead keys "header-identity" bytes = some (generation, logical) ∧
      Header.read keys logical = some h ∧ h.start = offset := by
  cases hp : physicalRead keys "header-identity" bytes with
  | none => simp [physicalHeaderRead, hp] at read
  | some pair =>
    obtain ⟨g, hb⟩ := pair
    cases hh : Header.read keys hb with
    | none => simp [physicalHeaderRead, hp, hh] at read
    | some hd =>
      by_cases he : g = generation ∧ hd.start = offset
      · have pairEq : hd = h ∧ hb = logical := by
          simpa [physicalHeaderRead, hp, hh, he] using read
        rcases pairEq with ⟨rfl, rfl⟩
        exact ⟨by rw [he.1], hh, he.2⟩
      · simp [physicalHeaderRead, hp, hh, he] at read

theorem physicalHeaderRead_foreign {keys : Keys} {generation offset g : Nat}
    {bytes logical : ByteArray} {h : Header}
    (hp : physicalRead keys "header-identity" bytes = some (g, logical))
    (hh : Header.read keys logical = some h) (foreign : ¬ (g = generation ∧ h.start = offset)) :
    physicalHeaderRead keys generation offset bytes = .error .foreignSegment := by
  simp [physicalHeaderRead, hp, hh, foreign]

/-- The concrete directory allocator exceeds each existing filename's generation. -/
theorem nextGeneration_gt {id : Nat} {ids : List Nat} (member : id ∈ ids) :
    id / 2 ^ 64 < nextGeneration ids := by
  induction ids with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih member) (Nat.le_max_right _ _)

/-- prepareAdoption read the current file before enumerating the directory under its writer
lock. That file's name is in the enumeration, so allocation cannot select its generation. -/
theorem nextGeneration_fresh {generation offset : Nat} {ids : List Nat}
    (bound : offset < 2 ^ 64) (member : segmentIdentity generation offset ∈ ids) :
    nextGeneration ids ≠ generation := by
  have h := nextGeneration_gt member
  have quotient : segmentIdentity generation offset / 2 ^ 64 = generation := by
    unfold segmentIdentity
    omega
  rw [quotient] at h
  omega

theorem generationFault_moved {expected actual : Nat} {bytes : ByteArray}
    (decoded : Stream.nat64.decode bytes = .ok actual) (moved : actual ≠ expected) :
    generationFault expected bytes = some .foreignSegment := by
  simp [generationFault, decoded, moved]

theorem generationFault_same {generation : Nat} {bytes : ByteArray}
    (decoded : Stream.nat64.decode bytes = .ok generation) :
    generationFault generation bytes = none := by
  simp [generationFault, decoded]

/-- Every existing file's authenticated generation/start names exactly that physical file. -/
def IdentityCorresponds (s : IdentityImage) : Prop :=
  ∀ id f, s.files id = some f →
    f.header.start < 2 ^ 64 ∧ id = segmentIdentity f.generation f.header.start

theorem identity_empty : IdentityCorresponds IdentityImage.empty := by
  intro id f h
  cases h

theorem identity_put {s : IdentityImage} (hs : IdentityCorresponds s) (f : SegmentImage)
    (hf : f.header.start < 2 ^ 64) : IdentityCorresponds (s.put f) := by
  intro id found h
  simp only [IdentityImage.put] at h
  split at h
  next he =>
    cases h
    exact ⟨hf, he⟩
  next _ => exact hs id found h

theorem identity_body {s : IdentityImage} (hs : IdentityCorresponds s) (id : Nat)
    (edit : ByteArray → ByteArray) : IdentityCorresponds (s.body id edit) := by
  intro j f h
  simp only [IdentityImage.body] at h
  split at h
  next _ =>
    cases hx : s.files j with
    | none => simp [hx] at h
    | some old =>
      simp only [hx, Option.map_some, Option.some.injEq] at h
      subst f
      exact hs j old hx
  next _ => exact hs j f h

theorem identity_publish {s : IdentityImage} (hs : IdentityCorresponds s)
    (g : Nat) (base index : ByteArray) : IdentityCorresponds (s.publish g base index) := hs

theorem identity_drop {s : IdentityImage} (hs : IdentityCorresponds s) (remove : Nat → Bool) :
    IdentityCorresponds (s.drop remove) := by
  intro id f h
  simp only [IdentityImage.drop] at h
  split at h
  next _ => cases h
  next _ => exact hs id f h

/-- Genesis puts its origin and base headers at generation zero. The same invariant covers
rotation/prepareAdoption (put), append/truncate (body), seal/adopt (publish), retention (drop). -/
inductive IdentityLife : IdentityImage → Prop where
  | genesis (origin base : SegmentImage) (ho : origin.header.start < 2 ^ 64)
      (hb : base.header.start < 2 ^ 64) :
      IdentityLife ((IdentityImage.empty.put { origin with generation := 0 }).put { base with generation := 0 })
  | put {s} (life : IdentityLife s) (f : SegmentImage) (hf : f.header.start < 2 ^ 64) :
      IdentityLife (s.put f)
  | body {s} (life : IdentityLife s) (id : Nat) (edit : ByteArray → ByteArray) :
      IdentityLife (s.body id edit)
  | publish {s} (life : IdentityLife s) (g : Nat) (base index : ByteArray) :
      IdentityLife (s.publish g base index)
  | drop {s} (life : IdentityLife s) (remove : Nat → Bool) : IdentityLife (s.drop remove)

theorem identity_life {s : IdentityImage} (life : IdentityLife s) : IdentityCorresponds s := by
  induction life with
  | genesis origin base ho hb =>
    exact identity_put (s := IdentityImage.empty.put { origin with generation := 0 })
      (identity_put (s := IdentityImage.empty) identity_empty { origin with generation := 0 } ho)
      { base with generation := 0 } hb
  | put _ f hf ih => exact identity_put ih f hf
  | body _ id edit ih => exact identity_body ih id edit
  | publish _ g base index ih => exact identity_publish ih g base index
  | drop _ remove ih => exact identity_drop ih remove

/-- A selected image's header names the requested LOGICAL offset and base generation.
This is filename/header correspondence only: it does not establish SlicesOf, file
availability, or IO refinement. The existing logical-reader seal premises are unchanged. -/
theorem identity_at {s : IdentityImage} (hs : IdentityCorresponds s) {offset : Nat} {f : SegmentImage}
    (h : s.at offset = some f) : f.generation = s.generation ∧ f.header.start = offset := by
  unfold IdentityImage.at at h
  split at h
  next ho =>
    obtain ⟨hf, hid⟩ := hs _ _ h
    obtain ⟨hg, hoff⟩ := segmentIdentity_injective ho hf hid
    exact ⟨hg.symm, hoff.symm⟩
  next _ => cases h

/-- Crash after the new header but before the base: every file the previous base selects
is byte-for-byte the same. The new generation is essential; removing that premise allows
the original in-place-header defect. -/
theorem adoption_prepared_at (s : IdentityImage) (f : SegmentImage)
    (hf : f.header.start < 2 ^ 64) (fresh : f.generation ≠ s.generation) :
    (s.put f).at = s.at := by
  funext offset
  unfold IdentityImage.at IdentityImage.put
  split
  next ho =>
    dsimp only
    rw [if_neg]
    intro he
    exact fresh (segmentIdentity_injective ho hf he).1.symm
  next _ => rfl

theorem adoption_prepared_base (s : IdentityImage) (f : SegmentImage) :
    (s.put f).base = s.base ∧ (s.put f).index = s.index ∧ (s.put f).generation = s.generation := by
  exact ⟨rfl, rfl, rfl⟩

/-- The interruption frame property with freshness discharged by the allocator.
The named old file was read successfully by prepareAdoption before the directory listing. -/
theorem adoption_allocated_at (s : IdentityImage) (f : SegmentImage) (ids : List Nat)
    (hf : f.header.start < 2 ^ 64) (oldOffset : Nat) (ho : oldOffset < 2 ^ 64)
    (member : segmentIdentity s.generation oldOffset ∈ ids)
    (allocated : f.generation = nextGeneration ids) :
    (s.put f).at = s.at := by
  apply adoption_prepared_at s f hf
  rw [allocated]
  exact nextGeneration_fresh ho member

/-- Feed the SAME logical reader core used by Segs.read. Because a prepared adoption cannot
change its selected files, the entire interrupted open equals the prior successful open,
including its World, entries and position. No claim that only the completed adoption opens. -/
theorem adoption_interrupted_opens {W F : Type} (keys : Keys) (c : Cadence) (world : Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (s : IdentityImage) (f : SegmentImage) (hf : f.header.start < 2 ^ 64)
    (ids : List Nat) (oldOffset : Nat) (ho : oldOffset < 2 ^ 64)
    (member : segmentIdentity s.generation oldOffset ∈ ids)
    (allocated : f.generation = nextGeneration ids) (starts : List Nat) (offset size : Nat) (o : Opening W)
    (opened : Id.run (openWith keys c world mark origin step s.base
      ((s.at offset).map (fun f => Header.bytes keys f.header) |>.getD ByteArray.empty) size s.index.size
      (fun off len => pure (.ok (s.index.extract off (off + len))))
      (fun off len => segRead
        (fun start => pure (.ok ((s.at start).map (·.header.tag.bytes) |>.getD ByteArray.empty)))
        (fun start pos len => pure (((s.at start).map (fun (f : SegmentImage) => f.body) |>.getD ByteArray.empty).extract pos (pos + len)))
        starts off len)) = .ok o) :
    Id.run (openWith keys c world mark origin step (s.put f).base
      (((s.put f).at offset).map (fun f => Header.bytes keys f.header) |>.getD ByteArray.empty) size (s.put f).index.size
      (fun off len => pure (.ok ((s.put f).index.extract off (off + len))))
      (fun off len => segRead
        (fun start => pure (.ok (((s.put f).at start).map (·.header.tag.bytes) |>.getD ByteArray.empty)))
        (fun start pos len => pure ((((s.put f).at start).map (fun (f : SegmentImage) => f.body) |>.getD ByteArray.empty).extract pos (pos + len)))
        starts off len)) = .ok o := by
  rw [adoption_allocated_at s f ids hf oldOffset ho member allocated]
  exact opened

/-- The non-vacuous opposite: selecting the new generation exposes the new header at its
logical start. An unselected prepared file and a committed adoption are observably distinct. -/
theorem adoption_published_at (s : IdentityImage) (f : SegmentImage)
    (hf : f.header.start < 2 ^ 64) (base index : ByteArray) :
    ((s.put f).publish f.generation base index).at f.header.start = some f := by
  simp [IdentityImage.at, IdentityImage.publish, IdentityImage.put, hf]

end Nanodregg.Host
