/-
# Host.Proofs.Seal — a seal's bytes open to the World it sealed (HOST-43)

A seal (`Base.seal`, which both checkpoints run: `memCheckpoint`, `fileCheckpoint`) of the World an
open returned, at the open's position, with the entries since the base, writes a new base file and
a page of index entries that `index.log` gains at its end. `sealed_opens`: the one open
(`openWith`) of the new base, the segment the old open validated (cut at `o.pos.offset`, which
`openWriter` leaves), and `index.log` with the page appended, returns the SAME World, with no
record replayed, no torn tail, at the same position, and its `sealed` is exactly the `Sealed`
the loop installs (`settle`: the offset, the World's size, its mark, the digest of its World bytes,
and the `IndexAt` the seal returns).

* `sealed_opens_clean` — the same over the segment itself when it ends at the open's position;
* `sealed_unindexed_refused` (the tooth: crash-before-index) — the same files with the page NOT
  appended are refused `indexShort` by name whenever the seal had an entry to write.

Premises: `hw`/`hP`, the World codec reads the opened World back; `horigin`, a fold step keeps
`origin` (the origin frame is checked against the NEW base's World); `hmono`, a fold step moves the
mark's step count (the new base's last entry must begin before its World, HOST-53); `hcap`, the base record bound
fits the u32 length field. The open's position is a u64 because the seal wrote it: `Base.file`
refuses any other (`positionUnfit`, `Base.file_offset_lt`). `sealed_opens_deployed` discharges every
premise at the deployed instance: `hP` by `Deployed.openWith_codecFits` (every World the deployed
open returns is in the World codec's domain), `hw`, `horigin`, `hmono` and `hcap` by
`Codec.Kernel.world_lawfulOn`, `foldStep_originChain`, `foldStep_steps` and `decide`.
-/
import Host.Proofs.Genesis
import Host.Proofs.Deployed
import Host.Proofs.Coherence

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray

variable {W F : Type}

private theorem ofBytes_bytes (d : Codec.Digest) : Codec.Digest.ofBytes? d.bytes = some d := by
  unfold Codec.Digest.ofBytes?
  rw [dif_pos d.size_eq]

private theorem bytes_ofBytes {b : ByteArray} {d : Codec.Digest} (h : Codec.Digest.ofBytes? b = some d) :
    d.bytes = b := by
  unfold Codec.Digest.ofBytes? at h
  split at h
  · cases h; rfl
  · cases h

/-- The bytes a segment holds after its initial tag end in the tag the last record chains to. -/
private theorem encodeAll_ends (s : Sealer) : ∀ (prev : ByteArray) (rs : List ByteArray),
    ∃ X, prev ++ encodeAll s prev rs = X ++ lastTag s prev rs
  | prev, [] => ⟨ByteArray.empty, by simp only [encodeAll, lastTag, ByteArray.append_empty, ByteArray.empty_append]⟩
  | prev, r :: rs => by
    obtain ⟨X, hX⟩ := encodeAll_ends s (s.tag (prev ++ r)) rs
    refine ⟨prev ++ lenBytes r.size ++ r ++ X, ?_⟩
    simp only [encodeAll, lastTag, frame]
    calc prev ++ (lenBytes r.size ++ r ++ s.tag (prev ++ r) ++ encodeAll s (s.tag (prev ++ r)) rs)
        = prev ++ lenBytes r.size ++ r ++ (s.tag (prev ++ r) ++ encodeAll s (s.tag (prev ++ r)) rs) := by
          simp only [ByteArray.append_assoc]
      _ = prev ++ lenBytes r.size ++ r ++ X ++ lastTag s (s.tag (prev ++ r)) rs := by
          rw [hX]; simp only [ByteArray.append_assoc]

theorem foldlM_origin {step : W → ByteArray → Except F W} {origin : W → ByteArray}
    (ho : ∀ w r w', step w r = .ok w' → origin w' = origin w) :
    ∀ (rs : List ByteArray) (w w' : W), rs.foldlM step w = .ok w' → origin w' = origin w
  | [], w, w', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | r :: rs, w, w', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      rw [foldlM_origin ho rs w₁ w' h, ho w r w₁ h₁]

/-- What the seal of an opened World holds, read off the old open and the seal. -/
theorem seal_facts (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) (file₀ I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size = .ok (page, ix', file)) :
    file.size ≤ frameMax c.baseRecordMax ∧
    Base.read keys c world file = .ok (⟨o.opened.world, o.pos.offset, o.pos.tag, ix'.count, ix'.last⟩,
      world.size o.opened.world, keys.worldDigest (worldBytesOf file (world.size o.opened.world))) ∧
    tagBytes ≤ o.pos.offset ∧ o.pos.offset ≤ S.size ∧
    S.extract (o.pos.offset - tagBytes) o.pos.offset = o.pos.tag.bytes ∧
    originFault (F := F) keys.segment (S.extract 0 (originLen o.pos.offset)) (origin o.opened.world) = none ∧
    I.size = o.sealed.index.count * entryBytes keys ∧
    ix'.count = o.sealed.index.count + o.index.size ∧ ix'.count ≤ indexMax ∧
    (I ++ page).size = ix'.count * entryBytes keys ∧
    indexNamed (keys.forStore (origin o.opened.world)) ix'.count ix'.last (mark o.opened.world).1
      ((I ++ page).extract (lastAt keys ix'.count).1
        ((lastAt keys ix'.count).1 + (lastAt keys ix'.count).2)) = none ∧
    Id.run (lastFrameFault (F := F) keys.segment c.recordBytesMax o.pos.offset
      (lastEntry (keys.forStore (origin o.opened.world)) ix'.count ((I ++ page).extract (lastAt keys ix'.count).1
        ((lastAt keys ix'.count).1 + (lastAt keys ix'.count).2)))
      (segReader (S.extract 0 o.pos.offset))) = none := by
  obtain ⟨b, baseBytes, digest, len, op, tag, hb, hlen, hoff, htag, hof, hwI, hi, hix, hlf, hop, htg, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file₀ I S h
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  dsimp only at hP hseal ⊢
  obtain ⟨rs, he, hf, hlt, _, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hfold := indexed_foldlM_fst mark step rs _ _ _ hf
  have hor : origin op.world.1 = origin b.world := foldlM_origin horigin rs _ _ hfold
  rw [hor] at hseal ⊢
  obtain ⟨hI, hent, hfile⟩ := seal_at_end _ _ _ _ _ _ _ _ hseal
  obtain ⟨_, hcnt, hmax, _, _, _⟩ := entries_ok hent
  obtain ⟨hle, hall⟩ := indexed_foldlM_steps mark step hmono rs _ _ _ hf (by simp)
  obtain ⟨hsz, hnamed⟩ := entries_named hent hI hix hle (fun e he => hall e (by simpa [sealEntries] using he))
  obtain ⟨hfs, hrd⟩ := Base.read_file hw hfile hP (by unfold indexMax at hmax; omega) hcap
  have ht32 : tagBytes = 32 := rfl
  -- the anchor: the 32 bytes before the open's position are the tag it chains from
  have htagb : tag.bytes = op.lastTag := bytes_ofBytes htg
  have hseg : S.extract b.offset (b.offset + op.validLen) = encodeAll keys.segment b.tag.bytes rs := by
    rw [← he, extract_extract]; congr 1 <;> omega
  obtain ⟨X, hX⟩ := encodeAll_ends keys.segment b.tag.bytes rs
  have hwhole : S.extract (b.offset - tagBytes) (b.offset + op.validLen) = X ++ tag.bytes := by
    rw [extract_eq_extract_append_extract b.offset (by omega) (by omega), htag, hseg, hX, htagb, hlt]
  have hXs : X.size = op.validLen := by
    have := congrArg ByteArray.size hwhole
    rw [size_append, tag.size_eq, size_extract] at this
    omega
  have hanchor : S.extract (b.offset + op.validLen - tagBytes) (b.offset + op.validLen) = tag.bytes := by
    have := congrArg (fun y => y.extract op.validLen (op.validLen + tagBytes)) hwhole
    simp only at this
    rw [extract_extract, extract_append_eq_right hXs.symm (by rw [hXs, tag.size_eq]; rfl),
      show b.offset - tagBytes + op.validLen = b.offset + op.validLen - tagBytes by omega,
      show min (b.offset - tagBytes + (op.validLen + tagBytes)) (b.offset + op.validLen)
        = b.offset + op.validLen by omega] at this
    exact this
  -- the origin frame the old open read is a prefix of the one the new open reads
  have hofn : originFault (F := F) keys.segment (S.extract 0 (originLen (b.offset + op.validLen)))
      (origin b.world) = none := by
    obtain ⟨r, hr, hre⟩ := (originFault_none_iff (F := F) _ _ _).mp hof
    have hle : originLen b.offset ≤ originLen (b.offset + op.validLen) := by unfold originLen; omega
    rw [originFault_none_iff]
    refine ⟨r, ?_, hre⟩
    rw [extract_eq_extract_append_extract (originLen b.offset) (Nat.zero_le _) hle]
    exact frameAt_append hr
  have hes : (sealEntries op.world.2.1).size = op.world.2.1.size := by simp [sealEntries]
  -- HOST-63: the new base's last entry is the frame that ends at the open's position
  have hlast : Id.run (lastFrameFault (F := F) keys.segment c.recordBytesMax (b.offset + op.validLen)
      (lastEntry (keys.forStore (origin b.world)) ix'.count ((I ++ page).extract (lastAt keys ix'.count).1
        ((lastAt keys ix'.count).1 + (lastAt keys ix'.count).2)))
      (segReader (S.extract 0 (b.offset + op.validLen)))) = none := by
    obtain ⟨hfit, hcnt', -, hp, hnil, hlastTag⟩ := entries_ok hent
    have hsz0 := indexed_foldlM_size mark step rs _ _ _ hf
    simp only [Array.size_empty, Nat.zero_add] at hsz0
    have hesl : (sealEntries op.world.2.1).toList = op.world.2.1.toList := by simp [sealEntries]
    rw [lastFrameFault_congr (S' := S) _ (fun i j hj => extract_prefix S hj)]
    have hencsz : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
      rw [← hseg, size_extract]; omega
    by_cases h0 : op.world.2.1.size = 0
    · have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrs0
      have hv0 : op.validLen = 0 := by simp [encodeAll] at hencsz; omega
      have hl0 : op.world.2.1.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
      have hix' := hnil (by rw [hesl]; exact hl0)
      subst hix'
      have hp0 : page = ByteArray.empty := by
        rw [hp, hesl, hl0]; rfl
      rw [hp0, ByteArray.append_empty, hv0, Nat.add_zero]
      exact hlf
    · have hne : rs ≠ [] := by intro hz; subst hz; simp at hsz0; exact h0 (by rw [hsz0]; rfl)
      have hp1 : S.extract (b.offset - tagBytes) (b.offset - tagBytes + tagBytes) = b.tag.bytes := by
        rw [show b.offset - tagBytes + tagBytes = b.offset by omega]; exact htag
      have hseg' : S.extract b.offset (b.offset + (encodeAll keys.segment b.tag.bytes rs).size) =
          encodeAll keys.segment b.tag.bytes rs := by rw [hencsz]; exact hseg
      obtain ⟨e, r, hback, hge, hr, hr32, hfr, hend⟩ :=
        indexed_last (rm := c.recordBytesMax) mark step rs b.world #[] b.offset b.tag.bytes hne hrs hp1 hseg' hf
      have hend' : e.offset + frameSize r = b.offset + op.validLen := by
        rw [hend, openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop]
      have hn : 0 < (sealEntries op.world.2.1).size := by rw [hes]; omega
      have hcpos : 0 < ix'.count := by omega
      have hentry : lastEntry (keys.forStore (origin b.world)) ix'.count ((I ++ page).extract
          (lastAt keys ix'.count).1 ((lastAt keys ix'.count).1 + (lastAt keys ix'.count).2)) = some e := by
        unfold lastEntry
        rw [if_neg (by omega), lastAt_read keys _ hcpos]
        have hoffe : (ix'.count - 1) * entryBytes keys =
            I.size + ((sealEntries op.world.2.1).size - 1) * entryBytes keys := by
          have hebf : entryBytes (keys.forStore (origin b.world)) = entryBytes keys := rfl
          rw [hI, hcnt', hebf, ← Nat.add_mul]; congr 1; dsimp only; omega
        rw [hoffe, Nat.add_assoc, ByteArray.extract_append_size_add, hp]
        have hr' := run_read (keys.forStore (origin b.world)) b.indexCount
          (sealEntries op.world.2.1).toList ((sealEntries op.world.2.1).size - 1) (by simp; omega) hfit
        rw [show entryBytes (keys.forStore (origin b.world)) = entryBytes keys from rfl] at hr'
        have hse : sealEntries op.world.2.1 = op.world.2.1 := by simp [sealEntries]
        dsimp only at hcnt'
        rw [show ix'.count - 1 = b.indexCount + ((sealEntries op.world.2.1).size - 1) by omega, hr']
        rw [Array.back?_eq_getElem?] at hback
        simp only [hse, Array.getElem_toList]
        rw [Array.getElem?_eq_getElem (by omega)] at hback
        exact hback
      rw [hentry]
      exact lastFrameFault_frame (by omega) hend' (by omega)
        (by rw [show e.offset - tagBytes + tagBytes = e.offset by omega] at hfr; exact hfr) hr hr32
  exact ⟨hfs, hrd, by omega, by omega, hanchor, hofn, hI, by rw [hcnt, hes], hmax, hsz, hnamed, hlast⟩

/-- **A seal's bytes open to the World it sealed** (HOST-43). The one open of base file `file₀`,
segment `S` and index bytes `I` returned `o`; the seal (`Base.seal` under this Store's index keys,
as both checkpoints call it) of `o`'s World at `o`'s position, with the entries since the base
(`sealEntries o.index`), from `o.sealed.index`, over an `index.log` of `I.size` bytes, returned
`(page, ix', file)`. Then the one open of `file`, the segment cut at `o.pos.offset` and `I ++ page`
returns: the same World, no record, no torn tail, the same position, no tail entry, no orphan,
and the `Sealed` the loop installs for this seal. -/
theorem sealed_opens (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) (file₀ I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size = .ok (page, ix', file)) :
    Id.run (openWith keys c world mark origin step file (S.extract 0 o.pos.offset).size (I ++ page).size
        (segReader (I ++ page)) (segReader (S.extract 0 o.pos.offset))) =
      .ok ⟨⟨o.opened.world, 0, 0, o.pos.tag.bytes, 0⟩,
        ⟨o.pos.offset, world.size o.opened.world, (mark o.opened.world).1, (mark o.opened.world).2,
          keys.worldDigest (worldBytesOf file (world.size o.opened.world)), ix'⟩, o.pos, #[], 0⟩ := by
  obtain ⟨hfs, hrd, hoff, hle, hanchor, hof, hI, hcnt, hmax, hsz, hnamed, hlast⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ I S h hP hseal
  have hS' : (S.extract 0 o.pos.offset).size = o.pos.offset := by simp only [size_extract]; omega
  have ⟨q1, q2, q3⟩ := tail_read (S.extract 0 o.pos.offset) (len := 0) hoff (by omega)
  have htr : tailRead c (world.size o.opened.world) o.pos.offset (S.extract 0 o.pos.offset).size = .ok 0 := by
    rw [hS']; exact tailRead_self _ _ _
  have hanchor' : (S.extract 0 o.pos.offset).extract (o.pos.offset - tagBytes) o.pos.offset = o.pos.tag.bytes := by
    rw [extract_prefix S (Nat.le_refl _)]; exact hanchor
  have hol : originLen o.pos.offset ≤ o.pos.offset := by unfold originLen; omega
  have hla := lastAt_within keys ix'.count
  have hempty : ((S.extract 0 o.pos.offset).extract o.pos.offset (S.extract 0 o.pos.offset).size).size = 0 := by
    simp only [size_extract]; omega
  unfold openWith
  simp only [segReader, pure_bind, Nat.zero_add]
  rw [if_neg (by omega), hrd]
  dsimp only
  rw [htr]
  dsimp only
  rw [if_neg (by omega), if_neg (by rw [q1]; simp), q2, hanchor', if_neg (by simp),
    if_neg (by simp only [size_extract, hS']; omega), extract_prefix S hol, hof]
  dsimp only
  rw [if_neg (by omega), if_neg (by omega), if_neg (by simp only [size_extract]; omega), hnamed]
  dsimp only
  simp only [Id.run] at hlast
  rw [hlast, show (none : Id (Option (StoreFault F))) = (pure none : Id (Option (StoreFault F))) from rfl,
    pure_bind]
  dsimp only
  rw [q3, openLog_empty keys.segment c.recordBytesMax (indexed mark step) _ _ _ hempty]
  dsimp only
  rw [ofBytes_bytes]
  simp only [Id.run, pure, hsz, Nat.sub_self, Nat.add_zero]

/-- `sealed_opens` over the segment itself, when it ends where the open validated it (no torn
tail: what `openWriter` leaves after truncating). -/
theorem sealed_opens_clean (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) (file₀ I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ S.size I.size (segReader I) (segReader S)) = .ok o)
    (hclean : S.size = o.pos.offset)
    (hP : P o.opened.world)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size = .ok (page, ix', file)) :
    ∃ o', Id.run (openWith keys c world mark origin step file S.size (I ++ page).size
        (segReader (I ++ page)) (segReader S)) = .ok o' ∧
      o'.opened.world = o.opened.world ∧ o'.opened.records = 0 ∧ o'.opened.torn = 0 ∧ o'.pos = o.pos := by
  have hs := sealed_opens keys c world mark origin step hw horigin hmono hcap file₀ I S h hP hseal
  rw [← hclean, extract_zero_size] at hs
  exact ⟨_, hs, rfl, rfl, rfl, rfl⟩

/-- **The tooth: crash before the index.** The same files with the seal's page NOT appended to
`index.log` (the new base installed over an `index.log` that never gained its entries) are refused
`indexShort` by name, whenever the seal had an entry to write (a record since the base). -/
theorem sealed_unindexed_refused (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) (file₀ I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size = .ok (page, ix', file))
    (hn : 0 < o.index.size) :
    Id.run (openWith keys c world mark origin step file (S.extract 0 o.pos.offset).size I.size
        (segReader I) (segReader (S.extract 0 o.pos.offset))) =
      .error (.base (.indexShort I.size (ix'.count * entryBytes keys))) := by
  obtain ⟨hfs, hrd, hoff, hle, hanchor, hof, hI, hcnt, hmax, hsz, hnamed, hlast⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ I S h hP hseal
  have hS' : (S.extract 0 o.pos.offset).size = o.pos.offset := by simp only [size_extract]; omega
  have ⟨q1, q2, q3⟩ := tail_read (S.extract 0 o.pos.offset) (len := 0) hoff (by omega)
  have htr : tailRead c (world.size o.opened.world) o.pos.offset (S.extract 0 o.pos.offset).size = .ok 0 := by
    rw [hS']; exact tailRead_self _ _ _
  have hanchor' : (S.extract 0 o.pos.offset).extract (o.pos.offset - tagBytes) o.pos.offset = o.pos.tag.bytes := by
    rw [extract_prefix S (Nat.le_refl _)]; exact hanchor
  have hol : originLen o.pos.offset ≤ o.pos.offset := by unfold originLen; omega
  have heb : 0 < entryBytes keys := by unfold entryBytes; omega
  have hmore := Nat.mul_le_mul_right (entryBytes keys) (show 1 ≤ o.index.size from hn)
  have hshort : I.size < ix'.count * entryBytes keys := by
    rw [hI, hcnt, Nat.add_mul]; rw [Nat.one_mul] at hmore; omega
  unfold openWith
  simp only [segReader, pure_bind, Nat.zero_add]
  rw [if_neg (by omega), hrd]
  dsimp only
  rw [htr]
  dsimp only
  rw [if_neg (by omega), if_neg (by rw [q1]; simp), q2, hanchor', if_neg (by simp),
    if_neg (by simp only [size_extract, hS']; omega), extract_prefix S hol, hof]
  dsimp only
  rw [if_neg (by omega), if_pos hshort]
  rfl

namespace Deployed

open Nanodregg.Kernel Nanodregg.Codec

/-- `sealed_opens` at the deployed instance, with no premise beyond the open's and the seal's
success: the deployed open, the deployed seal under `keys.forStore (originChain w)` (what
`fileCheckpoint` and `memCheckpoint` call with the deployed `originChain`). The codec premise is
`Codec.Kernel.world_lawfulOn` over `digestCodec_lawful.on` (`P` = `World.CodecFits` with the digest
predicate `fun _ => True`), which the opened World meets (`openWith_codecFits`); `horigin` is
`foldStep_originChain`, and the u32 bound is decided. -/
theorem sealed_opens_deployed (keys : Keys) (file₀ I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size = .ok (page, ix', file)) :
    Id.run (openWith keys c world recorder.mark originChain foldStep file (S.extract 0 o.pos.offset).size
        (I ++ page).size (segReader (I ++ page)) (segReader (S.extract 0 o.pos.offset))) =
      .ok ⟨⟨o.opened.world, 0, 0, o.pos.tag.bytes, 0⟩,
        ⟨o.pos.offset, world.size o.opened.world, (recorder.mark o.opened.world).1,
          (recorder.mark o.opened.world).2,
          keys.worldDigest (worldBytesOf file (world.size o.opened.world)), ix'⟩, o.pos, #[], 0⟩ :=
  sealed_opens keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide) file₀ I S h
    (openWith_codecFits h) hseal

/-- The tooth of `Base.file_offset_lt`: a base whose World fits but whose position is at or past
2^64 is refused `positionUnfit` by name, before anything is encoded. -/
theorem file_positionUnfit (keys : Keys) {w : World D} {seg : Position} (ix : IndexAt)
    (hsz : world.size w ≤ c.worldBytesMax) (hoff : 2 ^ 64 ≤ seg.offset) :
    Base.file keys c world w seg ix = .error (.positionUnfit seg.offset) := by
  unfold Base.file
  rw [if_neg (by omega), if_pos hoff]

/-- The tooth of `refuse_refusals_listing` (why a refusal weighs 96 in `openWith_listing_lt`): a
refusal recorded on a World with no refusals lists exactly three entries, its transaction's leaf, its
member's window count and the World's window total (KERNEL-55 R1). -/
theorem refuse_refusals_listing_three {w w' : World D} {r : Refused D} (he : w.refusals = .empty)
    (h : World.refuse X.env w r = .ok w') : w'.refusals.toList.length = 3 := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  rw [commitRefusal_refusals, he]
  have h0 : Trie.Routed (refusalSpec X.env) 0 (Trie.T.empty : Refusals D) := (Trie.canon_empty _ 0).1
  have p1 := Trie.toList_insert_perm (refusalSpec X.env) h0 (.tx r.txId) (.refused (w.height + 1) r.code r.member)
  have h1 := Trie.routed_insert (refusalSpec X.env) (.tx r.txId) (.refused (w.height + 1) r.code r.member) h0
  have p2 := Trie.toList_insert_perm (refusalSpec X.env) h1
    (.count r.member (refusalWindow w.height)) (.count (refusalCount X.env w r.member + 1))
  have h2 := Trie.routed_insert (refusalSpec X.env) (.count r.member (refusalWindow w.height))
    (.count (refusalCount X.env w r.member + 1)) h1
  have p3 := Trie.toList_insert_perm (refusalSpec X.env) h2
    (.total w.origin (refusalWindow w.height)) (.count (refusalTotal X.env w + 1))
  rw [p3.length_eq, List.length_append, (p2.filter _).length_eq, List.filter_append, List.length_append,
    ((p1.filter _).filter _).length_eq]
  simp [Trie.T.toList]

end Deployed

end Nanodregg.Host
