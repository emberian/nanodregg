/-
# Host.Proofs.Deployed — the deployed instance meets the premises of the generic open theorems

* `originChain_genesis` / `genesis_origin_passes` (HOST-25) — for every World `host genesis` makes
  (`Receive.genesisWorld`, what `Receive.genesis` returns: `genesis_ok`), the deployed `originChain` is the chain `recorder.mark` writes into the origin
  frame (KERNEL's `genesis_chain`), and the deployed genesis image passes the origin check;
* `mark_chain_width` (HOST-33) — every chain the deployed loop puts in an index entry is the width
  the deployed Store's entries hold (`Keys.ofKey`'s `chainBytes`), so `entryUnfit`'s chain arm
  cannot fire at the deployed instance (the generic round trip, `entriesSeq_read`, has no premise);
* `foldStep_originChain` (HOST-25) — a record the deployed reopen folds keeps `originChain`
  (`Record.step_origin`, from KERNEL's `fold_origin`), so every later base's World states the chain
  the origin frame holds;
* `genesisImage_opens_deployed` (one start path) — the deployed open of exactly what deployed
  genesis writes returns the World it was given, no records, no torn tail, for every World the
  World codec reads back whose chain is the genesis chain of its origin;
* `genesis_reopens` — the genesis image of the World `host genesis` makes (`Receive.genesis`) opens
  to it, no premise beyond the two successes (`genesisWorld_codecFits`, `genesis_chain_eq`);
* `import_reopens` — the genesis image of the World `host import` makes opens to it, and the
  reopened World's carried bytes are the file's, so `importWith`'s `carryMismatch reopen` compare
  passes, with no premise beyond the import's and genesis's own success (the carried journal's
  window is the carried codec's `kernel/carried-journal`, added on HOST-39's finding);
* `openWith_exportFile_ok` (HOST-28) — `host export` refuses no World the deployed open returns
  whose allowance is below 2^64 (`hallow`, the ONE named premise): the base World is in the World
  codec's domain because the codec read it (`kept_of_fits`), every record's admissions keep the
  rest (`Kept`, `Record.foldlM_kept`), and the cell listing is below 2^24 leaves
  (`openWith_listing_lt`: the base holds at most `baseRecordMax / 33` of them, and each leaf a
  Turn adds costs 32 bytes of the tail `tailRead` bounds). `hallow` waits on cv 01a14ba9-cbf4
  (KERNEL: `GenesisFits` / `CarryFits` / `World.CodecFits` must bound weight + allowance below
  2^64); it is reachable without that, through `host import`: a carried allowance of 2^64 − 1 and
  a light Turn that retires a heavy cell;
* `openWith_journalOk` (KERNEL-41) — the World the deployed writer's open returns has a `JournalOk`
  journal (a canonical trie, every entry in its window, heights distinct): its base's World because
  the deployed World codec read it (`Codec.Deployed.world_get_journalOk`), every record after it by
  `Record.foldlM_journalOk`; with `Host.admitBatch_journalOk`, every World the loop holds is, and the
  `JournalCanon` premise of `Host.lookup_expired_final` / `lookup_expired_never_committed` is
  discharged there.
-/
import Host.Deployed
import Host.Proofs.Base
import Host.Proofs.Carry
import Host.Proofs.Backup
import Host.Proofs.Genesis
import Codec.Proofs.Deployed
import Kernel.Proofs.JournalHead

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

theorem originChain_genesis (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    originChain (Receive.genesisWorld X name nonce allowance founders) =
      (recorder.mark (Receive.genesisWorld X name nonce allowance founders)).2 := by
  simp only [originChain, recorder, Receive.genesis_chain]

theorem genesis_origin_passes {F : Type} (keys : Keys) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) {img : Image}
    (h : genesisImage keys c world recorder.mark (Receive.genesisWorld X name nonce allowance founders) = .ok img) :
    originFault (F := F) keys.segment (img.segment.extract 0 (originLen img.segment.size))
      (originChain (Receive.genesisWorld X name nonce allowance founders)) = none :=
  genesisImage_origin keys c world recorder.mark originChain _ h
    (by show (Receive.genesisWorld X name nonce allowance founders).chain.bytes.size ≤ chainBytesMax
        rw [Digest.size_eq]; decide)
    (originChain_genesis name nonce allowance founders)

theorem foldStep_originChain {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    originChain w' = originChain w := by
  unfold originChain
  rw [Record.step_origin h]

/-- **The deployed chain is the deployed entry's width** (HOST-33): the chain `recorder.mark`
writes into every index entry is `chainBytes` long for every Store key, so no deployed seal is
refused `entryUnfit` for its chain. -/
theorem mark_chain_width (key : Codec.Digest) (w : World D) :
    (recorder.mark w).2.size = (Keys.ofKey key shapes).chainBytes := by
  simp only [recorder, Keys.ofKey, Codec.Digest.size_eq]

/-- `Carry.world_carried` at the deployed codec (HOST-28): a file `host import` accepts hashes to
the operator's digest, and the World it makes holds exactly the file's carried bytes at its anchor
height. The codec premise is CODEC's `digestCodec_lawful`. -/
theorem import_carried {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) :
    Carry.digestOf f = want ∧
      (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes w₀.carried = f.extract r.carriedAt f.size ∧
      w₀.height = r.head.height :=
  have ⟨hr, hw⟩ := Carry.importWorld_ok h
  Carry.world_carried Codec.Deployed.digestCodec_lawful.on hr hw

/-- `Carry.exportFile_reads` at the deployed codec: what `host export` writes, `host import`
reads back under the printed digest, to the exported World's carried bytes and height. -/
theorem export_reads {w : World D} {f : ByteArray}
    (h : Carry.exportFile X.env Codec.Deployed.digestCodec w = .ok f) :
    ∃ r, Carry.read X.env Codec.Deployed.digestCodec (Carry.digestOf f) f = .ok r ∧
      (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes r.carried =
        (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes w.carried ∧
      r.head = ⟨w.origin, w.height, w.chain⟩ :=
  Carry.exportFile_reads h


/-- **The World the deployed writer opens to is `JournalOk`** (KERNEL-41), whatever base file and
segment bytes the open reads. -/
theorem openWith_journalOk {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    o.opened.world.JournalOk X.env := by
  obtain ⟨b, _n, _d, rs, hb, hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file I S h
  obtain ⟨r, _, _, hd, _⟩ := Base.read_decode keys c world file hb
  simp only [Codec.Stream.decode] at hd
  split at hd
  · rename_i v j hget
    split at hd
    · cases hd
      obtain ⟨x, hx, hacc⟩ := Codec.Stream.refine_get_inner hget
      obtain ⟨_j, hw⟩ := Codec.Stream.product_get_fst hx
      obtain ⟨xw, xo, xt, xio, xit⟩ := x
      simp only [Option.some.injEq] at hacc
      subst hacc
      exact Record.foldlM_journalOk (Codec.Deployed.world_get_journalOk hw) hf
    · cases hd
  · cases hd

/-- A World `host genesis` makes starts at the genesis chain of its origin. -/
theorem genesis_chain_eq (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    (Receive.genesisWorld X name nonce allowance founders).chain =
      World.genesisChain X.env (Receive.genesisWorld X name nonce allowance founders).origin :=
  Receive.genesis_chain X name nonce allowance founders

/-- A World `host import` makes starts at the genesis chain of its NEW origin (KERNEL's
`carryWorld`), not at the exported World's chain. -/
theorem importWorld_chain_eq {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) :
    w₀.chain = World.genesisChain X.env w₀.origin := by
  obtain ⟨_, hw⟩ := Carry.importWorld_ok h
  obtain ⟨_, rfl⟩ := Receive.carry_ok.mp hw
  rfl

/-- The deployed `originChain` is the chain `recorder.mark` writes, for a World at the genesis
chain of its origin. -/
theorem originChain_mark {w : World D} (hc : w.chain = World.genesisChain X.env w.origin) :
    originChain w = (recorder.mark w).2 := by
  simp only [originChain, recorder, hc]

/-- **The deployed open of what deployed genesis writes is the World genesis was given** (one
start path, `genesisImage_opens` at the deployed instance). Premises: `hfit`, the deployed World
codec reads `w₀` back (`Codec.Kernel.world_lawfulOn` over `digestCodec_lawful.on`, whose digest
predicate is `fun _ => True`); `hc`, `w₀`'s chain is the genesis chain of its origin
(`genesis_chain_eq`, `importWorld_chain_eq`). -/
theorem genesisImage_opens_deployed (keys : Keys) {w₀ : World D}
    (hfit : Codec.Kernel.World.CodecFits X.env (fun _ => True) w₀)
    (hc : w₀.chain = World.genesisChain X.env w₀.origin) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    ∃ o, Id.run (openWith keys c world recorder.mark originChain foldStep img.base img.segment.size
        img.index.size (segReader img.index) (segReader img.segment)) = .ok o ∧
      o.opened.world = w₀ ∧ o.opened.records = 0 ∧ o.opened.torn = 0 ∧
        o.pos.offset = img.segment.size :=
  genesisImage_opens keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on) hfit h
    (by show w₀.chain.bytes.size ≤ chainBytesMax
        rw [Digest.size_eq]; decide)
    (originChain_mark hc)
    (by decide)

/-- Inserting `ps` lists at most `ps.length` more entries. -/
theorem insertAll_length {E : Env D} :
    ∀ {m : Cells D} (ps : List (D × Kernel.Entry)), Trie.Routed (trieSpec E) 0 m →
      (insertAll E m ps).toList.length ≤ m.toList.length + ps.length
  | _, [], _ => by simp [insertAll]
  | m, p :: rest, h => by
    have hr := Trie.routed_insert (trieSpec E) (.cell p.1) (.entry p.2) h
    have ih := insertAll_length (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest hr
    have hp := (Trie.toList_insert_perm (trieSpec E) h (.cell p.1) (.entry p.2)).length_eq
    have hf := List.length_filter_le (fun q : Slot D × Leaf => decide (q.1 ≠ Slot.cell p.1)) m.toList
    simp only [List.length_append, List.length_singleton] at hp
    show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).toList.length ≤ _
    simp only [List.length_cons]
    omega

/-- A genesis World's founders: two entries each. -/
theorem founderEntries_length (o : D) (founders : List (ByteArray × D)) :
    (founderEntries X o founders).length = 2 * founders.length := by
  simp [founderEntries, List.length_flatMap, List.map_const', List.sum_replicate_nat, List.length_zipIdx, Nat.mul_comm]

/-- **The World `host genesis` makes is in the deployed World codec's domain**: its cells trie is
canonical (`insertAll_canon`), every slot holds the leaf of its kind (`insertAll_fits`), every live
cell fits the cell codec (KERNEL's `genesis_cellsFit`), it lists two entries per founder (within
`worldMax`), its journal is empty, and its allowance is below 2^64 (`GenesisFits`). -/
theorem genesisWorld_codecFits {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} (hf : Receive.GenesisFits X name nonce allowance founders) :
    Codec.Kernel.World.CodecFits X.env (fun _ => True)
      (Receive.genesisWorld X name nonce allowance founders) := by
  have hcanon : Trie.Canon (trieSpec X.env) 0 (Receive.genesisWorld X name nonce allowance founders).trie :=
    insertAll_canon _ (genesis_canon X.env _ allowance)
  have hslot : (Receive.genesisWorld X name nonce allowance founders).Slotted X.env :=
    insertAll_fits _ (genesis_slotted X.env _ allowance)
  have hcf := genesis_cellsFit hf (fun d => by
    show d.bytes.size ≤ Bounds.valueBytesMax
    rw [Digest.size_eq]; decide)
  have hlen := insertAll_length (E := X.env) (m := .empty)
    (founderEntries X (originOf X name nonce allowance founders) founders) (Trie.canon_empty _ 0).1
  rw [founderEntries_length] at hlen
  have hfl := hf.2.2.2.1
  have hmem : ∀ p ∈ (Receive.genesisWorld X name nonce allowance founders).trie.toList,
      (Receive.genesisWorld X name nonce allowance founders).trie.get (trieSpec X.env) p.1 = some p.2 :=
    fun p hp => (Trie.mem_toList (trieSpec X.env) 0 _ hcanon.1 p.1 p.2).mp hp
  refine ⟨⟨⟨⟨?_, fun p hp => ⟨trivial, ?_⟩⟩, fun p hp => hslot _ _ (hmem p hp)⟩, hcanon⟩,
    ⟨⟨by simp [Receive.genesisWorld, World.genesis, Trie.T.toList], by simp [Receive.genesisWorld, World.genesis, Trie.T.toList]⟩,
      Trie.canon_empty _ 0⟩,
    by simp [Receive.genesisWorld, World.genesis], trivial, hf.2.2.1, trivial,
    journalFits_of_ok (genesisWorld_journalOk X name nonce allowance founders)⟩
  · have : (Trie.T.empty : Cells D).toList.length = 0 := rfl
    show (insertAll X.env .empty _).toList.length ≤ Codec.Kernel.worldMax
    unfold Codec.Kernel.worldMax Bounds.eventBytesMax at *
    omega
  · have hl := hcf _ _ (hmem p hp)
    obtain ⟨s, l⟩ := p
    cases l with
    | entry e =>
      cases e with
      | live c => exact hl
      | tomb => trivial
    | spent => trivial

/-- **`host genesis`'s Store reopens to the World genesis made** (one start path), with no premise
beyond the two successes: KERNEL's genesis, and the genesis image (which refuses only
`worldTooLarge`). -/
theorem genesis_reopens (keys : Keys) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    ∃ o, Id.run (openWith keys c world recorder.mark originChain foldStep img.base img.segment.size
        img.index.size (segReader img.index) (segReader img.segment)) = .ok o ∧
      o.opened.world = w₀ ∧ o.opened.records = 0 ∧ o.opened.torn = 0 ∧
        o.pos.offset = img.segment.size := by
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  exact genesisImage_opens_deployed keys (genesisWorld_codecFits hf)
    (genesis_chain_eq name nonce allowance founders) h

/-- What a carried file reads back to is in the carried codec's domain. -/
theorem read_carried_fits {want : Codec.Digest} {f : ByteArray} {r : Carry.Read D}
    (h : Carry.read X.env Codec.Deployed.digestCodec want f = .ok r) :
    Codec.Kernel.Carried.CodecFits X.env (fun _ => True) r.carried := by
  unfold Carry.read at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i cr hcr
  split at h
  · cases h
  cases h
  exact ((Codec.Kernel.carried_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on).eq_bytes_of_decode hcr).1

/-- **The World `host import` makes is in the deployed World codec's domain**: its trie, journal
(canonical, and the window of its carried height: CODEC-31's `kernel/carried-journal`, which
HOST-39's proof found missing), height and allowance are the carried state's (`read_carried_fits`),
the chain and origin are digests. -/
theorem importWorld_codecFits {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) :
    Codec.Kernel.World.CodecFits X.env (fun _ => True) w₀ := by
  obtain ⟨hr, hw⟩ := Carry.importWorld_ok h
  obtain ⟨_, rfl⟩ := Receive.carry_ok.mp hw
  have hfit := read_carried_fits hr
  exact ⟨hfit.1, hfit.2.2.2.1, hfit.2.2.1, trivial, hfit.2.1, trivial, hfit.2.2.2.2⟩

/-- **`host import`'s Store reopens to the World the import made, holding exactly the file's
carried bytes**: so `importWith`'s `carryMismatch reopen` compare passes whenever genesis writes
the image. No premise beyond the two successes. -/
theorem import_reopens (keys : Keys) {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) {img : Image}
    (hg : genesisImage keys c world recorder.mark w₀ = .ok img) :
    ∃ o, Id.run (openWith keys c world recorder.mark originChain foldStep img.base img.segment.size
        img.index.size (segReader img.index) (segReader img.segment)) = .ok o ∧
      o.opened.world = w₀ ∧ o.opened.records = 0 ∧ o.opened.torn = 0 ∧
        o.pos.offset = img.segment.size ∧
      (Codec.Kernel.carried X.env Codec.Deployed.digestCodec).bytes o.opened.world.carried =
        f.extract r.carriedAt f.size := by
  obtain ⟨o, ho, hw, hn, ht, hp⟩ :=
    genesisImage_opens_deployed keys (importWorld_codecFits h) (importWorld_chain_eq h) hg
  refine ⟨o, ho, hw, hn, ht, hp, ?_⟩
  rw [hw]
  exact (import_carried h).2.1

/-! ## What admission keeps of the World codec's domain (HOST-28) -/

/-- The parts of `World.CodecFits` every admission keeps: a canonical cells trie whose slots hold
the leaves of their kinds and whose live cells fit the cell codec, a `JournalOk` journal, and a
height below 2^64. The two it does not keep are the cell listing's length and the allowance. -/
def Kept (w : World D) : Prop :=
  w.Canon X.env ∧ w.Slotted X.env ∧ w.CellsFit Codec.Kernel.Cell.Fits X.env ∧ w.JournalOk X.env ∧ w.height < 2 ^ 64

theorem kept_admit {w w' : World D} {t : Turn D} (hk : Kept w) (h : World.admit X.env w t = .ok w') :
    Kept w' :=
  ⟨admit_canon hk.1 h, admit_slotted hk.2.1 h, admit_cellsFit hk.2.2.1 h, admit_journalOk hk.2.2.2.1 h,
    admit_height_lt h⟩

theorem kept_fold : ∀ {w w' : World D} {l : List (Turn D)}, Kept w → World.fold X.env w l = .ok w' → Kept w'
  | w, w', [], hk, h => by simp [World.fold] at h; subst h; exact hk
  | w, w', t :: rest, hk, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact kept_fold (kept_admit hk h₁) h₂

/-- The deployed reopen's fold over records keeps `Kept` (`Record.step_rooted`, `RootedFold.fold`). -/
theorem Record.foldlM_kept : ∀ {w w' : World D} {rs : List ByteArray}, Kept w → rs.foldlM foldStep w = .ok w' → Kept w'
  | w, w', [], hk, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hk
  | w, w', r :: rs, hk, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨_, _, hr⟩ := Record.step_rooted h₁
      exact Record.foldlM_kept (kept_fold hk (RootedFold.fold hr)) h

/-- A World in the World codec's domain is `Kept`. -/
theorem kept_of_fits {w : World D} (hf : Codec.Kernel.World.CodecFits X.env (fun _ => True) w) : Kept w := by
  refine ⟨hf.1.2, fun s l hg => hf.1.1.2 (s, l) ((Trie.mem_toList (trieSpec X.env) 0 w.trie hf.1.2.1 s l).mpr hg),
    fun s l hg => ?_, journalOk_of_fits hf.2.1.2 hf.2.2.2.2.2.2, hf.2.2.1⟩
  have hl := (hf.1.1.1.2 (s, l) ((Trie.mem_toList (trieSpec X.env) 0 w.trie hf.1.2.1 s l).mpr hg)).2
  cases l with
  | entry e =>
    cases e with
    | live c => exact hl
    | tomb => trivial
  | spent => trivial

/-- A `Kept` World whose cell listing is within `worldMax` and whose allowance is below 2^64 is in
the World codec's domain. -/
theorem fits_of_kept {w : World D} (hk : Kept w) (hcount : w.trie.toList.length ≤ Codec.Kernel.worldMax)
    (hallow : w.allowance < 2 ^ 64) : Codec.Kernel.World.CodecFits X.env (fun _ => True) w := by
  have hmem : ∀ p ∈ w.trie.toList, w.trie.get (trieSpec X.env) p.1 = some p.2 :=
    fun p hp => (Trie.mem_toList (trieSpec X.env) 0 _ hk.1.1 p.1 p.2).mp hp
  have hj := journal_bounded hk.2.2.2.1
  refine ⟨⟨⟨⟨hcount, fun p hp => ⟨trivial, ?_⟩⟩, fun p hp => hk.2.1 _ _ (hmem p hp)⟩, hk.1⟩,
    ⟨⟨by unfold Bounds.journalMax; omega, fun p hp => ⟨trivial, ?_, trivial⟩⟩, hk.2.2.2.1.1⟩,
    hk.2.2.2.2, trivial, hallow, trivial, journalFits_of_ok hk.2.2.2.1⟩
  · have hl := hk.2.2.1 _ _ (hmem p hp)
    obtain ⟨s, l⟩ := p
    cases l with
    | entry e =>
      cases e with
      | live c => exact hl
      | tomb => trivial
    | spent => trivial
  · have := (hk.2.2.2.1.2.1 p.1 p.2 (journalAt_of_mem hk.2.2.2.1.1 hp)).1
    have := hk.2.2.2.2
    omega

/-- The base World of a deployed open is `Kept`, and so is the World it opens to. -/
theorem openWith_kept {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    ∃ (b : Base (World D)) (n : Nat) (d : ByteArray) (rs : List ByteArray),
      Base.read keys c world file = .ok (b, n, d) ∧ Kept b.world ∧
        rs.foldlM foldStep b.world = .ok o.opened.world ∧ Kept o.opened.world := by
  obtain ⟨b, n, d, rs, hb, hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file I S h
  obtain ⟨r, _, _, hd, _⟩ := Base.read_decode keys c world file hb
  simp only [Codec.Stream.decode] at hd
  split at hd
  · rename_i v j hget
    split at hd
    · cases hd
      obtain ⟨x, hx, hacc⟩ := Codec.Stream.refine_get_inner hget
      obtain ⟨_j, hw⟩ := Codec.Stream.product_get_fst hx
      obtain ⟨xw, xo, xt, xio, xit⟩ := x
      simp only [Option.some.injEq] at hacc
      subst hacc
      have hw2 : (Codec.Kernel.world Codec.Deployed.env Codec.Deployed.digestCodec).get _ _ = .ok (xw, _j) := hw
      have hfits : Codec.Kernel.World.CodecFits Codec.Deployed.env (fun _ => True) xw :=
        Codec.Kernel.world_get_fits (E := Codec.Deployed.env) (dc := Codec.Deployed.digestCodec)
          Codec.Deployed.digestCodec_lawful.on hw2
      have hk := kept_of_fits hfits
      exact ⟨_, n, d, rs, hb, hk, hf, Record.foldlM_kept hk hf⟩
    · cases hd
  · cases hd

/-! ## The cell listing of an opened World (HOST-40) -/

theorem foldl_add_eq {β : Type} (f : β → Nat) : ∀ (l : List β) (a : Nat),
    l.foldl (fun n x => n + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq f l, List.map_cons, List.sum_cons]; omega

theorem sum_map_ge {β : Type} (f : β → Nat) (k : Nat) (hf : ∀ x, k ≤ f x) :
    ∀ l : List β, k * l.length ≤ (l.map f).sum
  | [] => by simp
  | x :: l => by
    have := sum_map_ge f k hf l
    have := hf x
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem sum_map_le {β : Type} (f g : β → Nat) (hf : ∀ x, f x ≤ g x) :
    ∀ l : List β, (l.map f).sum ≤ (l.map g).sum
  | [] => by simp
  | x :: l => by
    have := sum_map_le f g hf l
    have := hf x
    simp only [List.map_cons, List.sum_cons]
    omega

/-- One entry of the cells listing is at least 33 bytes: the slot's kind byte and its 32-byte id. -/
theorem listing_entry_size (x : Slot D × Leaf) :
    33 ≤ (Codec.Stream.product (Codec.Kernel.slot Codec.Deployed.digestCodec) Codec.Kernel.leaf).size x := by
  obtain ⟨s, l⟩ := x
  cases s <;>
    simp [Codec.Stream.product, Codec.Kernel.slot, Codec.Stream.refine, Codec.Stream.choice,
      Codec.Stream.tagged, Codec.Stream.digest]

/-- (i) **The World's bytes are at least 33 per listed leaf.** -/
theorem world_size_listing (w : World D) : 33 * w.trie.toList.length ≤ world.size w := by
  have h1 : (Codec.Kernel.cells Codec.Deployed.env Codec.Deployed.digestCodec).size w.trie ≤ world.size w := by
    show _ ≤ (Codec.Kernel.cells Codec.Deployed.env Codec.Deployed.digestCodec).size w.trie + _
    exact Nat.le_add_right _ _
  have h2 : (Codec.Kernel.cells Codec.Deployed.env Codec.Deployed.digestCodec).size w.trie =
      w.trie.toList.foldl (fun n x => n + (Codec.Stream.product (Codec.Kernel.slot Codec.Deployed.digestCodec)
        Codec.Kernel.leaf).size x) 4 := rfl
  rw [h2, foldl_add_eq] at h1
  have := sum_map_ge _ 33 listing_entry_size w.trie.toList
  omega

theorem spendAll_length {E : Env D} :
    ∀ {m : Cells D} (ns : List D), Trie.Routed (trieSpec E) 0 m →
      (spendAll E m ns).toList.length ≤ m.toList.length + ns.length
  | _, [], _ => by simp [spendAll]
  | m, n :: rest, h => by
    have hr := Trie.routed_insert (trieSpec E) (.nullifier n) .spent h
    have ih := spendAll_length (m := m.insert (trieSpec E) (.nullifier n) .spent) rest hr
    have hp := (Trie.toList_insert_perm (trieSpec E) h (.nullifier n) .spent).length_eq
    have hf := List.length_filter_le (fun q : Slot D × Leaf => decide (q.1 ≠ Slot.nullifier n)) m.toList
    simp only [List.length_append, List.length_singleton] at hp
    show (spendAll E (m.insert (trieSpec E) (.nullifier n) .spent) rest).toList.length ≤ _
    simp only [List.length_cons]
    omega

theorem mapEx_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, mapEx f l = .ok r → r.length = l.length
  | [], r, h => by simp [mapEx] at h; subst h; rfl
  | a :: rest, r, h => by
    unfold mapEx at h
    split at h
    · split at h
      · rename_i bs hbs
        cases h
        simp [mapEx_length hbs]
      · cases h
    · cases h

/-- (ii) **An admission adds at most one leaf per touch, created cell and nullifier**, and each of
those costs at least 32 bytes of the Turn's log weight. -/
theorem admit_listing {w w' : World D} {t : Turn D} (hc : w.Canon X.env)
    (h : World.admit X.env w t = .ok w') :
    32 * w'.trie.toList.length ≤ 32 * w.trie.toList.length + t.logWeight := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hp⟩ := hk.touches
  have hpl : posts.length ≤ t.touches.length := by
    rw [hp, ← mapEx_length hm]
    exact List.length_filterMap_le _ _
  have c1 := insertAll_canon (E := X.env) (posts.map Post.pair) hc
  have l1 := insertAll_length (E := X.env) (posts.map Post.pair) hc.1
  have c2 := insertAll_canon (E := X.env) (bornEntries t) c1
  have l2 := insertAll_length (E := X.env) (bornEntries t) c1.1
  have l3 := spendAll_length (E := X.env) t.nullifiers c2.1
  have ht := sum_map_ge Touch.weight 64 (fun x => by unfold Touch.weight digestWeight; omega) t.touches
  have hcr := sum_map_ge (fun p : D × Cell => digestWeight + p.2.weight) 32
    (fun p => by show 32 ≤ digestWeight + p.2.weight; unfold digestWeight; omega) t.creates
  have he : (posts.map Post.pair).length = posts.length := List.length_map _
  have hg : (bornEntries t).length = t.creates.length := by simp [bornEntries]
  show 32 * (spendAll X.env (insertAll X.env (insertAll X.env w.trie (posts.map Post.pair)) (bornEntries t))
    t.nullifiers).toList.length ≤ _
  have hlw : t.logWeight ≥ (t.touches.map Touch.weight).sum +
      (t.creates.map fun p => digestWeight + p.2.weight).sum + 32 * t.nullifiers.length := by
    unfold Turn.logWeight; simp only [show digestWeight = 32 from rfl]; omega
  omega

theorem fold_listing : ∀ {w w' : World D} {l : List (Turn D)}, w.Canon X.env → World.fold X.env w l = .ok w' →
    32 * w'.trie.toList.length ≤ 32 * w.trie.toList.length + (l.map Turn.logWeight).sum
  | w, w', [], _, h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, hc, h => by
    obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
    have a := admit_listing hc h₁
    have b := fold_listing (admit_canon hc h₁) h₂
    simp only [List.map_cons, List.sum_cons]
    omega

/-- (iii) **A record's bytes are at least the log weight of its Turns** (`turn_size_logWeight`). -/
theorem record_turns_le {r : ByteArray} {ps : List (Turn D × (D × D))}
    (h : (Record.codec Codec.Deployed.digestCodec).decode r = .ok ps) :
    ((ps.map Prod.fst).map Turn.logWeight).sum ≤ r.size := by
  have hl := Codec.Kernel.batch_lawfulOn Codec.Deployed.digestCodec_lawful.on recordTurnsMax (by decide)
  have hb := (hl.eq_bytes_of_decode h).2
  have hs : r.size = (Codec.Kernel.batch recordTurnsMax Codec.Deployed.digestCodec).size ps := by
    rw [hb, ← hl.size_eq]
  have e : (Codec.Kernel.batch recordTurnsMax Codec.Deployed.digestCodec).size ps =
      ps.foldl (fun n x => n + (Codec.Stream.product (Codec.Kernel.turn Codec.Deployed.digestCodec)
        (Codec.Stream.product Codec.Deployed.digestCodec Codec.Deployed.digestCodec)).size x) 4 := rfl
  rw [hs, e, foldl_add_eq, List.map_map]
  have hle := sum_map_le (Turn.logWeight ∘ Prod.fst)
    (Codec.Stream.product (Codec.Kernel.turn Codec.Deployed.digestCodec)
        (Codec.Stream.product Codec.Deployed.digestCodec Codec.Deployed.digestCodec)).size
    (fun x => by
      show x.1.logWeight ≤ (Codec.Kernel.turn Codec.Deployed.digestCodec).size x.1 + _
      rw [Codec.Kernel.turn_size_logWeight (fun _ => rfl)]
      exact Nat.le_add_right _ _) ps
  omega

theorem Record.foldlM_listing : ∀ {w w' : World D} {rs : List ByteArray}, w.Canon X.env →
    rs.foldlM foldStep w = .ok w' →
      32 * w'.trie.toList.length ≤ 32 * w.trie.toList.length + (rs.map ByteArray.size).sum
  | w, w', [], _, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | w, w', r :: rs, hc, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨ps, hd, hr⟩ := Record.step_rooted h₁
      have hf := RootedFold.fold hr
      have a := fold_listing hc hf
      have b := record_turns_le hd
      have ih := Record.foldlM_listing (fold_canon hc hf) h
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **Every World the deployed open returns lists fewer than 2^24 leaves.** The base World is at
most `c.baseRecordMax` bytes, 33 per leaf (`world_size_listing`); the tail `tailRead` admits is at
most `c.tailMax` of it, and every leaf a record's Turns add costs 32 of its bytes
(`admit_listing`, `record_turns_le`). -/
theorem openWith_listing_lt {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    o.opened.world.trie.toList.length < 2 ^ 24 := by
  obtain ⟨b, n, d, rs, hb, hf, _, _, _, he⟩ :=
    openWith_world keys c world recorder.mark originChain foldStep file I S h
  obtain ⟨b', n', d', len, _, _, hb', hlen, -⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep file I S h
  rw [hb] at hb'
  cases hb'
  obtain ⟨hs, hle⟩ := tailRead_ok hlen
  have hsz := congrArg ByteArray.size he
  rw [size_encodeAll_sum, ByteArray.size_extract, ByteArray.size_extract] at hsz
  have hrs := sum_map_le ByteArray.size frameSize (fun r => by unfold frameSize; omega) rs
  obtain ⟨r, hr, _, hd, hn⟩ := Base.read_decode keys c world file hb
  have hrec := (frameAt_record_size hr).1
  have hbl := Base.codec_lawfulOn (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
  have hbase := (hbl.eq_bytes_of_decode hd).2
  have hbs : (r.record.extract stampBytes r.record.size).size = (Base.codec world).size b := by
    rw [hbase]; exact (hbl.size_eq b).symm
  rw [ByteArray.size_extract, Nat.min_self] at hbs
  have hcs : (Base.codec world).size b = world.size b.world + (8 + (32 + (8 + 32))) := rfl
  have htail : (rs.map frameSize).sum ≤ len := by
    rw [← hsz, Nat.min_self]; omega
  obtain ⟨b₂, n₂, d₂, rs₂, hb₂, hk, hf₂, -⟩ := openWith_kept h
  rw [hb] at hb₂
  cases hb₂
  have hl := Record.foldlM_listing hk.1 hf
  have hw := world_size_listing b.world
  have e1 : c.baseRecordMax = 268435568 := rfl
  have e2 : c.tailMax n = 2 * max 1048576 (n / 4) + (4 + 33554432 + 32) := rfl
  have hm : max 1048576 (n / 4) ≤ 1048576 + n / 4 :=
    Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  unfold stampBytes at hbs
  omega

/-- **`host export` refuses no World the deployed open returns whose allowance is below 2^64**
(HOST-28's completeness, short of `hallow`). Every part of the carried codec's domain but the
allowance is proved: the base World's, read by the World codec, kept by every admission (`Kept`),
and the cell listing below 2^24 leaves (`openWith_listing_lt`). `hallow` is the ONE named premise
and waits on cv 01a14ba9-cbf4: KERNEL's `GenesisFits` / `CarryFits` / `World.CodecFits` must bound
weight + allowance below 2^64, which admission conserves. Without it the premise is reachable
through `host import`: a carried allowance of 2^64 − 1 and a light Turn that retires a heavy cell. -/
theorem openWith_exportFile_ok {keys : Keys} {file I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hallow : o.opened.world.allowance < 2 ^ 64) :
    Carry.exportFile X.env Codec.Deployed.digestCodec o.opened.world =
      .ok (Carry.file X.env Codec.Deployed.digestCodec o.opened.world) := by
  obtain ⟨_, _, _, _, _, _, _, hk⟩ := openWith_kept h
  have hcount : o.opened.world.trie.toList.length ≤ Codec.Kernel.worldMax := by
    have := openWith_listing_lt h
    unfold Codec.Kernel.worldMax
    omega
  have hf := fits_of_kept hk hcount hallow
  exact Carry.exportFile_ok Codec.Deployed.digestCodec_lawful.on (Codec.Kernel.carried_fits hf) trivial trivial
    hf.2.2.1

end Nanodregg.Host.Deployed
