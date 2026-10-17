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

end Nanodregg.Host.Deployed
