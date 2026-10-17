/-
# Kernel.Proofs.RootedDeployed — the rooted-World theorems with their premises discharged

`Kernel.Proofs.Rooted` assumes the digest's bytes are injective and its decoder canonical. CODEC
proves both for the deployed digest (`Codec.Proofs.Deployed`), so under the deployed `Ctx`: every
World an audited log reaches from a founders' genesis is rooted, and every enrolment admitted on
it acts for a founder through that founder's own genesis grant. And the phone's reads
(`Kernel.Proofs.Cells`) hold at the deployed codec for every World a checked genesis and a fold
reach (`deployed_reach`): `deployed_slot_inclusion_sound`, `deployed_live_inclusion_sound`,
`deployed_head_read_sound` (KERNEL-31).
-/
import Kernel.Proofs.Rooted
import Kernel.Proofs.Fold
import Kernel.Proofs.CellsFit
import Codec.Proofs.Deployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: an audited World is rooted at its founders.** -/
theorem deployed_audit_rooted (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) {w' : World Digest} {l : List (Turn Digest)}
    (h : audit (ctx program) (genesisWorld (ctx program) name nonce allowance founders) l = .ok w') :
    WorldRooted (ctx program) (GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders)) w' :=
  audit_rooted (fun _ _ hb => bytes_injective hb) (genesis_rooted _ name nonce allowance founders) h

/-- **Deployed: every enrolment is a founder's.** On a World an audited log reached from genesis,
a derived enrolment's grant chain ends at a founder's live genesis grant, issued by the founder the
chain acts for. -/
theorem deployed_enroll_founder (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) {w : World Digest} {l : List (Turn Digest)}
    (hw : audit (ctx program) (genesisWorld (ctx program) name nonce allowance founders) l = .ok w)
    {c : Call Digest} {key : ByteArray} {next : Digest} {possession : ByteArray} {via : Digest}
    {base : Nat} {d : Draft Digest}
    (h : enroll (ctx program) (pinned (ctx program).env w c.unsigned.pins) c ⟨c.unsigned.member, base⟩ key next possession via
      = .ok d) :
    ∃ p r cell, GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders) r ∧ w.live (ctx program).env r = some cell ∧
      slotDigest (ctx program) r cell grantIssuer = .ok p ∧
      Chain (ctx program) (pinned (ctx program).env w c.unsigned.pins) (worldId (ctx program)) (.enroll 0) true via
        c.unsigned.member p := by
  obtain ⟨⟨p, hc⟩, _⟩ := enroll_authorized h
  have hlook : ∀ x v, pinned (ctx program).env w c.unsigned.pins x = .ok v → v = w.live (ctx program).env x := by
    intro x v hx
    unfold pinned at hx
    split at hx
    · simp only [Except.ok.injEq] at hx; exact hx.symm
    · simp at hx
  obtain ⟨r, cell, hr, hl, hi⟩ := chain_rooted (deployed_audit_rooted program name nonce allowance founders hw)
    hlook (fun _ _ hd => (bytes_of_digestOf hd).symm) hc
  exact ⟨p, r, cell, hr, hl, hi, hc⟩

/-- **Deployed: a follower at the host's head holds the host's World.** `fold_reaches_host` with
every premise discharged at the deployed codec: 32-byte digests, injective digest bytes, and turn
bytes injective on bounded turns (CODEC's `turnBytes_injective`; every admitted turn is bounded). -/
theorem deployed_fold_reaches_host {g host follower : World Digest} {lh lf : List (Turn Digest)}
    (hh : World.fold env g lh = .ok host) (hf : World.fold env g lf = .ok follower)
    (hht : follower.height = host.height) (hc : follower.chain = host.chain) :
    follower = host ∨ Collision env.hash :=
  fold_reaches_host (n := 32) (fun d => d.size_eq) (fun _ _ h => bytes_injective h)
    (fun ht ht' h => turnBytes_injective ht ht' h) hh hf hht hc

/-! ## The phone's reads at the deployed codec (KERNEL-31) -/

/-- The deployed cell codec is injective on exactly the cells the kernel keeps (`Cell.Fits`). -/
theorem deployed_injOn : InjOn Nanodregg.Codec.Kernel.Cell.Fits env :=
  fun _ _ ha hb h => Nanodregg.Codec.Kernel.cellBytes_injective ha hb h

/-- A deployed digest's bytes fit a value slot (32 bytes). -/
theorem deployed_bytes_fit (d : Digest) : (env.bytes d).size ≤ Bounds.valueBytesMax := by
  show d.bytes.size ≤ Bounds.valueBytesMax
  rw [d.size_eq]; decide

/-- **Deployed: a World a checked genesis and a fold reach is canonical, and its cells fit.** -/
theorem deployed_reach (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Turn Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w) :
    w.Canon env ∧ w.CellsFit Nanodregg.Codec.Kernel.Cell.Fits env := by
  obtain ⟨hf, rfl⟩ := genesis_ok.mp hg
  exact ⟨fold_canon (receive_genesis_canon (ctx program) name nonce allowance founders) hl,
    fold_cellsFit (genesis_cellsFit hf deployed_bytes_fit) hl⟩

/-- **Deployed: inclusion is sound** on every World a checked genesis and a fold reach. -/
theorem deployed_slot_inclusion_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Turn Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) (w.root env) s (leafDigest env leaf) p = true) :
    w.trie.get (trieSpec env) s = some leaf ∨ Collision env.hash :=
  slot_inclusion_sound (n := 32) (fun d => d.size_eq) (fun _ _ h => bytes_injective h) deployed_injOn
    (deployed_reach program hg hl).1 (deployed_reach program hg hl).2 hlf hv

/-- **Deployed: a live cell proved against the root is the World's live cell**, or a collision. -/
theorem deployed_live_inclusion_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Turn Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    {c : Digest} {cell : Cell} (hcf : Nanodregg.Codec.Kernel.Cell.Fits cell) {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) (w.root env) (.cell c) (leafDigest env (.entry (.live cell))) p = true) :
    w.live env c = some cell ∨ Collision env.hash :=
  live_inclusion_sound (n := 32) (fun d => d.size_eq) (fun _ _ h => bytes_injective h) deployed_injOn
    (deployed_reach program hg hl).1 (deployed_reach program hg hl).2 hcf hv

/-- **Deployed: the phone's read from any canonical, fitting World** (a reopened base as well as a
folded one): a head record that hashes to the chain the next admitted turn reached, and a proof
against the record's root, show a slot of that World, or a collision. -/
theorem deployed_head_read_sound_from {w w' : World Digest} {t : Turn Digest} (hc : w.Canon env)
    (hwf : w.CellsFit Nanodregg.Codec.Kernel.Cell.Fits env) (h : World.admit env w t = .ok w')
    {prev td root' : Digest}
    (hhead : env.hash domChain (env.bytes prev ++ env.bytes td ++ env.bytes root') = w'.chain)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨ Collision env.hash :=
  head_read_sound (n := 32) (fun d => d.size_eq) (fun _ _ h => bytes_injective h) deployed_injOn hc h
    (admit_cellsFit hwf h) hhead hlf hv

/-- **Deployed: the phone's read on a reopened base.** A World decoded from base bytes by the
deployed World codec, then one admitted turn: `Canon` and `CellsFit` come from the decoder
(`world_decode_canon`, `world_decode_cellsFit`), so no premise about the World is left. -/
theorem deployed_head_read_sound_decoded {b : ByteArray} {w w' : World Digest} {t : Turn Digest}
    (hd : Codec.Deployed.world.decode b = .ok w) (h : World.admit env w t = .ok w')
    {prev td root' : Digest}
    (hhead : env.hash domChain (env.bytes prev ++ env.bytes td ++ env.bytes root') = w'.chain)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨ Collision env.hash :=
  deployed_head_read_sound_from (world_decode_canon hd).1 (world_decode_cellsFit hd) h hhead hlf hv

/-- **Deployed: the phone's read.** On a World a checked genesis and a fold reach, a head record
that hashes to the chain the next admitted turn reached, and a proof that verifies against the
record's root, show a slot of the World after that turn, or a collision. Every premise of
`head_read_sound` is discharged: 32-byte injective digests, `cellBytes` injective on `Cell.Fits`,
the World canonical and fitting. -/
theorem deployed_head_read_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Turn Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td root' : Digest}
    (hhead : env.hash domChain (env.bytes prev ++ env.bytes td ++ env.bytes root') = w'.chain)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨ Collision env.hash :=
  deployed_head_read_sound_from (deployed_reach program hg hl).1 (deployed_reach program hg hl).2 h hhead hlf hv

/-- **Deployed: the phone's read over the leaf's BYTES** (CLIENT-16). The leaf the phone shows is
what CODEC's leaf decoder returns from the served bytes, so `CellFit` comes from the decoder
(`Codec.Kernel.leaf_decode_cellFit`, toothed by `leaf_decode_refuses_misfit`) and no premise about
the leaf is left: a reached World, one admitted turn, the head record, the proof. -/
theorem deployed_head_read_sound_bytes (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Turn Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td root' : Digest}
    (hhead : env.hash domChain (env.bytes prev ++ env.bytes td ++ env.bytes root') = w'.chain)
    {s : Slot Digest} {b : ByteArray} {lf : Leaf} (hd : Nanodregg.Codec.Kernel.leaf.decode b = .ok lf)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env lf) p = true) :
    w'.trie.get (trieSpec env) s = some lf ∨ Collision env.hash :=
  deployed_head_read_sound program hg hl h hhead (Nanodregg.Codec.Kernel.leaf_decode_cellFit hd).1 hv

/-- **Deployed: the phone's read over leaf bytes, on a reopened base**: the World from the base
decoder, the leaf from the leaf decoder; no premise about either. -/
theorem deployed_head_read_sound_decoded_bytes {bw : ByteArray} {w w' : World Digest} {t : Turn Digest}
    (hdw : Codec.Deployed.world.decode bw = .ok w) (h : World.admit env w t = .ok w')
    {prev td root' : Digest}
    (hhead : env.hash domChain (env.bytes prev ++ env.bytes td ++ env.bytes root') = w'.chain)
    {s : Slot Digest} {b : ByteArray} {lf : Leaf} (hd : Nanodregg.Codec.Kernel.leaf.decode b = .ok lf)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env lf) p = true) :
    w'.trie.get (trieSpec env) s = some lf ∨ Collision env.hash :=
  deployed_head_read_sound_decoded hdw h hhead (Nanodregg.Codec.Kernel.leaf_decode_cellFit hd).1 hv

end Nanodregg.Kernel.Receive
