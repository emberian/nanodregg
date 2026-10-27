/-
# Kernel.Proofs.RootedDeployed — the rooted-World theorems with their premises discharged

`Kernel.Proofs.Rooted` assumes the digest's bytes are injective and its decoder canonical. CODEC
proves both for the deployed digest (`Codec.Proofs.Deployed`), so under the deployed `Ctx`: every
World an honest folded log reaches from a founders' genesis is rooted, and every enrolment admitted on
it acts for a founder through that founder's own genesis grant. And the phone's reads
(`Kernel.Proofs.Cells`) hold at the deployed codec for every World a checked genesis and a fold
reach (`deployed_reach`): `deployed_slot_inclusion_sound`, `deployed_live_inclusion_sound`,
`deployed_head_read_sound` (KERNEL-31); and the phone's journal reads against the head's journal
root (KERNEL-41): `deployed_head_journal_read`, `deployed_head_journal_absent`,
`deployed_head_absent_admitted`, with every premise but the claimed entry's height discharged.
Each escapes only by a collision among the inputs it names (KERNEL-56: `foldPres`, `headPres`,
`inclPres`, `readPres`); teeth `deployed_*_sep`.
-/
import Kernel.Proofs.Rooted
import Kernel.Proofs.Fold
import Kernel.Proofs.CellsFit
import Kernel.Proofs.JournalHead
import Kernel.Proofs.Refusals
import Codec.Proofs.Deployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- The deployed cell codec is injective on exactly the cells the kernel keeps (`Cell.Fits`). -/
theorem deployed_injOn : InjOn Nanodregg.Codec.Kernel.Cell.Fits env :=
  fun _ _ ha hb h => Nanodregg.Codec.Kernel.cellBytes_injective ha hb h

/-- **The deployed `Env` is lawful at 32** (KERNEL-37): 32-byte digests, injective digest bytes
(`bytes_injective`), turn bytes injective on bounded turns (`turnBytes_injective`), cell bytes
injective on `Cell.Fits` (`cellBytes_injective`). Every kernel theorem stated over a lawful `Env`
holds at the deployed codec with no premise about it. -/
theorem deployed_lawful : env.Lawful 32 where
  size d := d.size_eq
  n_le := Nat.le_refl 32
  bytes_inj := fun _ _ h => bytes_injective h
  turnBytes_injOn := fun ht ht' h => turnBytes_injective ht ht' h
  cellBytes_injOn := deployed_injOn

/-- **The deployed `Ctx` is lawful**, whatever its program: the deployed digest decoder reads every
digest's 32 bytes back (`Codec.Deployed.digestOf_bytes`). -/
theorem deployed_ctx_lawful (program : Program Digest) : (ctx program).Lawful :=
  ⟨fun d => Nanodregg.Codec.Deployed.digestOf_bytes d⟩

/-- **The floor of `Separates` at the deployed width** (`separates_lawful_floor` at `deployed_lawful`):
a lawful `Env` over the deployed `Digest` at 32 separates a concrete two-input list, and another does
not. Both are the deployed codec with a toy hash; the deployed hash is never evaluated. -/
theorem separates_floor_32 :
    (∃ E : Env Digest, E.Lawful 32 ∧ Separates E.hash [("a", ByteArray.empty), ("b", ByteArray.empty)]) ∧
      ∃ E : Env Digest, E.Lawful 32 ∧ ¬ Separates E.hash [("a", ByteArray.empty), ("b", ByteArray.empty)] :=
  separates_lawful_floor deployed_lawful (a := Digest.zero)
    (b := ⟨⟨Array.replicate 32 1⟩, by simp [ByteArray.size]⟩)
    (fun h => absurd (congrArg (fun d : Digest => d.bytes.data[0]!) h) (by decide))

/-- **Deployed: an honest folded log's World is rooted at its founders.** -/
theorem deployed_honest_rooted (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) (auth : Authority) {w' : World Digest} {l : List (Step Digest)}
    (hf : World.fold (ctx program).env (genesisWorld (ctx program) name nonce allowance founders auth) l = .ok w')
    (hh : Honest (ctx program) (genesisWorld (ctx program) name nonce allowance founders auth) l) :
    WorldRooted (ctx program) (GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders auth)) w' :=
  honest_rooted deployed_lawful (genesis_rooted _ name nonce allowance founders auth) hf hh

/-- **Deployed: every enrolment is a founder's.** On a World an honest folded log reached from genesis,
a derived enrolment's grant chain ends at a founder's live genesis grant, issued by the founder the
chain acts for. -/
theorem deployed_enroll_founder (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) (auth : Authority) {w : World Digest} {l : List (Step Digest)}
    (hf : World.fold (ctx program).env (genesisWorld (ctx program) name nonce allowance founders auth) l = .ok w)
    (hh : Honest (ctx program) (genesisWorld (ctx program) name nonce allowance founders auth) l)
    {c : Call Digest} {key : ByteArray} {next origin : Digest} {join : ByteArray} {via : Digest}
    {base : Nat} {d : Draft Digest}
    (h : enroll (ctx program) (pinned (ctx program).env w c.unsigned.pins) ⟨c.unsigned.member, base⟩ key next origin join via
      = .ok d) :
    ∃ p r cell, GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders auth) r ∧ w.live (ctx program).env r = some cell ∧
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
  obtain ⟨r, cell, hr, hl, hi⟩ := chain_rooted (deployed_honest_rooted program name nonce allowance founders auth hf hh)
    hlook (fun _ _ hd => (bytes_of_digestOf hd).symm) hc
  exact ⟨p, r, cell, hr, hl, hi, hc⟩

/-- **Deployed: a follower at the host's head holds the host's World**, or two of the inputs the two
folds compare collide (`foldPres`). `fold_reaches_host` with every premise discharged at the deployed codec: 32-byte digests, injective digest bytes, and turn
bytes injective on bounded turns (CODEC's `turnBytes_injective`; every admitted turn is bounded). The
follower compares `(steps, chain)` (KERNEL-47: a recorded refusal moves the steps, not the height). -/
theorem deployed_fold_reaches_host {g host follower : World Digest} {lh lf : List (Step Digest)}
    (hh : World.fold env g lh = .ok host) (hf : World.fold env g lf = .ok follower)
    (hst : follower.steps = host.steps) (hc : follower.chain = host.chain) :
    follower = host ∨ CollidesAmong env.hash (foldPres env g lf ++ foldPres env g lh) :=
  fold_reaches_host deployed_lawful hh hf hst hc

/-! ## The phone's reads at the deployed codec (KERNEL-31) -/

/-- A deployed digest's bytes fit a value slot (32 bytes). -/
theorem deployed_bytes_fit (d : Digest) : (env.bytes d).size ≤ Bounds.valueBytesMax := by
  show d.bytes.size ≤ Bounds.valueBytesMax
  rw [d.size_eq]; decide

/-- **Deployed: a World a checked genesis and a fold reach is canonical, and its cells fit.** -/
theorem deployed_reach (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w) :
    w.Canon env ∧ w.CellsFit Nanodregg.Codec.Kernel.Cell.Fits env := by
  obtain ⟨hf, rfl⟩ := genesis_ok.mp hg
  exact ⟨fold_canon (receive_genesis_canon (ctx program) name nonce allowance founders auth) hl,
    fold_cellsFit (genesis_cellsFit hf deployed_bytes_fit) hl⟩

/-- **Deployed: inclusion is sound** on every World a checked genesis and a fold reach. -/
theorem deployed_slot_inclusion_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) (w.root env) s (leafDigest env leaf) p = true) :
    w.trie.get (trieSpec env) s = some leaf ∨
      CollidesAmong env.hash (inclPres (trieSpec env) (leafPre env) s leaf p w.trie) :=
  slot_inclusion_sound deployed_lawful (deployed_reach program hg hl).1 (deployed_reach program hg hl).2
    hlf hv

/-- **Deployed: a live cell proved against the root is the World's live cell**, or two of the
inputs it compares collide. -/
theorem deployed_live_inclusion_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    {c : Digest} {cell : Cell} {v : Nat} (hcf : (Leaf.entry (.live cell v)).CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) (w.root env) (.cell c) (leafDigest env (.entry (.live cell v))) p = true) :
    w.entry env c = some (.live cell v) ∨
      CollidesAmong env.hash (inclPres (trieSpec env) (leafPre env) (.cell c) (.entry (.live cell v)) p w.trie) :=
  live_inclusion_sound deployed_lawful (deployed_reach program hg hl).1 (deployed_reach program hg hl).2
    hcf hv

/-- **Deployed: the phone's read from any canonical, fitting World** (a reopened base as well as a
folded one): a head record that hashes to the chain the next admitted turn reached, and a proof
against the record's root, show a slot of that World, or two of the inputs it compares collide. -/
theorem deployed_head_read_sound_from {w w' : World Digest} {t : Turn Digest} (hc : w.Canon env)
    (hwf : w.CellsFit Nanodregg.Codec.Kernel.Cell.Fits env) (h : World.admit env w t = .ok w')
    {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec env) (leafPre env) s leaf p w'.trie) :=
  head_read_sound deployed_lawful (s := .turn t) hc h (admit_cellsFit hwf h) hhead hrd hlf hv

/-- **Deployed: the phone's read on a reopened base.** A World decoded from base bytes by the
deployed World codec, then one admitted turn: `Canon` and `CellsFit` come from the decoder
(`world_decode_canon`, `world_decode_cellsFit`), so no premise about the World is left. -/
theorem deployed_head_read_sound_decoded {b : ByteArray} {w w' : World Digest} {t : Turn Digest}
    (hd : Codec.Deployed.world.decode b = .ok w) (h : World.admit env w t = .ok w')
    {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec env) (leafPre env) s leaf p w'.trie) :=
  deployed_head_read_sound_from (world_decode_canon hd).1 (world_decode_cellsFit hd) h hhead hrd hlf hv

/-- **Deployed: the phone's read.** On a World a checked genesis and a fold reach, a head record
that hashes to the chain the next admitted turn reached, and a proof that verifies against the
record's root, show a slot of the World after that turn, or two of the inputs it compares collide
(`headPres`, `inclPres`). Every premise of `head_read_sound` is discharged: 32-byte injective digests, `cellBytes` injective on `Cell.Fits`,
the World canonical and fitting. -/
theorem deployed_head_read_sound (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec env) (leafPre env) s leaf p w'.trie) :=
  deployed_head_read_sound_from (deployed_reach program hg hl).1 (deployed_reach program hg hl).2 h hhead hrd hlf hv

/-- **Deployed: the phone's read over the leaf's BYTES** (CLIENT-16). The leaf the phone shows is
what CODEC's leaf decoder returns from the served bytes, so `CellFit` comes from the decoder
(`Codec.Kernel.leaf_decode_cellFit`, toothed by `leaf_decode_refuses_misfit`) and no premise about
the leaf is left: a reached World, one admitted turn, the head record, the proof. -/
theorem deployed_head_read_sound_bytes (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {b : ByteArray} {lf : Leaf} (hd : Nanodregg.Codec.Kernel.leaf.decode b = .ok lf)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env lf) p = true) :
    w'.trie.get (trieSpec env) s = some lf ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec env) (leafPre env) s lf p w'.trie) :=
  deployed_head_read_sound program hg hl h hhead hrd (Nanodregg.Codec.Kernel.leaf_decode_cellFit hd).1 hv

/-- **Deployed: the phone's read over leaf bytes, on a reopened base**: the World from the base
decoder, the leaf from the leaf decoder; no premise about either. -/
theorem deployed_head_read_sound_decoded_bytes {bw : ByteArray} {w w' : World Digest} {t : Turn Digest}
    (hdw : Codec.Deployed.world.decode bw = .ok w) (h : World.admit env w t = .ok w')
    {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {b : ByteArray} {lf : Leaf} (hd : Nanodregg.Codec.Kernel.leaf.decode b = .ok lf)
    {p : Trie.Proof (Slot Digest) Digest}
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env lf) p = true) :
    w'.trie.get (trieSpec env) s = some lf ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec env) (leafPre env) s lf p w'.trie) :=
  deployed_head_read_sound_decoded hdw h hhead hrd (Nanodregg.Codec.Kernel.leaf_decode_cellFit hd).1 hv

/-- Every World a checked genesis and a fold reach holds `JournalOk` at the deployed codec. -/
theorem deployed_reach_journalOk (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w) :
    w.JournalOk env := by
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact reach_journalOk (X := ctx program) hl

/-- **Deployed: the phone's journal read.** On a World a checked genesis and a fold reach, a head
record that hashes to the chain the next admitted turn reached, and an inclusion proof against the
record's journal root, show the entry in that World's journal, or two of the inputs it compares collide.
The one premise left is the claimed entry's: its height is below 2^64 (a `u64` on the wire). -/
theorem deployed_head_journal_read (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : Digest} {e : Nat × Digest}
    (he : e.1 < 2 ^ 64) {p : Trie.Proof Digest Digest}
    (hv : Trie.verifyInclusion (journalSpec env) jroot' k (journalDigest env e) p = true) :
    w'.journalAt env k = some e ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (journalSpec env) (journalPre env) k e p w'.journal) :=
  head_journal_read deployed_lawful (by decide) (deployed_reach_journalOk program hg hl) h hhead hrd he hv

/-- **Deployed: the phone's journal absence**, no premise: the id is not in the journal of the World
after the turn, or two of the inputs it compares collide. -/
theorem deployed_head_journal_absent (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : Digest} {p : Trie.Proof Digest Digest}
    (hv : Trie.verifyExclusion (journalSpec env) jroot' k p = true) :
    w'.journalAt env k = none ∨
      CollidesAmong env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
        readPres (journalSpec env) k p w'.journal) :=
  head_journal_absent deployed_lawful (by decide) (deployed_reach_journalOk program hg hl).1 h hhead hrd hv

/-- **Deployed: while `journalForgets` is false, an admitted turn cannot be shown absent**, no
premise: a turn admitted on a reached World, and any World its log reaches below
`notBefore + 2 * windowMax`, admit no exclusion proof of the turn's transaction id against that
World's head but by a collision among the inputs the opening and the read compare. -/
theorem deployed_head_absent_admitted (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w₀ w₁ w₂ : World Digest} {l₀ l : List (Step Digest)}
    {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (h₀ : World.fold env g l₀ = .ok w₀)
    (h₁ : World.admit env w₀ t = .ok w₁) (hf : World.fold env w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w₂.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {p : Trie.Proof Digest Digest}
    (hv : Trie.verifyExclusion (journalSpec env) jroot' t.txId p = true):
    CollidesAmong env.hash (headPres env w₀ (.turn t :: l) w₂ prev tag td rd root' jroot' rroot' wroot' ++
      readPres (journalSpec env) t.txId p w₂.journal) :=
  head_absent_admitted deployed_lawful (by decide) (deployed_reach_journalOk program hg h₀).1 h₁ hf hnf hhead hrd hv

/-! ## Recorded refusals at the deployed codec (KERNEL-44, KERNEL-47) -/

/-- **Deployed: every World a checked genesis and a fold reach holds `RefusalsOk`**, no premise: a
canonical refusals trie whose every leaf fits its height (with `fold_member_refusals_le`, no log
records more than `Bounds.refusalsPerWindow` refusals of a member in a window). -/
theorem deployed_reach_refusalsOk (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w) :
    w.RefusalsOk env := by
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact fold_refusalsOk (genesisWorld_refusalsOk (ctx program) name nonce allowance founders auth) hl

/-- **Deployed: a recorded refusal is final**, no premise but the height: on a World a checked
genesis and a fold reach, after `judge` recorded call `c`'s refusal, every World a later log reaches
below the prune height answers `c` `refusedFinal` with the recorded code (the A→B→A defect closed). -/
theorem deployed_judge_recorded_final (program : Program Digest) {name nonce : ByteArray}
    {allowance : Nat} {founders : List (ByteArray × Digest)} {auth : Authority} {g w₀ w₁ w₂ : World Digest}
    {l₀ l : List (Step Digest)} {c : Call Digest} {v : Verdict Digest} {r : Refused Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (h₀ : World.fold env g l₀ = .ok w₀)
    (hj : judge (ctx program) w₀ c = .recorded v r w₁) (hf : World.fold env w₁ l = .ok w₂)
    (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax) :
    submit (ctx program) w₂ c = .error (.rejected (.refusedFinal v.code)) :=
  judge_recorded_final (deployed_reach_refusalsOk program hg h₀).1 (deployed_reach_journalOk program hg h₀).1 hj hf hlt

/-! ## Teeth at the deployed codec: under `Separates` of the inputs each theorem names, its binding
fact alone (every other deployed theorem's tooth is its generic one's: `head_read_sound_sep`,
`journal_*_sep`, `HeadSound.*_sep`) -/

/-- TOOTH (`deployed_fold_reaches_host`). -/
theorem deployed_fold_reaches_host_sep {g host follower : World Digest} {lh lf : List (Step Digest)}
    (hh : World.fold env g lh = .ok host) (hf : World.fold env g lf = .ok follower)
    (hst : follower.steps = host.steps) (hc : follower.chain = host.chain)
    (hsep : Separates env.hash (foldPres env g lf ++ foldPres env g lh)) : follower = host :=
  hsep.elim (deployed_fold_reaches_host hh hf hst hc)

/-- TOOTH (`deployed_head_read_sound`). -/
theorem deployed_head_read_sound_sep (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd)
    {s : Slot Digest} {leaf : Leaf} (hlf : leaf.CellFit Nanodregg.Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot Digest) Digest}
    (hsep : Separates env.hash (headPres env w [.turn t] w' prev tag td rd root' jroot' rroot' wroot' ++
      inclPres (trieSpec env) (leafPre env) s leaf p w'.trie))
    (hv : Trie.verifyInclusion (trieSpec env) root' s (leafDigest env leaf) p = true) :
    w'.trie.get (trieSpec env) s = some leaf :=
  hsep.elim (deployed_head_read_sound program hg hl h hhead hrd hlf hv)

/-- TOOTH (`deployed_head_absent_admitted`). -/
theorem deployed_head_absent_admitted_sep (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w₀ w₁ w₂ : World Digest} {l₀ l : List (Step Digest)}
    {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (h₀ : World.fold env g l₀ = .ok w₀)
    (h₁ : World.admit env w₀ t = .ok w₁) (hf : World.fold env w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w₂.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {p : Trie.Proof Digest Digest}
    (hsep : Separates env.hash (headPres env w₀ (.turn t :: l) w₂ prev tag td rd root' jroot' rroot' wroot' ++
      readPres (journalSpec env) t.txId p w₂.journal)) :
    Trie.verifyExclusion (journalSpec env) jroot' t.txId p = false :=
  head_absent_admitted_sep deployed_lawful (by decide) (deployed_reach_journalOk program hg h₀).1 h₁ hf hnf
    hhead hrd hsep

end Nanodregg.Kernel.Receive
