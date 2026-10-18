/-
# Kernel.Proofs.RefusalsHead — the phone reads the refusals against a head (KERNEL-44, KERNEL-47)

The twin of `Kernel.Proofs.JournalHead` for the third trie. The chain commits the refusals' root in
`rootsDigest`, so a phone that trusts one head can be shown that a call was refused (and with which
code, at which height), that a member's window count is what it is, or that a key is absent.

* `refusal_inclusion_sound` / `refusal_exclusion_sound`: a proof that verifies against a World's
  refusals root tells the truth about the key, or `Collision E.hash`;
  `refusal_prove_verifies` / `refusal_prove_absent`: the World proves every leaf it holds, and every
  key it does not.
* `head_refusal_read` / `head_refusal_absent`: the same against a head record that hashes to the
  chain any step (a Turn or a recorded refusal) reached, its `rd` opened to the four roots
  (`head_roots`).
* The prune horizon at the head: `fold_refused_retains` (`Kernel.Proofs.Refusals`) keeps a recorded
  `.tx` leaf through every fold below `h + 2 * windowMax`; `head_refused_retained` is what a phone
  is shown of it (the head's refusals root is the World's and the World's own proof of the record
  verifies against it), and `head_refused_not_absent` (the twin of `head_absent_admitted`): below
  that height no exclusion proof of the call verifies against the head, but by a collision.
Premises: `hE : E.Lawful n` (no `0 < n`: a refusals leaf body carries a 9-byte key besides the
digests, so an empty leaf is told from a full one at any digest size, `refusalBody_inj`); the
refusals trie canonical (`RefusalsCanon`), and, for inclusion, every leaf of the World and the
claimed leaf in the leaf codec's domain (`Codec.Kernel.RefusalLeaf.Fits`: every counter below 2^64;
`refusalDigest_inj`). Every reached World's leaves fit (`refusalsOk_fits` of `fold_refusalsOk`).
The claimed leaf's bound is load-bearing: `refusalDigest_wraps` / `refusal_inclusion_unbounded`.
At the deployed codec (`Receive.deployed_*` below) every premise but the claimed leaf's bound is
discharged for every World a checked genesis and a fold reach (`deployed_reach_refusalsOk`,
`deployed_reach_journalOk`).
-/
import Kernel.Proofs.JournalHead
import Kernel.Proofs.Refusals
import Kernel.Proofs.RootedDeployed
import Codec.Proofs.World

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The leaf digest and the leaf body are injective -/

theorem nat64_bytes_size (x : Nat) : (Nanodregg.Codec.Stream.nat64.bytes x).size = 8 := by
  rw [Nanodregg.Codec.Stream.nat64_bytes]; rfl

/-- A refusals leaf's bytes determine it, on the leaf codec's domain (every counter below 2^64). -/
theorem refusalLeafBytes_inj {v v' : RefusalLeaf} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    (hv' : Codec.Kernel.RefusalLeaf.Fits v') (h : refusalLeafBytes v = refusalLeafBytes v') : v = v' := by
  have h0 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  have h1 : (⟨#[1]⟩ : ByteArray).size = 1 := rfl
  cases v with
  | refused a c =>
      cases v' with
      | refused a' c' =>
          simp only [Codec.Kernel.RefusalLeaf.Fits] at hv hv'
          simp only [refusalLeafBytes] at h
          obtain ⟨hh, hc⟩ := bytes_append_inj h (by simp only [ByteArray.size_append, nat64_bytes_size])
          obtain ⟨-, ha⟩ := bytes_append_inj hh rfl
          rw [Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv.1 hv'.1 ha,
            Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv.2 hv'.2 hc]
      | count n' =>
          have := congrArg ByteArray.size h
          simp only [refusalLeafBytes, ByteArray.size_append, nat64_bytes_size, h0, h1] at this
          omega
  | count n =>
      cases v' with
      | refused a' c' =>
          have := congrArg ByteArray.size h
          simp only [refusalLeafBytes, ByteArray.size_append, nat64_bytes_size, h0, h1] at this
          omega
      | count n' =>
          simp only [Codec.Kernel.RefusalLeaf.Fits] at hv hv'
          simp only [refusalLeafBytes] at h
          obtain ⟨-, hn⟩ := bytes_append_inj h rfl
          rw [Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv hv' hn]

omit [Ord D] [DecidableEq D] in
/-- **A refusals leaf digest determines its leaf** on the leaf codec's domain, or the hash collides
in `domRefusal`. No premise on the `Env`. -/
theorem refusalDigest_inj {E : Env D} {v v' : RefusalLeaf} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    (hv' : Codec.Kernel.RefusalLeaf.Fits v') (h : refusalDigest E v = refusalDigest E v') :
    v = v' ∨ Collision E.hash := by
  by_cases hb : refusalLeafBytes v = refusalLeafBytes v'
  · exact .inl (refusalLeafBytes_inj hv hv' hb)
  · exact .inr ⟨domRefusal, _, _, hb, h⟩

omit [DecidableEq D] in
theorem refusalBody_size {E : Env D} {n : Nat} (hE : E.Lawful n) (kds : List (RefusalSlot D × D)) :
    (Trie.leafBody (refusalSpec E) kds).size = (1 + n + 8 + n) * kds.length := by
  induction kds with
  | nil => rfl
  | cons p rest ih =>
      show (refusalKeyBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (refusalSpec E) rest).size = _
      simp only [ByteArray.size_append, ih, refusalKeyBytes_size hE, hE.size, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]; omega

omit [DecidableEq D] in
/-- A refusals leaf's body determines its entries, at any digest size (the key's kind byte and its
eight counter bytes make every entry at least nine bytes). -/
theorem refusalBody_inj {E : Env D} {n : Nat} (hE : E.Lawful n) : ∀ x y : List (RefusalSlot D × D),
    Trie.leafBody (refusalSpec E) x = Trie.leafBody (refusalSpec E) y → x = y
  | [], [], _ => rfl
  | [], q :: ys, h => by
      have := congrArg ByteArray.size h
      rw [refusalBody_size hE, refusalBody_size hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, [], h => by
      have := congrArg ByteArray.size h
      rw [refusalBody_size hE, refusalBody_size hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, q :: ys, h => by
      change refusalKeyBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (refusalSpec E) xs =
        refusalKeyBytes E q.1 ++ E.bytes q.2 ++ Trie.leafBody (refusalSpec E) ys at h
      obtain ⟨hh, ht⟩ := bytes_append_inj h
        (by simp only [ByteArray.size_append, refusalKeyBytes_size hE, hE.size])
      obtain ⟨hk, hd⟩ := bytes_append_inj hh (by rw [refusalKeyBytes_size hE, refusalKeyBytes_size hE])
      rw [Prod.ext (refusalKeyBytes_inj hE hk) (hE.bytes_inj hd), refusalBody_inj hE xs ys ht]

omit [Ord D] [DecidableEq D] in
/-- A refusals-trie collision is a `Collision` of the kernel's hash (in `domTrie`). -/
theorem refusal_coll_collision {E : Env D} (h : Trie.Coll (refusalSpec E)) : Collision E.hash := by
  obtain ⟨a, b, hne, he⟩ := h; exact ⟨domTrie, a, b, hne, he⟩

/-- **Every leaf of a `RefusalsOk` World is in the leaf codec's domain**: the World's own
`refusalFits` bounds every counter. -/
theorem refusalsOk_fits {E : Env D} {w : World D} (hw : w.RefusalsOk E) :
    ∀ k v, w.refusalAt E k = some v → Codec.Kernel.RefusalLeaf.Fits v := fun k v hg =>
  Codec.Kernel.refusalLeaf_fits_of_refusalsFits (refusalsFits_of_ok hw) (k, v)
    ((Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 k v).mpr hg)

/-! ## The World proves what it holds, and what it does not -/

theorem fold_refusalsCanon {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.RefusalsCanon E)
    (h : World.fold E w l = .ok w') : w'.RefusalsCanon E :=
  fold_keeps (P := fun v => v.RefusalsCanon E) admit_refusalsCanon refuse_refusalsCanon hc h

/-- **A World proves every refusals leaf it holds.** -/
theorem refusal_prove_verifies {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    {v : RefusalLeaf} (hg : w.refusalAt E k = some v) :
    Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v)
      (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_includes (refusalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves every refusals key it does not hold.** -/
theorem refusal_prove_absent {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    (hg : w.refusalAt E k = none) :
    Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_excludes (refusalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-! ## Soundness at the World and at a head -/

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n)

include hE in
/-- **Refusals inclusion is sound at the World**: a claimed leaf proved against the refusals root is
the World's leaf, or a collision. -/
theorem refusal_inclusion_sound {w : World D} (hc : w.RefusalsCanon E)
    (hfit : ∀ k v, w.refusalAt E k = some v → Codec.Kernel.RefusalLeaf.Fits v) {k : RefusalSlot D}
    {v : RefusalLeaf} (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v) p = true) :
    w.refusalAt E k = some v ∨ Collision E.hash := by
  rcases Trie.inclusion_sound (refusalSpec E) (refusalBody_inj hE) (dbytes_pair_inj hE) hc.2.1 hp
    with ⟨v', hg, hd⟩ | c
  · rcases refusalDigest_inj (hfit k v' hg) hv hd with rfl | c
    · exact .inl hg
    · exact .inr c
  · exact .inr (refusal_coll_collision c)

include hE in
/-- **Refusals exclusion is sound at the World**: a key proved absent against the refusals root is
not in the World's refusals, or a collision. -/
theorem refusal_exclusion_sound {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k p = true) :
    w.refusalAt E k = none ∨ Collision E.hash := by
  rcases Trie.exclusion_sound (refusalSpec E) (refusalBody_inj hE) (dbytes_pair_inj hE) hc.2.1 hp
    with h | c
  · exact .inl h
  · exact .inr (refusal_coll_collision c)

include hE in
/-- **The phone's refusals read**: a head record that hashes to the chain a step (a Turn or a
recorded refusal) reached, and an inclusion proof against the record's refusals root, show the leaf
in that World's refusals, or a collision. -/
theorem head_refusal_read {w w' : World D} {s : Step D} (hw : w.RefusalsOk E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RefusalSlot D} {v : RefusalLeaf} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) rroot' k (refusalDigest E v) p = true) :
    w'.refusalAt E k = some v ∨ Collision E.hash := by
  rcases head_roots hE h hhead hrd with ⟨-, -, rfl, -⟩ | col
  · have hw' := step_refusalsOk hw h
    exact refusal_inclusion_sound hE hw'.1 (refusalsOk_fits hw') hv hp
  · exact .inr col

include hE in
/-- **The phone's refusals absence** against a head: the key is not in that World's refusals, or a
collision. -/
theorem head_refusal_absent {w w' : World D} {s : Step D} (hc : w.RefusalsCanon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RefusalSlot D} {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) rroot' k p = true) :
    w'.refusalAt E k = none ∨ Collision E.hash := by
  rcases head_roots hE h hhead hrd with ⟨-, -, rfl, -⟩ | col
  · exact refusal_exclusion_sound hE (step_refusalsCanon hc h) hp
  · exact .inr col

include hE in
/-- A head record that hashes to the chain of a World a log reached after a step names that World's
four roots, or a collision (the head is the log's last link). -/
theorem fold_head_roots {w₀ w₁ w₂ : World D} {s : Step D} {l : List (Step D)}
    (h₁ : World.step E w₀ s = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    (root' = w₂.root E ∧ jroot' = w₂.journalRoot E ∧ rroot' = w₂.refusalsRoot E ∧
      wroot' = w₂.rowsRoot E) ∨ Collision E.hash := by
  cases l with
  | nil =>
      simp [World.fold] at hf; subst hf
      exact head_roots hE h₁ hhead hrd
  | cons u us =>
      rcases List.eq_nil_or_concat (u :: us) with he | ⟨a, b, he⟩
      · cases he
      · rw [he, List.concat_eq_append] at hf
        obtain ⟨w₃, _, h₃⟩ := fold_append.mp hf
        obtain ⟨w₄, h₄, h₅⟩ := fold_cons_ok.mp h₃
        simp [World.fold] at h₅; subst h₅
        exact head_roots hE h₄ hhead hrd

/-! ## The prune horizon, at the head -/

include hE in
/-- **What a phone is shown of a recorded refusal** (`fold_refused_retains` at the head). After
`World.refuse` recorded `r` from `w₀`, on every World `w₂` a later log reaches below
`w₀.height + 1 + 2 * windowMax`, a head record that hashes to `w₂`'s chain opens to `w₂`'s refusals
root, and `w₂`'s own proof of the call's `.tx` leaf, refused at `w₀.height + 1` with `r.code`,
verifies against it; or the hash collides. -/
theorem head_refused_retained {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    (rroot' = w₂.refusalsRoot E ∧
      Trie.verifyInclusion (refusalSpec E) rroot' (.tx r.txId) (refusalDigest E (.refused (w₀.height + 1) r.code))
        (w₂.refusals.prove (refusalSpec E) (.tx r.txId)) = true) ∨ Collision E.hash := by
  obtain ⟨-, -, -, hj, -, -⟩ := refuse_facts h₁
  have hjc₁ : w₁.JournalCanon E := by
    unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
  have hc₁ := refuse_refusalsCanon hc h₁
  obtain ⟨hr₂, -⟩ := fold_refused_retains hc₁ hjc₁ hf (refuse_recorded h₁)
    ((refuse_journalAt h₁ _).trans hj) hlt
  rcases fold_head_roots hE (s := .refusal r) h₁ hf hhead hrd with ⟨-, -, rfl, -⟩ | col
  · exact .inl ⟨rfl, refusal_prove_verifies (fold_refusalsCanon hc₁ hf) hr₂⟩
  · exact .inr col

include hE in
/-- **Exclusion below the horizon refutes**: the twin of `head_absent_admitted`. After `World.refuse`
recorded `r` from `w₀`, no exclusion proof of the call's `.tx` key verifies against the head of any
World a later log reaches below `w₀.height + 1 + 2 * windowMax`, but by a collision. -/
theorem head_refused_not_absent {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) rroot' (.tx r.txId) p = true) : Collision E.hash := by
  obtain ⟨-, -, -, hj, -, -⟩ := refuse_facts h₁
  have hjc₁ : w₁.JournalCanon E := by
    unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
  have hc₁ := refuse_refusalsCanon hc h₁
  obtain ⟨hr₂, -⟩ := fold_refused_retains hc₁ hjc₁ hf (refuse_recorded h₁)
    ((refuse_journalAt h₁ _).trans hj) hlt
  rcases fold_head_roots hE (s := .refusal r) h₁ hf hhead hrd with ⟨-, -, rfl, -⟩ | col
  · rcases refusal_exclusion_sound hE (fold_refusalsCanon hc₁ hf) hp with hnone | col
    · rw [hr₂] at hnone; cases hnone
    · exact col
  · exact col

/-! ## Teeth -/

include hE in
/-- TOOTH (`refusal_inclusion_sound`): **a verifier accepting a wrong leaf refutes**. If the World
holds `v'` at `k`, a proof that verifies `v ≠ v'` at `k` against its root is a collision. -/
theorem refusal_inclusion_wrong_leaf {w : World D} (hw : w.RefusalsOk E) {k : RefusalSlot D}
    {v v' : RefusalLeaf} (hg : w.refusalAt E k = some v') (hne : v ≠ v')
    (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v) p = true) :
    Collision E.hash := by
  rcases refusal_inclusion_sound hE hw.1 (refusalsOk_fits hw) hv hp with h | c
  · rw [hg] at h; cases h; exact absurd rfl hne
  · exact c

include hE in
/-- TOOTH (`refusal_inclusion_sound`): **a proof for one key does not verify for another**. The
World's own proof of its leaf at `k`, presented at a key `k'` the World does not hold, is a
collision. -/
theorem refusal_inclusion_other_key {w : World D} (hw : w.RefusalsOk E) {k k' : RefusalSlot D}
    {v : RefusalLeaf} (hg : w.refusalAt E k = some v) (hg' : w.refusalAt E k' = none)
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k' (refusalDigest E v)
      (w.refusals.prove (refusalSpec E) k) = true) : Collision E.hash := by
  rcases refusal_inclusion_sound hE hw.1 (refusalsOk_fits hw) (refusalsOk_fits hw k v hg) hp with h | c
  · rw [hg'] at h; cases h
  · exact c

include hE in
/-- TOOTH (`refusal_exclusion_sound`): **a held key proved absent refutes.** -/
theorem refusal_exclusion_held {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    {v : RefusalLeaf} (hg : w.refusalAt E k = some v) {p : Trie.Proof (RefusalSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k p = true) : Collision E.hash := by
  rcases refusal_exclusion_sound hE hc hp with h | c
  · rw [hg] at h; cases h
  · exact c

end Sound

omit [Ord D] [DecidableEq D] in
/-- PLANT (the claimed leaf's bound): past 2^64 a refusals leaf digest wraps, with no collision.
`.refused (2^64) c` and `.refused 0 c` have one digest under any `Env`. -/
theorem refusalDigest_wraps (E : Env D) (c : Nat) :
    refusalDigest E (.refused (2 ^ 64) c) = refusalDigest E (.refused 0 c) := by
  have : Nanodregg.Codec.Stream.nat64.bytes (2 ^ 64) = Nanodregg.Codec.Stream.nat64.bytes 0 := by
    rw [Nanodregg.Codec.Stream.nat64_bytes, Nanodregg.Codec.Stream.nat64_bytes]
    congr 1
  simp only [refusalDigest, refusalLeafBytes]
  rw [this]

/-- TOOTH (`refusal_inclusion_sound`'s `hv`): **the claimed leaf's bound is load-bearing.** On any
canonical World holding `.refused 0 c` at `k`, the World's own proof verifies the out-of-domain leaf
`.refused (2^64) c` at `k`, which the World does not hold: dropping `hv`, the first disjunct is false
with no collision in sight. -/
theorem refusal_inclusion_unbounded {E : Env D} {w : World D} (hc : w.RefusalsCanon E)
    {k : RefusalSlot D} {c : Nat} (hg : w.refusalAt E k = some (.refused 0 c)) :
    Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E (.refused (2 ^ 64) c))
        (w.refusals.prove (refusalSpec E) k) = true ∧
      w.refusalAt E k ≠ some (.refused (2 ^ 64) c) := by
  refine ⟨by rw [refusalDigest_wraps]; exact refusal_prove_verifies hc hg, ?_⟩
  rw [hg]; intro h; cases h

end Nanodregg.Kernel

/-! ## At the deployed codec -/

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: the phone's refusals read.** On a World a checked genesis and a fold reach, a head
record that hashes to the chain the next step reached, and an inclusion proof against the record's
refusals root, show the leaf in that World's refusals, or a collision. The one premise left is the
claimed leaf's: its counters are below 2^64 (`u64`s on the wire). -/
theorem deployed_head_refusal_read (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : RefusalSlot Digest} {v : RefusalLeaf}
    (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (RefusalSlot Digest) Digest}
    (hp : Trie.verifyInclusion (refusalSpec env) rroot' k (refusalDigest env v) p = true) :
    w'.refusalAt env k = some v ∨ Collision env.hash :=
  head_refusal_read deployed_lawful (deployed_reach_refusalsOk program hg hl) h hhead hrd hv hp

/-- **Deployed: the phone's refusals absence**, no premise. -/
theorem deployed_head_refusal_absent (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : RefusalSlot Digest}
    {p : Trie.Proof (RefusalSlot Digest) Digest}
    (hp : Trie.verifyExclusion (refusalSpec env) rroot' k p = true) :
    w'.refusalAt env k = none ∨ Collision env.hash :=
  head_refusal_absent deployed_lawful (deployed_reach_refusalsOk program hg hl).1 h hhead hrd hp

/-- **Deployed: a recorded refusal is shown at every head below its horizon**, no premise. -/
theorem deployed_head_refused_retained (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w₀ w₁ w₂ : World Digest} {l₀ l : List (Step Digest)}
    {r : Refused Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl₀ : World.fold env g l₀ = .ok w₀)
    (h₁ : World.refuse env w₀ r = .ok w₁) (hf : World.fold env w₁ l = .ok w₂)
    (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w₂.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) :
    (rroot' = w₂.refusalsRoot env ∧
      Trie.verifyInclusion (refusalSpec env) rroot' (.tx r.txId)
        (refusalDigest env (.refused (w₀.height + 1) r.code))
        (w₂.refusals.prove (refusalSpec env) (.tx r.txId)) = true) ∨ Collision env.hash :=
  head_refused_retained deployed_lawful (deployed_reach_refusalsOk program hg hl₀).1
    (deployed_reach_journalOk program hg hl₀).1 h₁ hf hlt hhead hrd

/-- **Deployed: below its horizon a recorded refusal cannot be shown absent**, no premise. -/
theorem deployed_head_refused_not_absent (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w₀ w₁ w₂ : World Digest} {l₀ l : List (Step Digest)}
    {r : Refused Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl₀ : World.fold env g l₀ = .ok w₀)
    (h₁ : World.refuse env w₀ r = .ok w₁) (hf : World.fold env w₁ l = .ok w₂)
    (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w₂.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {p : Trie.Proof (RefusalSlot Digest) Digest}
    (hp : Trie.verifyExclusion (refusalSpec env) rroot' (.tx r.txId) p = true) : Collision env.hash :=
  head_refused_not_absent deployed_lawful (deployed_reach_refusalsOk program hg hl₀).1
    (deployed_reach_journalOk program hg hl₀).1 h₁ hf hlt hhead hrd hp

end Nanodregg.Kernel.Receive
