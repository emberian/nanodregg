/-
# Kernel.Proofs.RefusalsHead — the phone reads the refusals against a head (KERNEL-44, KERNEL-47)

The twin of `Kernel.Proofs.JournalHead` for the third trie. The chain commits the refusals' root in
`rootsDigest`, so a phone that trusts one head can be shown that a call was refused (and with which
code, at which height), that a member's window count is what it is, or that a key is absent.

* `refusal_inclusion_sound` / `refusal_exclusion_sound`: a proof that verifies against a World's
  refusals root tells the truth about the key, or two of the inputs the read compares collide
  (`inclPres`, `readPres`; KERNEL-56);
  `refusal_prove_verifies` / `refusal_prove_absent`: the World proves every leaf it holds, and every
  key it does not.
* `head_refusal_read` / `head_refusal_absent`: the same against a head record that hashes to the
  chain any step (a Turn or a recorded refusal) reached, its `rd` opened to the four roots
  (`head_roots`).
* The prune horizon at the head: `fold_refused_retains` (`Kernel.Proofs.Refusals`) keeps a recorded
  `.tx` leaf through every fold below `h + 2 * windowMax`; `head_refused_retained` is what a phone
  is shown of it (the head's refusals root is the World's and the World's own proof of the record
  verifies against it), and `head_refused_not_absent` (the twin of `head_absent_admitted`): below
  that height no exclusion proof of the call verifies against the head, but by a collision among the inputs it compares.
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

omit [DecidableEq D] in
/-- A refusals leaf's bytes determine it, on the leaf codec's domain (every counter below 2^64) and
a lawful `Env` (the charged member's bytes, KERNEL-50). -/
theorem refusalLeafBytes_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {v v' : RefusalLeaf D}
    (hv : Codec.Kernel.RefusalLeaf.Fits v) (hv' : Codec.Kernel.RefusalLeaf.Fits v')
    (h : refusalLeafBytes E v = refusalLeafBytes E v') : v = v' := by
  have h0 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  have h1 : (⟨#[1]⟩ : ByteArray).size = 1 := rfl
  cases v with
  | refused a c m =>
      cases v' with
      | refused a' c' m' =>
          simp only [Codec.Kernel.RefusalLeaf.Fits] at hv hv'
          simp only [refusalLeafBytes] at h
          obtain ⟨hac, hm⟩ := bytes_append_inj h
            (by simp only [ByteArray.size_append, nat64_bytes_size, h0])
          obtain ⟨hh, hc⟩ := bytes_append_inj hac (by simp only [ByteArray.size_append, nat64_bytes_size])
          obtain ⟨-, ha⟩ := bytes_append_inj hh rfl
          rw [Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv.1 hv'.1 ha,
            Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv.2 hv'.2 hc, hE.bytes_inj hm]
      | count n' =>
          have := congrArg ByteArray.size h
          simp only [refusalLeafBytes, ByteArray.size_append, nat64_bytes_size, h0, h1, hE.size] at this
          omega
  | count k =>
      cases v' with
      | refused a' c' m' =>
          have := congrArg ByteArray.size h
          simp only [refusalLeafBytes, ByteArray.size_append, nat64_bytes_size, h0, h1, hE.size] at this
          omega
      | count n' =>
          simp only [Codec.Kernel.RefusalLeaf.Fits] at hv hv'
          simp only [refusalLeafBytes] at h
          obtain ⟨-, hn⟩ := bytes_append_inj h rfl
          rw [Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv hv' hn]

omit [DecidableEq D] in
/-- **A refusals leaf digest determines its leaf** on the leaf codec's domain and a lawful `Env`, or
the two inputs collide (in `domRefusal`). -/
theorem refusalDigest_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {v v' : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    (hv' : Codec.Kernel.RefusalLeaf.Fits v') (h : refusalDigest E v = refusalDigest E v') :
    v = v' ∨ CollidesAmong E.hash [refusalPre E v, refusalPre E v'] := by
  by_cases hb : refusalLeafBytes E v = refusalLeafBytes E v'
  · exact .inl (refusalLeafBytes_inj hE hv hv' hb)
  · exact .inr (.pair (fun he => hb (congrArg Prod.snd he)) h)

omit [DecidableEq D] in
theorem refusalBody_size {E : Env D} {n : Nat} (hE : E.Lawful n) (kds : List (WindowSlot D × D)) :
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
theorem refusalBody_inj {E : Env D} {n : Nat} (hE : E.Lawful n) : ∀ x y : List (WindowSlot D × D),
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

/-- **Every leaf of a `RefusalsOk` World is in the leaf codec's domain**: the World's own
`refusalFits` bounds every counter. -/
theorem refusalsOk_fits {E : Env D} {w : World D} (hw : w.RefusalsOk E) :
    ∀ k v, w.refusals.get (refusalSpec E) k = some v → Codec.Kernel.RefusalLeaf.Fits v := fun k v hg =>
  Codec.Kernel.refusalLeaf_fits_of_refusalsFits (refusalsFits_of_ok hw) (k, v)
    ((Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 k v).mpr hg)

/-! ## The World proves what it holds, and what it does not -/

theorem fold_refusalsCanon {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.RefusalsCanon E)
    (h : World.fold E w l = .ok w') : w'.RefusalsCanon E :=
  fold_keeps (P := fun v => v.RefusalsCanon E) admit_refusalsCanon refuse_refusalsCanon hc h

/-- **A World proves every refusals leaf it holds.** -/
theorem refusal_prove_verifies {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : WindowSlot D}
    {v : RefusalLeaf D} (hg : w.refusals.get (refusalSpec E) k = some v) :
    Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v)
      (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_includes (refusalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves every refusals key it does not hold.** -/
theorem refusal_prove_absent {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : WindowSlot D}
    (hg : w.refusals.get (refusalSpec E) k = none) :
    Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_excludes (refusalSpec E) hc.2.1 hc.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-! ## Soundness at the World and at a head -/

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n)

include hE in
omit [DecidableEq D] in
/-- **The refusals' trie is a `HeadSound` instance** (KERNEL-52) on `RefusalLeaf.Fits`, at any
digest size (`refusalBody_inj`). -/
theorem refusal_headSound : HeadSound E (refusalSpec E) Codec.Kernel.RefusalLeaf.Fits (refusalPre E) :=
  ⟨refusalBody_inj hE, dbytes_pair_inj hE, fun _ => rfl, fun _ => rfl,
    fun hv hv' h => refusalLeafBytes_inj hE hv hv' (congrArg Prod.snd h)⟩

include hE in
/-- **Refusals inclusion is sound at the World**: a claimed leaf proved against the refusals root is
the World's leaf, or two of the inputs it compares collide. -/
theorem refusal_inclusion_sound {w : World D} (hc : w.RefusalsCanon E)
    (hfit : ∀ k v, w.refusals.get (refusalSpec E) k = some v → Codec.Kernel.RefusalLeaf.Fits v) {k : WindowSlot D}
    {v : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v) p = true) :
    w.refusals.get (refusalSpec E) k = some v ∨ CollidesAmong E.hash (inclPres (refusalSpec E) (refusalPre E) k v p w.refusals) :=
  (refusal_headSound hE).inclusion hc hfit hv hp

include hE in
/-- **Refusals exclusion is sound at the World**: a key proved absent against the refusals root is
not in the World's refusals, or two of the inputs it compares collide. -/
theorem refusal_exclusion_sound {w : World D} (hc : w.RefusalsCanon E) {k : WindowSlot D}
    {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k p = true) :
    w.refusals.get (refusalSpec E) k = none ∨ CollidesAmong E.hash (readPres (refusalSpec E) k p w.refusals) :=
  (refusal_headSound hE).exclusion hc hp

include hE in
/-- **The phone's refusals read**: a head record that hashes to the chain a step (a Turn or a
recorded refusal) reached, and an inclusion proof against the record's refusals root, show the leaf
in that World's refusals, or two of the inputs it compares collide. -/
theorem head_refusal_read {w w' : World D} {s : Step D} (hw : w.RefusalsOk E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : WindowSlot D} {v : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) rroot' k (refusalDigest E v) p = true) :
    w'.refusals.get (refusalSpec E) k = some v ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        inclPres (refusalSpec E) (refusalPre E) k v p w'.refusals) :=
  (refusal_headSound hE).head_read (fun _ _ r _ => r) (step_refusalsOk hw h).1 rfl
    (refusalsOk_fits (step_refusalsOk hw h)) (head_roots hE h hhead hrd) hv hp

include hE in
/-- **The phone's refusals absence** against a head: the key is not in that World's refusals, or a
collision. -/
theorem head_refusal_absent {w w' : World D} {s : Step D} (hc : w.RefusalsCanon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : WindowSlot D} {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) rroot' k p = true) :
    w'.refusals.get (refusalSpec E) k = none ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        readPres (refusalSpec E) k p w'.refusals) :=
  (refusal_headSound hE).head_absent (fun _ _ r _ => r) (step_refusalsCanon hc h) rfl
    (head_roots hE h hhead hrd) hp

/-! ## The prune horizon, at the head -/

include hE in
/-- **What a phone is shown of a recorded refusal** (`fold_refused_retains` at the head). After
`World.refuse` recorded `r` from `w₀`, on every World `w₂` a later log reaches below
`w₀.height + 1 + 2 * windowMax`, a head record that hashes to `w₂`'s chain opens to `w₂`'s refusals
root, and `w₂`'s own proof of the call's `.tx` leaf, refused at `w₀.height + 1` with `r.code`,
verifies against it; or two of the opening's inputs collide (`headPres`). -/
theorem head_refused_retained {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    (rroot' = w₂.refusalsRoot E ∧
      Trie.verifyInclusion (refusalSpec E) rroot' (.refusal (.tx r.txId)) (refusalDigest E (.refused (w₀.height + 1) r.code r.member))
        (w₂.refusals.prove (refusalSpec E) (.refusal (.tx r.txId))) = true) ∨
      CollidesAmong E.hash (headPres E w₀ (.refusal r :: l) w₂ prev g td rd root' jroot' rroot' wroot') := by
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
World a later log reaches below `w₀.height + 1 + 2 * windowMax`, but by a collision among the inputs it compares. -/
theorem head_refused_not_absent {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) rroot' (.refusal (.tx r.txId)) p = true) :
    CollidesAmong E.hash (headPres E w₀ (.refusal r :: l) w₂ prev g td rd root' jroot' rroot' wroot' ++
      readPres (refusalSpec E) (.refusal (.tx r.txId)) p w₂.refusals) := by
  obtain ⟨-, -, -, hj, -, -⟩ := refuse_facts h₁
  have hjc₁ : w₁.JournalCanon E := by
    unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
  have hc₁ := refuse_refusalsCanon hc h₁
  obtain ⟨hr₂, -⟩ := fold_refused_retains hc₁ hjc₁ hf (refuse_recorded h₁)
    ((refuse_journalAt h₁ _).trans hj) hlt
  rcases fold_head_roots hE (s := .refusal r) h₁ hf hhead hrd with ⟨-, -, rfl, -⟩ | col
  · rcases refusal_exclusion_sound hE (fold_refusalsCanon hc₁ hf) hp with hnone | col
    · unfold World.refusalAt at hr₂; rw [hr₂] at hnone; cases hnone
    · exact CollidesAmong.mono (fun x hx => List.mem_append_right _ hx) col
  · exact CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col

/-! ## Teeth -/

include hE in
/-- TOOTH (`refusal_inclusion_sound`): **a verifier accepting a wrong leaf refutes**. If the World
holds `v'` at `k`, a proof that verifies `v ≠ v'` at `k` against its root is a collision. -/
theorem refusal_inclusion_wrong_leaf {w : World D} (hw : w.RefusalsOk E) {k : WindowSlot D}
    {v v' : RefusalLeaf D} (hg : w.refusals.get (refusalSpec E) k = some v') (hne : v ≠ v')
    (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v) p = true) :
    CollidesAmong E.hash (inclPres (refusalSpec E) (refusalPre E) k v p w.refusals) := by
  rcases refusal_inclusion_sound hE hw.1 (refusalsOk_fits hw) hv hp with h | c
  · rw [hg] at h; cases h; exact absurd rfl hne
  · exact c

include hE in
/-- TOOTH (`refusal_inclusion_sound`): **a proof for one key does not verify for another**. The
World's own proof of its leaf at `k`, presented at a key `k'` the World does not hold, is a
collision. -/
theorem refusal_inclusion_other_key {w : World D} (hw : w.RefusalsOk E) {k k' : WindowSlot D}
    {v : RefusalLeaf D} (hg : w.refusals.get (refusalSpec E) k = some v) (hg' : w.refusals.get (refusalSpec E) k' = none)
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k' (refusalDigest E v)
      (w.refusals.prove (refusalSpec E) k) = true) :
    CollidesAmong E.hash (inclPres (refusalSpec E) (refusalPre E) k' v (w.refusals.prove (refusalSpec E) k) w.refusals) := by
  rcases refusal_inclusion_sound hE hw.1 (refusalsOk_fits hw) (refusalsOk_fits hw k v hg) hp with h | c
  · rw [hg'] at h; cases h
  · exact c

include hE in
/-- TOOTH (`refusal_exclusion_sound`): **a held key proved absent refutes.** -/
theorem refusal_exclusion_held {w : World D} (hc : w.RefusalsCanon E) {k : WindowSlot D}
    {v : RefusalLeaf D} (hg : w.refusals.get (refusalSpec E) k = some v) {p : Trie.Proof (WindowSlot D) D}
    (hp : Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k p = true) :
    CollidesAmong E.hash (readPres (refusalSpec E) k p w.refusals) := by
  rcases refusal_exclusion_sound hE hc hp with h | c
  · rw [hg] at h; cases h
  · exact c

/-! ### Teeth: under `Separates` of the inputs each theorem names, its binding fact alone -/

include hE in
omit [DecidableEq D] in
/-- TOOTH (`refusalDigest_inj`). -/
theorem refusalDigest_inj_sep {v v' : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    (hv' : Codec.Kernel.RefusalLeaf.Fits v') (hsep : Separates E.hash [refusalPre E v, refusalPre E v'])
    (h : refusalDigest E v = refusalDigest E v') : v = v' :=
  hsep.elim (refusalDigest_inj hE hv hv' h)

include hE in
/-- TOOTH (`refusal_inclusion_sound`). -/
theorem refusal_inclusion_sound_sep {w : World D} (hc : w.RefusalsCanon E)
    (hfit : ∀ k v, w.refusals.get (refusalSpec E) k = some v → Codec.Kernel.RefusalLeaf.Fits v) {k : WindowSlot D}
    {v : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (WindowSlot D) D}
    (hsep : Separates E.hash (inclPres (refusalSpec E) (refusalPre E) k v p w.refusals))
    (hp : Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E v) p = true) :
    w.refusals.get (refusalSpec E) k = some v :=
  hsep.elim (refusal_inclusion_sound hE hc hfit hv hp)

include hE in
/-- TOOTH (`refusal_exclusion_sound`). -/
theorem refusal_exclusion_sound_sep {w : World D} (hc : w.RefusalsCanon E) {k : WindowSlot D}
    {p : Trie.Proof (WindowSlot D) D} (hsep : Separates E.hash (readPres (refusalSpec E) k p w.refusals))
    (hp : Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k p = true) : w.refusals.get (refusalSpec E) k = none :=
  hsep.elim (refusal_exclusion_sound hE hc hp)

include hE in
/-- TOOTH (`head_refusal_read`). -/
theorem head_refusal_read_sep {w w' : World D} {s : Step D} (hw : w.RefusalsOk E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : WindowSlot D} {v : RefusalLeaf D} (hv : Codec.Kernel.RefusalLeaf.Fits v)
    {p : Trie.Proof (WindowSlot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      inclPres (refusalSpec E) (refusalPre E) k v p w'.refusals))
    (hp : Trie.verifyInclusion (refusalSpec E) rroot' k (refusalDigest E v) p = true) :
    w'.refusals.get (refusalSpec E) k = some v :=
  hsep.elim (head_refusal_read hE hw h hhead hrd hv hp)

include hE in
/-- TOOTH (`head_refusal_absent`). -/
theorem head_refusal_absent_sep {w w' : World D} {s : Step D} (hc : w.RefusalsCanon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : WindowSlot D} {p : Trie.Proof (WindowSlot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      readPres (refusalSpec E) k p w'.refusals))
    (hp : Trie.verifyExclusion (refusalSpec E) rroot' k p = true) : w'.refusals.get (refusalSpec E) k = none :=
  hsep.elim (head_refusal_absent hE hc h hhead hrd hp)

include hE in
/-- TOOTH (`head_refused_retained`): under a hash that separates the opening's inputs, a phone is
shown the recorded refusal at every head below its horizon. -/
theorem head_refused_retained_sep {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hsep : Separates E.hash (headPres E w₀ (.refusal r :: l) w₂ prev g td rd root' jroot' rroot' wroot'))
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    rroot' = w₂.refusalsRoot E ∧
      Trie.verifyInclusion (refusalSpec E) rroot' (.refusal (.tx r.txId)) (refusalDigest E (.refused (w₀.height + 1) r.code r.member))
        (w₂.refusals.prove (refusalSpec E) (.refusal (.tx r.txId))) = true :=
  hsep.elim (head_refused_retained hE hc hjc h₁ hf hlt hhead hrd)

include hE in
/-- TOOTH (`head_refused_not_absent`): under a hash that separates the inputs the opening and the
read compare, no exclusion proof of a recorded call verifies against a head below its horizon. -/
theorem head_refused_not_absent_sep {w₀ w₁ w₂ : World D} {r : Refused D} {l : List (Step D)}
    (hc : w₀.RefusalsCanon E) (hjc : w₀.JournalCanon E) (h₁ : World.refuse E w₀ r = .ok w₁)
    (hf : World.fold E w₁ l = .ok w₂) (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof (WindowSlot D) D}
    (hsep : Separates E.hash (headPres E w₀ (.refusal r :: l) w₂ prev g td rd root' jroot' rroot' wroot' ++
      readPres (refusalSpec E) (.refusal (.tx r.txId)) p w₂.refusals)) :
    Trie.verifyExclusion (refusalSpec E) rroot' (.refusal (.tx r.txId)) p = false := by
  cases hv : Trie.verifyExclusion (refusalSpec E) rroot' (.refusal (.tx r.txId)) p
  · rfl
  · exact absurd (head_refused_not_absent hE hc hjc h₁ hf hlt hhead hrd hv) hsep.not_collides

end Sound

omit [Ord D] [DecidableEq D] in
/-- PLANT (the claimed leaf's bound): past 2^64 a refusals leaf digest wraps, with no collision.
`.refused (2^64) c m` and `.refused 0 c m` have one digest under any `Env`. -/
theorem refusalDigest_wraps (E : Env D) (c : Nat) (m : D) :
    refusalDigest E (.refused (2 ^ 64) c m) = refusalDigest E (.refused 0 c m) := by
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
    {k : WindowSlot D} {c : Nat} {m : D} (hg : w.refusals.get (refusalSpec E) k = some (.refused 0 c m)) :
    Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E (.refused (2 ^ 64) c m))
        (w.refusals.prove (refusalSpec E) k) = true ∧
      w.refusals.get (refusalSpec E) k ≠ some (.refused (2 ^ 64) c m) := by
  refine ⟨by rw [refusalDigest_wraps]; exact refusal_prove_verifies hc hg, ?_⟩
  rw [hg]; intro h; cases h

end Nanodregg.Kernel

/-! ## At the deployed codec -/

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: the phone's refusals read.** On a World a checked genesis and a fold reach, a head
record that hashes to the chain the next step reached, and an inclusion proof against the record's
refusals root, show the leaf in that World's refusals, or two of the inputs it compares collide. The one premise left is the
claimed leaf's: its counters are below 2^64 (`u64`s on the wire). -/
theorem deployed_head_refusal_read (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : WindowSlot Digest} {v : RefusalLeaf Digest}
    (hv : Codec.Kernel.RefusalLeaf.Fits v) {p : Trie.Proof (WindowSlot Digest) Digest}
    (hp : Trie.verifyInclusion (refusalSpec env) rroot' k (refusalDigest env v) p = true) :
    w'.refusals.get (refusalSpec env) k = some v ∨
      CollidesAmong env.hash (headPres env w [s] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (refusalSpec env) (refusalPre env) k v p w'.refusals) :=
  head_refusal_read deployed_lawful (deployed_reach_refusalsOk program hg hl) h hhead hrd hv hp

/-- **Deployed: the phone's refusals absence**, no premise. -/
theorem deployed_head_refusal_absent (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : WindowSlot Digest}
    {p : Trie.Proof (WindowSlot Digest) Digest}
    (hp : Trie.verifyExclusion (refusalSpec env) rroot' k p = true) :
    w'.refusals.get (refusalSpec env) k = none ∨
      CollidesAmong env.hash (headPres env w [s] w' prev tag td rd root' jroot' rroot' wroot' ++
        readPres (refusalSpec env) k p w'.refusals) :=
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
      Trie.verifyInclusion (refusalSpec env) rroot' (.refusal (.tx r.txId))
        (refusalDigest env (.refused (w₀.height + 1) r.code r.member))
        (w₂.refusals.prove (refusalSpec env) (.refusal (.tx r.txId))) = true) ∨
      CollidesAmong env.hash (headPres env w₀ (.refusal r :: l) w₂ prev tag td rd root' jroot' rroot' wroot') :=
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
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {p : Trie.Proof (WindowSlot Digest) Digest}
    (hp : Trie.verifyExclusion (refusalSpec env) rroot' (.refusal (.tx r.txId)) p = true) :
    CollidesAmong env.hash (headPres env w₀ (.refusal r :: l) w₂ prev tag td rd root' jroot' rroot' wroot' ++
      readPres (refusalSpec env) (.refusal (.tx r.txId)) p w₂.refusals) :=
  head_refused_not_absent deployed_lawful (deployed_reach_refusalsOk program hg hl₀).1
    (deployed_reach_journalOk program hg hl₀).1 h₁ hf hlt hhead hrd hp

end Nanodregg.Kernel.Receive
