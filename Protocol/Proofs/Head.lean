/-
# Protocol.Proofs.Head — the anchor is on follow's fold, or the World forked (PROTOCOL-74)

* `anchorCheck_shared` / `anchorCheck_forked`: what the walk found is a prefix of the page's steps
  whose chain, advanced from follow's position exactly as `chainOf` advances it, is the anchor's or
  is not;
* `shared_on_fold` / `forked_on_fold`: over a page follow absorbed (`World.RootedFold` from its
  World, `absorbPage_admits`), that prefix FOLDS, from follow's World, to a World at the anchor's
  step count whose chain is the anchor's or is not;
* `anchor_binds`: **the member-facing statement.** Follow's World is a fold from a start `g`; it
  absorbed a page and passed the anchor `shared`; the other member's World `wg` is a fold from the
  same `g` at the anchor's `(steps, chain)`. Then follow's log up to the anchor IS the other
  member's log, or two of the inputs the two folds' chains compare collide (`fold_head_binds`);
* `forked_not_on_fold`: a `forked` walk is never free: follow's own fold holds, at the anchor's
  step count, a chain that is not the anchor's, so no log that reaches the anchor from `g` is
  follow's log up to there;
* `attestTip_sign`: the message follow offers custody under `sync --attest` is `Head.message` of
  follow's OWN World's head (consent, in the shape of `step_submit_planned`);
* `verified_ok`, `signer_ok`: what the two checks on an attestation establish.
-/
import Protocol.Command.Machine
import Kernel.Proofs.RootedFold
import Kernel.Proofs.Fold

namespace Nanodregg.Protocol.Head

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem Refusal.name_injective (a b : Refusal) (h : a.name = b.name) : a.tag = b.tag := by
  cases a <;> cases b <;> simp_all [Refusal.name, Refusal.tag]

theorem Refusal.all_complete (r : Refusal) : r ∈ Refusal.all := by cases r <;> decide

/-! ## The two checks on an attestation -/

omit [Ord D] in
/-- What `verified` accepted: the bytes decode to it, it names `origin`, and its signature verifies
under the key it names. -/
theorem verified_ok {X : Ctx D} {origin : D} {b : ByteArray} {a : Attestation D}
    (h : verified X origin b = .ok a) :
    ofBytes X b = some a ∧ a.head.origin = origin ∧
      X.verify a.key (message a.unsigned) a.signature = true := by
  unfold verified at h
  split at h
  · cases h
  · rename_i i hb
    split at h
    · cases h
    · rename_i ho
      split at h
      · cases h
      · rename_i hv
        cases h
        exact ⟨hb, by simpa using ho, by simpa using hv⟩

/-- What `signer` accepted: the member is live on `w` and the key named is its current one. -/
theorem signer_ok {X : Ctx D} {w : World D} {a : Attestation D} (h : signer X w a = .ok ()) :
    currentKey X.env w a.member = some a.key := by
  unfold signer at h
  split at h
  · cases h
  · rename_i k hk
    split at h
    · rename_i hkk; rw [hk, hkk]
    · cases h

/-! ## The walk -/

omit [Ord D] [DecidableEq D] in
/-- `shared`: a non-empty prefix of the steps reaches the anchor's step count with its chain. -/
theorem anchorCheck_shared {E : Env D} {steps : Nat} {chain : ByteArray} :
    ∀ {s : Nat} {c : D} {ts : List (Kernel.Step D × D)}, anchorCheck E steps chain s c ts = .shared →
      ∃ pre post, ts = pre ++ post ∧ s + pre.length = steps ∧ E.bytes (chainOf E c pre) = chain
  | _, _, [], h => by simp [anchorCheck] at h
  | s, c, (t, r) :: rest, h => by
      simp only [anchorCheck] at h
      split at h
      · rename_i hs
        split at h
        · rename_i hc
          exact ⟨[(t, r)], rest, rfl, by simpa using hs, by simpa [chainOf] using hc⟩
        · cases h
      · obtain ⟨pre, post, rfl, hl, hc⟩ := anchorCheck_shared h
        exact ⟨(t, r) :: pre, post, rfl, by simp only [List.length_cons]; omega,
          by simpa [chainOf] using hc⟩

omit [Ord D] [DecidableEq D] in
/-- `forked`: a non-empty prefix of the steps reaches the anchor's step count with ANOTHER chain. -/
theorem anchorCheck_forked {E : Env D} {steps : Nat} {chain : ByteArray} :
    ∀ {s : Nat} {c : D} {ts : List (Kernel.Step D × D)}, anchorCheck E steps chain s c ts = .forked →
      ∃ pre post, ts = pre ++ post ∧ s + pre.length = steps ∧ E.bytes (chainOf E c pre) ≠ chain
  | _, _, [], h => by simp [anchorCheck] at h
  | s, c, (t, r) :: rest, h => by
      simp only [anchorCheck] at h
      split at h
      · rename_i hs
        split at h
        · cases h
        · rename_i hc
          exact ⟨[(t, r)], rest, rfl, by simpa using hs, by simpa [chainOf] using hc⟩
      · obtain ⟨pre, post, rfl, hl, hc⟩ := anchorCheck_forked h
        exact ⟨(t, r) :: pre, post, rfl, by simp only [List.length_cons]; omega,
          by simpa [chainOf] using hc⟩

/-- A rooted run over `l₁ ++ l₂` is a rooted run over `l₁` to some state, then one over `l₂`. -/
theorem rooted_split {W T R N : Type} {admit : W → T → Except R W} {note : W → N} :
    ∀ {w w' : W} {l₁ l₂ : List (T × N)}, Rooted admit note w (l₁ ++ l₂) w' →
      ∃ v, Rooted admit note w l₁ v ∧ Rooted admit note v l₂ w'
  | w, _, [], _, h => ⟨w, by simp only [Rooted], h⟩
  | _, _, (_, _) :: _, _, h => by
      obtain ⟨w₁, ha, hn, hr⟩ := h
      obtain ⟨v, h₁, h₂⟩ := rooted_split hr
      exact ⟨v, ⟨w₁, ha, hn, h₁⟩, h₂⟩

/-- **The anchor is on follow's fold**: a page follow absorbed from its World `w` (`absorbPage_admits`)
whose walk is `shared` holds a prefix that folds, from `w`, to a World at the anchor's step count
with the anchor's chain. -/
theorem shared_on_fold {E : Env D} {w w' : World D} {ts : List (Kernel.Step D × D)} {steps : Nat}
    {chain : ByteArray} (hr : World.RootedFold E w ts w')
    (hs : anchorCheck E steps chain w.steps w.chain ts = .shared) :
    ∃ pre post v, ts = pre ++ post ∧ World.fold E w (pre.map Prod.fst) = .ok v ∧ v.steps = steps ∧
      E.bytes v.chain = chain := by
  obtain ⟨pre, post, rfl, hl, hc⟩ := anchorCheck_shared hs
  obtain ⟨v, h₁, -⟩ := rooted_split hr
  refine ⟨pre, post, v, rfl, RootedFold.fold h₁, ?_, ?_⟩
  · rw [fold_steps (RootedFold.fold h₁), List.length_map]; exact hl
  · rw [RootedFold.chain h₁]; exact hc

/-- **A fork is never free**: a `forked` walk holds a prefix that folds, from `w`, to a World at the
anchor's step count whose chain is NOT the anchor's. -/
theorem forked_on_fold {E : Env D} {w w' : World D} {ts : List (Kernel.Step D × D)} {steps : Nat}
    {chain : ByteArray} (hr : World.RootedFold E w ts w')
    (hs : anchorCheck E steps chain w.steps w.chain ts = .forked) :
    ∃ pre post v, ts = pre ++ post ∧ World.fold E w (pre.map Prod.fst) = .ok v ∧ v.steps = steps ∧
      E.bytes v.chain ≠ chain := by
  obtain ⟨pre, post, rfl, hl, hc⟩ := anchorCheck_forked hs
  obtain ⟨v, h₁, -⟩ := rooted_split hr
  refine ⟨pre, post, v, rfl, RootedFold.fold h₁, ?_, ?_⟩
  · rw [fold_steps (RootedFold.fold h₁), List.length_map]; exact hl
  · rw [RootedFold.chain h₁]; exact hc

/-- **Two members that compare heads hold one history up to the anchor** (DESIGN-TRUST T1; the
fork-consistency half of TOPLEVEL-SPEC §2.3 at the deployed act). Follow's World `w` is a fold of
`l₀` from a start `g`; it absorbed a page `pre ++ post` whose prefix `pre` reaches the other member's
step count with its chain (what a `shared` walk found: `anchorCheck_shared` gives exactly `pre`, `hl`
and `hc`); the other member's World `wg` is a fold of `lg` from the same `g`. Then follow's log up to
the anchor is `lg`, or two of the inputs the two folds' chains compare collide (`fold_head_binds`;
the lists are fixed by the premises, GATES-20s). -/
theorem anchor_binds {E : Env D} {n : Nat} (hE : E.Lawful n) {g w w' wg : World D}
    {l₀ lg : List (Kernel.Step D)} {pre post : List (Kernel.Step D × D)}
    (h₀ : World.fold E g l₀ = .ok w) (hr : World.RootedFold E w (pre ++ post) w')
    (hl : w.steps + pre.length = wg.steps) (hc : E.bytes (chainOf E w.chain pre) = E.bytes wg.chain)
    (hg : World.fold E g lg = .ok wg) :
    l₀ ++ pre.map Prod.fst = lg ∨
      CollidesAmong E.hash (foldPres E g (l₀ ++ pre.map Prod.fst) ++ foldPres E g lg) := by
  obtain ⟨v, h₁, -⟩ := rooted_split hr
  have hf := RootedFold.fold h₁
  have hfull : World.fold E g (l₀ ++ pre.map Prod.fst) = .ok v := fold_append.mpr ⟨w, h₀, hf⟩
  have hst : v.steps = wg.steps := by rw [fold_steps hf, List.length_map]; exact hl
  have hch : v.chain = wg.chain := hE.bytes_inj (by rw [RootedFold.chain h₁]; exact hc)
  exact fold_head_binds hE hfull hg hst hch

/-- **A `forked` walk names two histories**: no log that reaches the other member's head from `g`
is follow's log up to the anchor. -/
theorem forked_not_on_fold {E : Env D} {g w w' wg : World D} {l₀ lg : List (Kernel.Step D)}
    {ts : List (Kernel.Step D × D)}
    (h₀ : World.fold E g l₀ = .ok w) (hr : World.RootedFold E w ts w')
    (hs : anchorCheck E wg.steps (E.bytes wg.chain) w.steps w.chain ts = .forked)
    (hg : World.fold E g lg = .ok wg) :
    ∃ pre post, ts = pre ++ post ∧ l₀ ++ pre.map Prod.fst ≠ lg := by
  obtain ⟨pre, post, v, rfl, hf, -, hc⟩ := forked_on_fold hr hs
  refine ⟨pre, post, rfl, fun he => hc ?_⟩
  have hfull : World.fold E g (l₀ ++ pre.map Prod.fst) = .ok v := fold_append.mpr ⟨w, h₀, hf⟩
  rw [he] at hfull
  rw [fold_det hfull hg]

/-! ## Consent: the message follow signs under `sync --attest` is its own head's -/

omit [DecidableEq D] in
/-- Every `sign` the attest tip hands out carries `Head.message` of follow's OWN World's head, with
the member and the key the envelope was signed by: a continuation or a result cannot steer it. -/
theorem attestTip_sign {X : Ctx D} {me : Command.Self D} {w : World D} {argv : List ByteArray}
    {sb m k : ByteArray} (h : Command.attestTip X me w argv sb = .sign m k) :
    ∃ s u, Command.Signed.ofBytes sb = some s ∧
      unsignedBytes X.env (headOf X.env w) me.member s.key = some u ∧ m = message u := by
  unfold Command.attestTip at h
  split at h
  · simp [Command.refused] at h
  · rename_i s hs
    split at h
    · simp [Command.refused] at h
    · rename_i u hu
      unfold Command.next at h
      split at h
      · simp only [Command.Reply.sign.injEq] at h
        exact ⟨s, u, hs, hu, h.1.symm⟩
      · simp [Command.refused] at h

end Nanodregg.Protocol.Head
