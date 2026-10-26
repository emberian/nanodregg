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
* `verified_ok`, `signer_ok`: what the two checks on an attestation establish;
* `forkedSelfPost_forked` / `forkedSelfPost_none` (PROTOCOL-75): a `forkedPost` names a post the page
  carries whose position follow's own fold reached with another chain (never free); no `forkedPost`
  means every post the page reaches is reached with the posted chain;
* `body_post`: the body follow plans for `sync --post OBJ` is `invoke OBJ post` of `headText` of the
  World it plans on: follow's OWN head (consent, the shape of `attestTip_sign`).
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

/-! ## Self-heads through the writer (PROTOCOL-75) -/

/-- **A `forkedPost` is never free**: the post it names is one the page carries (`selfPosts`), and
follow's own fold holds, at the post's step count, a prefix of the page whose chain is NOT the posted
one (`forked_on_fold`). -/
theorem forkedSelfPost_forked {X : Ctx D} {w w' : World D} {ts : List (Kernel.Step D × D)} {s : Nat}
    {m : Option D} (hr : World.RootedFold X.env w ts w') (h : forkedSelfPost X w ts w' = some (s, m)) :
    ∃ c, (s, c, m) ∈ selfPosts X w' ts ∧
      ∃ pre post v, ts = pre ++ post ∧ World.fold X.env w (pre.map Prod.fst) = .ok v ∧ v.steps = s ∧
        X.env.bytes v.chain ≠ c := by
  unfold forkedSelfPost at h
  obtain ⟨p, hp, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨s', c, m'⟩ := p
  simp only at hf
  split at hf
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨c, hp, forked_on_fold hr hk⟩
  · cases hf

/-- **No `forkedPost`: every post on the fold.** When the walk refuses nothing, every self-head post
the page carries is at a position the page does not reach from follow's position (`unreached`: before
it, compared through follow's Store, or past it), or is reached with the posted chain
(`shared_on_fold`). -/
theorem forkedSelfPost_none {X : Ctx D} {w w' : World D} {ts : List (Kernel.Step D × D)}
    (hr : World.RootedFold X.env w ts w') (h : forkedSelfPost X w ts w' = none) :
    ∀ s c m, (s, c, m) ∈ selfPosts X w' ts →
      anchorCheck X.env s c w.steps w.chain ts = .unreached ∨
      ∃ pre post v, ts = pre ++ post ∧ World.fold X.env w (pre.map Prod.fst) = .ok v ∧ v.steps = s ∧
        X.env.bytes v.chain = c := by
  intro s c m hm
  unfold forkedSelfPost at h
  have hz := List.findSome?_eq_none_iff.mp h _ hm
  simp only at hz
  cases hk : anchorCheck X.env s c w.steps w.chain ts with
  | shared => exact .inr (shared_on_fold hr hk)
  | unreached => exact .inl rfl
  | forked => simp [hk] at hz

/-- **Consent: `sync --post` posts follow's OWN head.** The body follow plans for `sync --post OBJ` is
`invoke OBJ post` with the arguments read, at the head package's argument type, from `headText` of
the World it plans on: the chain, height, roots and step count of follow's own fold, never a
continuation's or a result's (the body is re-derived from the argv at phases 2 and 3). -/
theorem body_post {X : Ctx D} {me : Command.Self D} {w : World D} {s : Command.Signed} {o : D}
    {b : Body D} (h : Command.body X me w s (.post o) = .ok b) :
    ∃ p args, Command.invokedPackage X w o = .ok p ∧
      Lang.argsOf X.digestOf (Command.worldLook X.env w) p postMethod (headText X w) = .ok args ∧
      b = .invoke o postMethod args Command.invokeBudget none := by
  unfold Command.body at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i args ha
      cases h
      exact ⟨p, args, hp, ha, rfl⟩
    · cases h

end Nanodregg.Protocol.Head
