/-
# Spec.Proofs.Fork — A2′ FORK CONSISTENCY over the member's follower step

SUNDR's fork consistency at the deployed act (PROTOCOL-75: self-heads through the writer). A member
posts its own head `(steps, chain)` into a `Std.head` object of its World (`nd sync --post`); every
follow that absorbs a page carrying such a post walks the page against it (`Head.forkedSelfPost`).
The claim: whenever one frame of follow absorbs a page carrying a post of the head of ANOTHER fold
of the same start, at a position the page walks, either follow's log up to that position IS the
other fold's log (or two of the inputs the two folds' chains compare collide, an explicit list), or
the frame ends `refused forkedPost` and the page names a post whose position follow's own fold
passed with another chain. A writer that forks two members cannot show either a page that joins
the forks without the member saying so by name.

Premises (each a hypothesis of the claim, named):
* the two folds from one start `g` (`l₀` to follow's World, `lg` to the poster's): what makes the
  conclusion a statement about TWO members' histories (`fold_head_binds`);
* `f.world.steps < wg.steps`: a post at or behind follow's position is compared by the follow LOOP
  against its own Store (`Host.Follow.behindOr`, HOST-79), which is not a `System` field;
* `wg.steps ≤ f'.world.steps`: a post naming a step past the page's end is compared by NOBODY today
  (not the walk, not `behindOr`, and never again, since `selfPosts` reads only the cells a page
  touched), although an honest post always sits at an index past its own step count, so such a
  post is itself evidence of a fork or a forgery: cv task 01a17ac1-5204. Deleting this premise is
  that task's strengthening.

The refusal disjunct carries its evidence (the post and the fold that passed it with another
chain) because the reply cannot: `Command.refused` drops the step and poster, and a writer
refusal named `forkedPost` (`Refusal.host`) prints the same bytes (cv task 01a17ac1-5233).

What is owed: the `sync --to STEPS:CHAIN` arm (`absorbSync`'s anchor walk) as a second conjunct.
-/
import Spec.Proofs.Floor
import Spec.Sim.Fork
import Protocol.Proofs.Head
import Protocol.Proofs.Command
import Protocol.Proofs.PostOr
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The claim -/

/-- **A2′. Fork consistency of the member's follower.** One frame of follow that persists the
steps `ts` of a page, from a World `f.world` that is a fold of `l₀` from a start `g`: for every
self-head post the page carries (`Head.selfPosts`) that names the head of a World `wg`, a fold of
`lg` from the same `g`, at a step count the page walks (`f.world.steps < wg.steps ≤ f'.world.steps`):
follow's log up to that step count (the page's prefix of `wg.steps - f.world.steps` steps, fixed by
the premises) is `lg`, or two of the inputs the two folds' chains compare
collide; or the frame ends `refused forkedPost` and the page carries a post at a position follow's
own fold passed with another chain (the refusal is never free). -/
def ForkConsistent (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res : ByteArray)
    (ts : List (Step D × D)) (r : Command.Reply),
    S.follow me f kb res = (f', .steps ts, r) →
    ∀ {g wg : World D} {l₀ lg : List (Step D)} {m : Option D},
      S.fold g l₀ = .ok f.world → S.fold g lg = .ok wg →
      (wg.steps, S.X.env.bytes wg.chain, m) ∈ Head.selfPosts S.X f'.world ts →
      f.world.steps < wg.steps → wg.steps ≤ f'.world.steps →
      (l₀ ++ (ts.take (wg.steps - f.world.steps)).map Prod.fst = lg ∨
          CollidesAmong S.X.env.hash
            (foldPres S.X.env g (l₀ ++ (ts.take (wg.steps - f.world.steps)).map Prod.fst) ++
              foldPres S.X.env g lg)) ∨
      (∃ s c m', (s, c, m') ∈ Head.selfPosts S.X f'.world ts ∧
          (∃ pre post v, ts = pre ++ post ∧ S.fold f.world (pre.map Prod.fst) = .ok v ∧
            v.steps = s ∧ S.X.env.bytes v.chain ≠ c) ∧
          r = Command.refused (D := D) (.forkedPost s m'))

/-! ## The step lemma -/

/-- **What a frame that persists steps did**: nothing (no steps), or it absorbed a page
(`absorbSync`) whose steps are the ones persisted, follow's World is the page's end, and the reply
is `postOr`'s verdict on the page's self-head posts. (A sharpening of
`Protocol.Proofs.FollowHead.step_world`'s page arm with the reply.) -/
theorem step_steps {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)}
    {me : Command.Self D} {f f' : Command.Follow D} {kb res : ByteArray} {p : Command.Persist D}
    {ts : List (Step D × D)} {r : Command.Reply}
    (h : Command.step X dc B me f kb res = (f', p, r)) (hp : p = .steps ts) :
    ts = [] ∨ ∃ (cmd : Command.Cmd D) (evs : List ByteArray) (steps : Nat) (chain : ByteArray)
      (base : Nat) (wb : Option (World D)) (r₀ : Command.Reply),
      Command.absorbSync X me cmd f.world evs steps chain base = .ok (f'.world, ts, wb) ∧
      r = Command.postOr X f.world ts f'.world r₀ := by
  unfold Command.step at h
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := h)
  all_goals (try simp only [Command.Persist.steps.injEq, reduceCtorEq] at hp)
  all_goals first
    | exact .inl hp.symm
    | (subst hp; exact .inr ⟨_, _, _, _, _, _, _, ‹_›, rfl⟩)

omit [Ord D] [DecidableEq D] in
/-- The walk reaches every step count strictly after its start and no later than its end. -/
theorem anchorCheck_reached {E : Env D} {steps : Nat} {chain : ByteArray} :
    ∀ {s : Nat} {c : D} {ts : List (Step D × D)}, s < steps → steps ≤ s + ts.length →
      Head.anchorCheck E steps chain s c ts ≠ .unreached
  | _, _, [], h₁, h₂ => by simp only [List.length_nil] at h₂; omega
  | s, c, (t, r) :: rest, h₁, h₂ => by
      simp only [Head.anchorCheck]
      split
      · split <;> simp
      · rename_i hs
        simp only [List.length_cons] at h₂
        exact anchorCheck_reached (by omega) (by omega)

/-! ## The top theorem -/

/-- **A2′ of the deployed system**: `step_steps`, then `forkedSelfPost_none` (every post the page
walks is on follow's fold: `fold_head_binds` binds it to the other fold) or `forkedSelfPost_forked`
(the refusal names a post follow's own fold passed with another chain). -/
theorem top_forkConsistent (d : ByteArray → ByteArray) : ForkConsistent (deployed d) := by
  intro me f f' kb res ts r h g wg l₀ lg m h₀ hg hmem hlo hhi
  rw [fold_eq_world _ rfl rfl] at h₀ hg
  have h' : Command.step Host.Deployed.X Codec.Deployed.digestCodec (deployed d).B me f kb res =
      (f', .steps ts, r) := h
  rcases step_steps h' rfl with rfl | ⟨cmd, evs, steps, chain, base, wb, r₀, ha, hr⟩
  · simp [Head.selfPosts] at hmem
  · have hrf := Command.absorbPage_admits (Command.absorbSync_ok ha)
    have hlen : f'.world.steps = f.world.steps + ts.length := by
      rw [fold_steps (RootedFold.fold hrf), List.length_map]
    cases hfs : Head.forkedSelfPost Host.Deployed.X f.world ts f'.world with
    | none =>
      rcases Head.forkedSelfPost_none hrf hfs _ _ _ hmem with hu | ⟨pre, post, v, hts, hv, hvs, hvc⟩
      · exact absurd hu (anchorCheck_reached hlo (by omega))
      · have hfull : World.fold Host.Deployed.X.env g (l₀ ++ pre.map Prod.fst) = .ok v :=
          fold_append.mpr ⟨_, h₀, hv⟩
        have hpl : f.world.steps + pre.length = wg.steps := by
          rw [← hvs, fold_steps hv, List.length_map]
        have hpre : pre = ts.take (wg.steps - f.world.steps) := by
          rw [hts, List.take_left' (by omega)]
        subst hpre
        exact .inl (fold_head_binds deployed_lawful hfull hg hvs (deployed_lawful.bytes_inj hvc))
    | some sm =>
      obtain ⟨s, m'⟩ := sm
      obtain ⟨c, hc, pre, post, v, hts, hv, hvs, hvc⟩ := Head.forkedSelfPost_forked hrf hfs
      refine .inr ⟨s, c, m', hc, ⟨pre, post, v, hts, ?_, hvs, hvc⟩, ?_⟩
      · rw [fold_eq_world _ rfl rfl]; exact hv
      · rw [hr]; unfold Command.postOr; rw [hfs]

/-! ## The floor and the inhabited case (the trivial system and the run: `Spec.Sim.Fork`) -/

theorem refused_forkedPost (s : Nat) (m : Option Digest) :
    Command.refused (D := Digest) (.forkedPost s m) =
      .done CommandExit.refused.code.toUInt8 .empty forkedPostErr := rfl

theorem unforked_ne (r : Command.Reply) (s : Nat) (m : Option Digest) :
    unforked r ≠ Command.refused (D := Digest) (.forkedPost s m) := by
  rw [refused_forkedPost]
  cases r with
  | done e o err =>
    simp only [unforked]
    split
    · simp only [ne_eq, Command.Reply.done.injEq, not_and]
      intro h; exact absurd h (by decide)
    · rename_i hne
      simp only [ne_eq, Command.Reply.done.injEq, not_and]
      intro _ _ h; exact hne h
  | _ => simp [unforked]

theorem stepsOf_eq {p : Command.Persist Digest} (h : (stepsOf p).isSome = true) :
    p = .steps ((stepsOf p).getD []) := by
  cases p with
  | steps ts => rfl
  | adopt _ => simp [stepsOf] at h

/-- **The joining run**: follow, at genesis, absorbs fork A's page: it persists the page's steps,
which carry a post of fork B's head at step 1, a step the page walks; fork A's first step is not
fork B's, no two of the two prefixes' link inputs collide; and the deployed follower ends the
frame `refused forkedPost`. Fork B folds. -/
theorem run_forkedPost :
    (match World.fold Xd.env wGenesis wLog with
     | .ok wB =>
        match (deployed storeDigest).follow sMe ⟨wGenesis, none, none⟩ kKb kPage with
        | (f', p, r) =>
            (stepsOf p).isSome &&
              (Head.selfPosts Xd f'.world ((stepsOf p).getD [])).any
                (fun q => decide (q = (wB.steps, Xd.env.bytes wB.chain, some wMember))) &&
              decide (wB.steps = wGenesis.steps + 1) && decide (wB.steps ≤ f'.world.steps) &&
              decide ((((stepsOf p).getD []).take 1).map Prod.fst ≠ wLog) &&
              collisionFree Xd.env.hash
                (foldPres Xd.env wGenesis ((((stepsOf p).getD []).take 1).map Prod.fst) ++
                  foldPres Xd.env wGenesis wLog) &&
              forkedPostDone r
     | .error _ => false) = true := by
  native_decide

/-- The run, unpacked: a frame of the deployed follower from a World `g`, a fold of `g` to `w`,
and the facts the floor and the inhabited case read. -/
theorem run_unpacked :
    ∃ (g : World Digest) (lg : List (Step Digest)) (mm : Digest) (me : Command.Self Digest)
      (kb res : ByteArray) (f' : Command.Follow Digest) (p : Command.Persist Digest)
      (ts : List (Step Digest × Digest)) (r : Command.Reply) (w : World Digest),
      (deployed storeDigest).follow me ⟨g, none, none⟩ kb res = (f', p, r) ∧ p = .steps ts ∧
      World.fold Xd.env g lg = .ok w ∧
      (w.steps, Xd.env.bytes w.chain, some mm) ∈ Head.selfPosts Xd f'.world ts ∧
      w.steps = g.steps + 1 ∧ w.steps ≤ f'.world.steps ∧
      (ts.take 1).map Prod.fst ≠ lg ∧
      ¬ CollidesAmong Xd.env.hash (foldPres Xd.env g ((ts.take 1).map Prod.fst) ++ foldPres Xd.env g lg) ∧
      forkedPostDone r = true := by
  have hr := run_forkedPost
  revert hr
  generalize wGenesis = g
  generalize wLog = lg
  generalize wMember = mm
  generalize sMe = me
  generalize kKb = kb
  generalize kPage = res
  intro hr
  cases hgf : World.fold Xd.env g lg with
  | error e => rw [hgf] at hr; cases hr
  | ok w =>
    rw [hgf] at hr
    cases hR : (deployed storeDigest).follow me ⟨g, none, none⟩ kb res with
    | mk f' rest =>
      obtain ⟨p, r⟩ := rest
      rw [hR] at hr
      dsimp only at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨⟨⟨⟨⟨⟨hsome, hmem⟩, hs1⟩, hs2⟩, hne⟩, hcf⟩, hfp⟩ := hr
      obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp hmem
      simp only [decide_eq_true_eq] at hxe
      subst hxe
      exact ⟨g, lg, mm, me, kb, res, f', p, _, r, w, hR, stepsOf_eq hsome, hgf, hx, hs1, hs2, hne,
        not_collides hcf, hfp⟩

/-- **FLOOR (A2′).** The claim refuses the post-blind follower: on the joining run it persists a
page carrying fork B's head at a step it walks, follow's log up to there is not fork B's and no
listed input collides, and it does not end `refused forkedPost`. -/
theorem floor_forkConsistent : ¬ ForkConsistent (postBlind storeDigest) := by
  intro h
  obtain ⟨g, lg, mm, me, kb, res, f', p, ts, r, w, hR, rfl, hgf, hmem, hs1, hs2, hne, hcol, -⟩ := run_unpacked
  have ht : (postBlind storeDigest).follow me ⟨g, none, none⟩ kb res = (f', .steps ts, unforked r) := by
    show (((deployed storeDigest).follow me ⟨g, none, none⟩ kb res).1,
      ((deployed storeDigest).follow me ⟨g, none, none⟩ kb res).2.1,
      unforked ((deployed storeDigest).follow me ⟨g, none, none⟩ kb res).2.2) = _
    rw [hR]
  have hg : (postBlind storeDigest).fold g lg = .ok w := by
    rw [fold_eq_world _ rfl rfl]; exact hgf
  rcases h me ⟨g, none, none⟩ f' kb res ts (unforked r) ht (l₀ := []) rfl hg hmem (by simp only; omega) hs2 with
    (heq | hc) | ⟨s, c, m', -, -, hrr⟩
  · have hk : w.steps - g.steps = 1 := by omega
    simp only [hk, List.nil_append] at heq
    exact hne heq
  · have hk : w.steps - g.steps = 1 := by omega
    simp only [hk, List.nil_append] at hc
    exact hcol hc
  · exact unforked_ne r s m' hrr

/-- **INHABITED (A2′).** The deployed follower reaches the claim's refusal: at genesis it absorbs a
page carrying another fold's head at a step the page walks, and ends `refused forkedPost`. -/
theorem inhabited_forkConsistent :
    ∃ (me : Command.Self Digest) (f f' : Command.Follow Digest) (kb res : ByteArray)
      (ts : List (Step Digest × Digest)) (r : Command.Reply) (g wg : World Digest)
      (l₀ lg : List (Step Digest)) (m : Option Digest),
      (deployed storeDigest).follow me f kb res = (f', .steps ts, r) ∧
      (deployed storeDigest).fold g l₀ = .ok f.world ∧ (deployed storeDigest).fold g lg = .ok wg ∧
      (wg.steps, Xd.env.bytes wg.chain, m) ∈ Head.selfPosts Xd f'.world ts ∧
      f.world.steps < wg.steps ∧ wg.steps ≤ f'.world.steps ∧
      ∃ s m', r = Command.refused (D := Digest) (.forkedPost s m') := by
  obtain ⟨g, lg, mm, me, kb, res, f', p, ts, r, w, hR, rfl, hgf, hmem, hs1, hs2, -, -, hfp⟩ := run_unpacked
  refine ⟨me, ⟨g, none, none⟩, f', kb, res, ts, r, g, w, [], lg, some mm, hR, rfl,
    by rw [fold_eq_world _ rfl rfl]; exact hgf, hmem, by simp only; omega, hs2, 0, none, ?_⟩
  rw [refused_forkedPost]
  cases r with
  | done e o err =>
    simp only [forkedPostDone, Bool.and_eq_true, decide_eq_true_eq] at hfp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfp
    rfl
  | _ => simp [forkedPostDone] at hfp

end Nanodregg.Spec
