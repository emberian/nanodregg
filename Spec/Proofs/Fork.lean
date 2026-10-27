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

The other arm, `nd sync --to STEPS:CHAIN` (PROTOCOL-74: the member BEHIND catches up to another's
stated head), is `ForkConsistent.sync` below, with its own floor (`syncBlind`) and inhabited run.
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
    (ts = [] ∧ f'.world = f.world) ∨ ∃ (cmd : Command.Cmd D) (evs : List ByteArray) (steps : Nat)
      (chain : ByteArray) (base : Nat) (wb : Option (World D)) (cert : ByteArray) (r₀ : Command.Reply),
      Command.absorbSync X me cmd f.world evs steps chain base = .ok (f'.world, ts, wb) ∧
      r = Command.postOr X f.world ts f'.world cert r₀ ∧
      ∃ st, Command.State.ofBytes kb = some st ∧ Command.parse X.digestOf st.argv = .ok cmd := by
  unfold Command.step at h
  cases hst : Command.State.ofBytes kb with
  | none =>
    rw [hst] at h
    dsimp only at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Command.Persist.steps.injEq] at hp
    exact .inl ⟨hp.symm, rfl⟩
  | some st =>
    rw [hst] at h
    simp only [Option.map_some, Option.getD_some] at h
    cases hpa : Command.parse X.digestOf st.argv with
    | error r =>
      rw [hpa] at h
      dsimp only at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Command.Persist.steps.injEq] at hp
      exact .inl ⟨hp.symm, rfl⟩
    | ok cmd =>
      rw [hpa] at h
      dsimp only at h
      repeat' split at h
      all_goals (try simp only [Prod.mk.injEq] at h)
      all_goals (repeat' split at h)
      all_goals (try simp only [Prod.mk.injEq] at h)
      all_goals (obtain ⟨rfl, rfl, rfl⟩ := h)
      all_goals (try simp only [Command.Persist.steps.injEq, reduceCtorEq] at hp)
      all_goals first
        | exact .inl ⟨hp.symm, rfl⟩
        | (subst hp; exact .inr ⟨_, _, _, _, _, _, _, _, ‹_›, rfl, st, rfl, hpa⟩)

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
  rcases step_steps h' rfl with ⟨rfl, -⟩ | ⟨cmd, evs, steps, chain, base, wb, cert, r₀, ha, hr, -⟩
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

/-! ## A2′, the `sync --to` arm (PROTOCOL-74) -/

/-- **A2′ (sync). A member that catches up TO another member's stated head holds that member's
history up to it.** A frame of `sync --to STEPS:CHAIN` (the continuation's argv parses so) that
persists the page steps `ts` and moves follow's World from below the anchor's step count to it or
past it, where follow's World is a fold of `l₀` from `g` and the anchor is the head of a World `wg`
folded by `lg` from the same `g`: follow's log up to the anchor (the page's prefix of
`steps - f.world.steps` steps, fixed by the premises) is `lg`, or two of the listed inputs collide.
A page that would carry follow past the anchor on another chain is refused (`forkedWorld`, nothing
kept) or does not reach the position on this frame; either way the World stays below it, outside
the premise. -/
def ForkConsistent.sync (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res : ByteArray)
    (ts : List (Step D × D)) (r : Command.Reply) (st : Command.State) (steps : Nat) (chain : ByteArray),
    Command.State.ofBytes kb = some st →
    Command.parse S.X.digestOf st.argv = .ok (.sync (.to steps chain)) →
    S.follow me f kb res = (f', .steps ts, r) →
    ∀ {g wg : World D} {l₀ lg : List (Step D)},
      S.fold g l₀ = .ok f.world → S.fold g lg = .ok wg →
      wg.steps = steps → S.X.env.bytes wg.chain = chain →
      f.world.steps < steps → steps ≤ f'.world.steps →
      l₀ ++ (ts.take (steps - f.world.steps)).map Prod.fst = lg ∨
        CollidesAmong S.X.env.hash
          (foldPres S.X.env g (l₀ ++ (ts.take (steps - f.world.steps)).map Prod.fst) ++
            foldPres S.X.env g lg)

/-- What `absorbSync` accepted under `sync --to`: the walk did not find the anchor forked. -/
theorem absorbSync_to {X : Ctx D} {me : Command.Self D} {w w' : World D} {evs : List ByteArray}
    {s n b : Nat} {c ch : ByteArray} {ts : List (Step D × D)} {wb : Option (World D)}
    (h : Command.absorbSync X me (.sync (.to s c)) w evs n ch b = .ok (w', ts, wb)) :
    Head.anchorCheck X.env s c w.steps w.chain ts ≠ .forked := by
  unfold Command.absorbSync at h
  split at h
  · cases h
  · simp only [Command.syncAnchor] at h
    split at h
    · cases h
    · rename_i hne
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact hne

/-- **A2′ (sync) of the deployed system**: `step_steps` (the frame absorbed a page under the
continuation's own command), `absorbSync_to` (the walk was not `forked`), `anchorCheck_reached`
(nor `unreached`), so `shared`: `anchorCheck_shared`, then `anchor_binds`. -/
theorem top_forkConsistent_sync (d : ByteArray → ByteArray) : ForkConsistent.sync (deployed d) := by
  intro me f f' kb res ts r st steps chain hst hpa h g wg l₀ lg h₀ hg hws hwc hlo hhi
  rw [fold_eq_world _ rfl rfl] at h₀ hg
  have h' : Command.step Host.Deployed.X Codec.Deployed.digestCodec (deployed d).B me f kb res =
      (f', .steps ts, r) := h
  rcases step_steps h' rfl with ⟨-, hw⟩ | ⟨cmd, evs, n, ch, base, wb, -, r₀, ha, -, st', hst', hpa'⟩
  · rw [hw] at hhi; omega
  · rw [hst] at hst'
    obtain rfl := Option.some.inj hst'
    have hpa₀ : Command.parse Host.Deployed.X.digestOf st.argv = .ok (.sync (.to steps chain)) := hpa
    rw [hpa₀] at hpa'
    obtain rfl := (Except.ok.inj hpa').symm
    have hrf := Command.absorbPage_admits (Command.absorbSync_ok ha)
    have hlen : f'.world.steps = f.world.steps + ts.length := by
      rw [fold_steps (RootedFold.fold hrf), List.length_map]
    have hnf := absorbSync_to ha
    have hnu := anchorCheck_reached (E := Host.Deployed.X.env) (chain := chain) (c := f.world.chain)
      (ts := ts) hlo (by omega)
    cases hk : Head.anchorCheck Host.Deployed.X.env steps chain f.world.steps f.world.chain ts with
    | forked => exact absurd hk hnf
    | unreached => exact absurd hk hnu
    | shared =>
      obtain ⟨pre, post, hts, hl, hc⟩ := Head.anchorCheck_shared hk
      have hpre : pre = ts.take (steps - f.world.steps) := by
        rw [hts, List.take_left' (by omega)]
      rw [hts] at hrf
      have hb := Head.anchor_binds deployed_lawful h₀ hrf (hl.trans hws.symm)
        (hc.trans hwc.symm) hg
      rw [← hpre]
      exact hb

theorem toAnchor_eq {e : Except Command.ParseRefusal (Command.Cmd Digest)} {s : Nat} {c : ByteArray}
    (h : toAnchor e = some (s, c)) : e = .ok (.sync (.to s c)) := by
  unfold toAnchor at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

/-- The sync runs' facts, read back (generic in the system and the inputs). -/
theorem syncRunOk_sound {S : System Digest} {me : Command.Self Digest} {g : World Digest}
    {kb res : ByteArray} {lg : List (Step Digest)} (h : syncRunOk S me g kb res lg = true) :
    ∃ st wg f' ts r, Command.State.ofBytes kb = some st ∧
      Command.parse Xd.digestOf st.argv = .ok (.sync (.to wg.steps (Xd.env.bytes wg.chain))) ∧
      World.fold Xd.env g lg = .ok wg ∧ S.follow me ⟨g, none, none⟩ kb res = (f', .steps ts, r) ∧
      wg.steps = g.steps + 1 ∧ wg.steps ≤ f'.world.steps := by
  unfold syncRunOk at h
  cases hgf : World.fold Xd.env g lg with
  | error e => rw [hgf] at h; cases h
  | ok wg =>
    rw [hgf] at h
    cases hs : Command.State.ofBytes kb with
    | none => rw [hs] at h; simp at h
    | some st =>
      cases hR : S.follow me ⟨g, none, none⟩ kb res with
      | mk f' rest =>
        obtain ⟨p, r⟩ := rest
        rw [hs, hR] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨ha, ⟨hsome, hs1⟩, hs2⟩ := h
        exact ⟨st, wg, f', _, r, rfl, toAnchor_eq ha, rfl, by rw [← stepsOf_eq hsome], hs1, hs2⟩

theorem syncRunJoins_sound {S : System Digest} {me : Command.Self Digest} {g : World Digest}
    {kb res : ByteArray} {lg : List (Step Digest)} {f' : Command.Follow Digest}
    {ts : List (Step Digest × Digest)} {r : Command.Reply}
    (h : syncRunJoins S me g kb res lg = true) (hR : S.follow me ⟨g, none, none⟩ kb res = (f', .steps ts, r)) :
    (ts.take 1).map Prod.fst ≠ lg ∧
      ¬ CollidesAmong Xd.env.hash (foldPres Xd.env g ((ts.take 1).map Prod.fst) ++ foldPres Xd.env g lg) := by
  unfold syncRunJoins at h
  rw [hR] at h
  simp only [stepsOf, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, not_collides h.2⟩

/-- **The sync runs**: the post-blind-to-anchors follower, told `sync --to` fork B's head at step 1,
walks the joining page past it (its first step is not fork B's, no listed input collides); the
deployed follower, told `sync --to` fork A's own head at step 1, walks the same page past it. -/
theorem run_syncBlind :
    (syncRunOk (syncBlind storeDigest) sMe wGenesis kToKb kPage wLog &&
      syncRunJoins (syncBlind storeDigest) sMe wGenesis kToKb kPage wLog) = true := by
  native_decide

theorem run_syncShared : syncRunOk (deployed storeDigest) sMe wGenesis kToKbA kPage kLogA = true := by
  native_decide

/-- **FLOOR (A2′, sync).** The claim refuses the follower that reads `sync --to` as `sync`: on the
joining page it walks past fork B's head with fork A's chain. -/
theorem floor_forkConsistent_sync : ¬ ForkConsistent.sync (syncBlind storeDigest) := by
  intro h
  have hr := run_syncBlind
  simp only [Bool.and_eq_true] at hr
  obtain ⟨st, wg, f', ts, r, hst, hpa, hgf, hR, hs1, hs2⟩ := syncRunOk_sound hr.1
  obtain ⟨hne, hcol⟩ := syncRunJoins_sound hr.2 hR
  have hg : (syncBlind storeDigest).fold wGenesis wLog = .ok wg := by
    rw [fold_eq_world _ rfl rfl]; exact hgf
  rcases h sMe ⟨wGenesis, none, none⟩ f' kToKb kPage ts r st _ _ hst hpa hR (l₀ := []) rfl hg rfl rfl
      (by simp only; omega) hs2 with heq | hc
  · have hk : wg.steps - wGenesis.steps = 1 := by omega
    simp only [hk, List.nil_append] at heq
    exact hne heq
  · have hk : wg.steps - wGenesis.steps = 1 := by omega
    simp only [hk, List.nil_append] at hc
    exact hcol hc

/-- **INHABITED (A2′, sync).** The deployed follower, told to catch up to fork A's own head at step 1,
moves past it on the joining page: the claim's premise holds of the deployed system. -/
theorem inhabited_forkConsistent_sync :
    ∃ (me : Command.Self Digest) (f f' : Command.Follow Digest) (kb res : ByteArray)
      (ts : List (Step Digest × Digest)) (r : Command.Reply) (st : Command.State) (g wg : World Digest)
      (l₀ lg : List (Step Digest)),
      Command.State.ofBytes kb = some st ∧
      Command.parse Xd.digestOf st.argv = .ok (.sync (.to wg.steps (Xd.env.bytes wg.chain))) ∧
      (deployed storeDigest).follow me f kb res = (f', .steps ts, r) ∧
      (deployed storeDigest).fold g l₀ = .ok f.world ∧ (deployed storeDigest).fold g lg = .ok wg ∧
      f.world.steps < wg.steps ∧ wg.steps ≤ f'.world.steps := by
  obtain ⟨st, wg, f', ts, r, hst, hpa, hgf, hR, hs1, hs2⟩ := syncRunOk_sound run_syncShared
  exact ⟨sMe, ⟨wGenesis, none, none⟩, f', kToKbA, kPage, ts, r, st, wGenesis, wg, [], kLogA, hst, hpa,
    hR, rfl, by rw [fold_eq_world _ rfl rfl]; exact hgf, by simp only; omega, hs2⟩

end Nanodregg.Spec
