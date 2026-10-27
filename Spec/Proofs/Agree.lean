/-
# Spec.Proofs.Agree — A1′: an honest writer's page moves follow to the writer's World

TOPLEVEL-SPEC §2.2 (completeness; the writer–follower agreement). **The claim**
(`Agree.pageAbsorbs`): from a World whose rows are canonical, whatever batch the system's writer
admits (its machine over `S.handle`, the World's roots as each step's note), the system's follower
(`S.follow`, one frame of the member's command machine) at the log phase of a command without an
anchor, standing at that World and handed the writer's `log` page of exactly what the batch staged
(its events, the writer's World after the batch as the page's end and tip), moves to the World the
writer keeps. Stated at the step `host follow` runs, so a follower that does not take honest pages
is refused.

**Premises**, each needed:
* the call codec canonical (`decodeCall b = some c → callBytes c = b`): what makes a logged event
  decode to the call the writer judged (deployed: `Codec.Deployed.eq_callBytes_of_decodeCall`).
* `w.RowsCanon`: the one invariant `absorbStep` re-derivation reads (every `Kept` World has it).
* the batch staged at most `pageStepsMax` steps: a page holds no more (a longer batch is served
  over several pages; this claim is about one page).
* the follower's frame: its World is `w`, its continuation is a log phase (2) of a command other
  than `init` (whose phase 2 is custody's) and without a `sync --to`/`--check` anchor (whose
  fork walk is A2′'s), the reply is an `ok` holding that page.

**Top** `top_agree_pageAbsorbs`: `host_run_folds`, `Machine.staged_rooted`/`machine_commits` and
`honest_page_absorbed` (`Host/Proofs/Refine.lean`) give `absorbPage` of the page; `step_page_world`
(here, over `Command.step`'s log arm) lifts it to the step. **Floor** `floor_agree_pageAbsorbs`: the
deaf follower (`Spec.Sim.Agree.deafFollower`), on the founder's rotate batch. **Inhabited**
`inhabited_agree_pageAbsorbs`: the deployed follower moves on that page, to a World one step on.

**Owed (the gap)**: the page is stated as what the batch staged. That the deployed pager
(`Host.Page.kept` over the durable records) serves exactly those events and that end is IO and not
proved here (`Host/Proofs/Refine.lean`'s header: no theorem ties the segment's bytes to what
`admitBatch` staged).
-/
import Spec.Proofs.Cap
import Spec.Sim.Agree
import Host.Proofs.Refine
import Protocol.Proofs.Command

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- **A1′. An honest writer's page absorbs.** -/
def Agree.pageAbsorbs (S : System D) : Prop :=
  (∀ b c, S.X.decodeCall b = some c → S.X.callBytes c = b) →
  ∀ {w : World D} {qs : List (Host.Request Host.Frame)}, w.RowsCanon S.X.env →
    let r := ({ note := World.roots S.X.env, handle := S.handle, ok := Status.ok.code } :
      Host.Machine (World D) (Step D) Host.Frame D).admitBatch w qs
    r.2.staged.size ≤ Bounds.pageStepsMax →
    ∀ {me : Command.Self D} {f : Command.Follow D} {kb result p a sb pb ub tb : ByteArray}
      {st : Command.State} {cmd : Command.Cmd D} {pg : Command.LogPage} {pages : Nat},
      f.world = w → Command.State.ofBytes kb = some st → Command.parse S.X.digestOf st.argv = .ok cmd →
      st.phase = 2 → st.acc = [a, sb, pb, ub, tb] → Text.ofU64 pb = some pages →
      (∀ s, cmd ≠ .init s) → Command.syncAnchor S.X me cmd = none →
      Command.hostReply result = some (.ok, p) → Command.logPage p = some pg →
      pg.events = r.2.staged.toList.map (Host.Page.stepEvent ∘ Prod.fst) → pg.steps = r.1.steps →
      pg.chain = S.X.env.bytes r.1.chain → pg.tipSteps = r.1.steps →
      (S.follow me f kb result).1.world = r.1

theorem absorbSync_none {X : Ctx D} {me : Command.Self D} {cmd : Command.Cmd D} {w : World D}
    {evs : List ByteArray} {steps base : Nat} {chain : ByteArray} (h : Command.syncAnchor X me cmd = none) :
    Command.absorbSync X me cmd w evs steps chain base = Command.absorbPage X w evs steps chain base := by
  unfold Command.absorbSync
  rw [h]
  cases Command.absorbPage X w evs steps chain base <;> rfl

/-- **The log arm of follow's step**: at a log phase of a command other than `init`, an `ok` reply
holding a page whose stated end is its tip, absorbed by `absorbSync` to `w'`, moves follow to `w'`. -/
theorem step_page_world {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Command.Self D}
    {f : Command.Follow D} {kb result p a sb pb ub tb : ByteArray} {st : Command.State} {cmd : Command.Cmd D}
    {pg : Command.LogPage} {pages : Nat} {w' : World D} {ts : List (Step D × D)} {wb : Option (World D)}
    (hk : Command.State.ofBytes kb = some st) (hp : Command.parse X.digestOf st.argv = .ok cmd)
    (hph : st.phase = 2) (hacc : st.acc = [a, sb, pb, ub, tb]) (hi : ∀ s, cmd ≠ .init s)
    (hr : Command.hostReply result = some (.ok, p)) (hpg : Command.logPage p = some pg)
    (hpages : Text.ofU64 pb = some pages) (htip : ¬ pg.steps < pg.tipSteps)
    (hs : Command.absorbSync X me cmd f.world pg.events pg.steps pg.chain pg.baseSteps = .ok (w', ts, wb)) :
    (Command.step X dc B me f kb result).1.world = w' := by
  obtain ⟨argv, phase, acc⟩ := st
  simp only at hph hacc hp
  subst hph hacc
  have hcp : Command.custodyPhase false 2 = false := by decide
  have hsr : Command.stepResult (D := D) false 2 result = .ok result := by
    simp only [Command.stepResult, hcp, Bool.false_eq_true, ↓reduceIte]
  have hne : (pg.events.isEmpty && decide (pg.steps < pg.tipSteps)) = false := by simp [htip]
  unfold Command.step
  simp only [hk, Option.map_some, Option.getD_some, hp]
  cases cmd
  case init s => exact absurd rfl (hi s)
  all_goals
    simp only [hsr, hr, hpg, hpages, hne, hs, Bool.false_eq_true, ↓reduceIte]
    repeat' split
    all_goals first | rfl | simp_all

/-- **What a batch stages, as one page, `absorbPage` takes to the World the writer keeps**, wherever
the page's stated base cuts it (`host_run_folds`, `staged_rooted`, `honest_page_absorbed`). -/
theorem batch_page_absorbed (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {w : World D} (hcr : w.RowsCanon X.env) (qs : List (Host.Request Host.Frame))
    (hn : ((Host.machine X).admitBatch w qs).2.staged.size ≤ Bounds.pageStepsMax) (base : Nat) :
    ∃ wb?, Command.absorbPage X w
      (((Host.machine X).admitBatch w qs).2.staged.toList.map (Host.Page.stepEvent ∘ Prod.fst))
      ((Host.machine X).admitBatch w qs).1.steps (X.env.bytes ((Host.machine X).admitBatch w qs).1.chain) base =
        .ok (((Host.machine X).admitBatch w qs).1, ((Host.machine X).admitBatch w qs).2.staged.toList, wb?) := by
  obtain ⟨l, -, -, hh, hs⟩ := Host.host_run_folds X hX qs w {}
  have hs' : ((Host.machine X).admitBatch w qs).2.staged.toList.map Prod.fst = l := by
    simpa using hs
  have hr := (Host.machine X).staged_rooted (Host.machine_commits X) w qs
  rw [← hs'] at hh
  exact Host.honest_page_absorbed base hcr hr hh (by simpa using hn)

end

/-- **A1′ of the deployed system.** -/
theorem top_agree_pageAbsorbs (d : ByteArray → ByteArray) : Agree.pageAbsorbs (deployed d) := by
  intro hX w qs hcr r hn me f kb result p a sb pb ub tb st cmd pg pages hw hk hp hph hacc hpages hi hsa hr
    hpg hev hst hch htip
  have hX' : ∀ b c, Xd.decodeCall b = some c → Xd.callBytes c = b := hX
  have hcr' : w.RowsCanon Xd.env := hcr
  have hn' : ((Host.machine Xd).admitBatch w qs).2.staged.size ≤ Bounds.pageStepsMax := hn
  have hp' : Command.parse Xd.digestOf st.argv = .ok cmd := hp
  have hsa' : Command.syncAnchor Xd me cmd = none := hsa
  have hev' : pg.events = ((Host.machine Xd).admitBatch w qs).2.staged.toList.map (Host.Page.stepEvent ∘ Prod.fst) := hev
  have hst' : pg.steps = ((Host.machine Xd).admitBatch w qs).1.steps := hst
  have hch' : pg.chain = Xd.env.bytes ((Host.machine Xd).admitBatch w qs).1.chain := hch
  have htip' : pg.tipSteps = ((Host.machine Xd).admitBatch w qs).1.steps := htip
  obtain ⟨wb, hab⟩ := batch_page_absorbed Xd hX' hcr' qs hn' pg.baseSteps
  have hs : Command.absorbSync Xd me cmd f.world pg.events pg.steps pg.chain pg.baseSteps =
      .ok (((Host.machine Xd).admitBatch w qs).1, ((Host.machine Xd).admitBatch w qs).2.staged.toList, wb) := by
    rw [absorbSync_none hsa', hw, hev', hst', hch']
    exact hab
  exact step_page_world hk hp' hph hacc hi hr hpg hpages (by omega) hs

/-! ## The run: the founder's rotate, one batch, one page -/

/-- **The batch-and-page run**: the deployed writer's batch of one `submit` (the founder's rotate)
stages a step (at most a page of them) and moves the World; the continuation is a plain `sync` at its
log phase; the reply is an `ok` holding a page whose events are the staged ones and whose end and tip
are the writer's World. -/
theorem run_agree :
    (decide (((Host.machine Xd).admitBatch wGenesis agQs).2.staged.size ≤ Bounds.pageStepsMax) &&
      decide (((Host.machine Xd).admitBatch wGenesis agQs).1.steps ≠ wGenesis.steps) &&
      someThen (Command.State.ofBytes agKb) (fun st => decide (st.phase = 2) && decide (st.acc.length = 5) &&
        someThen (Text.ofU64 (st.acc.getD 2 .empty)) (fun _ => true) &&
        okThen (Command.parse Xd.digestOf st.argv) (fun cmd => agNotInit cmd && (Command.syncAnchor Xd wMe cmd).isNone)) &&
      someThen (Command.hostReply agPage) (fun sp => agIsOk sp.1 && someThen (Command.logPage sp.2) (fun pg =>
        decide (pg.events = ((Host.machine Xd).admitBatch wGenesis agQs).2.staged.toList.map
          (Host.Page.stepEvent ∘ Prod.fst)) &&
        decide (pg.steps = ((Host.machine Xd).admitBatch wGenesis agQs).1.steps) &&
        decide (pg.chain = Xd.env.bytes ((Host.machine Xd).admitBatch wGenesis agQs).1.chain) &&
        decide (pg.tipSteps = ((Host.machine Xd).admitBatch wGenesis agQs).1.steps)))) = true := by
  native_decide

theorem list_five {α : Type} : ∀ {l : List α}, l.length = 5 → ∃ a b c d e, l = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem agIsOk_eq {s : Status} (h : agIsOk s = true) : s = .ok := by
  cases s <;> first | rfl | cases h

theorem agNotInit_ne {cmd : Command.Cmd Digest} (h : agNotInit cmd = true) : ∀ s, cmd ≠ .init s := by
  rintro s rfl
  cases h

/-- What a run fact of `run_agree`'s shape gives, at any batch, events, page, continuation, start and
member: the claim's premises. -/
theorem agree_premises {w₀ : World Digest} {qs : List (Host.Request Host.Frame)}
    {page kb : ByteArray} {me : Command.Self Digest}
    (h : (decide (((Host.machine Xd).admitBatch w₀ qs).2.staged.size ≤ Bounds.pageStepsMax) && decide (((Host.machine Xd).admitBatch w₀ qs).1.steps ≠ w₀.steps) &&
      someThen (Command.State.ofBytes kb) (fun st => decide (st.phase = 2) && decide (st.acc.length = 5) &&
        someThen (Text.ofU64 (st.acc.getD 2 .empty)) (fun _ => true) &&
        okThen (Command.parse Xd.digestOf st.argv) (fun cmd => agNotInit cmd && (Command.syncAnchor Xd me cmd).isNone)) &&
      someThen (Command.hostReply page) (fun sp => agIsOk sp.1 && someThen (Command.logPage sp.2) (fun pg =>
        decide (pg.events = ((Host.machine Xd).admitBatch w₀ qs).2.staged.toList.map
          (Host.Page.stepEvent ∘ Prod.fst)) && decide (pg.steps = ((Host.machine Xd).admitBatch w₀ qs).1.steps) &&
        decide (pg.chain = Xd.env.bytes ((Host.machine Xd).admitBatch w₀ qs).1.chain) && decide (pg.tipSteps = ((Host.machine Xd).admitBatch w₀ qs).1.steps)))) = true) :
    ((Host.machine Xd).admitBatch w₀ qs).2.staged.size ≤ Bounds.pageStepsMax ∧ ((Host.machine Xd).admitBatch w₀ qs).1.steps ≠ w₀.steps ∧
      ∃ (st : Command.State) (cmd : Command.Cmd Digest) (p : ByteArray) (pg : Command.LogPage) (pages : Nat)
        (a sb pb ub tb : ByteArray),
        Command.State.ofBytes kb = some st ∧ Command.parse Xd.digestOf st.argv = .ok cmd ∧ st.phase = 2 ∧
        st.acc = [a, sb, pb, ub, tb] ∧ Text.ofU64 pb = some pages ∧ (∀ s, cmd ≠ .init s) ∧
        Command.syncAnchor Xd me cmd = none ∧ Command.hostReply page = some (.ok, p) ∧
        Command.logPage p = some pg ∧ pg.events = ((Host.machine Xd).admitBatch w₀ qs).2.staged.toList.map (Host.Page.stepEvent ∘ Prod.fst) ∧ pg.steps = ((Host.machine Xd).admitBatch w₀ qs).1.steps ∧
        pg.chain = Xd.env.bytes ((Host.machine Xd).admitBatch w₀ qs).1.chain ∧ pg.tipSteps = ((Host.machine Xd).admitBatch w₀ qs).1.steps := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hne⟩, hst⟩, hpg⟩ := h
  obtain ⟨st, hk, hst⟩ := someThen_eq hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨hph, hlen⟩, hpb⟩, hcmd⟩ := hst
  obtain ⟨a, sb, pb, ub, tb, hacc⟩ := list_five hlen
  obtain ⟨pages, hpages, -⟩ := someThen_eq hpb
  rw [hacc] at hpages
  obtain ⟨cmd, hp, hcmd⟩ := okThen_eq hcmd
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcmd
  obtain ⟨hi, hsa⟩ := hcmd
  obtain ⟨⟨s, p⟩, hr, hpg⟩ := someThen_eq hpg
  simp only [Bool.and_eq_true] at hpg
  obtain ⟨hok, hpg⟩ := hpg
  obtain ⟨pg, hl, hpg⟩ := someThen_eq hpg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpg
  obtain ⟨⟨⟨hev, hs⟩, hc⟩, ht⟩ := hpg
  have hs' : s = .ok := agIsOk_eq hok
  subst hs'
  exact ⟨hn, hne, st, cmd, p, pg, pages, a, sb, pb, ub, tb, hk, hp, hph, hacc, hpages, agNotInit_ne hi, hsa,
    hr, hl, hev, hs, hc, ht⟩

theorem deployed_callCanonical : ∀ b c, Xd.decodeCall b = some c → Xd.callBytes c = b :=
  fun _ _ h => (Codec.Deployed.eq_callBytes_of_decodeCall _ h).2.symm

/-- **FLOOR (A1′).** The claim refuses the follower that takes no page: handed the writer's page of
the founder's rotate batch at the genesis World, it stays at genesis, a step short of the writer. -/
theorem floor_agree_pageAbsorbs (d : ByteArray → ByteArray) : ¬ Agree.pageAbsorbs (deafFollower d) := by
  intro h
  obtain ⟨hn, hne, st, cmd, p, pg, pages, a, sb, pb, ub, tb, hk, hp, hph, hacc, hpages, hi, hsa, hr, hpg, hev,
    hst, hch, htip⟩ := agree_premises (me := wMe) run_agree
  have hcr : wGenesis.RowsCanon Xd.env := by unfold wGenesis; exact receive_genesis_rowsCanon Xd _ _ _ _ _
  revert hn hne hk hp hsa hr hev hst hch htip hcr
  generalize agKb = kb
  generalize agPage = page
  generalize agQs = qs
  generalize wMe = me
  generalize wGenesis = w₀
  intro hn hne hk hp hsa hr hev hst hch htip hcr
  have hw := h deployed_callCanonical (w := w₀) (qs := qs) hcr hn (me := me)
    (f := ⟨w₀, none, none⟩) rfl hk hp hph hacc hpages hi hsa hr hpg hev hst hch htip
  exact hne (congrArg World.steps hw).symm

/-- **INHABITED (A1′).** The deployed follower, handed that page, moves from genesis to the World the
writer keeps, a step on. -/
theorem inhabited_agree_pageAbsorbs (d : ByteArray → ByteArray) :
    ∃ (w : World Digest) (qs : List (Host.Request Host.Frame)) (me : Command.Self Digest)
      (f : Command.Follow Digest) (kb result : ByteArray),
      w.RowsCanon Xd.env ∧ f.world = w ∧
      ((deployed d).follow me f kb result).1.world = ((Host.machine Xd).admitBatch w qs).1 ∧
      ((Host.machine Xd).admitBatch w qs).1.steps ≠ w.steps := by
  obtain ⟨hn, hne, st, cmd, p, pg, pages, a, sb, pb, ub, tb, hk, hp, hph, hacc, hpages, hi, hsa, hr, hpg, hev,
    hst, hch, htip⟩ := agree_premises (me := wMe) run_agree
  have hcr : wGenesis.RowsCanon Xd.env := by unfold wGenesis; exact receive_genesis_rowsCanon Xd _ _ _ _ _
  revert hn hne hk hp hsa hr hev hst hch htip hcr
  generalize agKb = kb
  generalize agPage = page
  generalize agQs = qs
  generalize wMe = me
  generalize wGenesis = w₀
  intro hn hne hk hp hsa hr hev hst hch htip hcr
  have hw := top_agree_pageAbsorbs d deployed_callCanonical (w := w₀) (qs := qs) hcr hn (me := me)
    (f := ⟨w₀, none, none⟩) rfl hk hp hph hacc hpages hi hsa hr hpg hev hst hch htip
  exact ⟨w₀, qs, me, ⟨w₀, none, none⟩, kb, page, hcr, rfl, hw, hne⟩

end Nanodregg.Spec
