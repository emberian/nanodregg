/-
# Host.Proofs.Refine — `Host ⊑ Kernel`: every Host step is an honest fold of the kernel's, every reopen a fold

The Host's state's World component IS the kernel's abstract state (a projection, no abstraction
function), and every edge the Host takes on it is one of three kinds:

* **a step** — `(machine X).step`, one request of a batch, TOTAL over every frame code (the six
  protocol ops, a hang-up, an unknown code). `host_step_folds`: the World after it is the fold of
  ZERO or ONE kernel steps from the World before it, that list is `Honest` (each step is what
  `judge` decides of its own signed event: the follower's audit, `audit_ok`), the staged pairs grow
  by exactly that list (each with the roots after it), and a nonempty list comes only from a frame
  whose op is `submit`. MEASURED at the definition (`Host.Serve.handle`): `submit` is the only op
  whose arm commits, and only through `judge` (`step_submit` is that case, sharper: the World is
  `judge`'s); `lookup`, `read`, `log`, `command`, `resume`, a hang-up and an unknown code reply or
  defer and leave the World. `host_run_folds` composes a batch from any accumulator;
  `host_run_audits` says the follower's audit accepts what the Host staged, reaching the World the
  Host keeps.
* **a start** — `host genesis`, `host join` (`Protocol.Invite.accept`) and `host import` (KERNEL's
  carry) each make a fresh World, never a step from one: `host_start_kept` says each is `Kept`
  (the relation's invariant half), so `host_run_kept` applies from the first batch.
* **a reopen** (the crash edge) — `host_reopen_folds`: the World the deployed open returns is the
  fold, from a `Kept` base World, of exactly the steps the segment's records decode to, and those
  records are exactly the segment's bytes up to the open's position (`openWith_world`). A fold,
  NOT an audited one: the writer's reopen does not re-judge its own records (`foldStep`), and no
  theorem here ties the segment's bytes to what `admitBatch` staged, so `Honest` is not carried
  across a crash. That is the write side's theorem (a record appended is `Record.codec` of the
  staged batch), not proved here.

`seal`, `sealNow`, `makeRoom` and `finish` are not edges on the World: each is IO whose only pure
act on the resident is `Resident.install`, which rewrites `sealed`, `pending` and `index` and
leaves `world`. That half is IO; the kernel-sim plants (`same`, `reopened`: the four tries'
listings and roots after every seed and after every reopen) STAY as its witness, and as the
witness of IO order, which no theorem here speaks for.

The one premise of the generic theorems is the call codec's canonicity: a call the Ctx decodes
re-encodes to the very bytes it came from (`X.decodeCall b = some c → X.callBytes c = b`), which is
what makes a logged event decode to the call the Host judged. It is discharged at the deployed
`Ctx` by CODEC's `eq_callBytes_of_decodeCall`. Neither `Kept` nor `X.Lawful` is needed for the
fold; `Kept` is carried by the deployed corollaries (`kept_fold`). No landed theorem gains a
premise: this module adds statements and changes none.

Teeth, each a machine equal to the writer's except at ONE frame code (any of the six ops, a hang-up,
an unknown code), so one per op and more: `host_step_folds_tooth_unmoved` — an arm that stages a
step and keeps the World (a log that lies about the World), every `Ctx`, refused by the fold and
staged conjuncts; `host_step_folds_tooth_wrong_op` — an arm at any op but `submit` that commits
anything, refused by the op conjunct; `host_step_folds_tooth_unjudged` — on a `Ctx` that decodes
no call, an arm at a `submit` frame that takes a step `World.step` accepts: it `Commits` (so
`staged_rooted` holds of it), every other conjunct holds of `[s]`, and only `Honest` refuses it; `host_step_folds_tooth_censor` — at any `Ctx` meeting the
premise (the deployed one), an arm that records a refusal of a call `judge` would ADMIT, again a
machine that `Commits`, refused only by `Honest`. `kept_refutable` — `Kept` is not every World.
-/
import Host.Proofs.Serve
import Host.Proofs.Deployed
import Kernel.Proofs.Audit
import Kernel.Proofs.Origin
import Protocol.Proofs.Invite
import Codec.Proofs.Deployed

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- What the writer's handler commits: only a `submit` frame's decoded call, `judge`'s admitted Turn
or recorded refusal, to `judge`'s World. -/
private theorem handle_commit {X : Ctx D} {w w' : World D} {f : Frame} {s : Step D} {st : UInt8}
    {p : ByteArray} (h : handle X w f = .commit s w' st p) :
    Protocol.Op.ofCode? f.op = some .submit ∧ ∃ c, X.decodeCall f.payload = some c ∧
      ((∃ t, judge X w c = .admitted t w' ∧ s = .turn t) ∨
        (∃ v r, judge X w c = .recorded v r w' ∧ s = .refusal r)) := by
  unfold handle at h
  cases hop : Protocol.Op.ofCode? f.op with
  | none =>
    simp only [hop] at h
    split at h <;> cases h
  | some op =>
    cases op
    case submit =>
      simp only [hop] at h
      refine ⟨rfl, ?_⟩
      cases hc : X.decodeCall f.payload with
      | none => simp only [hc] at h; cases h
      | some c =>
        simp only [hc] at h
        refine ⟨c, rfl, ?_⟩
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rename_i t w₁ hj
              cases h
              exact .inl ⟨t, hj, rfl⟩
            · rename_i v r w₁ hj
              cases h
              exact .inr ⟨v, r, hj, rfl⟩
            · cases h
    all_goals
      simp only [hop] at h
      repeat' split at h
      all_goals cases h

/-- An `Honest` log continued by an `Honest` log from where it ends is `Honest`. -/
private theorem honest_append {X : Ctx D} :
    ∀ {w w₁ : World D} {l₁ l₂ : List (Step D)}, Honest X w l₁ → World.fold X.env w l₁ = .ok w₁ →
      Honest X w₁ l₂ → Honest X w (l₁ ++ l₂)
  | w, w₁, [], l₂, _, hf, h₂ => by
    simp only [World.fold, Except.ok.injEq] at hf
    subst hf
    exact h₂
  | w, w₁, .turn t :: rest, l₂, h₁, hf, h₂ => by
    obtain ⟨c, hd, hr, k⟩ := h₁
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    refine ⟨c, hd, hr, fun w' ha => ?_⟩
    have hv' : World.admit X.env w t = .ok v := hv
    rw [hv'] at ha
    cases ha
    exact honest_append (k v hv') hfr h₂
  | w, w₁, .refusal r :: rest, l₂, h₁, hf, h₂ => by
    obtain ⟨c, v₀, u, hd, hj, k⟩ := h₁
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    refine ⟨c, v₀, u, hd, hj, fun w' ha => ?_⟩
    have hv' : World.refuse X.env w r = .ok v := hv
    rw [hv'] at ha
    cases ha
    exact honest_append (k v hv') hfr h₂

/-- **`Host ⊑ Kernel`, one step.** Any request, from any batch accumulator: the World the writer's
machine keeps is the fold of at most one kernel step from the World before it; that step is
`Honest` (what `judge` decides of its own signed event); the staged pairs grow by exactly it, with
the roots after it; and a step is taken only for a `submit` frame. Total over every frame code by
`handle`'s match: a new op without a case does not compile, and one whose arm commits anything but
`judge`'s answer breaks this statement (`host_step_folds_tooth_unmoved`, `_wrong_op`, `_unjudged`,
`_censor`). -/
theorem host_step_folds (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w : World D) (out : Out (Step D × D)) (q : Request Frame) :
    ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok ((machine X).step (w, out) q).1 ∧ Honest X w l ∧
      ((machine X).step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env ((machine X).step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit) := by
  cases ha : handle X w q.body with
  | reply st p =>
    refine ⟨[], by simp, ?_, trivial, ?_, fun h => absurd rfl h⟩ <;>
      simp [Machine.step, machine, ha, World.fold]
  | defer d =>
    refine ⟨[], by simp, ?_, trivial, ?_, fun h => absurd rfl h⟩ <;>
      simp [Machine.step, machine, ha, World.fold]
  | commit s w' st p =>
    have hstep : (machine X).step (w, out) q =
        (w', { out with staged := out.staged.push (s, World.roots X.env w'),
                        replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
      simp [Machine.step, machine, ha]
    rw [hstep]
    obtain ⟨hop, c, hc, hj⟩ := handle_commit ha
    have hcb : X.decodeCall (X.callBytes c) = some c := by rw [hX _ _ hc]; exact hc
    have hws : World.step X.env w s = .ok w' := machine_commits X w q.body s w' st p ha
    refine ⟨[s], by simp, ?_, ?_, by simp, fun _ => hop⟩
    · simp only [World.fold, hws]
    · rcases hj with ⟨t, hjt, rfl⟩ | ⟨v, r, hjr, rfl⟩
      · obtain ⟨-, hr, -⟩ := submit_ok (Protocol.Settle.judge_admitted hjt)
        refine ⟨c, ?_, hr, fun _ _ => trivial⟩
        rw [(receive_derived hr).event]
        exact hcb
      · obtain ⟨-, -, hr, -⟩ := judge_recorded hjr
        refine ⟨c, v, w', ?_, recordedBy_of_judge hjr, fun _ _ => trivial⟩
        rw [hr]
        exact hcb

/-- **`Host ⊑ Kernel`, a batch.** Any requests, from any accumulator: the World the writer keeps is
the fold of an `Honest` list of kernel steps, at most one per request, and the steps staged are
exactly that list after those already staged (`Machine.staged_rooted` states the roots). -/
theorem host_run_folds (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b) :
    ∀ (qs : List (Request Frame)) (w : World D) (out : Out (Step D × D)),
      ∃ l : List (Step D), l.length ≤ qs.length ∧
        World.fold X.env w l = .ok ((machine X).run (w, out) qs).1 ∧ Honest X w l ∧
        ((machine X).run (w, out) qs).2.staged.toList.map Prod.fst = out.staged.toList.map Prod.fst ++ l
  | [], w, out => ⟨[], Nat.le_refl _, rfl, trivial, by simp [Machine.run]⟩
  | q :: qs, w, out => by
    obtain ⟨l₁, hl₁, hf₁, hh₁, hs₁, -⟩ := host_step_folds X hX w out q
    generalize hacc : (machine X).step (w, out) q = acc at hf₁ hs₁
    obtain ⟨w₁, out₁⟩ := acc
    obtain ⟨l₂, hl₂, hf₂, hh₂, hs₂⟩ := host_run_folds X hX qs w₁ out₁
    have hrun : (machine X).run (w, out) (q :: qs) = (machine X).run (w₁, out₁) qs := by
      simp only [Machine.run, List.foldl_cons, hacc]
    rw [hrun]
    refine ⟨l₁ ++ l₂, by simp; omega, fold_append.mpr ⟨w₁, hf₁, hf₂⟩, honest_append hh₁ hf₁ hh₂, ?_⟩
    rw [hs₂]
    simp only at hs₁
    rw [hs₁]
    simp [Function.comp_def]

/-- **The follower's audit accepts what the Host staged** (`audit_ok` as `host_run_folds`' case): a
batch from a World stages a log the audit re-derives step by step, reaching the World the Host
keeps. -/
theorem host_run_audits (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w : World D) (qs : List (Request Frame)) :
    audit X w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) =
      .ok ((machine X).admitBatch w qs).1 := by
  obtain ⟨l, -, hf, hh, hs⟩ := host_run_folds X hX qs w {}
  have hs' : ((machine X).admitBatch w qs).2.staged.toList.map Prod.fst = l := by
    simpa using hs
  rw [hs']
  exact audit_ok.mpr ⟨hf, hh⟩

/-- **TOOTH (`host_step_folds`, every frame code, every `Ctx`): a step that stages without moving
the World.** A machine equal to the writer's except that its arm at `q`'s frame code (any of the
six ops, a hang-up, an unknown code) stages a step and keeps the World: no list of at most one
kernel step folds to that World and is what was staged (a fold of one step moves the step
counter, `admit_steps`/`refuse_steps`). -/
theorem host_step_folds_tooth_unmoved (X : Ctx D) (w : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with handle := fun v f => if f.op = q.body.op then .commit s v st p else handle X v f }
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit) := by
  intro m
  have hm : m.step (w, out) q =
      (w, { out with staged := out.staged.push (s, World.roots X.env w),
                     replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine]
  rw [hm]
  rintro ⟨l, hl, hf, -, hs, -⟩
  match l, hl with
  | [], _ => simp at hs
  | [x], _ =>
    obtain ⟨w₁, hx, hn⟩ := fold_cons_ok.mp hf
    have h1 : w₁.steps = w.steps + 1 := by
      cases x with
      | turn t => exact admit_steps hx
      | refusal r => exact refuse_steps hx
    simp only [World.fold, Except.ok.injEq] at hn
    rw [hn] at h1
    omega

/-- **TOOTH (`host_step_folds`'s op conjunct): a World-moving arm at any op but `submit`.** A machine
equal to the writer's except that its arm at `q`'s frame code, which is not `submit`'s, commits any
step: the step theorem fails of it (an empty list is not what was staged, a nonempty one is not
`submit`'s). -/
theorem host_step_folds_tooth_wrong_op (X : Ctx D) (w w' : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray)
    (hop : Protocol.Op.ofCode? q.body.op ≠ some .submit) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with handle := fun v f => if f.op = q.body.op then .commit s w' st p else handle X v f }
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit) := by
  intro m
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (s, World.roots X.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine]
  rw [hm]
  rintro ⟨l, -, -, -, hs, ho⟩
  match l with
  | [] => simp at hs
  | x :: _ => exact hop (ho (List.cons_ne_nil x _))

/-- **TOOTH (`host_step_folds`'s `Honest` conjunct, every frame code): a step the kernel takes but
`judge` did not decide.** On a `Ctx` that decodes no call (any `Ctx` with its decoder emptied), a
machine equal to the writer's except that its arm at `q`'s frame code takes step `s` by
`World.step` wherever the kernel accepts it: it `Commits` to `World.step` (so `staged_rooted`, the
landed batch theorem, holds of it); at a `submit` frame where `s` is accepted, `[s]` meets EVERY
other conjunct of the step theorem (fold, staged, op), and the step theorem fails of it: no
nonempty log is `Honest` on that `Ctx`. So `Honest` alone refuses it. -/
theorem host_step_folds_tooth_unjudged (X : Ctx D) (w w' : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray) (hs : World.step X.env w s = .ok w')
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) :
    let X' : Ctx D := { X with decodeCall := fun _ => none }
    let m : Machine (World D) (Step D) Frame D :=
      { machine X' with
        handle := fun v f =>
          if f.op = q.body.op then
            (match World.step X'.env v s with
             | .ok v' => .commit s v' st p
             | .error _ => handle X' v f)
          else handle X' v f }
    m.Commits (World.step X'.env) ∧
    (∃ l : List (Step D), l.length ≤ 1 ∧ World.fold X'.env w l = .ok (m.step (w, out) q).1 ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X'.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit)) ∧
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X'.env w l = .ok (m.step (w, out) q).1 ∧ Honest X' w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X'.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit) := by
  intro X' m
  have hs' : World.step X'.env w s = .ok w' := hs
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (s, World.roots X'.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine, hs']
  refine ⟨?_, ⟨[s], by simp, by rw [hm]; simp only [World.fold, hs'], by rw [hm]; simp, fun _ => hop⟩, ?_⟩
  · intro v f s₁ v₁ st₁ p₁ h
    simp only [m] at h
    split at h
    · split at h
      · rename_i v' hv
        cases h
        exact hv
      · exact machine_commits X' v f s₁ v₁ st₁ p₁ h
    · exact machine_commits X' v f s₁ v₁ st₁ p₁ h
  rw [hm]
  rintro ⟨l, -, -, hh, hs, -⟩
  match l with
  | [] => simp at hs
  | .turn t :: _ =>
    obtain ⟨c, hd, -⟩ := hh
    cases hd
  | .refusal r :: _ =>
    obtain ⟨c, -, -, hd, -⟩ := hh
    cases hd

/-- **TOOTH (`host_step_folds`'s `Honest` conjunct at a decoding `Ctx`): a censoring writer.** At
any `Ctx` meeting the step theorem's premise (the deployed one: `deployed_canonical`), take a frame
carrying call `c` that `judge` would ADMIT on `w`, and a judged-refusal record `r` of that very event (no cancel field, `hk`: a record carrying one is
a member’s cancel, which `recordedBy` re-judges by `cancel`, and whose forgery is `audit_cancel_forged`’s tooth)
which `World.refuse` accepts on `w`. A machine equal to the writer's except that its arm at the
frame's code records `r` wherever `World.refuse` accepts it `Commits` to `World.step`; at a `submit`
frame `[.refusal r]` meets every other conjunct of the step theorem, and the step theorem fails of
it: the one step it staged is a refusal `judge` did not record. So `Honest` alone refuses it. The
premises' joint satisfiability (a refusal record of an admissible call's event that `World.refuse`
accepts on the same World) is not witnessed in Lean. -/
theorem host_step_folds_tooth_censor (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w w₁ w' : World D) (out : Out (Step D × D)) (q : Request Frame) (c : Call D) (t : Turn D)
    (r : Refused D) (st : UInt8) (p : ByteArray)
    (hc : X.decodeCall q.body.payload = some c) (hj : judge X w c = .admitted t w₁)
    (he : r.event = X.callBytes c) (hk : r.cancel.size = 0) (hr : World.refuse X.env w r = .ok w')
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with
        handle := fun v f =>
          if f.op = q.body.op then
            (match World.refuse X.env v r with
             | .ok v' => .commit (.refusal r) v' st p
             | .error _ => handle X v f)
          else handle X v f }
    m.Commits (World.step X.env) ∧
    (∃ l : List (Step D), l.length ≤ 1 ∧ World.fold X.env w l = .ok (m.step (w, out) q).1 ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit)) ∧
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → Protocol.Op.ofCode? q.body.op = some .submit) := by
  intro m
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (.refusal r, World.roots X.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine, hr]
  have hr' : World.step X.env w (.refusal r) = .ok w' := hr
  refine ⟨?_, ⟨[.refusal r], by simp, by rw [hm]; simp only [World.fold, hr'], by rw [hm]; simp,
    fun _ => hop⟩, ?_⟩
  · intro v f s₁ v₁ st₁ p₁ h
    simp only [m] at h
    split at h
    · split at h
      · rename_i v' hv
        cases h
        exact hv
      · exact machine_commits X v f s₁ v₁ st₁ p₁ h
    · exact machine_commits X v f s₁ v₁ st₁ p₁ h
  rw [hm]
  rintro ⟨l, hl, -, hh, hs, -⟩
  match l, hl with
  | [], _ => simp at hs
  | [x], _ =>
    simp at hs
    subst hs
    obtain ⟨c', v, u, hd, hjr, -⟩ := hh
    rw [he, hX _ _ hc, hc] at hd
    cases hd
    rw [recordedBy, if_pos hk, hj] at hjr
    cases hjr

end Nanodregg.Host

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

/-- The deployed call codec is canonical: the generic theorems' one premise. -/
private theorem deployed_canonical : ∀ b c, X.decodeCall b = some c → X.callBytes c = b :=
  fun _ _ h => (Codec.Deployed.eq_callBytes_of_decodeCall _ h).2.symm

/-- **`Host ⊑ Kernel` at the deployed instance, a batch**: from a `Kept` World, the World the writer
keeps after any batch is `Kept`, is the fold of the `Honest` log it staged, and the follower's audit
accepts that log. No premise beyond `Kept`, which every start makes (`host_start_kept`) and every
reopen returns (`host_reopen_folds`). -/
theorem host_run_kept {w : World D} (hk : Kept w) (qs : List (Request Frame)) :
    Kept ((machine X).admitBatch w qs).1 ∧
      World.fold X.env w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) =
        .ok ((machine X).admitBatch w qs).1 ∧
      Honest X w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) ∧
      audit X w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) =
        .ok ((machine X).admitBatch w qs).1 := by
  have ha := host_run_audits X deployed_canonical w qs
  obtain ⟨hf, hh⟩ := audit_ok.mp ha
  exact ⟨kept_fold hk hf, hf, hh, ha⟩

/-- **The three starts are `Kept`.** The World `host genesis` makes (`Receive.genesis`), the one
`host join` accepts (`Protocol.Invite.accept`: the genesis World of the signed inputs), and the one
`host import` carries (`Carry.importWorld`, KERNEL's carry): none is a step, each is a fresh World,
and each meets the relation's invariant. -/
theorem host_start_kept :
    (∀ {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)} {w : World D},
      Receive.genesis X name nonce allowance founders = .ok w → Kept w) ∧
    (∀ {trusted inv : ByteArray} {i : Protocol.Invite.Invitation D} {w : World D},
      Protocol.Invite.accept X trusted inv = .ok (i, w) → Kept w) ∧
    (∀ {name nonce : ByteArray} {pin : Carry.Pin D} {f : ByteArray} {r : Carry.Read D} {w : World D},
      Carry.importWorld X Codec.Deployed.digestCodec name nonce pin f = .ok (w, r) → Kept w) := by
  have hg : ∀ {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)} {w : World D},
      Receive.genesis X name nonce allowance founders = .ok w → Kept w := by
    intro name nonce allowance founders w h
    obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp h
    exact kept_of_fits (genesisWorld_codecFits hf)
  exact ⟨hg, fun h => hg (Protocol.Invite.accept_ok h).2.2.2,
    fun h => kept_of_fits (importWorld_codecFits h)⟩

/-- A run of deployed reopen steps over records is the fold of the steps those records decode to. -/
private theorem foldlM_foldStep_folds :
    ∀ {w w' : World D} {rs : List ByteArray}, rs.foldlM foldStep w = .ok w' →
      ∃ pss : List (List (Step D × D)),
        rs.mapM (Record.codec Codec.Deployed.digestCodec).decode = .ok pss ∧
        World.fold X.env w (pss.flatMap (·.map Prod.fst)) = .ok w'
  | w, w', [], h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | w, w', r :: rs, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨ps, hd, hr⟩ := Record.step_rooted h₁
      obtain ⟨pss, h₂, hf⟩ := foldlM_foldStep_folds h
      refine ⟨ps :: pss, by simp [List.mapM_cons, hd, h₂, bind, Except.bind, pure, Except.pure], ?_⟩
      simp only [List.flatMap_cons]
      exact fold_append.mpr ⟨w₁, RootedFold.fold hr, hf⟩

/-- **`Host ⊑ Kernel` at the crash edge.** Whatever base file and segment bytes the deployed open
reads, the World it returns is the fold, from the `Kept` World of the base it read, of exactly the
steps its segment's records decode to, those records being exactly the segment's bytes from the
base's offset to the open's position; and that World is `Kept`. With `host_run_kept`, every World
the writer holds, across any number of crashes, is a fold from a base. -/
theorem host_reopen_folds {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    ∃ (b : Base (World D)) (n : Nat) (d : ByteArray) (rs : List ByteArray) (pss : List (List (Step D × D))),
      Base.read keys c world file = .ok (b, n, d) ∧ Kept b.world ∧
      (S.extract b.offset S.size).extract 0 (o.pos.offset - b.offset) = Log.encodeAll keys.segment b.tag.bytes rs ∧
      rs.mapM (Record.codec Codec.Deployed.digestCodec).decode = .ok pss ∧
      World.fold X.env b.world (pss.flatMap (·.map Prod.fst)) = .ok o.opened.world ∧ Kept o.opened.world := by
  obtain ⟨b, n, d, rs, hb, hf, -, -, -, he⟩ :=
    openWith_world keys c world recorder.mark originChain foldStep file H I S h
  obtain ⟨b', n', d', rs', hb', hk, -, hk'⟩ := openWith_kept h
  rw [hb] at hb'
  cases hb'
  obtain ⟨pss, h₂, hfold⟩ := foldlM_foldStep_folds hf
  exact ⟨b, n, d, rs, pss, hb, hk, he, h₂, hfold, hk'⟩

/-- **TOOTH (`Kept`, the relation's invariant half, is not every World).** Any World with its step
counter set to 2^64 is not `Kept`: the start and reopen theorems say something. -/
theorem kept_refutable (w : World D) : ¬ Kept { w with steps := 2 ^ 64 } := by
  intro h
  exact absurd h.stepsLt (by simp)

end Nanodregg.Host.Deployed
