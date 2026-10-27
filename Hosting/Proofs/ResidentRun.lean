/-
# Hosting.Proofs.ResidentRun — the order of a tick's effects, on every path (HOSTING-36)

The resident's tick is a tree of effects (`Resident.Prog`); `tick` performs `tickP`'s tree and
nothing else. `Runs p es a` is one path through a tree: the effects `es` it performs, each with the
result it had (ANY result: a member command's reply or failure, a keep or forget that failed, every
`AskEnd`), and the value `a` it ends with. Every theorem here is over every path, so it covers
every reply the member and broker sockets and the volume could give.

`core es` drops the `say` lines (stderr), leaving the effects on the world. A command's bytes are a
function of its name (`Cmd.argv`), so a name in a trace is the command sent.

- `tick_order`: the core of every path is `TickCore`: the describe only when no shape is known,
  and then the read only at the shape the description read as; the read; then the act `decideTick`
  chose from the rings THAT read returned (`ActCore`):
  - idle: one forget if an answer was kept, else nothing;
  - answer the kept ring `r` with `t`: `deliver r t`;
  - ask about `r`: keep `(r, intentText)` first; only if that keep succeeded, the ask (exactly
    `askOf conf r`); then, by how the ask ended: never sent → a forget; answered `a` → keep
    `answerText a`; lost → keep `(unanswered WHY)`; only if that keep succeeded, `deliver r` of it.
  `deliver r t` is ONE invoke of `answer` for `(r, t)`, then by its reply (`DeliverAfter`): taken
  → a forget; refused → the re-read, and a forget only if the re-read no longer lists `r`.
- `tick_counts` reads that off: at most one describe; at most one ask, for the HEAD of the rings
  the read returned (`decide_ask`: the lowest pending, no kept ring pending), right after the
  intent was kept; at most one invoke: of the kept answer (the decision `answer`, no ask), or of
  THIS tick's answer text right after it was kept (the intent replaced).
- `kept_follows`: on every path that goes on (`.next m'`), the answer the tick hands the next one
  (`m'.kept`) is what its successful keeps and forgets leave, in order, from the one it was given:
  the memory never holds a text the volume did not report kept.
- Retries (HOSTING-48): `tick_retry`: a path holding an `Unsettled` effect (a member command that
  failed or answered an exit that does not settle it, `declined NAME` and `behind` among them; an
  ask never sent) ends `Retried`: one more retry counted, below `retriesMax`, or `retryExhausted` at
  it. `tick_lt`: every memory a tick hands on is below the bound. `Ticks` is the one chain of a
  process's ticks, and `no_refusal_repeats_forever`: a chain whose every tick is unsettled is at
  most `retriesMax - m.retries` long.
- Teeth (`order_refuses_*`): an ask before the intent, an ask after a failed intent keep, an invoke
  of the intent itself, an invoke of another pair than the kept one, an invoke with nothing kept, a
  second ask, a forget after a refused answer whose ring the re-read still lists, a second
  describe, a describe with a shape known. Reach: `ask_path_exists`.

The interpreter (HOSTING-37): `tick` is `(tickP w m).interp (ioHandler w)` (`tick_def`), and
`interp_runs` proves that `interp` performs exactly a path, one handler call per node in tree order,
continuing on its result, at the recording handler for every oracle (`interp_order`: the recorded
trace is `TickCore`). The volume: `Proofs.ResidentVolume` (keep and forget durable and atomic under
the stated contract; the seed after a crash). What is code, not theorem: `ioHandler`'s five fields
ARE the five calls (`command w.member (c.argv w.conf)`, `keep`, `forget`, `ask`, `say`), and
`interp`'s proof is at one handler: that IO's bind sequences effects is the runtime's.
-/
import Hosting.Resident.Trace
import Hosting.Proofs.Resident

namespace Nanodregg.Hosting.Proofs.ResidentRun

open Nanodregg.Hosting Nanodregg.Hosting.Resident
open Nanodregg.Lang.Contextual.Slot

/-- A path through a tick's term: the effects it performs, with SOME result for each, and its end;
a hole's path is the path of its filling (`fill`, the deployed slots). -/
inductive Runs : Prog Tick → List Ev → Tick → Prop
  | done (a : Tick) : Runs (.done a) [] a
  | cmd {c k es a} (x : Except String Reply) : Runs (k x) es a → Runs (.cmd c k) (.cmd c x :: es) a
  | keep {r t k es a} (b : Bool) : Runs (k b) es a → Runs (.keep r t k) (.keep r t b :: es) a
  | forget {k es a} (b : Bool) : Runs (k b) es a → Runs (.forget k) (.forget b :: es) a
  | ask {r q k es a} (x : AskEnd) : Runs (k x) es a → Runs (.ask r q k) (.ask r q x :: es) a
  | say {s k es a} : Runs (k ()) es a → Runs (.sayK s k) (.say s :: es) a
  | hole {h es a} : Runs (fill h) es a → Runs (.hole h) es a

@[simp] theorem core_nil : core [] = [] := rfl
@[simp] theorem core_say (s : String) (es : List Ev) : core (.say s :: es) = core es := by
  simp [core, Ev.quiet]
@[simp] theorem core_cmd (c : Cmd) (x : Except String Reply) (es : List Ev) :
    core (.cmd c x :: es) = .cmd c x :: core es := by simp [core, Ev.quiet]
@[simp] theorem core_keep (r : Ring) (t : ByteArray) (b : Bool) (es : List Ev) :
    core (.keep r t b :: es) = .keep r t b :: core es := by simp [core, Ev.quiet]
@[simp] theorem core_forget (b : Bool) (es : List Ev) : core (.forget b :: es) = .forget b :: core es := by
  simp [core, Ev.quiet]
@[simp] theorem core_ask (r : Ring) (q : Broker.Ask) (x : AskEnd) (es : List Ev) :
    core (.ask r q x :: es) = .ask r q x :: core es := by simp [core, Ev.quiet]

theorem core_append (l₁ l₂ : List Ev) : core (l₁ ++ l₂) = core l₁ ++ core l₂ := by
  simp [core, List.filter_append]

/-! ## Retries: the vocabulary -/

/-- An effect that did not settle, so the tick it ends is a retry (`retry`): a member command that
failed (`.error`) or answered an exit that is not its settling one (a describe, a read or the re-read
anything but `ok`; an answer neither `ok` nor `refused`), or an ask that never left. -/
def Unsettled : Ev → Prop
  | .cmd (.invoke _ _ _) x => match x with
    | .error _ => True
    | .ok rr => rr.exit ≠ Protocol.CommandExit.ok.code ∧ rr.exit ≠ Protocol.CommandExit.refused.code
  | .cmd (.probe _) x => probeGone x = none
  | .cmd _ x => match x with
    | .error _ => True
    | .ok rr => rr.exit ≠ Protocol.CommandExit.ok.code
  | .ask _ _ (.notSent _) => True
  | _ => False

/-- A tick from a memory holding `n` retries ended on one more: it goes on with `n + 1`, still below
`retriesMax`, or `n + 1` reached the bound and it ended `retryExhausted`. -/
def Retried (n : Nat) (a : Tick) : Prop :=
  (∃ m', a = .next m' ∧ m'.retries = n + 1 ∧ m'.retries < retriesMax) ∨
    (retriesMax ≤ n + 1 ∧ ∃ d, a = .stop .retryExhausted d)

theorem retry_retried (m : Mem) (why : String) : Retried m.retries (retry m why) := by
  unfold retry Retried
  split
  · exact .inl ⟨_, rfl, rfl, by assumption⟩
  · exact .inr ⟨by omega, _, rfl⟩

theorem retry_next {m m' : Mem} {why : String} (h : retry m why = .next m') :
    m' = { m with retries := m.retries + 1 } := by
  unfold retry at h
  split at h
  · cases h; rfl
  · cases h

theorem done_retry {m m' : Mem} {why : String} {es : List Ev} (h : Runs (.done (retry m why)) es (.next m')) :
    es = [] ∧ m' = { m with retries := m.retries + 1 } := by
  generalize hx : retry m why = x at h
  cases h
  exact ⟨rfl, retry_next hx⟩

theorem done_retried {m : Mem} {why : String} {es : List Ev} {a : Tick} (h : Runs (.done (retry m why)) es a) :
    es = [] ∧ Retried m.retries a := by
  cases h; exact ⟨rfl, retry_retried m why⟩

/-- The probes of the cells `cs` a waiting ring's answer cites, `gone` the cells found gone so far,
then the `use` slot's effects: nothing when the queue stops, else one forget. A probe that does not
settle ends it. -/
def ProbesCore (r : Ring) (p : List Ring) : List ByteArray → List ByteArray → List Ev → Prop
  | [], gone, rest => if useChoice r p gone = .stop then rest = [] else ∃ b, rest = [.forget b]
  | c :: cs, gone, rest => ∃ y rest', rest = .cmd (.probe c) y :: rest' ∧
      match probeGone y with
      | some true => ProbesCore r p cs (c :: gone) rest'
      | some false => ProbesCore r p cs gone rest'
      | none => rest' = []

/-- What follows the re-read `p` of a refused answer for `r`: a ring that still waits has the cells
its answer cites probed, then the `use` slot; a ring that left is forgotten. -/
def RefusedCore (r : Ring) (p : List Ring) (rest : List Ev) : Prop :=
  if r ∈ p then ProbesCore r p (aimCells r) [] rest else ∃ b, rest = [.forget b]

/-- What follows an invoke for ring `r` that answered `x`: taken (exit ok) → one forget; refused →
the re-read, and a forget ONLY when the re-read listed the rings and `r` is no longer among them
(a refused answer whose ring still waits keeps its text); anything else (a transport failure,
another exit) → nothing. -/
def DeliverAfter (sh : Shape) (r : Ring) : Except String Reply → List Ev → Prop
  | .error _, rest => rest = []
  | .ok rr, rest =>
    if rr.exit = Protocol.CommandExit.ok.code then ∃ b, rest = [.forget b]
    else if rr.exit = Protocol.CommandExit.refused.code then
      ∃ y rest', rest = .cmd (.reread sh) y :: rest' ∧
        match readRings sh y with
        | some p => RefusedCore r p rest'
        | none => rest' = []
    else rest = []

/-- `deliver r t`: one invoke of `answer` for `(r, t)`, then `DeliverAfter` on its reply. -/
def DeliverCore (sh : Shape) (r : Ring) (t : ByteArray) (es : List Ev) : Prop :=
  ∃ x rest, es = .cmd (.invoke sh r t) x :: rest ∧ DeliverAfter sh r x rest

/-- After an ask that ended `x`: a forget when it never left; else its answer text kept for `r`
and, only if that keep succeeded, `deliver r` of that text. -/
def AfterAsk (sh : Shape) (r : Ring) (x : AskEnd) (es : List Ev) : Prop :=
  match askText x with
  | none => ∃ b, es = [.forget b]
  | some t => es = [.keep r t false] ∨ ∃ rest, es = .keep r t true :: rest ∧ DeliverCore sh r t rest

/-- What a tick does after reading the rings `p`, for the kept answer `k`: `decideTick p k`'s act. -/
def ActCore (c : Conf) (sh : Shape) (k : Option (Ring × ByteArray)) (p : List Ring) (es : List Ev) :
    Prop :=
  match decideTick p k with
  | .idle => (k.isSome ∧ ∃ b, es = [.forget b]) ∨ (k = none ∧ es = [])
  | .answer r t => DeliverCore sh r t es
  | .ask r => es = [.keep r intentText false] ∨
      ∃ x rest, es = .keep r intentText true :: .ask r (askOf c r) x :: rest ∧ AfterAsk sh r x rest

/-- The read at `sh`, then (if it returned rings) the act on the rings whose answer stands. -/
def ReadCore (c : Conf) (sh : Shape) (m : Mem) (es : List Ev) : Prop :=
  ∃ y rest, es = .cmd (.read sh) y :: rest ∧
    match readRings sh y with
    | none => rest = []
    | some p => ActCore c sh m.kept (live m p) rest

/-- A tick's effects: with a shape, the read and the act; without one, the describe first, then
(if the description read as a bell) the read and the act at the shape it read. -/
def TickCore (c : Conf) (m : Mem) (es : List Ev) : Prop :=
  match m.shape with
  | some sh => ReadCore c sh m es
  | none => ∃ y rest, es = .cmd .describe y :: rest ∧
      match describedShape c y with
      | none => rest = []
      | some sh => ReadCore c sh m rest

/-! ## The order -/

theorem forgetThen_core {n : Tick} {es : List Ev} {a : Tick} (h : Runs (forgetThen n) es a) :
    ∃ b, core es = [.forget b] := by
  unfold forgetThen at h
  cases h with
  | forget b h => cases b <;> simp at h <;> cases h <;> exact ⟨_, rfl⟩

/-- The `serve` slot's choice is `decideTick` over the rings whose answer stands: the kept ring's
answer while it waits and stands, else an ask about the lowest such ring, else idling. -/
theorem serveChoice_eq (m : Mem) (p : List Ring) : serveChoice m p = decideTick (live m p) m.kept := by
  have hu : ∀ q, q ∈ p → serveSlot.usable (serveHolds m p) (Act.ask q) = stands m q := by
    intro q hq
    cases hs : stands m q <;> simp [Slot.usable, Slot.dead, serveSlot, serveHolds, hq, hs]
  have hmap : (p.map Act.ask).filter (serveSlot.usable (serveHolds m p)) = (live m p).map Act.ask := by
    rw [List.filter_map]
    unfold live
    congr 1
    apply List.filter_congr
    intro q hq
    simp only [Function.comp_apply]
    exact hu q hq
  have hidle : serveSlot.usable (serveHolds m p) Act.idle = true := by
    simp [Slot.usable, Slot.dead, serveSlot]
  have hlive : ∀ r, r ∈ live m p ↔ r ∈ p ∧ stands m r = true := by
    intro r; simp [live, List.mem_filter]
  unfold serveChoice Slot.alternatives serveOrder decideTick
  cases hk : m.kept with
  | none =>
    simp only [List.nil_append, List.filter_append, hmap, List.filter_cons, hidle, if_true,
      List.filter_nil]
    cases live m p <;> rfl
  | some kt =>
    obtain ⟨r, t⟩ := kt
    simp only [List.singleton_append, List.filter_append, hmap, List.filter_cons, hidle, if_true,
      List.filter_nil]
    have ha : serveSlot.usable (serveHolds m p) (Act.answer r t) = decide (r ∈ live m p) := by
      have := hlive r
      by_cases h1 : r ∈ p <;> by_cases h2 : stands m r = true <;>
        simp_all [Slot.usable, Slot.dead, serveSlot, serveHolds]
    rw [ha]
    by_cases hr : r ∈ live m p
    · simp [hr]
    · simp only [hr, decide_false, Bool.false_eq_true, if_false]
      cases live m p <;> rfl

/-- Dropping the withdrawn rings that left `pending` changes the standing of no ring in it. -/
theorem stands_prune (m : Mem) {p : List Ring} {r : Ring} (hr : r ∈ p) :
    stands (m.prune p) r = stands m r := by
  unfold stands Mem.prune
  have : ∀ l : List (Ring × String),
      (l.filter fun x => decide (x.1 ∈ p)).any (fun x => x.1 == r) = l.any (fun x => x.1 == r) := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      by_cases hx : x.1 ∈ p
      · simp [hx, ih]
      · have hne : (x.1 == r) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; exact hx (he ▸ hr)
        simp [hx, ih, hne]
  simp only [this]

/-- Dropping the withdrawn rings that left `pending` changes no ring's standing in it. -/
theorem live_prune (m : Mem) (p : List Ring) : live (m.prune p) p = live m p := by
  unfold live
  apply List.filter_congr
  intro r hr
  exact stands_prune m hr

/-- What follows a refused answer, by the `use` slot: nothing but its line when the queue stops,
else one forget. -/
theorem useP_core {m : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {es : List Ev} {a : Tick} (h : Runs (useP m r n line p gone) es a) :
    if useChoice r p gone = .stop then core es = [] else ∃ b, core es = [.forget b] := by
  unfold useP at h
  cases hc : useChoice r p gone with
  | closed =>
    rw [hc] at h
    cases h with | say h => obtain ⟨b, hb⟩ := forgetThen_core h; exact ⟨b, by simp [hb]⟩
  | withdraw c =>
    rw [hc] at h
    cases h with | say h => obtain ⟨b, hb⟩ := forgetThen_core h; exact ⟨b, by simp [hb]⟩
  | stop => rw [hc] at h; cases h; rfl

/-- A ring no longer pending closes the `use` slot. -/
theorem useChoice_gone {r : Ring} {p : List Ring} {gone : List ByteArray} (hr : r ∉ p) :
    useChoice r p gone = .closed := by
  simp [useChoice, Slot.alternatives, useOrder, Slot.usable, Slot.dead, useSlot, useHolds, hr]

theorem probes_core {sh : Shape} {m : Mem} {r : Ring} {n line : String} {p : List Ring} :
    ∀ {cs gone : List ByteArray} {es : List Ev} {a : Tick},
      Runs (probesP sh m r n line p cs gone) es a → ProbesCore r p cs gone (core es)
  | [], gone, es, a, h => by
    simp only [probesP] at h
    cases h with | hole h => exact useP_core h
  | c :: cs, gone, es, a, h => by
    simp only [probesP] at h
    cases h with
    | cmd y h =>
      rename_i es'
      refine ⟨y, core es', by simp, ?_⟩
      dsimp only at h
      cases hy : probeGone y with
      | none =>
        rw [hy] at h
        cases h with | say h => cases h; rfl
      | some b =>
        cases b
        · rw [hy] at h; exact probes_core h
        · rw [hy] at h; exact probes_core h

theorem refused_core {sh : Shape} {m : Mem} {r : Ring} {n line : String} {p : List Ring} {es : List Ev}
    {a : Tick} (h : Runs (refusedP sh m r n line p) es a) : RefusedCore r p (core es) := by
  unfold refusedP at h
  unfold RefusedCore
  split at h
  · rename_i hr
    rw [if_pos hr]
    exact probes_core h
  · rename_i hr
    rw [if_neg hr]
    cases h with
    | hole h =>
      have hc := useP_core h
      rw [useChoice_gone hr] at hc
      simpa using hc

/-- Every path through the probes: the settled probes, then either an unsettled probe and a retry, or
a path of the `use` hole's filling at the cells found gone. -/
theorem probesP_path {sh : Shape} {m : Mem} {r : Ring} {n line : String} {p : List Ring} :
    ∀ {cs gone : List ByteArray} {es : List Ev} {a : Tick},
      Runs (probesP sh m r n line p cs gone) es a →
      ∃ pre rest, es = pre ++ rest ∧ (∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) ∧
        ((∃ c y s why, rest = [.cmd (.probe c) y, .say s] ∧ probeGone y = none ∧ a = retry m why) ∨
          ∃ gone', Runs (useP m r n line p gone') rest a)
  | [], gone, es, a, h => by
    simp only [probesP] at h
    cases h with | hole h => exact ⟨[], es, rfl, by simp, .inr ⟨gone, h⟩⟩
  | c :: cs, gone, es, a, h => by
    simp only [probesP] at h
    cases h with
    | cmd y h =>
      dsimp only at h
      cases hy : probeGone y with
      | none =>
        rw [hy] at h
        cases h with
        | say h => cases h; exact ⟨[], _, rfl, by simp, .inl ⟨c, y, _, _, rfl, hy, rfl⟩⟩
      | some b =>
        have step : ∀ {es' : List Ev}, (∃ pre rest, es' = pre ++ rest ∧
            (∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) ∧
            ((∃ c y s why, rest = [.cmd (.probe c) y, .say s] ∧ probeGone y = none ∧ a = retry m why) ∨
              ∃ gone', Runs (useP m r n line p gone') rest a)) →
            ∃ pre rest, .cmd (.probe c) y :: es' = pre ++ rest ∧
              (∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) ∧
              ((∃ c y s why, rest = [.cmd (.probe c) y, .say s] ∧ probeGone y = none ∧ a = retry m why) ∨
                ∃ gone', Runs (useP m r n line p gone') rest a) := by
          rintro es' ⟨pre, rest, rfl, hpre, hr⟩
          refine ⟨.cmd (.probe c) y :: pre, rest, rfl, ?_, hr⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨c, y, rfl, by simp [hy]⟩
          · exact hpre e he
        cases b
        · rw [hy] at h; exact step (probesP_path h)
        · rw [hy] at h; exact step (probesP_path h)

/-- Every path after a refused answer's re-read: a ring that left goes to `use` with nothing probed;
a ring that waits goes through the probes. -/
theorem refusedP_path {sh : Shape} {m : Mem} {r : Ring} {n line : String} {p : List Ring} {es : List Ev}
    {a : Tick} (h : Runs (refusedP sh m r n line p) es a) :
    ∃ pre rest, es = pre ++ rest ∧ (∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) ∧
      ((∃ c y s why, rest = [.cmd (.probe c) y, .say s] ∧ probeGone y = none ∧ a = retry m why) ∨
        ∃ gone', Runs (useP m r n line p gone') rest a) := by
  unfold refusedP at h
  split at h
  · exact probesP_path h
  · cases h with | hole h => exact ⟨[], es, rfl, by simp, .inr ⟨[], h⟩⟩

theorem deliver_core {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    {a : Tick} (h : Runs (deliverP sh m r t) es a) : DeliverCore sh r t (core es) := by
  obtain ⟨arg, harg⟩ := Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r t)
  unfold deliverP at h
  rw [harg] at h
  cases h with
  | cmd x h =>
    rename_i es'
    rw [core_cmd]
    refine ⟨x, core es', rfl, ?_⟩
    rcases x with e | rr
    · simp only at h; cases h with | say h => cases h; simp [DeliverAfter]
    · simp only at h
      unfold DeliverAfter
      split at h
      · rename_i hok
        simp only [hok, if_true]
        cases h with
        | say h => obtain ⟨b, hb⟩ := forgetThen_core h; exact ⟨b, by simp [hb]⟩
      · rename_i hok
        simp only [hok, if_false]
        split at h
        · rename_i href
          simp only [href, if_true]
          cases h with
          | cmd y h =>
            rename_i es''
            refine ⟨y, core es'', by simp, ?_⟩
            unfold readRings
            rcases y with e | rr'
            · simp only at h ⊢
              cases h with | say h => cases h; rfl
            · simp only at h ⊢
              split at h
              · rename_i hx
                simp only [hx, if_false]
                cases h with | say h => cases h; rfl
              · rename_i hx
                simp only [Decidable.not_not] at hx
                simp only [hx, if_true]
                split at h
                · rename_i e he
                  simp only [he, Except.toOption]
                  cases h; rfl
                · rename_i p hp
                  simp only [hp, Except.toOption]
                  exact refused_core h
        · rename_i href
          simp only [href, if_false]
          cases h with | say h => cases h; rfl

theorem answered_core {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    {a : Tick} (h : Runs (answeredP sh m r t) es a) :
    core es = [.keep r t false] ∨ ∃ rest, core es = .keep r t true :: rest ∧ DeliverCore sh r t rest := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp only [Bool.false_eq_true, if_false] at h
        cases h; simp
      · simp only [if_true] at h
        exact .inr ⟨_, by simp, deliver_core h⟩

theorem actOn_core {w : Where} {sh : Shape} {m : Mem} {p : List Ring} {es : List Ev} {a : Tick}
    (h : Runs (actOn w sh m p) es a) : ActCore w.conf sh m.kept (live m p) (core es) := by
  unfold actOn at h
  rw [serveChoice_eq] at h
  unfold ActCore
  rcases hd : decideTick (live m p) m.kept with _ | ring | ⟨ring, t⟩
  · rw [hd] at h
    simp only at h ⊢
    cases hk : m.kept with
    | none => rw [hk] at h; simp at h; cases h; simp
    | some kt =>
      rw [hk] at h; simp at h
      obtain ⟨b, hb⟩ := forgetThen_core h
      exact .inl ⟨rfl, b, hb⟩
  · rw [hd] at h
    simp only at h ⊢
    cases h with
    | keep b h =>
      cases b
      · simp only [Bool.not_false, if_true] at h
        cases h; exact .inl (by simp)
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h with
        | ask x h =>
          rename_i es'
          refine .inr ⟨x, core es', by simp, ?_⟩
          unfold AfterAsk
          rcases x with why | ans | why
          · simp only [askText] at h ⊢
            cases h with
            | say h => obtain ⟨b, hb⟩ := forgetThen_core h; exact ⟨b, by simp [hb]⟩
          · simp only [askText] at h ⊢
            exact answered_core h
          · simp only [askText] at h ⊢
            cases h with
            | say h =>
              rcases answered_core h with hc | ⟨rest, hc, hd⟩
              · exact .inl (by rw [core_say]; exact hc)
              · exact .inr ⟨rest, by rw [core_say]; exact hc, hd⟩
  · rw [hd] at h
    simp only at h ⊢
    exact deliver_core h

theorem read_core {w : Where} {sh : Shape} {m : Mem} {es : List Ev} {a : Tick}
    (h : Runs (readP w sh m) es a) : ReadCore w.conf sh m (core es) := by
  unfold readP at h
  cases h with
  | cmd y h =>
    rename_i es'
    rw [core_cmd]
    refine ⟨y, core es', rfl, ?_⟩
    rcases y with e | rr
    · simp only [readRings]; simp only at h; cases h with | say h => cases h; rfl
    · simp only at h
      unfold readRings
      split at h
      · rename_i hx
        simp only [hx, if_false]
        cases h with | say h => cases h; rfl
      · rename_i hx
        simp only [Decidable.not_not] at hx
        simp only [hx, if_true]
        split at h
        · rename_i e he
          simp only [he, Except.toOption]
          cases h; rfl
        · rename_i p hp
          simp only [hp, Except.toOption]
          cases h with
          | hole h => simpa [fill, live_prune] using actOn_core h

/-- **The order of a tick's effects**, on every path of the tree `tick` performs: `TickCore`. -/
theorem tick_order {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a) :
    TickCore w.conf m (core es) := by
  unfold tickP at h
  unfold TickCore
  cases hs : m.shape with
  | some sh =>
    rw [hs] at h
    exact read_core h
  | none =>
    rw [hs] at h
    simp only at h ⊢
    cases h with
    | cmd y h =>
      rename_i es'
      rw [core_cmd]
      refine ⟨y, core es', rfl, ?_⟩
      rcases y with e | rr
      · simp only [describedShape]; simp only at h; cases h with | say h => cases h; rfl
      · simp only at h
        unfold describedShape
        split at h
        · rename_i hx
          simp only [hx, if_false]
          cases h with | say h => cases h; rfl
        · rename_i hx
          simp only [Decidable.not_not] at hx
          simp only [hx, if_true]
          split at h
          · rename_i sh hsh
            simp only [hsh, Except.toOption]
            cases h with
            | say h => simpa using read_core h
          · rename_i e he
            simp only [he, Except.toOption]
            cases h; rfl

/-! ## Counted: what the order says, stated on its own -/

theorem probesCore_mem {r : Ring} {p : List Ring} :
    ∀ {cs gone : List ByteArray} {l : List Ev}, ProbesCore r p cs gone l →
      ∀ e ∈ l, (∃ b, e = .forget b) ∨ ∃ c y, e = .cmd (.probe c) y
  | [], gone, l, h => by
    intro e he
    simp only [ProbesCore] at h
    split at h
    · subst h; cases he
    · obtain ⟨b, rfl⟩ := h; simp at he; exact .inl ⟨b, he⟩
  | c :: cs, gone, l, h => by
    intro e he
    simp only [ProbesCore] at h
    obtain ⟨y, rest', rfl, h'⟩ := h
    rcases List.mem_cons.mp he with rfl | he
    · exact .inr ⟨c, y, rfl⟩
    · split at h'
      · exact probesCore_mem h' e he
      · exact probesCore_mem h' e he
      · subst h'; cases he

theorem refusedCore_mem {r : Ring} {p : List Ring} {l : List Ev} (h : RefusedCore r p l) :
    ∀ e ∈ l, (∃ b, e = .forget b) ∨ ∃ c y, e = .cmd (.probe c) y := by
  unfold RefusedCore at h
  split at h
  · exact probesCore_mem h
  · obtain ⟨b, rfl⟩ := h; intro e he; simp at he; exact .inl ⟨b, he⟩

/-- Forgets and probes ask nothing, invoke nothing, describe nothing. -/
theorem quiet_counts {l : List Ev} (h : ∀ e ∈ l, (∃ b, e = .forget b) ∨ ∃ c y, e = .cmd (.probe c) y) :
    asks l = [] ∧ invokes l = [] ∧ describes l = 0 := by
  induction l with
  | nil => simp [asks, invokes, describes]
  | cons e l ih =>
    obtain ⟨ha, hi, hd⟩ := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [asks, invokes, describes] at ha hi hd
    rcases h e List.mem_cons_self with ⟨b, rfl⟩ | ⟨c, y, rfl⟩ <;>
      simp [asks, invokes, describes, ha, hi, hd]

theorem deliver_counts {sh : Shape} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : DeliverCore sh r t es) : asks es = [] ∧ invokes es = [(r, t)] ∧ describes es = 0 ∧
      ∃ x rest, es = .cmd (.invoke sh r t) x :: rest := by
  obtain ⟨x, rest, rfl, hr⟩ := h
  have : asks rest = [] ∧ invokes rest = [] ∧ describes rest = 0 := by
    unfold DeliverAfter at hr
    split at hr
    · subst hr; simp [asks, invokes, describes]
    · split at hr
      · obtain ⟨b, rfl⟩ := hr; simp [asks, invokes, describes]
      · split at hr
        · obtain ⟨y, rest', rfl, hr'⟩ := hr
          split at hr'
          · obtain ⟨ha, hi, hd⟩ := quiet_counts (refusedCore_mem hr')
            simp only [asks, invokes, describes] at ha hi hd
            simp [asks, invokes, describes, ha, hi, hd]
          · subst hr'; simp [asks, invokes, describes]
        · subst hr; simp [asks, invokes, describes]
  obtain ⟨ha, hi, hd⟩ := this
  refine ⟨?_, ?_, ?_, x, rest, rfl⟩
  · simpa [asks] using ha
  · simpa [invokes] using hi
  · simpa [describes] using hd

theorem afterAsk_counts {sh : Shape} {r : Ring} {x : AskEnd} {es : List Ev}
    (h : AfterAsk sh r x es) :
    asks es = [] ∧ describes es = 0 ∧ (invokes es = [] ∨
      ∃ t y rest, askText x = some t ∧ invokes es = [(r, t)] ∧
        es = .keep r t true :: .cmd (.invoke sh r t) y :: rest) := by
  unfold AfterAsk at h
  split at h
  · obtain ⟨b, rfl⟩ := h; simp [asks, invokes, describes]
  · rename_i t ht
    rcases h with rfl | ⟨rest, rfl, hd⟩
    · simp [asks, invokes, describes]
    · obtain ⟨ha, hi, hdsc, y, rest', rfl⟩ := deliver_counts hd
      refine ⟨by simpa [asks] using ha, by simpa [describes] using hdsc,
        .inr ⟨t, y, rest', ht, ?_, rfl⟩⟩
      simpa [invokes] using hi

/-- What an act asks and invokes, against the decision. -/
theorem act_counts {c : Conf} {sh : Shape} {k : Option (Ring × ByteArray)} {p : List Ring}
    {es : List Ev} (h : ActCore c sh k p es) :
    describes es = 0 ∧
    (asks es = [] ∨ ∃ r x post, decideTick p k = .ask r ∧ asks es = [r] ∧
      es = .keep r intentText true :: .ask r (askOf c r) x :: post) ∧
    (invokes es = [] ∨ ∃ r t, invokes es = [(r, t)] ∧
      ((decideTick p k = .answer r t ∧ asks es = []) ∨
       ∃ x y post, decideTick p k = .ask r ∧ askText x = some t ∧
         es = .keep r intentText true :: .ask r (askOf c r) x :: .keep r t true ::
           .cmd (.invoke sh r t) y :: post)) := by
  unfold ActCore at h
  split at h
  · rcases h with ⟨-, b, rfl⟩ | ⟨-, rfl⟩ <;> simp [asks, invokes, describes]
  · rename_i r t hd
    obtain ⟨ha, hi, hdsc, -⟩ := deliver_counts h
    exact ⟨hdsc, .inl ha, .inr ⟨r, t, hi, .inl ⟨hd, ha⟩⟩⟩
  · rename_i r hd
    rcases h with rfl | ⟨x, rest, rfl, ha⟩
    · simp [asks, invokes, describes]
    · obtain ⟨ha', hdsc, hi⟩ := afterAsk_counts ha
      refine ⟨by simpa [describes] using hdsc, .inr ⟨r, x, rest, hd, ?_, rfl⟩, ?_⟩
      · simp only [asks] at ha' ⊢
        simp [ha']
      · rcases hi with hi | ⟨t, y, rest', ht, hi, rfl⟩
        · exact .inl (by simpa [invokes] using hi)
        · exact .inr ⟨r, t, by simpa [invokes] using hi, .inr ⟨x, y, rest', hd, ht, rfl⟩⟩

/-- What a read and its act ask and invoke. -/
theorem read_counts {c : Conf} {sh : Shape} {m : Mem} {es : List Ev}
    (h : ReadCore c sh m es) :
    describes es = 0 ∧
    (asks es = [] ∨ ∃ r y p x post, readRings sh y = some p ∧ decideTick (live m p) m.kept = .ask r ∧
      asks es = [r] ∧ es = .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf c r) x :: post) ∧
    (invokes es = [] ∨ ∃ r t, invokes es = [(r, t)] ∧
      ((∃ y p, readRings sh y = some p ∧ decideTick (live m p) m.kept = .answer r t ∧ asks es = []) ∨
       ∃ y p x z post, readRings sh y = some p ∧ decideTick (live m p) m.kept = .ask r ∧ askText x = some t ∧
         es = .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf c r) x ::
           .keep r t true :: .cmd (.invoke sh r t) z :: post)) := by
  obtain ⟨y, rest, rfl, hr⟩ := h
  split at hr
  · subst hr; simp [asks, invokes, describes]
  · rename_i p hp
    obtain ⟨hd, ha, hi⟩ := act_counts hr
    refine ⟨by simpa [describes] using hd, ?_, ?_⟩
    · rcases ha with ha | ⟨r, x, post, hdk, ha, rfl⟩
      · exact .inl (by simpa [asks] using ha)
      · exact .inr ⟨r, y, p, x, post, hp, hdk, by simpa [asks] using ha, rfl⟩
    · rcases hi with hi | ⟨r, t, hi, ⟨hdk, ha⟩ | ⟨x, z, post, hdk, ht, rfl⟩⟩
      · exact .inl (by simpa [invokes] using hi)
      · exact .inr ⟨r, t, by simpa [invokes] using hi, .inl ⟨y, p, hp, hdk, by simpa [asks] using ha⟩⟩
      · exact .inr ⟨r, t, by simpa [invokes] using hi, .inr ⟨y, p, x, z, post, hp, hdk, ht, rfl⟩⟩

/-- **The tick's effects, counted** (every path):
- at most one describe, and only when no shape was known;
- at most one ask: for a ring `r` that `decideTick` chose from the rings the tick's read returned whose answer
  stands (`live`)
  (`ask_is_head`: the head, so the lowest pending), right after the intent was kept for `r`;
- at most one invoke: of the kept answer the decision named (no ask on that path), or of the text
  this tick's ask ended with (`askText`), right after that text was kept (the intent replaced). -/
theorem tick_counts {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a) :
    describes (core es) ≤ 1 ∧ (0 < describes (core es) → m.shape = none) ∧
    (asks (core es) = [] ∨ ∃ r sh y p x pre post, readRings sh y = some p ∧
      decideTick (live m p) m.kept = .ask r ∧ asks (core es) = [r] ∧
      core es = pre ++ .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf w.conf r) x :: post) ∧
    (invokes (core es) = [] ∨ ∃ r t, invokes (core es) = [(r, t)] ∧
      ((∃ sh y p, readRings sh y = some p ∧ decideTick (live m p) m.kept = .answer r t ∧ asks (core es) = []) ∨
       ∃ sh y p x z pre post, readRings sh y = some p ∧ decideTick (live m p) m.kept = .ask r ∧
         askText x = some t ∧
         core es = pre ++ .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf w.conf r) x ::
           .keep r t true :: .cmd (.invoke sh r t) z :: post)) := by
  have ho := tick_order h
  unfold TickCore at ho
  split at ho
  · rename_i sh hs
    obtain ⟨hd, ha, hi⟩ := read_counts ho
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rcases ha with ha | ⟨r, y, p, x, post, hp, hdk, ha, hc⟩
      · exact .inl ha
      · exact .inr ⟨r, sh, y, p, x, [], post, hp, hdk, ha, hc⟩
    · rcases hi with hi | ⟨r, t, hi, ⟨y, p, hp, hdk, ha⟩ | ⟨y, p, x, z, post, hp, hdk, ht, hc⟩⟩
      · exact .inl hi
      · exact .inr ⟨r, t, hi, .inl ⟨sh, y, p, hp, hdk, ha⟩⟩
      · exact .inr ⟨r, t, hi, .inr ⟨sh, y, p, x, z, [], post, hp, hdk, ht, hc⟩⟩
  · rename_i hs
    obtain ⟨d, rest, hc, hr⟩ := ho
    rw [hc]
    split at hr
    · subst hr; simp [asks, invokes, describes, hs]
    · rename_i sh _
      obtain ⟨hd, ha, hi⟩ := read_counts hr
      have hd' : describes (.cmd .describe d :: rest) = 1 := by simpa [describes] using hd
      refine ⟨by omega, fun _ => hs, ?_, ?_⟩
      · rcases ha with ha | ⟨r, y, p, x, post, hp, hdk, ha, hc'⟩
        · exact .inl (by simpa [asks] using ha)
        · exact .inr ⟨r, sh, y, p, x, [.cmd .describe d], post, hp, hdk,
            by simpa [asks] using ha, by rw [hc']; rfl⟩
      · rcases hi with hi | ⟨r, t, hi, ⟨y, p, hp, hdk, ha⟩ | ⟨y, p, x, z, post, hp, hdk, ht, hc'⟩⟩
        · exact .inl (by simpa [invokes] using hi)
        · exact .inr ⟨r, t, by simpa [invokes] using hi,
            .inl ⟨sh, y, p, hp, hdk, by simpa [asks] using ha⟩⟩
        · exact .inr ⟨r, t, by simpa [invokes] using hi,
            .inr ⟨sh, y, p, x, z, [.cmd .describe d], post, hp, hdk, ht, by rw [hc']; rfl⟩⟩

/-- The ring a tick asks about is the head of the rings its read returned, and no kept ring was
among them (`decide_ask`): with the range read's ascending key order, the lowest pending ring. -/
theorem ask_is_head {p : List Ring} {k : Option (Ring × ByteArray)} {r : Ring}
    (h : decideTick p k = .ask r) : p.head? = some r ∧ ∀ q t, k = some (q, t) → q ∉ p :=
  Nanodregg.Hosting.Proofs.Resident.decide_ask h

/-! ## The kept answer follows the volume -/

@[simp] theorem keptAfter_say (k : Option (Ring × ByteArray)) (s : String) (es : List Ev) :
    keptAfter k (.say s :: es) = keptAfter k es := rfl

theorem forgetThen_next {n : Tick} {m' : Mem} {es : List Ev} (h : Runs (forgetThen n) es (.next m')) :
    n = .next m' ∧ es = [.forget true] := by
  unfold forgetThen at h
  cases h with
  | forget b h =>
    cases b
    · simp at h; cases h
    · simp at h; cases h; exact ⟨rfl, rfl⟩

/-- What `use` hands the next tick holds no kept answer: every path that goes on forgot it. -/
theorem useP_kept {m m' : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {es : List Ev} (h : Runs (useP m r n line p gone) es (.next m')) (K : Option (Ring × ByteArray)) :
    m'.kept = keptAfter K es := by
  unfold useP at h
  cases hc : useChoice r p gone with
  | closed =>
    rw [hc] at h
    cases h with | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
  | withdraw c =>
    rw [hc] at h
    cases h with | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
  | stop => rw [hc] at h; cases h

/-- A ring that still waits, with every cell its answer cites there, stops the queue. -/
theorem useChoice_stop {r : Ring} {p : List Ring} {gone : List ByteArray} (hr : r ∈ p)
    (hn : ∀ c ∈ aimCells r, c ∉ gone) : useChoice r p gone = .stop := by
  unfold useChoice Slot.alternatives useOrder
  have hw : ((aimCells r).map UseCand.withdraw).filter (useSlot.usable (useHolds r p gone)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp [Slot.usable, Slot.dead, useSlot, useHolds, hn c hc]
  have hcl : useSlot.usable (useHolds r p gone) .closed = false := by
    simp [Slot.usable, Slot.dead, useSlot, useHolds, hr]
  have hst : useSlot.usable (useHolds r p gone) .stop = true := by simp [Slot.usable, Slot.dead, useSlot]
  rw [List.filter_append, List.filter_append, hw]
  simp only [List.filter_cons, List.filter_nil, hcl, hst]
  rfl

/-- A ring that still waits, a cell its answer cites found gone, is withdrawn by the first such cell. -/
theorem useChoice_withdraw {r : Ring} {p : List Ring} {gone : List ByteArray} (hr : r ∈ p)
    {c : ByteArray} (hc : (aimCells r).find? (fun x => gone.any fun g => decide (g = x)) = some c) :
    useChoice r p gone = .withdraw c := by
  unfold useChoice Slot.alternatives useOrder
  have hf : ((aimCells r).map UseCand.withdraw).filter (useSlot.usable (useHolds r p gone)) =
      ((aimCells r).filter (fun x => gone.any fun g => decide (g = x))).map UseCand.withdraw := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    cases hx : gone.any (fun g => decide (g = x)) <;> simp [Slot.usable, Slot.dead, useSlot, useHolds, hr, hx]
  have hh : ((aimCells r).filter (fun x => gone.any fun g => decide (g = x))).head? = some c := by
    rw [List.head?_filter]; exact hc
  obtain ⟨post, hpost⟩ : ∃ post, (aimCells r).filter (fun x => gone.any fun g => decide (g = x)) = c :: post := by
    cases h' : (aimCells r).filter (fun x => gone.any fun g => decide (g = x)) with
    | nil => rw [h'] at hh; cases hh
    | cons x xs => rw [h'] at hh; cases hh; exact ⟨xs, rfl⟩
  have hcl : useSlot.usable (useHolds r p gone) .closed = false := by
    simp [Slot.usable, Slot.dead, useSlot, useHolds, hr]
  have hst : useSlot.usable (useHolds r p gone) .stop = true := by simp [Slot.usable, Slot.dead, useSlot]
  rw [List.filter_append, List.filter_append, hf, hpost]
  simp only [List.filter_cons, List.filter_nil, hcl, hst]
  rfl

theorem keptAfter_probes {K : Option (Ring × ByteArray)} {pre l : List Ev}
    (h : ∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) :
    keptAfter K (pre ++ l) = keptAfter K l := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
    obtain ⟨c, y, rfl, -⟩ := h e List.mem_cons_self
    simp only [List.cons_append, keptAfter]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

theorem refusedP_kept {sh : Shape} {m m' : Mem} {r : Ring} {n line : String} {p : List Ring}
    {es : List Ev} (h : Runs (refusedP sh m r n line p) es (.next m')) : m'.kept = keptAfter m.kept es := by
  obtain ⟨pre, rest, rfl, hpre, hr⟩ := refusedP_path h
  rw [keptAfter_probes hpre]
  rcases hr with ⟨c, y, s, why, rfl, -, hr⟩ | ⟨gone, hr⟩
  · obtain rfl := retry_next hr.symm; rfl
  · exact useP_kept hr _

theorem deliver_kept {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (deliverP sh m r t) es (.next m')) : m'.kept = keptAfter m.kept es := by
  unfold deliverP at h
  split at h
  · cases h
  · cases h with
    | cmd x h =>
      simp only [keptAfter]
      rcases x with e | rr
      · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
      · simp only at h
        split at h
        · cases h with
          | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
        · split at h
          · cases h with
            | cmd y h =>
              simp only [keptAfter]
              rcases y with e | rr'
              · simp only at h
                cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
              · simp only at h
                split at h
                · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
                · split at h
                  · cases h
                  · exact refusedP_kept h
          · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl

/-- **An abandoned ring does not stop the queue** (cv 01a1682e-7f9d, LANG-76): an answer refused
while the re-read `pending` no longer lists its ring (another member retired it between the read
and the answer) ends the tick `next`, its kept answer forgotten, or `volume` if the forget failed;
never `answerRefused`. The next tick reads the queue again. -/
theorem deliver_gone_continues {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {n : Tick}
    (h : Runs (deliverP sh m r t) es n) {rr : Reply} (href : rr.exit = Protocol.CommandExit.refused.code)
    {y : Except String Reply} {p : List Ring} (hp : readRings sh y = some p) (hr : r ∉ p) {rest : List Ev}
    (hes : es = .cmd (.invoke sh r t) (.ok rr) :: .cmd (.reread sh) y :: rest) :
    n = .next { m with kept := none, retries := 0 } ∨ n = .stop .volume "forget" := by
  subst hes
  obtain ⟨arg, harg⟩ := Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r t)
  unfold deliverP at h
  rw [harg] at h
  cases h with
  | cmd x h =>
    simp only at h
    have hne : rr.exit ≠ Protocol.CommandExit.ok.code := by rw [href]; decide
    rw [if_neg hne, if_pos href] at h
    cases h with
    | cmd y' h =>
      unfold readRings at hp
      rcases y with e | rr'
      · simp at hp
      · simp only at h hp
        split at hp
        · rename_i hx
          rw [if_neg (fun hn => hn hx)] at h
          cases hra : readOut sh rr' with
          | error e => rw [hra] at hp; simp [Except.toOption] at hp
          | ok q =>
            rw [hra] at hp
            simp only [Except.toOption, Option.some.injEq] at hp
            subst hp
            simp only [hra, refusedP, if_neg hr] at h
            cases h with
            | hole h =>
              simp only [fill, useP, useChoice_gone hr] at h
              cases h with
              | say h =>
                unfold forgetThen at h
                cases h with
                | forget b h =>
                  cases b
                  · simp at h; cases h; exact .inr rfl
                  · simp at h; cases h; exact .inl rfl
        · cases hp

theorem answered_kept {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (answeredP sh m r t) es (.next m')) : m'.kept = keptAfter (some (r, t)) es ∧
      ∃ es', es = .say s!"asked; answer {t.size} bytes" :: .keep r t true :: es' := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [if_true] at h
        exact ⟨by simpa [keptAfter] using deliver_kept h, _, rfl⟩

theorem actOn_kept {w : Where} {sh : Shape} {m m' : Mem} {p : List Ring} {es : List Ev}
    (h : Runs (actOn w sh m p) es (.next m')) : m'.kept = keptAfter m.kept es := by
  unfold actOn at h
  split at h
  · split at h
    · obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
    · rename_i hk
      cases h
      cases hm : m.kept with
      | none => rfl
      | some _ => simp [hm] at hk
  · exact deliver_kept h
  · cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h with
        | ask x h =>
          simp only [keptAfter]
          rcases x with why | ans | why
          · simp only at h
            cases h with
            | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; obtain rfl := retry_next hn; rfl
          · simp only at h
            obtain ⟨hk, es', rfl⟩ := answered_kept h
            simpa [keptAfter] using hk
          · simp only at h
            cases h with
            | say h =>
              obtain ⟨hk, es', rfl⟩ := answered_kept h
              simpa [keptAfter] using hk

theorem read_kept {w : Where} {sh : Shape} {m m' : Mem} {es : List Ev}
    (h : Runs (readP w sh m) es (.next m')) : m'.kept = keptAfter m.kept es := by
  unfold readP at h
  cases h with
  | cmd y h =>
    simp only [keptAfter]
    rcases y with e | rr
    · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
    · simp only at h
      split at h
      · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
      · split at h
        · cases h
        · cases h with | hole h => simpa [fill] using actOn_kept h

/-- **The kept answer follows the volume**: on every path a tick goes on from (`.next m'`), the
answer it hands the next tick is what its successful keeps and forgets leave, in order, from the
one it was handed. So by induction over ticks from `run`'s seed (the volume's kept file), the
resident never holds, and so never invokes, a text the volume did not report kept. -/
theorem kept_follows {w : Where} {m m' : Mem} {es : List Ev} (h : Runs (tickP w m) es (.next m')) :
    m'.kept = keptAfter m.kept es := by
  unfold tickP at h
  split at h
  · exact read_kept h
  · cases h with
    | cmd y h =>
      simp only [keptAfter]
      rcases y with e | rr
      · simp only at h; cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
      · simp only at h
        split at h
        · cases h with | say h => obtain ⟨rfl, rfl⟩ := done_retry h; rfl
        · split at h
          · cases h with | say h => simpa using read_kept h
          · cases h

/-! ## No refusal repeats forever (HOSTING-48) -/

theorem mem_core_cons {e e₀ : Ev} {es : List Ev} (h : e ∈ core (e₀ :: es)) : e = e₀ ∨ e ∈ core es := by
  unfold core at h ⊢
  rw [List.filter_cons] at h
  split at h
  · exact List.mem_cons.mp h
  · exact .inr h

theorem unsettled_cons {e₀ : Ev} {es : List Ev} (h₀ : ¬ Unsettled e₀)
    (h : ∃ e ∈ core (e₀ :: es), Unsettled e) : ∃ e ∈ core es, Unsettled e := by
  obtain ⟨e, he, hu⟩ := h
  rcases mem_core_cons he with rfl | he
  · exact absurd hu h₀
  · exact ⟨e, he, hu⟩

theorem not_unsettled_keep (r : Ring) (t : ByteArray) (b : Bool) : ¬ Unsettled (.keep r t b) := id
theorem not_unsettled_forget (b : Bool) : ¬ Unsettled (.forget b) := id
theorem not_unsettled_say (s : String) : ¬ Unsettled (.say s) := id

theorem forgetThen_settled {n : Tick} {es : List Ev} {a : Tick} (h : Runs (forgetThen n) es a) :
    ¬ ∃ e ∈ core es, Unsettled e := by
  obtain ⟨b, hb⟩ := forgetThen_core h
  rintro ⟨e, he, hu⟩
  rw [hb, List.mem_singleton] at he
  subst he; exact hu

/-- `deliver r t`: a path holding an unsettled effect ends a retry. -/
theorem refusedP_retry {sh : Shape} {m : Mem} {r : Ring} {n line : String} {p : List Ring}
    {es : List Ev} {a : Tick} (h : Runs (refusedP sh m r n line p) es a)
    (hu : ∃ e ∈ core es, Unsettled e) : Retried m.retries a := by
  obtain ⟨pre, rest, rfl, hpre, hr⟩ := refusedP_path h
  rcases hr with ⟨c, y, s, why, rfl, -, rfl⟩ | ⟨gone, hr⟩
  · exact retry_retried m why
  · exfalso
    obtain ⟨e, he, hue⟩ := hu
    rw [core_append] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨c, y, rfl, hy⟩ := hpre e (List.mem_filter.mp he).1
      exact hy hue
    · have hc := useP_core hr
      split at hc
      · rw [hc] at he; cases he
      · obtain ⟨b, hb⟩ := hc
        rw [hb] at he
        simp at he
        subst he
        exact hue

theorem deliver_retry {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {a : Tick}
    (h : Runs (deliverP sh m r t) es a) (hu : ∃ e ∈ core es, Unsettled e) : Retried m.retries a := by
  unfold deliverP at h
  split at h
  · cases h; simp at hu
  · cases h with
    | cmd x h =>
      rcases x with err | rr
      · simp only at h
        cases h with | say h => exact (done_retried h).2
      · simp only at h
        split at h
        · rename_i hok
          cases h with
          | say h =>
            obtain ⟨b, hb⟩ := forgetThen_core h
            simp [hb, Unsettled, hok] at hu
        · rename_i hok
          split at h
          · rename_i href
            cases h with
            | cmd y h =>
              rcases y with err | rr'
              · simp only at h
                cases h with | say h => exact (done_retried h).2
              · simp only at h
                split at h
                · cases h with | say h => exact (done_retried h).2
                · rename_i hx
                  split at h
                  · cases h; simp [Unsettled, href, hx] at hu
                  · obtain ⟨e, he, hue⟩ := hu
                    rw [core_cmd, core_cmd] at he
                    rcases List.mem_cons.mp he with rfl | he
                    · simp [Unsettled, href] at hue
                    rcases List.mem_cons.mp he with rfl | he
                    · simp [Unsettled, hx] at hue
                    exact refusedP_retry h ⟨e, he, hue⟩
          · cases h with | say h => exact (done_retried h).2

theorem answered_retry {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {a : Tick}
    (h : Runs (answeredP sh m r t) es a) (hu : ∃ e ∈ core es, Unsettled e) : Retried m.retries a := by
  unfold answeredP at h
  cases h with
  | say h =>
    have hu1 := unsettled_cons (not_unsettled_say _) hu
    cases h with
    | keep b h =>
      have hu2 := unsettled_cons (not_unsettled_keep _ _ _) hu1
      cases b
      · simp only [Bool.false_eq_true, if_false] at h
        cases h; simp at hu2
      · simp only [if_true] at h
        have := deliver_retry h hu2
        exact this

/-- What a tick does with the rings it read: a path holding an unsettled effect ends a retry, or
`volume` when the forget after an ask that never left failed. -/
theorem actOn_retry {w : Where} {sh : Shape} {m : Mem} {p : List Ring} {es : List Ev} {a : Tick}
    (h : Runs (actOn w sh m p) es a) (hu : ∃ e ∈ core es, Unsettled e) :
    Retried m.retries a ∨ a = .stop .volume "forget" := by
  unfold actOn at h
  split at h
  · split at h
    · exact absurd hu (forgetThen_settled h)
    · cases h; simp at hu
  · exact .inl (deliver_retry h hu)
  · cases h with
    | keep b h =>
      cases b
      · simp only [Bool.not_false, if_true] at h
        cases h; simp [Unsettled] at hu
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h with
        | ask x h =>
          rcases x with why | ans | why
          · simp only at h
            cases h with
            | say h =>
              unfold forgetThen at h
              cases h with
              | forget b h =>
                cases b
                · simp only [Bool.false_eq_true, if_false] at h; cases h; exact .inr rfl
                · simp only [if_true] at h; exact .inl (done_retried h).2
          · simp only at h
            have := answered_retry h
              (unsettled_cons (by simp [Unsettled]) (unsettled_cons (not_unsettled_keep _ _ _) hu))
            exact .inl this
          · simp only at h
            cases h with
            | say h =>
              have := answered_retry h (unsettled_cons (not_unsettled_say _)
                (unsettled_cons (by simp [Unsettled]) (unsettled_cons (not_unsettled_keep _ _ _) hu)))
              exact .inl this

theorem read_retry {w : Where} {sh : Shape} {m : Mem} {es : List Ev} {a : Tick}
    (h : Runs (readP w sh m) es a) (hu : ∃ e ∈ core es, Unsettled e) :
    Retried m.retries a ∨ a = .stop .volume "forget" := by
  unfold readP at h
  cases h with
  | cmd y h =>
    rcases y with err | rr
    · simp only at h; cases h with | say h => exact .inl (done_retried h).2
    · simp only at h
      split at h
      · cases h with | say h => exact .inl (done_retried h).2
      · rename_i hx
        split at h
        · cases h; simp [Unsettled, hx] at hu
        · cases h with
          | hole h =>
            simp only [fill] at h
            have := actOn_retry h (unsettled_cons (by simpa [Unsettled] using hx) hu)
            exact this

/-- **A tick that did not settle ends a retry**: on every path of `tick` holding an unsettled effect
(`Unsettled`: a member command failed or answered an exit that does not settle it, `declined NAME`
and `behind` among them; an ask never sent), the tick goes on with one more retry counted, below
`retriesMax`, or ends `retryExhausted` once that count reached it; or ends `volume` when the forget
after an unsent ask failed. -/
theorem tick_retry {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a)
    (hu : ∃ e ∈ core es, Unsettled e) : Retried m.retries a ∨ a = .stop .volume "forget" := by
  unfold tickP at h
  split at h
  · exact read_retry h hu
  · cases h with
    | cmd y h =>
      rcases y with err | rr
      · simp only at h; cases h with | say h => exact .inl (done_retried h).2
      · simp only at h
        split at h
        · cases h with | say h => exact .inl (done_retried h).2
        · rename_i hx
          split at h
          · cases h with
            | say h =>
              have := read_retry h (unsettled_cons (not_unsettled_say _)
                (unsettled_cons (by simpa [Unsettled] using hx) hu))
              exact this
          · cases h
            obtain ⟨_, he, hu'⟩ := unsettled_cons (by simpa [Unsettled] using hx) hu
            cases he

theorem retry_lt {m m' : Mem} {why : String} (h : retry m why = .next m') : m'.retries < retriesMax := by
  unfold retry at h
  split at h
  · cases h; assumption
  · cases h

theorem done_retry_lt {m m' : Mem} {why : String} {es : List Ev} (h : Runs (.done (retry m why)) es (.next m')) :
    m'.retries < retriesMax := by
  generalize hx : retry m why = x at h
  cases h
  exact retry_lt hx

theorem forgetThen_lt {n : Tick} {m' : Mem} {es : List Ev} (hn : ∀ m'', n = .next m'' → m''.retries < retriesMax)
    (h : Runs (forgetThen n) es (.next m')) : m'.retries < retriesMax :=
  hn _ (forgetThen_next h).1

theorem retriesMax_pos : 0 < retriesMax := by decide

/-- Every memory `use` hands on has its retries reset. -/
theorem useP_lt {m m' : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {es : List Ev} (h : Runs (useP m r n line p gone) es (.next m')) : m'.retries < retriesMax := by
  unfold useP at h
  cases hc : useChoice r p gone with
  | closed =>
    rw [hc] at h
    cases h with | say h => exact forgetThen_lt (fun _ he => by cases he; exact retriesMax_pos) h
  | withdraw c =>
    rw [hc] at h
    cases h with | say h => exact forgetThen_lt (fun _ he => by cases he; exact retriesMax_pos) h
  | stop => rw [hc] at h; cases h

theorem refusedP_lt {sh : Shape} {m m' : Mem} {r : Ring} {n line : String} {p : List Ring}
    {es : List Ev} (h : Runs (refusedP sh m r n line p) es (.next m')) : m'.retries < retriesMax := by
  obtain ⟨pre, rest, rfl, -, hr⟩ := refusedP_path h
  rcases hr with ⟨c, y, s, why, rfl, -, hr⟩ | ⟨gone, hr⟩
  · exact retry_lt hr.symm
  · exact useP_lt hr

theorem deliver_lt {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (deliverP sh m r t) es (.next m')) : m'.retries < retriesMax := by
  unfold deliverP at h
  split at h
  · cases h
  · cases h with
    | cmd x h =>
      rcases x with e | rr
      · simp only at h; cases h with | say h => exact done_retry_lt h
      · simp only at h
        split at h
        · cases h with
          | say h => exact forgetThen_lt (fun _ he => by cases he; exact retriesMax_pos) h
        · split at h
          · cases h with
            | cmd y h =>
              rcases y with e | rr'
              · simp only at h
                cases h with | say h => exact done_retry_lt h
              · simp only at h
                split at h
                · cases h with | say h => exact done_retry_lt h
                · split at h
                  · cases h
                  · exact refusedP_lt h
          · cases h with | say h => exact done_retry_lt h

theorem answered_lt {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (answeredP sh m r t) es (.next m')) : m'.retries < retriesMax := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [if_true] at h
        exact deliver_lt h

theorem actOn_lt {w : Where} {sh : Shape} {m m' : Mem} {p : List Ring} {es : List Ev}
    (h : Runs (actOn w sh m p) es (.next m')) : m'.retries < retriesMax := by
  unfold actOn at h
  split at h
  · split at h
    · exact forgetThen_lt (fun _ he => by cases he; exact retriesMax_pos) h
    · cases h; exact retriesMax_pos
  · exact deliver_lt h
  · cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h with
        | ask x h =>
          rcases x with why | ans | why
          · simp only at h
            cases h with
            | say h => exact forgetThen_lt (fun _ he => retry_lt he) h
          · simp only at h
            exact answered_lt h
          · simp only at h
            cases h with
            | say h => exact answered_lt h

theorem read_lt {w : Where} {sh : Shape} {m m' : Mem} {es : List Ev}
    (h : Runs (readP w sh m) es (.next m')) : m'.retries < retriesMax := by
  unfold readP at h
  cases h with
  | cmd y h =>
    rcases y with e | rr
    · simp only at h; cases h with | say h => exact done_retry_lt h
    · simp only at h
      split at h
      · cases h with | say h => exact done_retry_lt h
      · split at h
        · cases h
        · cases h with | hole h => simp only [fill] at h; exact actOn_lt h

/-- **Every memory a tick hands on is below the bound** (`m'.retries < retriesMax`), so
`no_refusal_repeats_forever` applies from every tick a process reaches, not only its first. -/
theorem tick_lt {w : Where} {m m' : Mem} {es : List Ev} (h : Runs (tickP w m) es (.next m')) :
    m'.retries < retriesMax := by
  unfold tickP at h
  split at h
  · exact read_lt h
  · cases h with
    | cmd y h =>
      rcases y with e | rr
      · simp only at h; cases h with | say h => exact done_retry_lt h
      · simp only at h
        split at h
        · cases h with | say h => exact done_retry_lt h
        · split at h
          · cases h with | say h => exact read_lt h
          · cases h

/-- A chain of ticks of one process life: each a path of `tickP` (every reply, every keep and
forget result, `Runs`) from the memory the last one went on with; the last ends `stop`, or the
chain is cut at a tick boundary (`nil`). The one inductive over a process's ticks (HOSTING-48:
`Lifetime`, its flattened twin, is deleted). -/
inductive Ticks (w : Where) : Mem → List (List Ev) → Prop
  | nil (m : Mem) : Ticks w m []
  | last {m : Mem} {es : List Ev} {e : Exit} {d : String} :
      Runs (tickP w m) es (.stop e d) → Ticks w m [es]
  | next {m m' : Mem} {es : List Ev} {ess : List (List Ev)} :
      Runs (tickP w m) es (.next m') → Ticks w m' ess → Ticks w m (es :: ess)


/-- **No refusal repeats forever** (HOSTING-48; COLLATION A13). In any chain of ticks from a memory
below the bound (the start's `retries = 0`; every memory a tick hands on, `tick_lt`), if every tick
holds an unsettled effect (`declined NAME`, `behind`, `uncertain`, `client`, `open`,
`hostContradicted`, `pageIo`, a transport failure, a refusal whose re-read failed, an ask never
sent), the chain is at most `retriesMax - m.retries` ticks long: the tick that reaches the bound ends
`retryExhausted` (`tick_retry`), by name, never a silent loop. -/
theorem no_refusal_repeats_forever {w : Where} {m : Mem} {ess : List (List Ev)} (h : Ticks w m ess)
    (hm : m.retries < retriesMax) (hu : ∀ es ∈ ess, ∃ e ∈ core es, Unsettled e) :
    ess.length ≤ retriesMax - m.retries := by
  induction h with
  | nil => simp
  | last _ => simp only [List.length_singleton]; omega
  | @next m₀ m₁ es ess hr _ ih =>
    rcases tick_retry hr (hu _ List.mem_cons_self) with hr' | he
    · rcases hr' with ⟨m₂, he, h1, h2⟩ | ⟨-, d, he⟩
      · cases he
        have := ih h2 (fun es' he' => hu es' (List.mem_cons_of_mem _ he'))
        simp only [List.length_cons]; omega
      · cases he
    · cases he

/-- **An undecodable read ends the resident by name** (HOSTING-49): a read whose reply is `ok` but whose
stdout is not UTF-8 ends the tick `undecodable read`, with no effect after the read: never "nothing
pending", never a forget of the kept answer, never an ask. -/
theorem read_undecodable_stops {w : Where} {sh : Shape} {m : Mem} {es : List Ev} {a : Tick}
    (h : Runs (readP w sh m) es a) {rr : Reply} {rest : List Ev} (hes : es = .cmd (.read sh) (.ok rr) :: rest)
    (hok : rr.exit = Protocol.CommandExit.ok.code) (hu : String.fromUTF8? rr.stdout = none) :
    a = .stop .undecodable "read" ∧ rest = [] := by
  subst hes
  unfold readP at h
  cases h with
  | cmd y h =>
    simp only [hok, ne_eq, not_true_eq_false, if_false] at h
    have : readOut sh rr = .error (.undecodable, "read") := by unfold readOut; rw [hu]
    rw [this] at h
    cases h
    exact ⟨rfl, rfl⟩

/-! ## Teeth: orders the grammar refuses -/

theorem order_refuses_ask_before_keep (c : Conf) (sh : Shape) (k : Option (Ring × ByteArray))
    (p : List Ring) (r : Ring) (q : Broker.Ask) (x : AskEnd) (rest : List Ev) :
    ¬ ActCore c sh k p (.ask r q x :: rest) := by
  unfold ActCore; split <;> simp [DeliverCore]

theorem order_refuses_ask_after_failed_keep (c : Conf) (sh : Shape) (k : Option (Ring × ByteArray))
    (p : List Ring) (r : Ring) (q : Broker.Ask) (x : AskEnd) (rest : List Ev) :
    ¬ ActCore c sh k p (.keep r intentText false :: .ask r q x :: rest) := by
  unfold ActCore; split <;> simp [DeliverCore]

theorem order_refuses_intent_invoke (sh : Shape) (r : Ring) (x : AskEnd) (t : ByteArray)
    (y : Except String Reply) (rest : List Ev) :
    ¬ AfterAsk sh r x (.cmd (.invoke sh r t) y :: rest) := by
  unfold AfterAsk; split <;> simp

theorem order_refuses_second_ask (sh : Shape) (r r' : Ring) (x x' : AskEnd) (q : Broker.Ask)
    (rest : List Ev) : ¬ AfterAsk sh r x (.ask r' q x' :: rest) := by
  unfold AfterAsk; split <;> simp

theorem order_refuses_invoke_other (sh sh' : Shape) (r r' : Ring) (t t' : ByteArray)
    (hne : (r', t') ≠ (r, t)) (y : Except String Reply) (rest : List Ev) :
    ¬ DeliverCore sh r t (.cmd (.invoke sh' r' t') y :: rest) := by
  rintro ⟨x, rest', h, -⟩
  simp only [List.cons.injEq, Ev.cmd.injEq, Cmd.invoke.injEq] at h
  exact hne (by rw [h.1.1.2.1, h.1.1.2.2])

/-- A refused answer whose ring the re-read still lists is never followed directly by a forget: the
cells its answer cites are probed first, and with none of them gone the kept text stays for the
restart. -/
theorem order_refuses_forget_while_pending (sh : Shape) (r : Ring) (t : ByteArray) (rr : Reply)
    (href : rr.exit = Protocol.CommandExit.refused.code) (y : Except String Reply) (p : List Ring)
    (hp : readRings sh y = some p) (hr : r ∈ p) (b : Bool) :
    ¬ DeliverCore sh r t [.cmd (.invoke sh r t) (.ok rr), .cmd (.reread sh) y, .forget b] := by
  rintro ⟨x, rest, h, hd⟩
  simp only [List.cons.injEq, Ev.cmd.injEq, true_and] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [DeliverAfter, href, if_true] at hd
  obtain ⟨y', rest', h', hd'⟩ := hd
  simp only [List.cons.injEq, Ev.cmd.injEq, true_and] at h'
  obtain ⟨rfl, rfl⟩ := h'
  simp only [hp, RefusedCore, if_pos hr] at hd'
  cases hc : aimCells r with
  | nil =>
    rw [hc] at hd'
    have hs := useChoice_stop (gone := []) hr (fun c h => by simp [hc] at h)
    rw [ProbesCore, if_pos hs] at hd'
    cases hd'
  | cons c cs =>
    rw [hc] at hd'
    simp only [ProbesCore] at hd'
    obtain ⟨y', rest', h', -⟩ := hd'
    cases h'

theorem order_refuses_invoke_unkept (c : Conf) (sh : Shape) (p : List Ring) (r : Ring)
    (t : ByteArray) (y : Except String Reply) (rest : List Ev) :
    ¬ ActCore c sh none p (.cmd (.invoke sh r t) y :: rest) := by
  have hn : ∀ r t, decideTick p none ≠ .answer r t := by
    intro r t; cases p <;> simp [decideTick]
  unfold ActCore
  split
  · simp
  · rename_i hd; exact absurd hd (hn _ _)
  · simp

theorem order_refuses_two_describes (c : Conf) (m : Mem) (y y' : Except String Reply)
    (rest : List Ev) : ¬ TickCore c m (.cmd .describe y :: .cmd .describe y' :: rest) := by
  unfold TickCore
  split
  · simp [ReadCore]
  · rintro ⟨_, _, h, h'⟩
    simp only [List.cons.injEq, Ev.cmd.injEq] at h
    obtain ⟨-, rfl⟩ := h
    split at h'
    · simp at h'
    · simp [ReadCore] at h'

theorem order_refuses_describe_with_shape (c : Conf) (m : Mem) (sh : Shape) (hs : m.shape = some sh)
    (y : Except String Reply) (rest : List Ev) : ¬ TickCore c m (.cmd .describe y :: rest) := by
  unfold TickCore; rw [hs]; simp [ReadCore]

/-! ## Reach: the ask arm is a path -/

theorem deliver_runs {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {arg : String}
    (h : answerArg r t = some arg) :
    Runs (deliverP sh m r t) [.cmd (.invoke sh r t) (.error "e"), .say "answer unsettled e"]
      (retry m "answer e") := by
  unfold deliverP
  rw [h]
  exact Runs.cmd (.error "e") (Runs.say (Runs.done _))

/-- For every ring `decideTick` asks about and every answer the broker could give, a path keeps the
intent, asks, keeps the answer and invokes it. -/
theorem ask_path_exists {w : Where} {sh : Shape} {m : Mem} {p : List Ring} {r : Ring}
    (hd : decideTick (live m p) m.kept = .ask r) (ans : Broker.Answer) :
    ∃ es a, Runs (actOn w sh m p) es a ∧ asks (core es) = [r] ∧
      invokes (core es) = [(r, answerText ans)] := by
  obtain ⟨arg, harg⟩ :=
    Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r (answerText ans))
  unfold actOn
  rw [serveChoice_eq, hd]
  let t := answerText ans
  refine ⟨[.keep r intentText true, .ask r (askOf w.conf r) (.answered ans),
    .say s!"asked; answer {t.size} bytes", .keep r t true, .cmd (.invoke sh r t) (.error "e"),
    .say "answer unsettled e"], retry { m with kept := some (r, t) } "answer e", ?_, by simp [asks],
    by simp [invokes, t]⟩
  apply Runs.keep true
  apply Runs.ask (.answered ans)
  apply Runs.say
  apply Runs.keep true
  simp only [if_true]
  exact deliver_runs harg

/-! ## The interpreter performs exactly a path -/

/-- `tick` is the tree performed by the deployed handler, by definition. -/
theorem tick_def (w : Where) (m : Mem) : tick w m = (tickP w m).interp (ioHandler w) := rfl

/-- `p`'s holes nest at most `n` deep on every path: a hole's filling fits one less. -/
inductive Fits : Nat → Prog Tick → Prop
  | ret {n : Nat} (a : Tick) : Fits n (.done a)
  | call {n : Nat} {op : Eff} {k : (r : Eff.Resp op) → Prog Tick} :
      (∀ r, Fits n (k r)) → Fits n (Lang.Contextual.Protocol.Prot.call (S := sig) (i := ()) op k)
  | hole {n : Nat} {h : Hole} : Fits n (fill h) → Fits (n + 1) (.hole h)

theorem Fits.mono {n : Nat} {p : Prog Tick} (h : Fits n p) : Fits (n + 1) p := by
  induction h with
  | ret a => exact .ret a
  | call _ ih => exact .call ih
  | hole _ ih => exact .hole ih

/-- Walk a term node by node: each call's continuation at every result, each `if` and `match`. -/
macro "fits_walk" : tactic => `(tactic| repeat (first
  | exact Fits.ret _
  | (apply Fits.call; intro x; dsimp only)
  | split))

theorem forgetThen_fits (n : Nat) (t : Tick) : Fits n (forgetThen t) := by
  unfold forgetThen; fits_walk

theorem useP_fits (n : Nat) (m : Mem) (r : Ring) (k line : String) (p : List Ring)
    (gone : List ByteArray) : Fits n (useP m r k line p gone) := by
  unfold useP
  split <;> first | exact Fits.ret _ | (apply Fits.call; intro _; exact forgetThen_fits _ _)

theorem probesP_fits (n : Nat) (sh : Shape) (m : Mem) (r : Ring) (k line : String) (p : List Ring) :
    ∀ (cs gone : List ByteArray), Fits (n + 1) (probesP sh m r k line p cs gone)
  | [], gone => by simp only [probesP]; exact Fits.hole (useP_fits _ _ _ _ _ _ _)
  | c :: cs, gone => by
    simp only [probesP]
    apply Fits.call
    intro y
    dsimp only
    split
    · exact probesP_fits n sh m r k line p cs _
    · exact probesP_fits n sh m r k line p cs _
    · exact Fits.call fun _ => Fits.ret _

theorem refusedP_fits (n : Nat) (sh : Shape) (m : Mem) (r : Ring) (k line : String) (p : List Ring) :
    Fits (n + 1) (refusedP sh m r k line p) := by
  unfold refusedP
  split
  · exact probesP_fits _ _ _ _ _ _ _ _ _
  · exact Fits.hole (useP_fits _ _ _ _ _ _ _)

theorem deliverP_fits (n : Nat) (sh : Shape) (m : Mem) (r : Ring) (t : ByteArray) :
    Fits (n + 1) (deliverP sh m r t) := by
  unfold deliverP
  repeat (first
    | exact Fits.ret _
    | exact forgetThen_fits _ _
    | exact refusedP_fits _ _ _ _ _ _ _
    | (apply Fits.call; intro x; dsimp only)
    | split)

theorem answeredP_fits (n : Nat) (sh : Shape) (m : Mem) (r : Ring) (t : ByteArray) :
    Fits (n + 1) (answeredP sh m r t) := by
  unfold answeredP
  repeat (first
    | exact Fits.ret _
    | exact deliverP_fits _ _ _ _ _
    | (apply Fits.call; intro x; dsimp only)
    | split)

theorem actOn_fits (n : Nat) (w : Where) (sh : Shape) (m : Mem) (p : List Ring) :
    Fits (n + 1) (actOn w sh m p) := by
  unfold actOn
  repeat (first
    | exact Fits.ret _
    | exact forgetThen_fits _ _
    | exact deliverP_fits _ _ _ _ _
    | exact answeredP_fits _ _ _ _ _
    | (apply Fits.call; intro x; dsimp only)
    | split)

theorem readP_fits (n : Nat) (w : Where) (sh : Shape) (m : Mem) : Fits (n + 2) (readP w sh m) := by
  unfold readP
  repeat (first
    | exact Fits.ret _
    | (apply Fits.hole; exact actOn_fits _ _ _ _ _)
    | (apply Fits.call; intro x; dsimp only)
    | split)

/-- **Every tick fits `holesMax`**: `serve`'s filling holds `use`, whose filling holds no hole. -/
theorem tickP_fits (w : Where) (m : Mem) : Fits holesMax (tickP w m) := by
  unfold tickP holesMax
  repeat (first
    | exact Fits.ret _
    | exact readP_fits _ _ _ _
    | (apply Fits.call; intro x; dsimp only)
    | split)

theorem interpN_call {M : Type → Type} [Monad M] [LawfulMonad M] (h : Handler M) (n : Nat) (op : Eff)
    (k : (r : Eff.Resp op) → Prog Tick) :
    Prog.interpN h n (Lang.Contextual.Protocol.Prot.call (S := sig) (i := ()) op k) =
      h.call op >>= fun r => Prog.interpN h n (k r) := by
  unfold Prog.interpN
  have : Lang.Contextual.Slot.interp (W := Empty) (fun op => h.call op) (fun hl => .ok (fill hl)) n
      (Lang.Contextual.Protocol.Prot.call (S := sig) (i := ()) op k) =
      h.call op >>= fun r =>
        Lang.Contextual.Slot.interp (W := Empty) (fun op => h.call op) (fun hl => .ok (fill hl)) n (k r) := by
    cases n <;> rfl
  rw [this, bind_assoc]

/-- **The interpreter performs exactly a path** (HOSTING-37): at the recording handler, whatever
results the oracle gives, `interpN` appends to the trace exactly one event per effect it passes,
in term order, with the result it continued on, filling each hole by `fill` as it reaches it, and
ends with the path's end: the appended events and the value are a `Runs` path, for every term whose
holes fit the bound. A node performed twice, skipped, or continued on another result would append a
trace that is no path (`interpTwice_no_path`). -/
theorem interp_runs (o : Oracle) {n : Nat} {p : Prog Tick} (hf : Fits n p) (c : Nat) (es : List Ev) :
    ∃ es', ((p.interpN (recorder o) n).run (c, es)).2.2 = es ++ es' ∧
      Runs p es' ((p.interpN (recorder o) n).run (c, es)).1 := by
  induction hf generalizing c es with
  | @ret n a =>
    have : (Prog.interpN (recorder o) n (.done a)).run (c, es) = (a, (c, es)) := by cases n <;> rfl
    exact ⟨[], by rw [this]; simp, by rw [this]; exact Runs.done a⟩
  | @call n op k _ ih =>
    rw [interpN_call]
    cases op with
    | cmd cm =>
      obtain ⟨es', h1, h2⟩ := ih (o.cmd c) (c + 1) (es ++ [.cmd cm (o.cmd c)])
      exact ⟨.cmd cm (o.cmd c) :: es', by simpa [Handler.call, recorder] using h1,
        by simpa [Handler.call, recorder] using Runs.cmd (o.cmd c) h2⟩
    | keep r t =>
      obtain ⟨es', h1, h2⟩ := ih (o.keep c) (c + 1) (es ++ [.keep r t (o.keep c)])
      exact ⟨.keep r t (o.keep c) :: es', by simpa [Handler.call, recorder] using h1,
        by simpa [Handler.call, recorder] using Runs.keep (o.keep c) h2⟩
    | forget =>
      obtain ⟨es', h1, h2⟩ := ih (o.forget c) (c + 1) (es ++ [.forget (o.forget c)])
      exact ⟨.forget (o.forget c) :: es', by simpa [Handler.call, recorder] using h1,
        by simpa [Handler.call, recorder] using Runs.forget (o.forget c) h2⟩
    | ask r q =>
      obtain ⟨es', h1, h2⟩ := ih (o.ask c) (c + 1) (es ++ [.ask r q (o.ask c)])
      exact ⟨.ask r q (o.ask c) :: es', by simpa [Handler.call, recorder] using h1,
        by simpa [Handler.call, recorder] using Runs.ask (o.ask c) h2⟩
    | say s =>
      obtain ⟨es', h1, h2⟩ := ih () (c + 1) (es ++ [.say s])
      exact ⟨.say s :: es', by simpa [Handler.call, recorder] using h1,
        by simpa [Handler.call, recorder] using Runs.say h2⟩
  | @hole n hl _ ih =>
    obtain ⟨es', h1, h2⟩ := ih c es
    exact ⟨es', h1, Runs.hole h2⟩

/-- So every order theorem holds of what the interpreter performs: the tick's recorded trace is
`TickCore` (and `tick_counts`, `kept_follows` follow the same way). -/
theorem interp_order (o : Oracle) (w : Where) (m : Mem) :
    TickCore w.conf m (core (((tickP w m).interp (recorder o)).run (0, [])).2.2) := by
  obtain ⟨es', h1, h2⟩ := interp_runs o (tickP_fits w m) 0 []
  unfold Prog.interp
  rw [h1]
  simpa using tick_order h2

/-- Tooth: an interpreter that performs a node's call twice (`interpTwice`) records, for some tree
and every oracle, a trace that is no path of that tree: `interp_runs` refutes it. -/
theorem interpTwice_no_path (o : Oracle) :
    ¬ Runs (Prog.cmd .describe fun _ => .done (.stop .lifetime ""))
      (((Prog.cmd .describe fun _ => .done (.stop .lifetime "")).interpTwice (recorder o)).run (0, [])).2.2
      (.stop .lifetime "") := by
  intro h
  simp only [Prog.interpTwice, Lang.Contextual.Protocol.fold, recorder] at h
  cases h with
  | cmd _ h => cases h

end Nanodregg.Hosting.Proofs.ResidentRun
