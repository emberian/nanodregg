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

/-- A path through a tree: the effects it performs, with SOME result for each, and its end. -/
inductive Runs {α : Type} : Prog α → List Ev → α → Prop
  | done (a : α) : Runs (.done a) [] a
  | cmd {c k es a} (x : Except String Reply) : Runs (k x) es a → Runs (.cmd c k) (.cmd c x :: es) a
  | keep {r t k es a} (b : Bool) : Runs (k b) es a → Runs (.keep r t k) (.keep r t b :: es) a
  | forget {k es a} (b : Bool) : Runs (k b) es a → Runs (.forget k) (.forget b :: es) a
  | ask {r q k es a} (x : AskEnd) : Runs (k x) es a → Runs (.ask r q k) (.ask r q x :: es) a
  | say {s k es a} : Runs k es a → Runs (.say s k) (.say s :: es) a

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
        | some p => if r ∈ p then rest' = [] else ∃ b, rest' = [.forget b]
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

/-- The read at `sh`, then (if it returned rings) the act on them. -/
def ReadCore (c : Conf) (sh : Shape) (k : Option (Ring × ByteArray)) (es : List Ev) : Prop :=
  ∃ y rest, es = .cmd (.read sh) y :: rest ∧
    match readRings sh y with
    | none => rest = []
    | some p => ActCore c sh k p rest

/-- A tick's effects: with a shape, the read and the act; without one, the describe first, then
(if the description read as a bell) the read and the act at the shape it read. -/
def TickCore (c : Conf) (m : Mem) (es : List Ev) : Prop :=
  match m.shape with
  | some sh => ReadCore c sh m.kept es
  | none => ∃ y rest, es = .cmd .describe y :: rest ∧
      match describedShape y with
      | none => rest = []
      | some sh => ReadCore c sh m.kept rest

/-! ## The order -/

theorem forgetThen_core {n : Tick} {es : List Ev} {a : Tick} (h : Runs (forgetThen n) es a) :
    ∃ b, core es = [.forget b] := by
  unfold forgetThen at h
  cases h with
  | forget b h => cases b <;> simp at h <;> cases h <;> exact ⟨_, rfl⟩

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
              cases h with | say h => split at h <;> cases h <;> rfl
            · simp only at h ⊢
              split at h
              · rename_i hx
                simp only [hx, if_false]
                cases h with | say h => split at h <;> cases h <;> rfl
              · rename_i hx
                simp only [Decidable.not_not] at hx
                simp only [hx, if_true]
                split at h
                · rename_i e he
                  simp only [he, Except.toOption]
                  cases h; rfl
                · rename_i p hp
                  simp only [hp, Except.toOption]
                  split at h
                  · rename_i hr
                    simp only [hr, if_true]
                    cases h; rfl
                  · rename_i hr
                    simp only [hr, if_false]
                    cases h with
                    | say h => obtain ⟨b, hb⟩ := forgetThen_core h; exact ⟨b, by simp [hb]⟩
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
    (h : Runs (actOn w sh m p) es a) : ActCore w.conf sh m.kept p (core es) := by
  unfold actOn at h
  unfold ActCore
  rcases hd : decideTick p m.kept with _ | ring | ⟨ring, t⟩
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
    (h : Runs (readP w sh m) es a) : ReadCore w.conf sh m.kept (core es) := by
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
          exact actOn_core h

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
            cases h with | say h => cases h; rfl

/-! ## Counted: what the order says, stated on its own -/

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
          · split at hr'
            · subst hr'; simp [asks, invokes, describes]
            · obtain ⟨b, rfl⟩ := hr'; simp [asks, invokes, describes]
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
theorem read_counts {c : Conf} {sh : Shape} {k : Option (Ring × ByteArray)} {es : List Ev}
    (h : ReadCore c sh k es) :
    describes es = 0 ∧
    (asks es = [] ∨ ∃ r y p x post, readRings sh y = some p ∧ decideTick p k = .ask r ∧
      asks es = [r] ∧ es = .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf c r) x :: post) ∧
    (invokes es = [] ∨ ∃ r t, invokes es = [(r, t)] ∧
      ((∃ y p, readRings sh y = some p ∧ decideTick p k = .answer r t ∧ asks es = []) ∨
       ∃ y p x z post, readRings sh y = some p ∧ decideTick p k = .ask r ∧ askText x = some t ∧
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
- at most one ask: for a ring `r` that `decideTick` chose from the rings the tick's read returned
  (`ask_is_head`: the head, so the lowest pending), right after the intent was kept for `r`;
- at most one invoke: of the kept answer the decision named (no ask on that path), or of the text
  this tick's ask ended with (`askText`), right after that text was kept (the intent replaced). -/
theorem tick_counts {w : Where} {m : Mem} {es : List Ev} {a : Tick} (h : Runs (tickP w m) es a) :
    describes (core es) ≤ 1 ∧ (0 < describes (core es) → m.shape = none) ∧
    (asks (core es) = [] ∨ ∃ r sh y p x pre post, readRings sh y = some p ∧
      decideTick p m.kept = .ask r ∧ asks (core es) = [r] ∧
      core es = pre ++ .cmd (.read sh) y :: .keep r intentText true :: .ask r (askOf w.conf r) x :: post) ∧
    (invokes (core es) = [] ∨ ∃ r t, invokes (core es) = [(r, t)] ∧
      ((∃ sh y p, readRings sh y = some p ∧ decideTick p m.kept = .answer r t ∧ asks (core es) = []) ∨
       ∃ sh y p x z pre post, readRings sh y = some p ∧ decideTick p m.kept = .ask r ∧
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

theorem deliver_kept {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (deliverP sh m r t) es (.next m')) : m'.kept = keptAfter m.kept es := by
  unfold deliverP at h
  split at h
  · cases h
  · cases h with
    | cmd x h =>
      simp only [keptAfter]
      rcases x with e | rr
      · simp only at h; cases h with | say h => cases h; rfl
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
                cases h with | say h => split at h <;> cases h; rfl
              · simp only at h
                split at h
                · cases h with | say h => split at h <;> cases h; rfl
                · split at h
                  · cases h
                  · split at h
                    · cases h
                    · cases h with
                      | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
          · cases h with | say h => cases h; rfl

/-- **An abandoned ring does not stop the queue** (cv 01a1682e-7f9d, LANG-76): an answer refused
while the re-read `pending` no longer lists its ring (another member retired it between the read
and the answer) ends the tick `next`, its kept answer forgotten, or `volume` if the forget failed;
never `answerRefused`. The next tick reads the queue again. -/
theorem deliver_gone_continues {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {n : Tick}
    (h : Runs (deliverP sh m r t) es n) {rr : Reply} (href : rr.exit = Protocol.CommandExit.refused.code)
    {y : Except String Reply} {p : List Ring} (hp : readRings sh y = some p) (hr : r ∉ p) {rest : List Ev}
    (hes : es = .cmd (.invoke sh r t) (.ok rr) :: .cmd (.reread sh) y :: rest) :
    n = .next { m with kept := none, unread := 0 } ∨ n = .stop .volume "forget" := by
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
          cases hra : Ring.readAll sh ((String.fromUTF8? rr'.stdout).getD "") with
          | error e => rw [hra] at hp; simp [Except.toOption] at hp
          | ok q =>
            rw [hra] at hp
            simp only [Except.toOption, Option.some.injEq] at hp
            subst hp
            simp only [hra, if_neg hr] at h
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
            | say h => obtain ⟨hn, rfl⟩ := forgetThen_next h; cases hn; rfl
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
    · simp only at h; cases h with | say h => cases h; rfl
    · simp only at h
      split at h
      · cases h with | say h => cases h; rfl
      · split at h
        · cases h
        · exact actOn_kept h

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
      · simp only at h; cases h with | say h => cases h; rfl
      · simp only at h
        split at h
        · cases h with | say h => cases h; rfl
        · split at h
          · cases h with | say h => simpa using read_kept h
          · cases h with | say h => cases h

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

/-- A refused answer whose ring the re-read still lists is never followed by a forget: the kept
text stays for the restart. -/
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
  simp [hp, hr] at hd'

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
      (.next m) := by
  unfold deliverP
  rw [h]
  exact Runs.cmd (.error "e") (Runs.say (Runs.done _))

/-- For every ring `decideTick` asks about and every answer the broker could give, a path keeps the
intent, asks, keeps the answer and invokes it. -/
theorem ask_path_exists {w : Where} {sh : Shape} {m : Mem} {p : List Ring} {r : Ring}
    (hd : decideTick p m.kept = .ask r) (ans : Broker.Answer) :
    ∃ es a, Runs (actOn w sh m p) es a ∧ asks (core es) = [r] ∧
      invokes (core es) = [(r, answerText ans)] := by
  obtain ⟨arg, harg⟩ :=
    Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r (answerText ans))
  unfold actOn
  rw [hd]
  let t := answerText ans
  refine ⟨[.keep r intentText true, .ask r (askOf w.conf r) (.answered ans),
    .say s!"asked; answer {t.size} bytes", .keep r t true, .cmd (.invoke sh r t) (.error "e"),
    .say "answer unsettled e"], .next { m with kept := some (r, t) }, ?_, by simp [asks],
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

/-- **The interpreter performs exactly a path** (HOSTING-37): at the recording handler, whatever
results the oracle gives, `interp` appends to the trace exactly one event per node it passes, in
tree order, with the result it continued on, and ends with the path's end: the appended events
and the value are a `Runs` path. A node performed twice, skipped, or continued on another result
would append a trace that is no path (`two_calls_no_path`). -/
theorem interp_runs (o : Oracle) {α : Type} (p : Prog α) (n : Nat) (es : List Ev) :
    ∃ es', ((p.interp (recorder o)).run (n, es)).2.2 = es ++ es' ∧
      Runs p es' ((p.interp (recorder o)).run (n, es)).1 := by
  induction p generalizing n es with
  | done a => exact ⟨[], by simp [Prog.interp]; rfl, Runs.done a⟩
  | cmd c k ih =>
    obtain ⟨es', h1, h2⟩ := ih (o.cmd n) (n + 1) (es ++ [.cmd c (o.cmd n)])
    exact ⟨.cmd c (o.cmd n) :: es', by simpa [Prog.interp, recorder] using h1,
      by simpa [Prog.interp, recorder] using Runs.cmd (o.cmd n) h2⟩
  | keep r t k ih =>
    obtain ⟨es', h1, h2⟩ := ih (o.keep n) (n + 1) (es ++ [.keep r t (o.keep n)])
    exact ⟨.keep r t (o.keep n) :: es', by simpa [Prog.interp, recorder] using h1,
      by simpa [Prog.interp, recorder] using Runs.keep (o.keep n) h2⟩
  | forget k ih =>
    obtain ⟨es', h1, h2⟩ := ih (o.forget n) (n + 1) (es ++ [.forget (o.forget n)])
    exact ⟨.forget (o.forget n) :: es', by simpa [Prog.interp, recorder] using h1,
      by simpa [Prog.interp, recorder] using Runs.forget (o.forget n) h2⟩
  | ask r q k ih =>
    obtain ⟨es', h1, h2⟩ := ih (o.ask n) (n + 1) (es ++ [.ask r q (o.ask n)])
    exact ⟨.ask r q (o.ask n) :: es', by simpa [Prog.interp, recorder] using h1,
      by simpa [Prog.interp, recorder] using Runs.ask (o.ask n) h2⟩
  | say s k ih =>
    obtain ⟨es', h1, h2⟩ := ih (n + 1) (es ++ [.say s])
    exact ⟨.say s :: es', by simpa [Prog.interp, recorder] using h1,
      by simpa [Prog.interp, recorder] using Runs.say h2⟩

/-- So every order theorem holds of what the interpreter performs: the tick's recorded trace is
`TickCore` (and `tick_counts`, `kept_follows` follow the same way). -/
theorem interp_order (o : Oracle) (w : Where) (m : Mem) :
    TickCore w.conf m (core (((tickP w m).interp (recorder o)).run (0, [])).2.2) := by
  obtain ⟨es', h1, h2⟩ := interp_runs o (tickP w m) 0 []
  rw [h1]
  simpa using tick_order h2

/-- Tooth: an interpreter that performs a node's call twice (`interpTwice`) records, for some tree
and every oracle, a trace that is no path of that tree: `interp_runs` refutes it. -/
theorem interpTwice_no_path (o : Oracle) :
    ¬ Runs (Prog.cmd .describe fun _ => .done ())
      (((Prog.cmd .describe fun _ => .done ()).interpTwice (recorder o)).run (0, [])).2.2 () := by
  intro h
  simp only [Prog.interpTwice, recorder] at h
  cases h with
  | cmd _ h => cases h

end Nanodregg.Hosting.Proofs.ResidentRun
