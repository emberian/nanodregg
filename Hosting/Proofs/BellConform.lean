/-
# Hosting.Proofs.BellConform — the resident keeps the Bell's round across ticks (PROT-3's host half)

The Bell's round is one exchange: a ring, ONE ask about it, one answer (`Hosting.Resident.Bell`'s
header: "Exactly one ask per ring"; the meter is charged per ask). `Proofs.ResidentRun.tick_order`
states one tick's effects as a function of what `decideTick` chose, so it holds of ANY `decideTick`,
and `tick_counts` is one ask per TICK. Nothing there says the next tick will not ask the same ring
again. This module states it across ticks: once an ask about a ring has left in full, the resident
asks about that ring again only after something FREED it, an invoke of its answer that came back
`ok`, or a read of the pending rings that no longer listed it.

- `ResidentRun.Ticks w m ess`: a chain of ticks of one process life, each a path of `tickP` (every
  reply, every keep and forget result, `Runs`), each tick from the memory the last one went on with.
- (private) `debtRun`: reading a trace, the ring whose spent ask is not yet freed; an ask while one is owed
  breaks the round (`none`); a spent ask owes its ring (a not-sent ask owes nothing: it is forgotten
  and may be asked again, as the meter was not charged); `frees r` clears it.
- `bell_resident_conforms`: on every chain, between two asks about one ring, the first spent, an
  effect in between frees it.

The tooth is `decideTick`'s kept-pending check. Drop it (a kept ring still pending is asked about
again) and a chain asks twice with nothing in between, while `tick_order` and `tick_counts` stay
true of the planted `decideTick`: `act_debt` reads `decideTick`'s own arms, not the
`Proofs.Resident.decide_*` facts, so the plant names this proof.

What this is NOT: the plan's `proj bellG resident`. There is no global type here (PROT-3 runs on the
cheap branch, plan §8.5: the Bell is two kernel roles and one round), so no theorem says these paths
are a projection's; PROT-3's object half is the kernel's (`machine_reached` and a docstring), not a
`bell_object_conforms` stated here. The paths are protocol paths through
`Lang.Proofs.Contextual.Protocol.nano_runs_iff` (cited, not re-proved). One process life: across a
restart the kept answer is the volume's (`Proofs.ResidentVolume`), not composed here. Nothing about
the member socket is assumed: an `ok` invoke frees the ring by the resident's own reading, and what
the member's World holds then is E2's, not this module's.
-/
import Hosting.Proofs.ResidentRun

namespace Nanodregg.Hosting.Proofs.BellConform

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun

/-- An effect that frees ring `r` for another ask: an invoke of `r`'s answer answered `ok`, or a read
of the pending rings (the tick's read or the re-read) that listed them without `r`. -/
def Frees (r : Ring) : Ev → Prop
  | .cmd (.invoke _ r' _) (.ok rr) => r' = r ∧ rr.exit = Protocol.CommandExit.ok.code
  | .cmd (.read sh) y => ∃ p, readRings sh y = some p ∧ r ∉ p
  | .cmd (.reread sh) y => ∃ p, readRings sh y = some p ∧ r ∉ p
  | _ => False

/-- `Frees`, decided (the round below is a fold over it). -/
private def frees (r : Ring) : Ev → Bool
  | .cmd (.invoke _ r' _) (.ok rr) => decide (r' = r) && decide (rr.exit = Protocol.CommandExit.ok.code)
  | .cmd (.read sh) y => match readRings sh y with
    | some p => !decide (r ∈ p)
    | none => false
  | .cmd (.reread sh) y => match readRings sh y with
    | some p => !decide (r ∈ p)
    | none => false
  | _ => false

private theorem frees_true {r : Ring} {e : Ev} (h : frees r e = true) : Frees r e := by
  cases e with
  | cmd c x =>
    cases c with
    | invoke sh r' t =>
      cases x with
      | error _ => simp [frees] at h
      | ok rr => simp only [frees, Bool.and_eq_true, decide_eq_true_eq] at h; exact h
    | read sh =>
      simp only [frees] at h
      split at h
      · rename_i p hp; exact ⟨p, hp, by simpa using h⟩
      · cases h
    | reread sh =>
      simp only [frees] at h
      split at h
      · rename_i p hp; exact ⟨p, hp, by simpa using h⟩
      · cases h
    | describe => simp [frees] at h
  | _ => simp [frees] at h

/-- One effect on the owed ring: an ask while a ring is owed breaks the round (`none`); an ask
owes its ring when it was spent (`askText`: it left in full); anything else frees the owed ring
when it `frees` it. -/
private def debtStep (d : Option Ring) : Ev → Option (Option Ring)
  | .ask r _ x => match d with
    | none => some (if (askText x).isSome then some r else none)
    | some _ => none
  | e => some (match d with
    | some r => if frees r e then none else some r
    | none => none)

/-- The owed ring after a trace, from `d`; `none` if the trace breaks the round. -/
private def debtRun : Option Ring → List Ev → Option (Option Ring)
  | d, [] => some d
  | d, e :: es => (debtStep d e).bind fun d' => debtRun d' es

/-- The memory holds the owed ring's answer (or intent). -/
private def Owes (k : Option (Ring × ByteArray)) (d : Option Ring) : Prop :=
  ∀ r, d = some r → ∃ t, k = some (r, t)

private theorem owes_none (k : Option (Ring × ByteArray)) : Owes k none := by
  intro r h; cases h

private theorem debtRun_append (d : Option Ring) (l₁ l₂ : List Ev) :
    debtRun d (l₁ ++ l₂) = (debtRun d l₁).bind fun d' => debtRun d' l₂ := by
  induction l₁ generalizing d with
  | nil => simp [debtRun]
  | cons e l ih =>
    simp only [List.cons_append, debtRun]
    cases debtStep d e with
    | none => rfl
    | some d' => simp [ih]

theorem keptAfter_core (k : Option (Ring × ByteArray)) (es : List Ev) :
    keptAfter k (core es) = keptAfter k es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | say s => simp [ih]
    | keep r t b => cases b <;> simp [keptAfter, ih]
    | forget b => cases b <;> simp [keptAfter, ih]
    | cmd c x => simp [keptAfter, ih]
    | ask r q x => simp [keptAfter, ih]

/-! ## One tick keeps the round -/

/-- `deliver r t` from a memory holding `(r, t)`, with nothing owed or `r` owed. -/
private theorem deliver_debt {sh : Shape} {r : Ring} {t : ByteArray} {l : List Ev} {d : Option Ring}
    (h : DeliverCore sh r t l) (hd : d = none ∨ d = some r) :
    ∃ d', debtRun d l = some d' ∧ Owes (keptAfter (some (r, t)) l) d' := by
  obtain ⟨x, rest, rfl, ha⟩ := h
  rcases x with e | rr
  · simp only [DeliverAfter] at ha
    subst ha
    rcases hd with rfl | rfl
    · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
    · refine ⟨some r, by simp [debtRun, debtStep, frees], ?_⟩
      intro q hq; cases hq; exact ⟨t, rfl⟩
  · simp only [DeliverAfter] at ha
    split at ha
    · rename_i hok
      obtain ⟨b, rfl⟩ := ha
      refine ⟨none, ?_, owes_none _⟩
      rcases hd with rfl | rfl <;> simp [debtRun, debtStep, frees, hok]
    · rename_i hok
      split at ha
      · rename_i href
        obtain ⟨y, rest', rfl, hy⟩ := ha
        split at hy
        · rename_i p hp
          split at hy
          · rename_i hr
            subst hy
            rcases hd with rfl | rfl
            · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
            · refine ⟨some r, by simp [debtRun, debtStep, frees, hok, hp, hr], ?_⟩
              intro q hq; cases hq; exact ⟨t, by simp [keptAfter]⟩
          · rename_i hr
            obtain ⟨b, rfl⟩ := hy
            refine ⟨none, ?_, owes_none _⟩
            rcases hd with rfl | rfl <;> simp [debtRun, debtStep, frees, hok, hp, hr]
        · rename_i hp
          subst hy
          rcases hd with rfl | rfl
          · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
          · refine ⟨some r, by simp [debtRun, debtStep, frees, hok, hp], ?_⟩
            intro q hq; cases hq; exact ⟨t, by simp [keptAfter]⟩
      · rename_i href
        subst ha
        rcases hd with rfl | rfl
        · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
        · refine ⟨some r, by simp [debtRun, debtStep, frees, hok], ?_⟩
          intro q hq; cases hq; exact ⟨t, rfl⟩

/-- After a spent or unsent ask about `r`: what `AfterAsk` leaves owes at most `r`. -/
private theorem afterAsk_debt {sh : Shape} {r : Ring} {x : AskEnd} {l : List Ev}
    (h : AfterAsk sh r x l) :
    ∃ d', debtRun (if (askText x).isSome then some r else none) l = some d' ∧
      Owes (keptAfter (some (r, intentText)) l) d' := by
  unfold AfterAsk at h
  split at h
  · rename_i hx
    obtain ⟨b, rfl⟩ := h
    exact ⟨none, by simp [hx, debtRun, debtStep], owes_none _⟩
  · rename_i t hx
    simp only [hx, Option.isSome_some, if_true]
    rcases h with rfl | ⟨rest, rfl, hd⟩
    · refine ⟨some r, by simp [debtRun, debtStep, frees], ?_⟩
      intro q hq; cases hq; exact ⟨intentText, by simp [keptAfter]⟩
    · obtain ⟨d', h1, h2⟩ := deliver_debt hd (.inr rfl)
      refine ⟨d', by simpa [debtRun, debtStep, frees] using h1, ?_⟩
      simpa [keptAfter] using h2

/-- The act on the rings `p` a read returned, from a memory `k` that holds what is owed, with the
owed ring among `p` (the read did not free it). Read off `decideTick`'s own arms, not its
`Proofs.Resident.decide_*` facts, so a `decideTick` that asks while its kept ring is pending stops
THIS proof (the ask arm with `r` owed and pending). -/
private theorem act_debt {c : Conf} {sh : Shape} {k : Option (Ring × ByteArray)} {p : List Ring}
    {l : List Ev} {d : Option Ring} (h : ActCore c sh k p l) (hd : Owes k d)
    (hp : ∀ r, d = some r → r ∈ p) :
    ∃ d', debtRun d l = some d' ∧ Owes (keptAfter k l) d' := by
  -- nothing owed: only the act's own ask can owe, and `deliver` of a kept pair owes nothing new
  cases d with
  | none =>
    unfold ActCore at h
    split at h
    · rcases h with ⟨-, b, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
      · exact ⟨none, by simp [debtRun], owes_none _⟩
    · rename_i r t hdec
      have hk : k = some (r, t) := by
        unfold decideTick at hdec
        split at hdec
        · split at hdec
          · cases hdec; rfl
          · split at hdec <;> cases hdec
        · split at hdec <;> cases hdec
      subst hk
      exact deliver_debt h (.inl rfl)
    · rcases h with rfl | ⟨x, rest, rfl, ha⟩
      · exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
      · obtain ⟨d', h1, h2⟩ := afterAsk_debt ha
        exact ⟨d', by simpa [debtRun, debtStep] using h1, by simpa [keptAfter] using h2⟩
  -- `q` owed: the memory holds `q`'s pair and `q` is pending, so `decideTick` answers it
  | some q =>
    obtain ⟨u, rfl⟩ := hd q rfl
    have hq := hp q rfl
    unfold ActCore at h
    split at h
    · rename_i hdec
      simp only [decideTick, hq, if_true] at hdec
      cases hdec
    · rename_i r t hdec
      simp only [decideTick, hq, if_true, Act.answer.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      exact deliver_debt h (.inr rfl)
    · rename_i r hdec
      simp only [decideTick, hq, if_true] at hdec
      cases hdec

/-- A read at `sh`, then the act. The read itself frees the owed ring when it lists the rings
without it, so the act sees an owed ring only among the rings it read. -/
private theorem read_debt {c : Conf} {sh : Shape} {k : Option (Ring × ByteArray)} {l : List Ev}
    {d : Option Ring} (h : ReadCore c sh k l) (hd : Owes k d) :
    ∃ d', debtRun d l = some d' ∧ Owes (keptAfter k l) d' := by
  obtain ⟨y, rest, rfl, hy⟩ := h
  split at hy
  · rename_i hr
    subst hy
    cases d with
    | none => exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
    | some q =>
      refine ⟨some q, by simp [debtRun, debtStep, frees, hr], ?_⟩
      simpa [keptAfter] using hd
  · rename_i p hr
    cases d with
    | none =>
      obtain ⟨d', h1, h2⟩ := act_debt hy (owes_none _) (fun _ h => by cases h)
      exact ⟨d', by simpa [debtRun, debtStep] using h1, by simpa [keptAfter] using h2⟩
    | some q =>
      by_cases hq : q ∈ p
      · obtain ⟨d', h1, h2⟩ := act_debt hy hd (fun r h => by cases h; exact hq)
        exact ⟨d', by simpa [debtRun, debtStep, frees, hr, hq] using h1,
          by simpa [keptAfter] using h2⟩
      · obtain ⟨d', h1, h2⟩ := act_debt hy (owes_none _) (fun _ h => by cases h)
        exact ⟨d', by simpa [debtRun, debtStep, frees, hr, hq] using h1,
          by simpa [keptAfter] using h2⟩

/-- **One tick keeps the round**: from a memory that holds what is owed, a tick's effects never ask
while a ring is owed, and what they leave owed is held by the memory they leave. -/
private theorem tickCore_debt {c : Conf} {m : Mem} {l : List Ev} {d : Option Ring} (h : TickCore c m l)
    (hd : Owes m.kept d) : ∃ d', debtRun d l = some d' ∧ Owes (keptAfter m.kept l) d' := by
  unfold TickCore at h
  split at h
  · exact read_debt h hd
  · obtain ⟨y, rest, rfl, hy⟩ := h
    split at hy
    · subst hy
      cases d with
      | none => exact ⟨none, by simp [debtRun, debtStep], owes_none _⟩
      | some q => exact ⟨some q, by simp [debtRun, debtStep, frees], by simpa [keptAfter] using hd⟩
    · obtain ⟨d', h1, h2⟩ := read_debt hy hd
      cases d with
      | none => exact ⟨d', by simpa [debtRun, debtStep] using h1, by simpa [keptAfter] using h2⟩
      | some q => exact ⟨d', by simpa [debtRun, debtStep, frees] using h1,
          by simpa [keptAfter] using h2⟩

/-! ## Across ticks -/

private theorem ticks_debt {w : Where} {m : Mem} {ess : List (List Ev)} {d : Option Ring}
    (h : Ticks w m ess) (hd : Owes m.kept d) : (debtRun d (core ess.flatten)).isSome := by
  induction h generalizing d with
  | nil m => simp [debtRun, core]
  | last hr =>
    obtain ⟨d', h1, -⟩ := tickCore_debt (tick_order hr) hd
    simp [h1]
  | next hr _ ih =>
    rename_i m m' es ess
    obtain ⟨d', h1, h2⟩ := tickCore_debt (tick_order hr) hd
    rw [List.flatten_cons, core_append, debtRun_append, h1]
    simp only [Option.bind_some]
    apply ih
    rw [kept_follows hr, ← keptAfter_core]
    exact h2

/-- Reading the round off a trace: between two asks about one ring, the first spent, an effect
frees it. -/
private theorem debtRun_frees {d : Option Ring} {pre mid post : List Ev} {r : Ring} {q q' : Broker.Ask}
    {x x' : AskEnd} (hx : (askText x).isSome)
    (h : (debtRun d (pre ++ .ask r q x :: mid ++ .ask r q' x' :: post)).isSome) :
    ∃ e ∈ mid, frees r e = true := by
  rw [List.append_assoc, debtRun_append] at h
  cases hpre : debtRun d pre with
  | none => simp [hpre] at h
  | some d₁ =>
    simp only [hpre, Option.bind_some, List.cons_append, debtRun] at h
    cases d₁ with
    | some _ => simp [debtStep] at h
    | none =>
      simp only [debtStep, hx, if_true, Option.bind_some] at h
      -- through `mid` the owed ring stays `r` until something frees it
      have key : ∀ (l : List Ev), (debtRun (some r) (l ++ .ask r q' x' :: post)).isSome →
          ∃ e ∈ l, frees r e = true := by
        intro l
        induction l with
        | nil => intro h; simp [debtRun, debtStep] at h
        | cons e l ih =>
          intro h
          by_cases hf : frees r e = true
          · exact ⟨e, List.mem_cons_self .., hf⟩
          · cases e with
            | ask r₀ q₀ x₀ => simp [debtRun, debtStep] at h
            | _ =>
              simp only [List.cons_append, debtRun, debtStep, hf, Bool.false_eq_true, if_false,
                Option.bind_some] at h
              obtain ⟨e', he', hf'⟩ := ih h
              exact ⟨e', List.mem_cons_of_mem _ he', hf'⟩
      exact key mid h

/-- **The resident keeps the Bell's round** (PROT-3's host half): on every chain of ticks, between
two asks about the same ring, the first of them spent (it left in full, so the meter was charged),
the trace holds an effect that freed the ring: an invoke of its answer that came back `ok`, or a
read of the pending rings that no longer listed it. With nothing freeing a ring, it is asked about
once. -/
theorem bell_resident_conforms {w : Where} {m : Mem} {ess : List (List Ev)} {r : Ring}
    {pre mid post : List Ev} {q q' : Broker.Ask} {x x' : AskEnd} (h : Ticks w m ess)
    (hc : core ess.flatten = pre ++ .ask r q x :: mid ++ .ask r q' x' :: post)
    (hx : (askText x).isSome) : ∃ e ∈ mid, Frees r e := by
  have hd := ticks_debt h (owes_none m.kept)
  rw [hc] at hd
  obtain ⟨e, he, hf⟩ := debtRun_frees hx hd
  exact ⟨e, he, frees_true hf⟩

end Nanodregg.Hosting.Proofs.BellConform
