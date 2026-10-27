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
- (private) `debtRun`: reading a trace, the rings whose spent ask is not yet freed (several at once:
  a ring whose answer was WITHDRAWN by the `use` slot stays owed while it waits, and the queue goes on
  past it); an ask about an owed ring breaks the round (`none`); a spent ask owes its ring (a not-sent
  ask owes nothing: it is forgotten and may be asked again, as the meter was not charged); `frees q`
  clears `q`. `Owes m D`: every owed ring is the kept answer's ring, or does not stand (`stands`), so no
  `serve` acts on it. Proved over the paths of the term (`Runs`), hole by hole: a withdrawal adds the
  ring to `Mem.withdrawn` and keeps it owed; `Mem.prune` drops only rings the same read freed.
- `bell_resident_conforms`: on every chain, between two asks about one ring, the first spent, an
  effect in between frees it.
- `undecodable_frees_nothing` (HOSTING-49): a read reply whose stdout is not UTF-8 frees no ring (it
  used to read as zero pending rings, freeing every one: the double ask READ-HOSTING D2 measured).

The tooth is `decideTick`'s kept-pending check (`decide_ask`: an ask only while the kept ring is not
live). Drop it (a kept ring still pending is asked about again) and a chain asks twice with nothing in
between, while `tick_order` and `tick_counts` stay true of the planted `decideTick`. The withdrawal
does not weaken the claim: `Frees` is unchanged, a withdrawn ring is never asked again while it waits.

What this is NOT: the plan's `proj bellG resident`. There is no global type here (PROT-3 runs on the
cheap branch, plan §8.5: the Bell is two kernel roles and one round), so no theorem says these paths
are a projection's; PROT-3's object half is the kernel's (`machine_reached` and a docstring), not a
`bell_object_conforms` stated here. The paths are paths of the resident's term, a protocol of the
open calculus (`Hosting.Resident.Prog`). One process life: across a
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

/-- **An undecodable read frees nothing** (HOSTING-49, READ-HOSTING D2): a read or re-read reply
whose stdout is not UTF-8 lists no rings (`readOut` refuses it `undecodable` before any parse), so it
never frees the ring the resident asked about, and a second ask of it is not permitted by
`bell_resident_conforms` on its account. Before HOSTING-49 such a reply read as `""`, zero pending
rings, and freed every ring. -/
theorem undecodable_frees_nothing {r : Ring} {sh : Shape} {rr : Reply}
    (h : String.fromUTF8? rr.stdout = none) :
    ¬ Frees r (.cmd (.read sh) (.ok rr)) ∧ ¬ Frees r (.cmd (.reread sh) (.ok rr)) := by
  have hn : readRings sh (.ok rr) = none := by
    simp only [readRings, readOut, h]
    split <;> rfl
  constructor <;> rintro ⟨p, hp, -⟩ <;> rw [hn] at hp <;> cases hp

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
    | probe _ => simp [frees] at h
  | _ => simp [frees] at h

theorem keptAfter_core (k : Option (Ring × ByteArray)) (es : List Ev) :
    keptAfter k (core es) = keptAfter k es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | say s => simp [ih]
    | keep r t b => cases b <;> simp [keptAfter, ih]
    | forget b => cases b <;> simp [keptAfter, ih]
    | note l b => simp [keptAfter, ih]
    | cmd c x => simp [keptAfter, ih]
    | ask r q x => simp [keptAfter, ih]

/-- One effect on the owed rings: an ask about an owed ring breaks the round (`none`); a spent ask
(`askText`: it left in full) owes its ring (a not-sent ask owes nothing: the meter was not charged);
anything else frees each owed ring it `frees`. Several rings may be owed at once: a ring whose
answer was WITHDRAWN (the `use` slot) stays owed while it waits, and the queue goes on past it. -/
private def debtStep (D : List Ring) : Ev → Option (List Ring)
  | .ask r _ x => if r ∈ D then none else some (if (askText x).isSome then r :: D else D)
  | e => some (D.filter fun q => !frees q e)

/-- The owed rings after a trace, from `D`; `none` if the trace breaks the round. -/
private def debtRun : List Ring → List Ev → Option (List Ring)
  | D, [] => some D
  | D, e :: es => (debtStep D e).bind fun D' => debtRun D' es

/-- The memory accounts for every owed ring: it is the kept answer's ring, or its answer was
withdrawn (it no longer stands, so no `serve` acts on it while it waits). -/
private def Owes (m : Mem) (D : List Ring) : Prop :=
  ∀ q ∈ D, (∃ t, m.kept = some (q, t)) ∨ stands m q = false

/-- A path keeps the round from the owed rings `D`: it never asks about an owed ring, and the memory
it goes on with (if it goes on) accounts for what it leaves owed. -/
private def Keeps (D : List Ring) (a : Tick) (es : List Ev) : Prop :=
  ∃ D', debtRun D (core es) = some D' ∧ ∀ m', a = .next m' → Owes m' D'

private theorem debtRun_append (D : List Ring) (l₁ l₂ : List Ev) :
    debtRun D (l₁ ++ l₂) = (debtRun D l₁).bind fun D' => debtRun D' l₂ := by
  induction l₁ generalizing D with
  | nil => simp [debtRun]
  | cons e l ih =>
    simp only [List.cons_append, debtRun]
    cases debtStep D e with
    | none => rfl
    | some D' => simp [ih]

/-- An effect that is not an ask leaves owed exactly the owed rings it does not free. -/
private theorem debtRun_free {D : List Ring} {e : Ev} {es : List Ev} (ha : ∀ r q x, e ≠ .ask r q x) :
    debtRun D (e :: es) = debtRun (D.filter fun q => !frees q e) es := by
  cases e with
  | ask r q x => exact absurd rfl (ha r q x)
  | _ => simp [debtRun, debtStep]

/-- An effect that is not an ask and frees nothing leaves the owed rings as they were. -/
private theorem debtRun_quiet {D : List Ring} {e : Ev} {es : List Ev} (hq : ∀ q, frees q e = false)
    (ha : ∀ r q x, e ≠ .ask r q x) : debtRun D (e :: es) = debtRun D es := by
  rw [debtRun_free ha]
  congr 1
  exact List.filter_eq_self.mpr (fun q _ => by simp [hq q])

private theorem owes_kept_none {m : Mem} {D : List Ring} {r : Ring} {t : ByteArray}
    (hk : m.kept = some (r, t)) (hD : Owes m D) (hr : r ∉ D) (n : Nat) :
    Owes { m with kept := none, retries := n } D := by
  intro q hq
  rcases hD q hq with ⟨u, hu⟩ | hs
  · rw [hk] at hu; cases hu; exact absurd hq hr
  · exact .inr hs

private theorem forgetThen_debt {n : Tick} {es : List Ev} {a : Tick} {D : List Ring}
    (h : Runs (forgetThen n) es a) (hn : ∀ m', n = .next m' → Owes m' D) : Keeps D a es := by
  unfold forgetThen at h
  cases h with
  | forget b h =>
    have hd : debtRun D (core (.forget b :: [])) = some D := by simp [debtRun, debtStep, frees]
    cases b
    · simp at h; cases h; exact ⟨D, hd, fun _ h => by cases h⟩
    · simp at h; cases h; exact ⟨D, hd, hn⟩

/-- A ring the `use` slot closed is no longer pending. -/
private theorem useChoice_closed {r : Ring} {p : List Ring} {gone : List ByteArray}
    (h : useChoice r p gone = .closed) : r ∉ p := by
  intro hr
  cases hf : (aimCells r).find? (fun x => gone.any fun g => decide (g = x)) with
  | none =>
    rw [useChoice_stop hr (fun c hc hg => by
      have := List.find?_eq_none.mp hf c hc
      simp only [List.any_eq_true, decide_eq_true_eq] at this
      exact this ⟨c, hg, rfl⟩)] at h
    cases h
  | some c => rw [useChoice_withdraw hr hf] at h; cases h

/-- What follows a refused answer keeps the round: a closed slot leaves owed only rings other than
the answered one, each withdrawn; a withdrawal adds the ring to the withdrawn, so it stays owed and
accounted for; a stop goes on with nothing. -/
private theorem useP_debt {m : Mem} {r : Ring} {t : ByteArray} {n line : String} {p : List Ring}
    {gone : List ByteArray} {es : List Ev} {a : Tick} {D : List Ring} (h : Runs (useP m r n line p gone) es a)
    (hk : m.kept = some (r, t)) (hD : Owes m D) (hp : ∀ q ∈ D, q ∈ p) : Keeps D a es := by
  unfold useP at h
  cases hc : useChoice r p gone with
  | closed =>
    rw [hc] at h
    have hr : r ∉ D := fun hr => useChoice_closed hc (hp r hr)
    cases h with
    | say h =>
      obtain ⟨D', hd, ho⟩ := forgetThen_debt h (fun m' hm => by
        cases hm; exact owes_kept_none hk hD hr 0)
      exact ⟨D', by simpa using hd, ho⟩
  | withdraw c =>
    rw [hc] at h
    cases h with
    | say h =>
      cases h with
      | note b h =>
        cases b
        · simp at h; cases h
          exact ⟨D, by simp [debtRun, debtStep, frees], fun _ h => by cases h⟩
        · simp only [if_true] at h
          obtain ⟨D', hd, ho⟩ := forgetThen_debt (D := D) h (fun m' hm => by
            cases hm
            intro q hq
            refine .inr ?_
            by_cases hqr : q = r
            · subst hqr; simp [stands]
            · rcases hD q hq with ⟨u, hu⟩ | hs
              · rw [hk] at hu; cases hu; exact absurd rfl hqr
              · simp only [stands, Bool.not_eq_false', List.any_eq_true] at hs ⊢
                obtain ⟨x, hx, he⟩ := hs
                exact ⟨x, List.mem_cons_of_mem _ hx, he⟩)
          exact ⟨D', by rw [core_say, core_note, debtRun_quiet (by simp [frees]) (by simp)]; exact hd, ho⟩
  | stop =>
    rw [hc] at h
    cases h
    exact ⟨D, by simp [debtRun], fun _ h => by cases h⟩

/-- Probes free nothing and ask nothing. -/
private theorem debtRun_probes {D : List Ring} {pre l : List Ev}
    (h : ∀ e ∈ pre, ∃ c y, e = .cmd (.probe c) y ∧ probeGone y ≠ none) :
    debtRun D (core pre ++ l) = debtRun D l := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
    obtain ⟨c, y, rfl, -⟩ := h e List.mem_cons_self
    rw [core_cmd, List.cons_append, debtRun_quiet (by simp [frees]) (by simp)]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- What follows the re-read of a refused answer keeps the round. -/
private theorem refused_debt {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {n line : String}
    {p : List Ring} {es : List Ev} {a : Tick} {D : List Ring} (h : Runs (refusedP sh m r n line p) es a)
    (hk : m.kept = some (r, t)) (hD : Owes m D) (hp : ∀ q ∈ D, q ∈ p) : Keeps D a es := by
  obtain ⟨pre, rest, rfl, hpre, hr⟩ := refusedP_path h
  rcases hr with ⟨c, y, s, why, rfl, -, rfl⟩ | ⟨gone, hr⟩
  · refine ⟨D, ?_, fun m' hm => ?_⟩
    · rw [core_append, debtRun_probes hpre, core_cmd, debtRun_quiet (by simp [frees]) (by simp)]
      simp [debtRun, core, Ev.quiet]
    · obtain rfl := retry_next hm; exact hD
  · obtain ⟨D', hd, ho⟩ := useP_debt hr hk hD hp
    exact ⟨D', by rw [core_append, debtRun_probes hpre]; exact hd, ho⟩

/-- `deliver r t` from a memory holding `(r, t)` keeps the round. -/
private theorem deliver_debt {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {a : Tick}
    {D : List Ring} (h : Runs (deliverP sh m r t) es a) (hk : m.kept = some (r, t)) (hD : Owes m D) :
    Keeps D a es := by
  have hret : ∀ {why : String} {es' : List Ev}, Runs (.done (retry m why)) es' a →
      ∀ D₀, (∀ q ∈ D₀, q ∈ D) → debtRun D₀ (core es') = some D₀ ∧ ∀ m', a = .next m' → Owes m' D₀ := by
    intro why es' h' D₀ hsub
    cases h'
    refine ⟨by simp [debtRun], fun m' hm => ?_⟩
    obtain rfl := retry_next hm
    exact fun q hq => hD q (hsub q hq)
  obtain ⟨arg, harg⟩ := Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r t)
  unfold deliverP at h
  rw [harg] at h
  cases h with
  | cmd x h =>
    rcases x with e | rr
    · simp only at h
      cases h with
      | say h =>
        obtain ⟨hd, ho⟩ := hret h D (fun _ h => h)
        exact ⟨D, by rw [core_cmd, debtRun_quiet (by simp [frees]) (by simp), core_say]; exact hd, ho⟩
    · simp only at h
      split at h
      · rename_i hok
        cases h with
        | say h =>
          have hr : r ∉ D.filter fun q => !frees q (.cmd (.invoke sh r t) (.ok rr)) := by
            simp [List.mem_filter, frees, hok]
          obtain ⟨D', hd, ho⟩ := forgetThen_debt h (fun m' hm => by
            cases hm
            exact owes_kept_none hk (fun q hq => hD q (List.mem_filter.mp hq).1) hr 0)
          exact ⟨D', by rw [core_cmd, debtRun_free (by simp), core_say]; exact hd, ho⟩
      · rename_i hok
        have hnf : ∀ q, frees q (.cmd (.invoke sh r t) (.ok rr)) = false := by simp [frees, hok]
        split at h
        · cases h with
          | cmd y h =>
            rcases y with e | rr'
            · simp only at h
              cases h with
              | say h =>
                obtain ⟨hd, ho⟩ := hret h D (fun _ h => h)
                refine ⟨D, ?_, ho⟩
                rw [core_cmd, debtRun_quiet hnf (by simp), core_cmd,
                  debtRun_quiet (by simp [frees, readRings]) (by simp), core_say]
                exact hd
            · simp only at h
              split at h
              · rename_i hx
                cases h with
                | say h =>
                  obtain ⟨hd, ho⟩ := hret h D (fun _ h => h)
                  refine ⟨D, ?_, ho⟩
                  rw [core_cmd, debtRun_quiet hnf (by simp), core_cmd,
                    debtRun_quiet (by simp [frees, readRings, hx]) (by simp), core_say]
                  exact hd
              · rename_i hx
                simp only [Decidable.not_not] at hx
                split at h
                · cases h; exact ⟨_, rfl, fun _ h => by cases h⟩
                · rename_i p hp
                  have hrr : readRings sh (.ok rr') = some p := by
                    simp [readRings, hx, hp, Except.toOption]
                  obtain ⟨D', hd, ho⟩ := refused_debt (D := D.filter fun q => decide (q ∈ p)) h hk
                    (fun q hq => hD q (List.mem_filter.mp hq).1)
                    (fun q hq => by simpa using (List.mem_filter.mp hq).2)
                  refine ⟨D', ?_, ho⟩
                  rw [core_cmd, debtRun_quiet hnf (by simp), core_cmd, debtRun_free (by simp)]
                  simpa [frees, hrr] using hd
        · cases h with
          | say h =>
            obtain ⟨hd, ho⟩ := hret h D (fun _ h => h)
            exact ⟨D, by rw [core_cmd, debtRun_quiet hnf (by simp), core_say]; exact hd, ho⟩

/-- After the ask, `answeredP` keeps the round from a memory that accounts for the debt with the
asked ring's answer kept. -/
private theorem answered_debt {sh : Shape} {m : Mem} {r : Ring} {t : ByteArray} {es : List Ev} {a : Tick}
    {D : List Ring} (h : Runs (answeredP sh m r t) es a) (hD : Owes { m with kept := some (r, t) } D) :
    Keeps D a es := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
        exact ⟨D, by simp [debtRun, debtStep, frees], fun _ h => by cases h⟩
      · simp only [if_true] at h
        obtain ⟨D', hd, ho⟩ := deliver_debt h rfl hD
        exact ⟨D', by rw [core_say, core_keep, debtRun_quiet (by simp [frees]) (by simp)]; exact hd, ho⟩

/-- The act on the rings `p` a read returned, from a memory that accounts for the debt, every owed
ring among `p` (the read freed the others). The ask arm is where the round could break: `decideTick`
asks only about a ring whose answer stands while the kept ring is not live (`decide_ask`), so never
about an owed ring. A `decideTick` that asked while its kept ring is live would stop this proof. -/
private theorem actOn_debt {w : Where} {sh : Shape} {m : Mem} {p : List Ring} {es : List Ev} {a : Tick}
    {D : List Ring} (h : Runs (actOn w sh m p) es a) (hD : Owes m D) (hp : ∀ q ∈ D, q ∈ p) :
    Keeps D a es := by
  have hlive : ∀ q, q ∈ live m p ↔ q ∈ p ∧ stands m q = true := by
    intro q; simp [live, List.mem_filter]
  -- an owed ring that is the kept one but not live does not stand
  have hnl : ∀ q ∈ D, (∀ u, m.kept = some (q, u) → q ∉ live m p) → stands m q = false := by
    intro q hq hk
    rcases hD q hq with ⟨u, hu⟩ | hs
    · have := hk u hu
      rw [hlive] at this
      cases hs : stands m q
      · rfl
      · exact absurd ⟨hp q hq, hs⟩ this
    · exact hs
  unfold actOn at h
  rw [serveChoice_eq] at h
  rcases hd : decideTick (live m p) m.kept with _ | ring | ⟨ring, t⟩
  · -- idle: the kept ring, if any, is not live
    rw [hd] at h
    have hk : ∀ q u, m.kept = some (q, u) → q ∉ live m p := by
      intro q u hu hq
      rw [hu, Nanodregg.Hosting.Proofs.Resident.decide_kept_first u hq] at hd
      cases hd
    have ho : Owes { m with kept := none, retries := 0 } D :=
      fun q hq => .inr (hnl q hq (fun u hu => hk q u hu))
    simp only at h
    split at h
    · exact forgetThen_debt h (fun m' hm => by cases hm; exact ho)
    · cases h; exact ⟨D, by simp [debtRun], fun m' hm => by cases hm; exact ho⟩
  · -- ask about `ring`: the head of the live rings, with the kept ring not live
    rw [hd] at h
    obtain ⟨hhead, hk⟩ := Nanodregg.Hosting.Proofs.Resident.decide_ask hd
    have hrl : ring ∈ live m p := by
      cases hl : live m p with
      | nil => rw [hl] at hhead; cases hhead
      | cons x xs => rw [hl] at hhead; cases hhead; exact List.mem_cons_self
    have hst : ∀ q ∈ D, stands m q = false := fun q hq => hnl q hq (fun u hu => hk q u hu)
    have hrD : ring ∉ D := by
      intro hr
      have := (hlive ring).1 hrl
      rw [hst ring hr] at this
      cases this.2
    simp only at h
    cases h with
    | keep b h =>
      cases b
      · simp only [Bool.not_false, if_true] at h
        cases h
        exact ⟨D, by simp [debtRun, debtStep, frees], fun _ h => by cases h⟩
      · simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        have hk1 : debtRun D (core (.keep ring intentText true :: [])) = some D := by
          simp [debtRun, debtStep, frees]
        cases h with
        | ask x h =>
          have hstep : ∀ (l : List Ev), debtRun D (core (.keep ring intentText true ::
              .ask ring (askOf w.conf ring) x :: l)) =
              debtRun (if (askText x).isSome then ring :: D else D) (core l) := by
            intro l
            rw [core_keep, debtRun_quiet (by simp [frees]) (by simp), core_ask]
            simp [debtRun, debtStep, hrD]
          have hown : ∀ u, Owes { m with kept := some (ring, u) } (ring :: D) := by
            intro u q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact .inl ⟨u, rfl⟩
            · exact .inr (hst q hq)
          rcases x with why | ans | why
          · simp only at h
            cases h with
            | say h =>
              obtain ⟨D', hd', ho⟩ := forgetThen_debt (D := D) h (fun m' hm => by
                obtain rfl := retry_next hm
                exact fun q hq => .inr (hst q hq))
              exact ⟨D', by rw [hstep]; simpa [askText] using hd', ho⟩
          · simp only at h
            obtain ⟨D', hd', ho⟩ := answered_debt h (hown _)
            exact ⟨D', by rw [hstep]; simpa [askText] using hd', ho⟩
          · simp only at h
            cases h with
            | say h =>
              obtain ⟨D', hd', ho⟩ := answered_debt h (hown _)
              exact ⟨D', by rw [hstep]; simpa [askText] using hd', ho⟩
  · -- answer the kept ring
    rw [hd] at h
    obtain ⟨hk, -⟩ := Nanodregg.Hosting.Proofs.Resident.decide_answer hd
    exact deliver_debt h hk hD

/-- A read at `sh`, then the act. The read frees every owed ring it does not list, so the act sees
owed rings only among the rings it read; the withdrawn rings it prunes are exactly ones it freed. -/
private theorem read_debt {w : Where} {sh : Shape} {m : Mem} {es : List Ev} {a : Tick} {D : List Ring}
    (h : Runs (readP w sh m) es a) (hD : Owes m D) : Keeps D a es := by
  have hret : ∀ {why : String} {es' : List Ev}, Runs (.done (retry m why)) es' a →
      debtRun D (core es') = some D ∧ ∀ m', a = .next m' → Owes m' D := by
    intro why es' h'
    cases h'
    exact ⟨by simp [debtRun], fun m' hm => by obtain rfl := retry_next hm; exact hD⟩
  unfold readP at h
  cases h with
  | cmd y h =>
    rcases y with e | rr
    · simp only at h
      cases h with
      | say h =>
        obtain ⟨hd, ho⟩ := hret h
        exact ⟨D, by rw [core_cmd, debtRun_quiet (by simp [frees, readRings]) (by simp), core_say]; exact hd, ho⟩
    · simp only at h
      split at h
      · rename_i hx
        cases h with
        | say h =>
          obtain ⟨hd, ho⟩ := hret h
          exact ⟨D, by
            rw [core_cmd, debtRun_quiet (by simp [frees, readRings, hx]) (by simp), core_say]; exact hd, ho⟩
      · rename_i hx
        simp only [Decidable.not_not] at hx
        split at h
        · cases h; exact ⟨_, rfl, fun _ h => by cases h⟩
        · rename_i p hp
          cases h with
          | hole h =>
            have hrr : readRings sh (.ok rr) = some p := by
              simp [readRings, hx, hp, Except.toOption]
            obtain ⟨D', hd, ho⟩ := actOn_debt (D := D.filter fun q => decide (q ∈ p)) h
              (fun q hq => by
                have ⟨hqD, hqp⟩ := List.mem_filter.mp hq
                rcases hD q hqD with hk | hs
                · exact .inl hk
                · exact .inr (by rw [stands_prune m (by simpa using hqp)]; exact hs))
              (fun q hq => by simpa using (List.mem_filter.mp hq).2)
            refine ⟨D', ?_, ho⟩
            rw [core_cmd, debtRun_free (by simp)]
            simpa [frees, hrr] using hd

/-- **One tick keeps the round**: from a memory that accounts for what is owed, a tick's effects
never ask about an owed ring, and the memory it goes on with accounts for what they leave owed. -/
private theorem tick_debt {w : Where} {m : Mem} {es : List Ev} {a : Tick} {D : List Ring}
    (h : Runs (tickP w m) es a) (hD : Owes m D) : Keeps D a es := by
  unfold tickP at h
  split at h
  · exact read_debt h hD
  · cases h with
    | cmd y h =>
      have hq : ∀ q, frees q (.cmd .describe y) = false := by simp [frees]
      rcases y with e | rr
      · simp only at h
        cases h with
        | say h =>
          cases h
          exact ⟨D, by simp [debtRun, debtStep, frees], fun m' hm => by obtain rfl := retry_next hm; exact hD⟩
      · simp only at h
        split at h
        · cases h with
          | say h =>
            cases h
            exact ⟨D, by simp [debtRun, debtStep, frees], fun m' hm => by obtain rfl := retry_next hm; exact hD⟩
        · split at h
          · cases h with
            | say h =>
              obtain ⟨D', hd, ho⟩ := read_debt (D := D) h hD
              exact ⟨D', by rw [core_cmd, debtRun_quiet hq (by simp), core_say]; exact hd, ho⟩
          · cases h; exact ⟨D, by simp [debtRun, debtStep, frees], fun _ h => by cases h⟩

/-! ## Across ticks -/

private theorem ticks_debt {w : Where} {m : Mem} {ess : List (List Ev)} {D : List Ring}
    (h : Ticks w m ess) (hD : Owes m D) : (debtRun D (core ess.flatten)).isSome := by
  induction h generalizing D with
  | nil m => simp [debtRun, core]
  | last hr =>
    obtain ⟨D', h1, -⟩ := tick_debt hr hD
    simp [h1]
  | next hr _ ih =>
    obtain ⟨D', h1, h2⟩ := tick_debt hr hD
    rw [List.flatten_cons, core_append, debtRun_append, h1]
    exact ih (h2 _ rfl)

/-- An effect that does not free `r` leaves `r` owed (an ask about another ring only adds). -/
private theorem debtStep_keeps {D D' : List Ring} {e : Ev} (h : debtStep D e = some D') {r : Ring}
    (hr : r ∈ D) (hf : frees r e = false) : r ∈ D' := by
  cases e with
  | ask r₀ q₀ x₀ =>
    simp only [debtStep] at h
    split at h
    · cases h
    · cases h; split <;> simp [hr]
  | _ => simp only [debtStep, Option.some.injEq] at h; subst h; simp [List.mem_filter, hr, hf]

/-- Reading the round off a trace: between two asks about one ring, the first spent, an effect
frees it. -/
private theorem debtRun_frees {D : List Ring} {pre mid post : List Ev} {r : Ring} {q q' : Broker.Ask}
    {x x' : AskEnd} (hx : (askText x).isSome)
    (h : (debtRun D (pre ++ .ask r q x :: mid ++ .ask r q' x' :: post)).isSome) :
    ∃ e ∈ mid, frees r e = true := by
  rw [List.append_assoc, debtRun_append] at h
  cases hpre : debtRun D pre with
  | none => simp [hpre] at h
  | some D₁ =>
    rw [hpre, Option.bind_some, List.cons_append] at h
    have hr1 : r ∉ D₁ := by
      intro hr; simp [debtRun, debtStep, hr] at h
    have hstep : debtRun D₁ (.ask r q x :: (mid ++ .ask r q' x' :: post)) =
        debtRun (r :: D₁) (mid ++ .ask r q' x' :: post) := by
      simp [debtRun, debtStep, hr1, hx]
    rw [hstep] at h
    -- through `mid` the ring stays owed until something frees it
    have key : ∀ (l : List Ev) (E : List Ring), r ∈ E →
        (debtRun E (l ++ .ask r q' x' :: post)).isSome → ∃ e ∈ l, frees r e = true := by
      intro l
      induction l with
      | nil => intro E hE h; simp [debtRun, debtStep, hE] at h
      | cons e l ih =>
        intro E hE h
        by_cases hf : frees r e = true
        · exact ⟨e, List.mem_cons_self .., hf⟩
        · simp only [List.cons_append, debtRun] at h
          cases hs : debtStep E e with
          | none => simp [hs] at h
          | some E' =>
            rw [hs, Option.bind_some] at h
            obtain ⟨e', he', hf'⟩ := ih E' (debtStep_keeps hs hE (by simpa using hf)) h
            exact ⟨e', List.mem_cons_of_mem _ he', hf'⟩
    exact key mid _ List.mem_cons_self h

/-- **The resident keeps the Bell's round** (PROT-3's host half): on every chain of ticks, between
two asks about the same ring, the first of them spent (it left in full, so the meter was charged),
the trace holds an effect that freed the ring: an invoke of its answer that came back `ok`, or a
read of the pending rings that no longer listed it. With nothing freeing a ring, it is asked about
once. -/
theorem bell_resident_conforms {w : Where} {m : Mem} {ess : List (List Ev)} {r : Ring}
    {pre mid post : List Ev} {q q' : Broker.Ask} {x x' : AskEnd} (h : Ticks w m ess)
    (hc : core ess.flatten = pre ++ .ask r q x :: mid ++ .ask r q' x' :: post)
    (hx : (askText x).isSome) : ∃ e ∈ mid, Frees r e := by
  have hd := ticks_debt h (D := []) (fun _ h => by cases h)
  rw [hc] at hd
  obtain ⟨e, he, hf⟩ := debtRun_frees hx hd
  exact ⟨e, he, frees_true hf⟩

end Nanodregg.Hosting.Proofs.BellConform
