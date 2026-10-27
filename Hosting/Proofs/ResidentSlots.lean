/-
# Hosting.Proofs.ResidentSlots — the resident's repair is the slot's (`Lang.Contextual.Slot.slot_repair`)

The resident's tick has two holes (`Hosting.Resident.Hole`), each filled from a slot when the run reaches
it. This module states the resident's repair as the slot's, at those two slots.

- `resident_repair` (`slot_repair` at the `serve` slot, at the view of one read): an act on a ring is
  usable iff the ring is pending in this read and its answer stands; a blocked act names exactly the
  supports that fail; the act the slot fills is usable.
- `use_withdraws`: an answer refused while its ring still waits, a cell the answer cites (the aim's
  `via` grant or its target) probed and found gone (`read CELL ?` refused `missingCell`), is WITHDRAWN
  by that name: the log line names the cell, the kept answer is forgotten, and the ring joins
  `Mem.withdrawn` under the cell's name.
- `withdrawn_blocked`, `withdrawn_not_served`: a withdrawn ring's acts read blocked by the name
  `stands r` while it is listed, and the `serve` slot never fills with them.
- `serve_keeps_withdrawn`: a withdrawal lasts while the ring is listed: every tick's `serve` hole hands
  it on to the next tick's memory (`slot_repair`'s permanence, along ticks that list the ring).
- `serve_repairs`: the repair. With the withdrawn ring skipped, the slot fills with the next live ring's
  ask, in the same tick, which reads usable with its evidence: no restart, no reinstall.

What is not here: the withdrawn list is memory, not the volume. A restart asks a withdrawn ring once
more (one meter charge) and withdraws it again.
-/
import Hosting.Proofs.ResidentRun

namespace Nanodregg.Hosting.Proofs.ResidentSlots

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun
open Nanodregg.Lang.Contextual.Slot

/-- `slot_repair` at the `serve` slot, at the view of one read (`serveHolds m p`): (1) an act is usable
iff every support it cites holds: for an act on a ring, the ring is pending in this read and its answer
stands; (2) a blocked act names exactly its failing supports, at least one; (3) a usable act reads usable
the moment it is selected, with its evidence; and (4) the act the slot fills (`serveChoice`) is usable. -/
theorem resident_repair (m : Mem) (p : List Ring) (c : Act) :
    ((∃ ev, serveSlot.read (serveHolds m p) (some c) = .usable c ev) ↔
        ∀ f ∈ serveSlot.supports c, serveHolds m p f = true) ∧
    (∀ c' d, serveSlot.read (serveHolds m p) (some c) = .blocked c' d →
        d ≠ [] ∧ ∀ f, f ∈ d ↔ f ∈ serveSlot.supports c ∧ serveHolds m p f = false) ∧
    (∀ c', serveSlot.usable (serveHolds m p) c' = true →
        serveSlot.read (serveHolds m p) (some c') = .usable c' (serveSlot.evidence (serveHolds m p) c')) ∧
    serveSlot.usable (serveHolds m p) (serveChoice m p) = true := by
  obtain ⟨h1, h2, -, h4⟩ := slot_repair serveSlot (fun (_ : Unit) => serveHolds m p) (fun _ _ => True) () c
  refine ⟨h1.trans (by simp [serveSlot]), h2, h4, ?_⟩
  unfold serveChoice
  cases ha : serveSlot.alternatives (serveHolds m p) (serveOrder m p) with
  | nil => simp [Slot.usable, Slot.dead, serveSlot]
  | cons a rest =>
    have : a ∈ serveSlot.alternatives (serveHolds m p) (serveOrder m p) := by rw [ha]; exact List.mem_cons_self
    exact (List.mem_filter.mp this).2

private theorem stands_false {m : Mem} {r : Ring} {c : String} (hw : (r, c) ∈ m.withdrawn) :
    stands m r = false := by
  simp only [stands, Bool.not_eq_eq_eq_not, Bool.not_false, List.any_eq_true, beq_iff_eq]
  exact ⟨(r, c), hw, rfl⟩

/-- A withdrawn ring's acts read BLOCKED by the name `stands r` (its only failing support) while the
read lists it: the answer is stored, not usable. -/
theorem withdrawn_blocked {m : Mem} {p : List Ring} {r : Ring} {c : String} (hw : (r, c) ∈ m.withdrawn)
    (hp : r ∈ p) :
    serveSlot.read (serveHolds m p) (some (.ask r)) = .blocked (.ask r) [.stands r] ∧
      ∀ t, serveSlot.read (serveHolds m p) (some (.answer r t)) = .blocked (.answer r t) [.stands r] := by
  have hs := stands_false hw
  refine ⟨?_, fun t => ?_⟩ <;>
    simp [Slot.read, Slot.dead, serveSlot, serveHolds, hp, hs]

/-- The `serve` slot never fills with a withdrawn ring's act: no ask about it, no answer for it. -/
theorem withdrawn_not_served {m : Mem} {p : List Ring} {r : Ring} {c : String} (hw : (r, c) ∈ m.withdrawn) :
    serveChoice m p ≠ .ask r ∧ ∀ t, serveChoice m p ≠ .answer r t := by
  have hs := stands_false hw
  have hl : r ∉ live m p := by simp [live, List.mem_filter, hs]
  rw [serveChoice_eq]
  refine ⟨fun h => ?_, fun t h => ?_⟩
  · obtain ⟨hh, -⟩ := Nanodregg.Hosting.Proofs.Resident.decide_ask h
    cases hlv : live m p with
    | nil => rw [hlv] at hh; cases hh
    | cons x xs =>
      rw [hlv] at hh; cases hh
      exact hl (by rw [hlv]; exact List.mem_cons_self)
  · exact hl (Nanodregg.Hosting.Proofs.Resident.decide_answer h).2

/-- The `use` slot withdraws only by the name of a cell the ring's answer cites that the probes found
gone, while the ring still waits. -/
theorem use_withdraw_names {r : Ring} {p : List Ring} {gone : List ByteArray} {c : ByteArray}
    (h : useChoice r p gone = .withdraw c) : r ∈ p ∧ c ∈ aimCells r ∧ c ∈ gone := by
  have hmem : UseCand.withdraw c ∈ useSlot.alternatives (useHolds r p gone) (useOrder r) := by
    unfold useChoice at h
    cases ha : useSlot.alternatives (useHolds r p gone) (useOrder r) with
    | nil => rw [ha] at h; cases h
    | cons a rest => rw [ha] at h; cases h; exact List.mem_cons_self
  obtain ⟨ho, hu⟩ := List.mem_filter.mp hmem
  simp [Slot.usable, Slot.dead, useSlot, useHolds] at hu
  simp [useOrder] at ho
  exact ⟨hu.1, ho, hu.2⟩

/-- **Withdrawn by name.** An answer refused while its ring waits, a cell the answer cites probed and
found gone (the `use` slot's `withdraw c`): every path that goes on says so naming the cell, forgets
the kept answer, and hands on a memory where the ring is withdrawn under the cell's name and nothing is
kept. -/
theorem use_withdraws {m m' : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {c : ByteArray} {es : List Ev} (hc : useChoice r p gone = .withdraw c)
    (h : Runs (useP m r n line p gone) es (.next m')) :
    es = [.say s!"answer withdrawn {r.notBefore} {Lang.Print.hex r.ringer}: its support {Lang.Print.hex c} is gone ({line})",
      .note ((r, Lang.Print.hex c) :: m.withdrawn) true, .forget true] ∧
      (r, Lang.Print.hex c) ∈ m'.withdrawn ∧ m'.kept = none := by
  unfold useP at h
  rw [hc] at h
  cases h with
  | say h =>
    cases h with
    | note b h =>
      cases b
      · simp at h; cases h
      · simp only [if_true] at h
        obtain ⟨hn, rfl⟩ := forgetThen_next h
        cases hn
        exact ⟨rfl, List.mem_cons_self, rfl⟩

/-! ## A withdrawal lasts while the ring is listed -/

theorem useP_withdrawn {m m' : Mem} {r : Ring} {n line : String} {p : List Ring} {gone : List ByteArray}
    {es : List Ev} (h : Runs (useP m r n line p gone) es (.next m')) : ∀ x ∈ m.withdrawn, x ∈ m'.withdrawn := by
  unfold useP at h
  split at h
  · cases h with | say h => obtain ⟨hn, -⟩ := forgetThen_next h; cases hn; exact fun x hx => hx
  · cases h with
    | say h =>
      cases h with
      | note b h =>
        cases b
        · simp at h; cases h
        · simp only [if_true] at h
          obtain ⟨hn, -⟩ := forgetThen_next h; cases hn; exact fun x hx => List.mem_cons_of_mem _ hx
  · cases h

theorem refusedP_withdrawn {sh : Shape} {m m' : Mem} {r : Ring} {n line : String} {p : List Ring}
    {es : List Ev} (h : Runs (refusedP sh m r n line p) es (.next m')) : ∀ x ∈ m.withdrawn, x ∈ m'.withdrawn := by
  obtain ⟨pre, rest, rfl, -, hr⟩ := refusedP_path h
  rcases hr with ⟨c, y, s, why, rfl, -, hr⟩ | ⟨gone, hr⟩
  · obtain rfl := retry_next hr.symm; exact fun x hx => hx
  · exact useP_withdrawn hr

theorem deliver_withdrawn {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (deliverP sh m r t) es (.next m')) : ∀ x ∈ m.withdrawn, x ∈ m'.withdrawn := by
  unfold deliverP at h
  split at h
  · cases h
  · cases h with
    | cmd x h =>
      rcases x with e | rr
      · simp only at h; cases h with | say h => obtain ⟨-, rfl⟩ := done_retry h; exact fun x hx => hx
      · simp only at h
        split at h
        · cases h with
          | say h => obtain ⟨hn, -⟩ := forgetThen_next h; cases hn; exact fun x hx => hx
        · split at h
          · cases h with
            | cmd y h =>
              rcases y with e | rr'
              · simp only at h
                cases h with | say h => obtain ⟨-, rfl⟩ := done_retry h; exact fun x hx => hx
              · simp only at h
                split at h
                · cases h with | say h => obtain ⟨-, rfl⟩ := done_retry h; exact fun x hx => hx
                · split at h
                  · cases h
                  · exact refusedP_withdrawn h
          · cases h with | say h => obtain ⟨-, rfl⟩ := done_retry h; exact fun x hx => hx

theorem answered_withdrawn {sh : Shape} {m m' : Mem} {r : Ring} {t : ByteArray} {es : List Ev}
    (h : Runs (answeredP sh m r t) es (.next m')) : ∀ x ∈ m.withdrawn, x ∈ m'.withdrawn := by
  unfold answeredP at h
  cases h with
  | say h =>
    cases h with
    | keep b h =>
      cases b
      · simp at h; cases h
      · simp only [if_true] at h; exact deliver_withdrawn (m := { m with kept := some (r, t) }) h

theorem actOn_withdrawn {w : Where} {sh : Shape} {m m' : Mem} {p : List Ring} {es : List Ev}
    (h : Runs (actOn w sh m p) es (.next m')) : ∀ x ∈ m.withdrawn, x ∈ m'.withdrawn := by
  unfold actOn at h
  split at h
  · split at h
    · obtain ⟨hn, -⟩ := forgetThen_next h; cases hn; exact fun x hx => hx
    · cases h; exact fun x hx => hx
  · exact deliver_withdrawn h
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
            | say h =>
              obtain ⟨hn, -⟩ := forgetThen_next h
              obtain rfl := retry_next hn
              exact fun x hx => hx
          · simp only at h; exact answered_withdrawn h
          · simp only at h; cases h with | say h => exact answered_withdrawn h

/-- **A withdrawal lasts while the ring is listed.** The `serve` hole, reached with the read `p`, hands
every withdrawal of a ring `p` still lists on to the next tick's memory: along ticks that list the ring,
`stands r` is false at every later view, the permanence `slot_repair`'s third clause asks for. -/
theorem serve_keeps_withdrawn {w : Where} {sh : Shape} {m m' : Mem} {p : List Ring} {es : List Ev}
    (h : Runs (fill (.serve w sh m p)) es (.next m')) {x : Ring × String} (hx : x ∈ m.withdrawn)
    (hp : x.1 ∈ p) : x ∈ m'.withdrawn :=
  actOn_withdrawn (m := m.prune p) h x (List.mem_filter.mpr ⟨hx, decide_eq_true hp⟩)

/-! ## The repair -/

/-- **The repair: no restart, no reinstall.** When the kept answer is not live (withdrawn, gone, or
none) and `q` is the first ring whose answer stands, the `serve` slot fills with the ask about `q` in
this tick, and that act reads usable with its evidence: the same slot, another candidate. -/
theorem serve_repairs {m : Mem} {p : List Ring} {q : Ring}
    (hk : ∀ r t, m.kept = some (r, t) → r ∉ live m p) (hq : (live m p).head? = some q) :
    serveChoice m p = .ask q ∧
      serveSlot.read (serveHolds m p) (some (.ask q)) =
        .usable (.ask q) (serveSlot.evidence (serveHolds m p) (.ask q)) := by
  have hc : serveChoice m p = .ask q := by
    rw [serveChoice_eq]
    cases hl : live m p with
    | nil => rw [hl] at hq; cases hq
    | cons y ys =>
      rw [hl] at hq hk
      cases hq
      unfold decideTick
      cases hkm : m.kept with
      | none => rfl
      | some rt =>
        obtain ⟨r, t⟩ := rt
        simp [hk r t hkm]
  refine ⟨hc, (resident_repair m p (.ask q)).2.2.1 _ ?_⟩
  have := (resident_repair m p (.ask q)).2.2.2
  rwa [hc] at this

end Nanodregg.Hosting.Proofs.ResidentSlots
