/-
# Kernel.Proofs.Admit — what an admitted turn guarantees

Every theorem here is about `World.admit` itself (the receive path), not about a model of it.
-/
import Kernel.World
import Kernel.Proofs.Check

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every check `admit` runs, as facts. -/
structure Checked (E : Env D) (w : World D) (t : Turn D) (posts : List (D × Cell)) : Prop where
  bounds : checkBounds t = .ok ()
  journal : checkJournal E w t = .ok ()
  shape : checkShape t = .ok ()
  window : checkWindow w t = .ok ()
  pins : checkPins E w t = .ok ()
  nullifiers : checkNullifiers w t = .ok ()
  charge : checkCharge w t = .ok ()
  creates : checkCreates E w t = .ok ()
  retires : forEx (checkRetire w) t.retires = .ok ()
  legs : mapEx (postLeg w) t.legs = .ok posts

theorem check_ok {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Cell)}
    (h : check E w t = .ok posts) : Checked E w t posts := by
  unfold check at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, ⟨⟩, h3, ⟨⟩, h4, ⟨⟩, h5, ⟨⟩, h6, ⟨⟩, h7, ⟨⟩, h8, ⟨⟩, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem admit_ok {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    ∃ posts, Checked E w t posts ∧ w' = commit E w t posts := by
  unfold World.admit at h
  cases hc : check E w t with
  | error r => simp [hc] at h
  | ok posts =>
      simp [hc] at h
      exact ⟨posts, check_ok hc, h.symm⟩

theorem admit_height {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : w'.height = w.height + 1 := by
  obtain ⟨_, _, rfl⟩ := admit_ok h; rfl

theorem admit_chain {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : w'.chain = chainNext E w.chain t := by
  obtain ⟨_, _, rfl⟩ := admit_ok h; rfl

/-- **Charge exactness.** An admitted turn paid exactly its weight, could afford it, and the
budget fell by exactly that. -/
theorem admit_charge {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    t.charge = t.weight ∧ t.charge ≤ w.allowance ∧ w'.allowance + t.charge = w.allowance := by
  obtain ⟨_, hc, rfl⟩ := admit_ok h
  have hch := hc.charge
  unfold checkCharge at hch
  simp only [except_bind_ok] at hch
  obtain ⟨⟨⟩, h1, h2⟩ := hch
  rw [req_ok, decide_eq_true_eq] at h1 h2
  refine ⟨h1, h2, ?_⟩
  show w.allowance - t.charge + t.charge = w.allowance
  omega

/-- **Guards from the intent.** Every cell the signer pinned is, in the pre-state, exactly what
the signer saw. -/
theorem admit_pins {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : ∀ p ∈ t.pins, pinOf E (w.live p.1) = p.2 := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have hp := forEx_ok.mp hc.pins
  intro p hmem
  have := hp p hmem
  unfold pinCheck at this
  rw [req_ok, decide_eq_true_eq] at this
  exact this

/-- **The staleness refusal.** A turn whose pin disagrees with the World is admitted by no
World transition. -/
theorem stale_refused {E : Env D} {w : World D} {t : Turn D} {p : D × D}
    (hmem : p ∈ t.pins) (hstale : pinOf E (w.live p.1) ≠ p.2) :
    ∀ w', World.admit E w t ≠ .ok w' :=
  fun _ h => hstale (admit_pins h p hmem)

/-- If every check before the pins passes, a stale pin is refused BY NAME: `stale c` for a
pinned cell `c` whose digest disagrees. -/
theorem stale_named {E : Env D} {w : World D} {t : Turn D}
    (hb : checkBounds t = .ok ()) (hj : checkJournal E w t = .ok ())
    (hs : checkShape t = .ok ()) (hw : checkWindow w t = .ok ())
    (hstale : ∃ p ∈ t.pins, pinOf E (w.live p.1) ≠ p.2) :
    ∃ p ∈ t.pins, pinOf E (w.live p.1) ≠ p.2 ∧ World.admit E w t = .error (.stale p.1) := by
  suffices key : ∀ (l : List (D × D)), (∃ p ∈ l, pinOf E (w.live p.1) ≠ p.2) →
      ∃ p ∈ l, pinOf E (w.live p.1) ≠ p.2 ∧
        forEx (pinCheck E w) l = .error (.stale p.1) by
    obtain ⟨p, hp, hne, hf⟩ := key t.pins hstale
    refine ⟨p, hp, hne, ?_⟩
    have hpins : checkPins E w t = .error (.stale p.1) := hf
    unfold World.admit check
    simp [hb, hj, hs, hw, hpins, bind, Except.bind]
  intro l
  induction l with
  | nil => intro ⟨_, h, _⟩; simp at h
  | cons q rest ih =>
      intro hex
      by_cases hq : pinOf E (w.live q.1) = q.2
      · have hrest : ∃ p ∈ rest, pinOf E (w.live p.1) ≠ p.2 := by
          obtain ⟨p, hp, hne⟩ := hex
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact absurd hq hne
          · exact ⟨p, hp, hne⟩
        obtain ⟨p, hp, hne, hf⟩ := ih hrest
        refine ⟨p, List.mem_cons_of_mem _ hp, hne, ?_⟩
        have hq' : pinCheck E w q = .ok () := by simp [pinCheck, req, hq]
        simp [forEx, hq', hf]
      · refine ⟨q, by simp, hq, ?_⟩
        have hq' : pinCheck E w q = .error (.stale q.1) := by simp [pinCheck, req, hq]
        simp [forEx, hq']

/-- An exact retry of an admitted transaction is answered `replayed` with its height, whatever
else is true of the World now (only the static bounds are checked first). -/
theorem replay_named {E : Env D} {w : World D} {t : Turn D} {h : Nat}
    (hb : checkBounds t = .ok ()) (hj : w.journal[t.txId]? = some (h, turnDigest E t)) :
    World.admit E w t = .error (.replayed h) := by
  have : checkJournal E w t = .error (.replayed h) := by simp [checkJournal, hj]
  unfold World.admit check
  simp [hb, this, bind, Except.bind]

/-- An admitted transaction was new, and is journalled at the new height with its digest. -/
theorem admit_journal [Std.TransOrd D] {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    w.journal[t.txId]? = none ∧ w'.journal[t.txId]? = some (w.height + 1, turnDigest E t) := by
  obtain ⟨_, hc, rfl⟩ := admit_ok h
  refine ⟨?_, by simp [commit]⟩
  have hj := hc.journal
  unfold checkJournal at hj
  cases hjt : w.journal[t.txId]? with
  | none => rfl
  | some e =>
      obtain ⟨hh, d⟩ := e
      simp only [hjt] at hj
      split at hj <;> simp at hj

end Nanodregg.Kernel
