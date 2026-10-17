/-
# Kernel.Proofs.Admit — what an admitted turn guarantees

Every theorem here is about `World.admit` itself (the receive path), not about a model of it.
-/
import Kernel.World
import Kernel.Proofs.Check

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- Distinct constructors have distinct wire names (law 7): equal names, same constructor. -/
theorem Reject.name_injective (a b : Reject D) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Reject.name] <;> rfl

/-- Every check `admit` runs, as facts; `raw` is what each touch leaves (`none`: unchanged). -/
structure Checked (E : Env D) (w : World D) (t : Turn D) (posts : List (D × Entry)) : Prop where
  bounds : checkBounds t = .ok ()
  journal : checkJournal w t = .ok ()
  shape : checkShape t = .ok ()
  window : checkWindow w t = .ok ()
  touches : ∃ raw, mapEx (touchCheck E w) t.touches = .ok raw ∧ posts = raw.reduceOption
  nullifiers : checkNullifiers w t = .ok ()
  charge : checkCharge w t = .ok ()
  creates : checkCreates E w t = .ok ()

theorem check_ok {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Entry)}
    (h : check E w t = .ok posts) : Checked E w t posts := by
  unfold check at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, ⟨⟩, h3, ⟨⟩, h4, raw, h5, ⟨⟩, h6, ⟨⟩, h7, ⟨⟩, h8, h9⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h9
  exact ⟨h1, h2, h3, h4, ⟨raw, h5, h9.symm⟩, h6, h7, h8⟩

/-- Every touch of a checked turn passed `touchCheck`. -/
theorem Checked.touch {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Entry)}
    (hk : Checked E w t posts) : ∀ x ∈ t.touches, ∃ r, touchCheck E w x = .ok r := by
  obtain ⟨raw, hm, _⟩ := hk.touches
  exact mapEx_each hm

/-- A touch that passes saw what the signer saw. -/
theorem touchCheck_pin {E : Env D} {w : World D} {x : Touch D} {r : Option (D × Entry)}
    (h : touchCheck E w x = .ok r) : pinOf E (w.live x.cell) = x.seen := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hp, _⟩ := h
  exact of_decide_eq_true (req_ok.mp hp)

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

/-- **The weight bound.** An admitted turn costs at most `Bounds.weightMax`, its log record
included: the static budget HOST sizes a turn record and a batch by (a batch of `n` admitted
turns appends at most `n * Bounds.weightMax` record bytes, given CODEC's
`size (encode t) ≤ t.logWeight`). -/
theorem admit_weight {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    t.charge = t.weight ∧ t.logWeight ≤ t.weight ∧ t.weight ≤ Bounds.weightMax := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have hb := hc.bounds
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hw, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hw
  exact ⟨(admit_charge h).1, Nat.le_add_right _ _, hw⟩

/-- **Guards from the intent.** Every cell the turn touches is, in the pre-state, exactly what
the signer saw. -/
theorem admit_pins {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : ∀ x ∈ t.touches, pinOf E (w.live x.cell) = x.seen := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  intro x hx
  obtain ⟨_, hr⟩ := hc.touch x hx
  exact touchCheck_pin hr

/-- **The staleness refusal.** A turn whose pin disagrees with the World is admitted by no
World transition. -/
theorem stale_refused {E : Env D} {w : World D} {t : Turn D} {x : Touch D}
    (hmem : x ∈ t.touches) (hstale : pinOf E (w.live x.cell) ≠ x.seen) :
    ∀ w', World.admit E w t ≠ .ok w' :=
  fun _ h => hstale (admit_pins h x hmem)

/-- A stale touch is refused `stale` before anything about its write or retirement is judged. -/
theorem touchCheck_stale {E : Env D} {w : World D} {x : Touch D}
    (hstale : pinOf E (w.live x.cell) ≠ x.seen) : touchCheck E w x = .error (.stale x.cell) := by
  unfold touchCheck
  simp [req, hstale, bind, Except.bind]

/-- **Stale BY NAME.** If the checks before the touches pass and the first touch that fails is
stale, the turn is refused `stale` naming that cell. -/
theorem stale_named {E : Env D} {w : World D} {t : Turn D} {pre post : List (Touch D)}
    {x : Touch D} (hb : checkBounds t = .ok ()) (hj : checkJournal w t = .ok ())
    (hs : checkShape t = .ok ()) (hw : checkWindow w t = .ok ())
    (ht : t.touches = pre ++ x :: post) (hpre : ∀ y ∈ pre, ∃ r, touchCheck E w y = .ok r)
    (hstale : pinOf E (w.live x.cell) ≠ x.seen) :
    World.admit E w t = .error (.stale x.cell) := by
  have hm : mapEx (touchCheck E w) t.touches = .error (.stale x.cell) := by
    rw [ht]; exact mapEx_error_at (touchCheck_stale hstale) post hpre
  unfold World.admit check
  simp [hb, hj, hs, hw, hm, bind, Except.bind]

/-- A retry of an admitted transaction is answered `replayed` with its height, whatever else is
true of the World now (only the static bounds are checked first). -/
theorem replay_named {E : Env D} {w : World D} {t : Turn D} {h : Nat} {d : D}
    (hb : checkBounds t = .ok ()) (hj : w.journal[t.txId]? = some (h, d)) :
    World.admit E w t = .error (.replayed h) := by
  have : checkJournal w t = .error (.replayed h) := by simp [checkJournal, hj]
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
      simp [hjt] at hj

end Nanodregg.Kernel
