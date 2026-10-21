/- The pinned point reader against an independent identity/version model. -/
import Lang.Proofs.StdHole

namespace Nanodregg.Lang.Std


/-- Actual lookup distinguishes absent, current and moved by cell identity and
version equality for arbitrary digest bytes and poster, not just fixtures. -/
theorem holeProbePoint_meaning (cell pin : ByteArray) (point : Option HolePoint)
    (lib : List Term) (env : Env) :
    BigStep lib ((holePointData point).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0])
      (.ok (.nat (holePointObservation cell pin point))) := by
  apply BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl)
  cases point with
  | none => exact .case (.var rfl) rfl .nat
  | some p =>
    refine BigStep.case (.var rfl) rfl ?_
    have he : BigStep lib
        ((match holePointData (some p) with | .inj _ d => d | _ => .record []).toVal ::
          (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal ::
          (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
        (.prim .deq (.get (.get (.var 0) "key") "cell") (.get (.var 2) "cell"))
        (.ok (.bool (decide (p.cell = cell)))) :=
      .prim (p := .deq) (x := .digest p.cell) (y := .digest cell) (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl)))
        (.get (.var rfl) (.field rfl (.var rfl))) (by simp [primEval])
    by_cases hcell : p.cell = cell
    · apply BigStep.iteT (by simpa only [holePointData, hcell, decide_true] using he)
      cases hpin : p.pin with
      | none =>
        simp only [holePointObservation, hcell, hpin, ↓reduceIte]
        apply BigStep.case (ℓ := "none") (w := .record []) ?_ rfl .nat
        exact .get (.var rfl) (.field (t := .var 0) (env := [(Data.inj "none" (.record [])).toVal]) (by simp [Data.rowToVal, Row.find?]) (.var rfl))
      | some v =>
        refine BigStep.case (ℓ := "some")
          (w := (Data.record [("by", .digest p.author), ("pin", .digest v)]).toVal) ?_ rfl ?_
        · exact .get (.var rfl) (.field (t := .var 0) (env := [(Data.inj "some" (.record [("by", .digest p.author), ("pin", .digest v)])).toVal]) (by simp [Data.rowToVal, Row.find?]) (.var rfl))
        have hp : BigStep lib
            ((Data.record [("by", .digest p.author), ("pin", .digest v)]).toVal ::
              (match holePointData (some p) with | .inj _ d => d | _ => .record []).toVal ::
              (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal ::
              (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
            (.prim .deq (.get (.var 0) "pin") (.get (.var 3) "pin"))
            (.ok (.bool (decide (v = pin)))) :=
          .prim (p := .deq) (x := .digest v) (y := .digest pin) (.get (.var rfl) (.field rfl (.var rfl)))
            (.get (.var rfl) (.field rfl (.var rfl))) (by simp [primEval])
        by_cases hv : v = pin
        · simpa only [holePointObservation, hcell, ↓reduceIte, hpin, hv] using
            (BigStep.iteT (by simpa only [holePointData, hcell, hpin, hv, decide_true] using hp) (BigStep.nat (n := 1)))
        · simpa only [holePointObservation, hcell, ↓reduceIte, hpin, hv] using
            (BigStep.iteF (by simpa only [holePointData, hcell, hpin, hv, decide_false] using hp) (BigStep.nat (n := 2)))
    · simpa only [holePointObservation, hcell, ↓reduceIte] using
        (BigStep.iteF (by simpa only [holePointData, hcell, decide_false] using he) (BigStep.nat (n := 0)))

end Nanodregg.Lang.Std
