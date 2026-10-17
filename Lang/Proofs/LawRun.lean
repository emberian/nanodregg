/-
# Lang.Proofs.LawRun — the one law runner never ends `stuck` on a loaded package's law (LANG-42)

`law_never_stuck` (Lang.Proofs.Invoke) covers the machine run inside `runLaw`. This covers the
extraction after it. `extract_progress`: extracting a typed value at a data type fails, if at all,
by a named budget or arithmetic fault of a forced suspension, never by `stuck`. So
`runLaw_never_stuck`: the receiver's `runLaw` on a loaded package's law, on states it read and a
request in bounds, returns a verdict or a named fault, and its "a value of another shape is `stuck`"
arm is unreachable. Teeth: a function type is not data, and extraction at it is `stuck`
(`extract_fn_stuck`). A law that returns a number in place of a verdict is `stuck` in `runLaw`
(`runLaw_nat_stuck`), so the typing premise is what the theorem uses.
-/
import Lang.Proofs.CallLive

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

section
variable {Δ : List Ty}

theorem force_progress {m : Machine} (hlib : LibTy Δ m.lib) {fuel : Nat} {t : Term} {env : Env}
    {Γ : List Ty} {A : Ty} {f : Fault} (he : EnvTy Δ env Γ) (ht : HasType Δ Γ t A)
    (h : m.force fuel t env = .error f) : f ≠ .stuck := by
  unfold Machine.force at h
  have hr := run_sound (cap := Bounds.stackMax) hlib fuel 0 (State.init t env) (.eval he ht .nil)
  split at h
  · cases h
  · rename_i f' used hf
    rw [hf] at hr
    cases h
    exact hr

theorem unknot_progress {m : Machine} (hlib : LibTy Δ m.lib) : ∀ {rounds fuel : Nat} {v : Val}
    {r : List (Label × Ty)} {f : Fault}, ValTy Δ v (.record r) → m.unknot rounds fuel v = .error f →
    f ≠ .stuck
  | rounds, fuel, .record fs', r, f, _, h => by simp [Machine.unknot] at h
  | 0, fuel, .knot b env, r, f, _, h => by
    simp only [Machine.unknot, Except.error.injEq] at h; subst h; decide
  | k + 1, fuel, .knot b env, r, f, hv, h => by
    cases hv with
    | knot he hb =>
      simp only [Machine.unknot] at h
      split at h
      · rename_i v' fuel' hf
        exact unknot_progress hlib (force_typed hlib (.cons (.knot he hb) he) hb hf) h
      · rename_i e hf
        cases h
        exact force_progress hlib (.cons (.knot he hb) he) hb hf
  | _, _, .nat _, _, _, hv, _ => by cases hv
  | _, _, .bool _, _, _, hv, _ => by cases hv
  | _, _, .bytes _, _, _, hv, _ => by cases hv
  | _, _, .digest _, _, _, hv, _ => by cases hv
  | _, _, .clo _ _, _, _, hv, _ => by cases hv
  | _, _, .inj _ _, _, _, hv, _ => by cases hv

mutual
/-- **Extraction makes progress**: a value typed at a data type extracts, or fails by a named fault
of a forced suspension (budget, stack, arithmetic), never `stuck`. -/
theorem extract_progress {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (T : Ty) {fuel : Nat} {v : Val}
    {f : Fault}, T.isData = true → ValTy Δ v T → m.extract T fuel v = .error f → f ≠ .stuck
  | .nat, _, _, _, _, hv, h => by cases hv; simp [Machine.extract] at h
  | .bool, _, _, _, _, hv, h => by cases hv; simp [Machine.extract] at h
  | .bytes, _, _, _, _, hv, h => by cases hv; simp [Machine.extract] at h
  | .digest, _, _, _, _, hv, h => by cases hv; simp [Machine.extract] at h
  | .fn _ _, _, _, _, hd, _, _ => by simp [Ty.isData] at hd
  | .record row, _, v, _, hd, hv, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i fs fuel' hu
      split at h
      · cases h
      · rename_i e hr
        cases h
        exact extractRow_progress hlib row (by simpa [Ty.isData] using hd) (unknot_typed hlib hv hu) hr
    · rename_i e hu
      cases h
      exact unknot_progress hlib hv hu
  | .sum row, _, v, _, hd, hv, h => by
    cases hv with
    | inj hf hw =>
      simp only [Machine.extract] at h
      split at h
      · cases h
      · rename_i e ha
        cases h
        exact extractArm_progress hlib row (by simpa [Ty.isData] using hd) hf hw ha

theorem extractArm_progress {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (row : List (Label × Ty)) {ℓ : Label}
    {A : Ty} {fuel : Nat} {w : Val} {f : Fault}, Ty.rowData row = true → Row.find? ℓ row = some A →
    ValTy Δ w A → m.extractArm row ℓ fuel w = .error f → f ≠ .stuck
  | [], _, _, _, _, _, _, hf, _, _ => by cases hf
  | (k, B) :: row, ℓ, A, _, _, _, hd, hf, hw, h => by
    simp only [Ty.rowData, Bool.and_eq_true] at hd
    simp only [Machine.extractArm] at h
    simp only [Row.find?] at hf
    split at h
    · rename_i hk
      rw [if_pos hk] at hf; cases hf
      exact extract_progress hlib B hd.1 hw h
    · rename_i hk
      rw [if_neg hk] at hf
      exact extractArm_progress hlib row hd.2 hf hw h

theorem extractRow_progress {m : Machine} (hlib : LibTy Δ m.lib) : ∀ (row : List (Label × Ty)) {fuel : Nat}
    {fs : List (Label × (Term × Env))} {f : Fault}, Ty.rowData row = true →
    ThunksTy Δ fs row → m.extractRow row fuel fs = .error f → f ≠ .stuck
  | [], _, _, _, _, ht, h => by
    cases ht; simp [Machine.extractRow] at h
  | (ℓ, A) :: row, _, _, _, hd, ht, h => by
    simp only [Ty.rowData, Bool.and_eq_true] at hd
    cases ht with
    | cons he htm hrest =>
      simp only [Machine.extractRow, if_true] at h
      split at h
      · rename_i v fuel' hfo
        split at h
        · rename_i d fuel'' hx
          split at h
          · cases h
          · rename_i e hr
            cases h
            exact extractRow_progress hlib row hd.2 hrest hr
        · rename_i e hx
          cases h
          exact extract_progress hlib A hd.1 (force_typed hlib he htm hfo) hx
      · rename_i e hfo
        cases h
        exact force_progress hlib he htm hfo
end
end

theorem verdict_shape {d : Data} (h : Conforms d verdictTy) :
    d = .inj "ok" (.record []) ∨ ∃ why, d = .inj "refused" (.bytes why) := by
  cases h with
  | inj hf hd =>
    rename_i ℓ A d'
    simp only [Row.find?] at hf
    split at hf
    · cases hf; rename_i he; subst he; left; rw [conf_unit hd]
    · split at hf
      · cases hf; rename_i he; subst he; obtain ⟨b, rfl⟩ := conf_bytes hd; exact .inr ⟨b, rfl⟩
      · cases hf

/-- **The receiver's law run is never stuck**: on a loaded package's law, on old and new states
read at its state row and a request in bounds, `runLaw` returns a verdict (`ok`, or `refused` with
the author's bytes) or a named budget/arithmetic fault. Neither its machine run (`law_never_stuck`)
nor its extraction (`extract_progress`) ends `stuck`, and the extracted verdict is one of its two
arms (`verdict_shape`). -/
theorem runLaw_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ : Label} {old new : Slots} {od nd : Data} {r : Req D}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hl : ℓ ∈ p.laws)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hnew : readState digestOf (recordRow p.state) new = .ok nd)
    (hr : reqOk bytesOf r = true) :
    runLaw L.lib (.get (.ref g) ℓ) od nd (reqData bytesOf r) ≠ .error .stuck := by
  have hrun := law_never_stuck (ticks := lawTicks) hload hp hl hold hnew hr
  have hlib := (load_libTy hload).1
  have happ : applyAt (.get (.ref g) ℓ) = apply3 g ℓ := rfl
  unfold runLaw
  rw [happ]
  split
  · rename_i f used hf
    rw [hf] at hrun
    intro h; cases h; exact hrun rfl
  · rename_i v used hv
    rw [hv] at hrun
    split
    · simp
    · simp
    · rename_i x h1 h2 hx
      exfalso
      obtain ⟨d, left⟩ := x
      rcases verdict_shape (extract_conforms (m := ⟨L.lib⟩) hlib verdictTy hrun hx) with rfl | ⟨why, rfl⟩
      · exact h1 _ _ rfl
      · exact h2 _ _ rfl
    · rename_i f hx
      intro h; cases h
      exact extract_progress (m := ⟨L.lib⟩) hlib verdictTy (by decide) hrun hx rfl

/-! ## Teeth -/

/-- A function type is not data: extraction at it is `stuck`, which is why `extract_progress`
takes `isData`. -/
theorem extract_fn_stuck : (Machine.mk []).extract (.fn .nat .nat) 5 (.clo (.var 0) []) = .error .stuck := rfl

private def natLaw : Term := .lam (.record []) (.lam (.record []) (.lam reqTy (.nat 5)))

/-- A law that returns a number where a verdict belongs IS stuck in `runLaw`, so
`runLaw_never_stuck` needs the closure's typing (a law field checked at `lawTy`). -/
theorem runLaw_nat_stuck :
    (match runLaw [] natLaw (.record []) (.record []) (.record []) with
      | .error .stuck => true
      | _ => false) = true := by decide

end Nanodregg.Lang
