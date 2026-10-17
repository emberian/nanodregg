/-
# Hosting.Proofs.Wire — the controller ↔ launcher frames are lawful and say what they carry

`actionCodec_lawful` / `reportCodec_lawful`: the two families have distinct codes, so their codecs
are lawful (canonical; `Codec.Tagged.codec_lawful`). `actionOf_wire` / `reportOf_wire`: the wire value
of an action or report reads back as that action or report, so `decode_encodeAction` says the bytes
the launcher decodes ARE the controller's action. The refusal and failure tables are injective in
code and name and list every case, so the emitted Rust enums are total and agree with Lean.
-/
import Hosting.Wire
import Codec.Proofs.Layout

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Codec Nanodregg.Hosting Nanodregg.Hosting.Wire

namespace Refusal

theorem mem_all (r : Hosting.Refusal) : r ∈ Hosting.Refusal.all := by cases r <;> decide

theorem ofCode?_code (r : Hosting.Refusal) : Hosting.Refusal.ofCode? r.code = some r := by
  cases r <;> decide

theorem code_injective {a b : Hosting.Refusal} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [Hosting.Refusal.code]

theorem name_injective {a b : Hosting.Refusal} (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Hosting.Refusal.name]

end Refusal

namespace LaunchFailure

theorem mem_all (r : Hosting.LaunchFailure) : r ∈ Hosting.LaunchFailure.all := by cases r <;> decide

theorem ofCode?_code (r : Hosting.LaunchFailure) : Hosting.LaunchFailure.ofCode? r.code = some r := by
  cases r <;> decide

theorem code_injective {a b : Hosting.LaunchFailure} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [Hosting.LaunchFailure.code]

theorem name_injective {a b : Hosting.LaunchFailure} (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Hosting.LaunchFailure.name]

end LaunchFailure

theorem actionCodes_nodup : (actionCases.map (·.2.1)).Nodup := by decide
theorem reportCodes_nodup : (reportCases.map (·.2.1)).Nodup := by decide

theorem actionCodec_lawful : Stream.Lawful actionCodec :=
  Tagged.codec_lawful _ _ _ actionCodes_nodup

theorem reportCodec_lawful : Stream.Lawful reportCodec :=
  Tagged.codec_lawful _ _ _ reportCodes_nodup

private theorem bytes?_val {b : ByteArray} {v : Bytes Bounds.frameMax} (h : bytes? b = some v) :
    v.val = b := by
  unfold bytes? at h; split at h <;> simp_all; rw [← h]

private theorem path?_val {p : Path} {v : WPath} (h : path? p = some v) : v.val = p := by
  unfold path? at h; split at h <;> simp_all; rw [← h]

private theorem mapM_path? : ∀ {ps : List Path} {a : List WPath}, ps.mapM path? = some a →
    a.map (·.val) = ps
  | [], a, h => by simp at h; subst h; rfl
  | p :: ps, a, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    rcases hp : path? p with _ | v <;> simp [hp] at h
    rcases hr : ps.mapM path? with _ | rest <;> simp [hr] at h
    subst h
    simp [path?_val hp, mapM_path? hr]

private theorem paths?_val {ps : List Path} {v : Bounded Bounds.frameMax WPath}
    (h : paths? ps = some v) : unpaths v = ps := by
  unfold paths? at h
  simp only [bind, Option.bind] at h
  rcases hm : ps.mapM path? with _ | a <;> simp [hm] at h
  obtain ⟨-, rfl⟩ := h
  simp [unpaths, mapM_path? hm]

private theorem refusal_get {r : Hosting.Refusal} {h} :
    (Hosting.Refusal.ofCode? r.code).get h = r := by
  simp [Refusal.ofCode?_code]

private theorem failure_get {r : Hosting.LaunchFailure} {h} :
    (Hosting.LaunchFailure.ofCode? r.code).get h = r := by
  simp [LaunchFailure.ofCode?_code]

/-- The wire value of an action reads back as the action. -/
theorem actionOf_wire {a : Action} {w : ActionTy} (h : actionWire? a = some w) : actionOf w = a := by
  rcases a with ⟨g, v⟩
  simp only [actionWire?, bind, Option.bind] at h
  rcases hg : bytes? g with _ | gv <;> simp [hg] at h
  rcases v with p | _ | why
  · simp only at h
    rcases h1 : path? p.program with _ | a1 <;> simp [h1] at h
    rcases h2 : paths? p.read with _ | a2 <;> simp [h2] at h
    rcases h3 : paths? p.write with _ | a3 <;> simp [h3] at h
    rcases h4 : paths? p.exec with _ | a4 <;> simp [h4] at h
    rcases h6 : paths? p.connect with _ | a6 <;> simp [h6] at h
    rcases h5 : paths? p.hidden with _ | a5 <;> simp [h5] at h
    subst h
    simp [actionOf, bytes?_val hg, path?_val h1, paths?_val h2, paths?_val h3, paths?_val h4,
      paths?_val h5, paths?_val h6]
  · simp at h; subst h; simp [actionOf, bytes?_val hg]
  · simp at h; subst h; simp [actionOf, bytes?_val hg, refusal_get]

/-- The wire value of a report reads back as the report. -/
theorem reportOf_wire {e : Report} {w : ReportTy} (h : reportWire? e = some w) : reportOf w = e := by
  rcases e with ⟨g, t⟩ | ⟨g, s, t⟩ | ⟨g, why, t⟩ <;>
    simp only [reportWire?, bind, Option.bind] at h <;>
    rcases hg : bytes? g with _ | gv <;> simp [hg] at h <;> subst h <;>
    simp [reportOf, bytes?_val hg, failure_get]

/-- A report of a grain name that fits a frame has a wire value (the launcher's names are the
controller's, 64 bytes). -/
theorem reportWire_some (e : Report) (hg : (match e with
    | .started g _ | .exited g _ _ | .failed g _ _ => g).size ≤ Bounds.frameMax) :
    (reportWire? e).isSome = true := by
  rcases e with ⟨g, t⟩ | ⟨g, s, t⟩ | ⟨g, why, t⟩ <;>
    simp [reportWire?, bytes?, bind, Option.bind, hg] <;> simp_all

/-- The bytes `encodeAction` hands the launcher decode, by the one codec, to the action. -/
theorem decode_encodeAction {a : Action} {b : ByteArray} (h : encodeAction a = some b) :
    (actionCodec.decode b).map actionOf = .ok a := by
  simp only [encodeAction, bind, Option.bind] at h
  rcases hw : actionWire? a with _ | w <;> simp [hw] at h
  obtain ⟨-, rfl⟩ := h
  rw [Stream.decode_bytes actionCodec_lawful]
  simp [Except.map, actionOf_wire hw]

/-- What the launcher encodes the controller decodes. -/
theorem decodeReport_bytes {e : Report} {w : ReportTy} (h : reportWire? e = some w) :
    decodeReport (reportCodec.bytes w) = .ok e := by
  simp [decodeReport, Stream.decode_bytes reportCodec_lawful, Except.map, reportOf_wire h]

/-! ## Names, not positions

The Rust launcher reads a launch frame's fields BY NAME (emitted from `actionCases`); Lean fills
them by POSITION. `launch_fields` ties the two (by `Wire.pathNamed`/`pathsNamed`): the field named `program` carries the plan's
program, and each `paths` field named `read`, `write`, `exec`, `connect`, `hidden` carries that list of the
plan. A swap of two same-typed slots in `actionWire?` and `actionOf` together keeps `actionOf_wire`
true and turns this red. -/

/-- A launch's frame carries each plan field under that field's name. -/
theorem launch_fields {g : ByteArray} {p : Plan} {w : ActionTy}
    (h : actionWire? { grain := g, verdict := .launch p } = some w) :
    ∃ v, w = ⟨⟨0, by decide⟩, v⟩ ∧
      pathNamed "program" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.program ∧
      pathsNamed "read" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.read ∧
      pathsNamed "write" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.write ∧
      pathsNamed "exec" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.exec ∧
      pathsNamed "connect" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.connect ∧
      pathsNamed "hidden" (actionCases.get ⟨0, by decide⟩).2.2 v = some p.hidden := by
  simp only [actionWire?, bind, Option.bind] at h
  rcases hg : bytes? g with _ | gv <;> simp [hg] at h
  rcases h1 : path? p.program with _ | a1 <;> simp [h1] at h
  rcases h2 : paths? p.read with _ | a2 <;> simp [h2] at h
  rcases h3 : paths? p.write with _ | a3 <;> simp [h3] at h
  rcases h4 : paths? p.exec with _ | a4 <;> simp [h4] at h
  rcases h6 : paths? p.connect with _ | a6 <;> simp [h6] at h
  rcases h5 : paths? p.hidden with _ | a5 <;> simp [h5] at h
  subst h
  refine ⟨_, rfl, ?_⟩
  simp [pathNamed, pathsNamed, actionCases, path?_val h1, paths?_val h2, paths?_val h3, paths?_val h4,
    paths?_val h5, paths?_val h6]

/-- Tooth: the premise of `actionOf_wire` is met — a kill of a 64-byte name has a wire value and
encodes, and a refusal reads back as ITS refusal, not another. -/
theorem kill_encodes : (encodeAction { grain := ⟨Array.replicate 64 97⟩, verdict := .kill }).isSome := by
  decide

theorem refuse_reads_back :
    (actionWire? { grain := ⟨#[97]⟩, verdict := .refuse .crashLoop }).map actionOf =
      some { grain := ⟨#[97]⟩, verdict := .refuse .crashLoop } := by
  decide

end Nanodregg.Hosting.Proofs
