/-
# Hosting.Proofs.Resident — what the resident's decisions guarantee (HOSTING-27, HOSTING-31)

- `parse_argv`, `place_args`, `accepted_is_plan`: an argv the resident accepts is EXACTLY Lean's
  `plan` for the resident grain it names, joined onto three roots, field for field in `Plan` order.
  A reordered, dropped or extra path is never accepted (grain-launch's `plan_argv` order is checked
  here, at the receiving end).
- `decide_idle`, `decide_kept_first`, `decide_ask`, `decide_answer` (over `decideTick`, every
  pending ring lowest first): nothing pending is idle; a kept ring still pending is answered with
  its kept text wherever it stands, so it is never asked about again, even when a lower ring lands;
  an ask is only for the LOWEST pending ring (the listing's head: key order is ring order) and only
  when no kept ring is pending; an answer is only the kept text for the kept ring, which is pending.
- `ofRow_row`, `read_iff_row`: the resident's ring for a range-read line is exactly the row datum
  `Lang.Read.readData` reads at `pending`'s row type, which `Protocol.Proofs.Command.rangeLines_reads`
  says is the listed row: what it answers is a row the bell holds.
- `fit_size`, `answerText_size`: every answer text is 1..`textMax` bytes.
- `answerArg_some`, `keptText_some`: both always print, so `answer unprintable` is unreachable and
  `keep` never fails for want of a text.
- `answerArg_reads`: the printed `answer` argument reads back, at the described argument type, to
  exactly `(record (notBefore N) (ringer #H) (text T))` for the ring and text decided: what `invoke`
  checks is the ring the resident picked and the text it kept.
- `kept_reads`: what the volume keeps reads back to the same ring and text, so a restart answers
  that ring from it rather than asking again.
- `exit_codes_nodup`: each end has its own code.
-/
import Hosting.Resident.Run
import Lang.Proofs.Print

namespace Nanodregg.Hosting.Proofs.Resident

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Lang

theorem parse_argv {argv : List ByteArray} {a : Args} (h : parse argv = some a) : a.argv = argv := by
  simp only [parse, Option.filter_eq_some_iff, decide_eq_true_eq] at h
  exact h.2

theorem place_args {a : Args} {p : Placed} (h : place a = some p) : p.args = a := by
  simp only [place, Option.filter_eq_some_iff, decide_eq_true_eq] at h
  exact h.2

/-- An accepted argv is the plan Lean computes for the resident grain it names, every path joined
onto its root, in `Plan` order: argv = program, then count and paths of read, write, exec, broker,
member, each `joinOnto` its root. -/
theorem accepted_is_plan {argv : List ByteArray} {a : Args} {p : Placed}
    (ha : parse argv = some a) (hp : place a = some p) :
    argv = p.args.argv ∧ Hosting.plan p.label p.grain = .ok p.plan ∧ p.grain.kind = .resident := by
  refine ⟨by rw [place_args hp, parse_argv ha], p.planned, ?_⟩
  simp only [place, Option.filter_eq_some_iff] at hp
  obtain ⟨hc, -⟩ := hp
  unfold candidate at hc
  split at hc
  · split at hc
    · dsimp only at hc
      split at hc
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hc
        obtain ⟨_, _, _, _, _, _, rfl⟩ := hc
        rfl
      · simp at hc
    · simp at hc
  · simp at hc

theorem decide_idle (k : Option (Ring × ByteArray)) : decideTick [] k = .idle := by
  match k with
  | none => rfl
  | some (r, t) => simp [decideTick]

/-- A kept ring still pending is answered with its kept text, wherever it stands in the queue: a
ring that lands below it (a backdated notBefore) does not displace it, so it is never asked about
again. -/
theorem decide_kept_first {p : List Ring} {r : Ring} (t : ByteArray) (h : r ∈ p) :
    decideTick p (some (r, t)) = .answer r t := by
  simp [decideTick, h]

/-- An ask is only for the listing's head, and only when no kept ring is pending. The head is the
LOWEST pending ring because the listing is the range read's, in ascending key order
(`Protocol.Proofs.Command.rangeLines_reads`, `Lang.Proofs.KeyOrder.range_keys_ascend_read`); this
theorem is about the head, not the order. -/
theorem decide_ask {p : List Ring} {k : Option (Ring × ByteArray)} {r : Ring}
    (h : decideTick p k = .ask r) : p.head? = some r ∧ ∀ q t, k = some (q, t) → q ∉ p := by
  match k, p with
  | none, [] => simp [decideTick] at h
  | none, q :: _ =>
    simp only [decideTick, Act.ask.injEq] at h
    subst h
    simp
  | some (q, t), p =>
    simp only [decideTick] at h
    split at h
    · simp at h
    · rename_i hq
      refine ⟨?_, fun q' t' he => ?_⟩
      · match p, h with
        | q0 :: _, h => simp only [Act.ask.injEq] at h; subst h; rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact hq

/-- An answer is only the kept text, for the kept ring, while it is pending. -/
theorem decide_answer {p : List Ring} {k : Option (Ring × ByteArray)} {r : Ring} {t : ByteArray}
    (h : decideTick p k = .answer r t) : k = some (r, t) ∧ r ∈ p := by
  match k, p with
  | none, [] => simp [decideTick] at h
  | none, _ :: _ => simp [decideTick] at h
  | some (q, u), p =>
    simp only [decideTick] at h
    split at h
    · simp only [Act.answer.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by assumption⟩
    · match p, h with
      | [], h => simp at h
      | _ :: _, h => simp at h

theorem ofRow_row (r : Ring) : Ring.ofRow r.row = .ok r := rfl

theorem ofRow_eq {v : Data} {r : Ring} (h : Ring.ofRow v = .ok r) : v = r.row := by
  unfold Ring.ofRow at h
  split at h
  · cases h; rfl
  · cases h

/-- The resident's ring for a line is exactly the row datum the line reads to at `pending`'s row
type: by `Protocol.Proofs.Command.rangeLines_reads` that is the row the range read listed in that
place, so the resident answers a row the bell holds, at the key it holds it. -/
theorem read_iff_row (sh : Shape) (s : String) (r : Ring) :
    Ring.read sh s = .ok r ↔ Read.readData (rowTy sh.pending) s = .ok r.row := by
  unfold Ring.read
  cases hv : Read.readData (rowTy sh.pending) s with
  | error e => simp
  | ok v =>
    simp only [Except.ok.injEq]
    exact ⟨fun h => by rw [ofRow_eq h], fun h => by rw [h]; rfl⟩

theorem utf8Prefix_go_size (t : ByteArray) : ∀ k, (utf8Prefix.go t k).size ≤ k
  | 0 => by simp [utf8Prefix.go]
  | k + 1 => by
    unfold utf8Prefix.go
    split
    · exact Nat.le_succ_of_le (utf8Prefix_go_size t k)
    · simp only [ByteArray.size_extract]; omega

theorem utf8Prefix_size (t : ByteArray) (n : Nat) : (utf8Prefix t n).size ≤ n := by
  unfold utf8Prefix
  split
  · assumption
  · exact utf8Prefix_go_size t n

theorem named_empty_size : (named "empty reply").size = 13 := by decide

/-- Every fitted text is one the bell's `answer` takes: 1..`textMax` bytes. -/
theorem fit_size (t : ByteArray) : 0 < (fit t).size ∧ (fit t).size ≤ textMax := by
  unfold fit
  simp only
  split
  · rw [named_empty_size]; decide
  · rename_i h
    refine ⟨?_, utf8Prefix_size t textMax⟩
    simp only [ByteArray.isEmpty, beq_iff_eq] at h
    omega

theorem answerText_size (a : Broker.Answer) :
    0 < (answerText a).size ∧ (answerText a).size ≤ textMax := by
  cases a <;> exact fit_size _

theorem textMax_le_bytesMax : textMax ≤ Lang.Bounds.bytesMax := by decide

/-- The printed `answer` argument reads back to exactly the picked ring's key and the decided text. -/
theorem answerArg_reads {r : Ring} {t : ByteArray} {s : String} (hn : r.notBefore < Lang.Bounds.natLimit)
    (hg : r.ringer.size ≤ Lang.Bounds.digestBytesMax) (ht : t.size ≤ Lang.Bounds.bytesMax)
    (h : answerArg r t = some s) : Read.readData answerArgTy s = .ok (answerDatum r t) :=
  Print.readData_data (.record (.cons (.nat hn) (.cons (.digest hg) (.cons (.bytes ht) .nil)))) (by decide) h

/-- What the volume keeps reads back to the same ring (key and text) and answer. -/
theorem kept_reads {r : Ring} {t : ByteArray} {s : String} (hn : r.notBefore < Lang.Bounds.natLimit)
    (hx : r.text.size ≤ Lang.Bounds.bytesMax) (hg : r.ringer.size ≤ Lang.Bounds.digestBytesMax)
    (ht : t.size ≤ Lang.Bounds.bytesMax) (h : keptText r t = some s) : keptRead s = some (r, t) := by
  have := Print.readData_data (T := keptTy)
    (.record (.cons (.bytes ht) (.cons (.nat hn) (.cons (.digest hg) (.cons (.bytes hx) .nil))))) (by decide) h
  simp [keptRead, this]

theorem bytesSx_flat (t : ByteArray) : Print.need (Print.bytesSx t) = 1 ∧ Print.width (Print.bytesSx t) = 0 := by
  unfold Print.bytesSx
  split
  · split <;> simp [Print.need, Print.width, Print.atom]
  · simp [Print.need, Print.width, Print.atom]

/-- The `answer` argument always prints: the resident's `answer unprintable` end is unreachable. -/
theorem answerArg_some (r : Ring) (t : ByteArray) : (answerArg r t).isSome = true := by
  obtain ⟨hn, hw⟩ := bytesSx_flat t
  have h1 : Wire.labelOk "text" = true := by decide
  have h2 : Wire.labelOk "notBefore" = true := by decide
  have h3 : Wire.labelOk "ringer" = true := by decide
  simp only [answerArg, answerDatum, Print.data, Print.dataSx, Print.dataFieldsSx, Print.label, h1, h2, h3]
  simp [Print.fits, Print.fitsB]
  unfold Print.list Print.digestSx Print.atom
  simp only [Print.need, Print.needs, Print.width, Print.widths, hn, hw]
  constructor <;> simp [Read.depthMax, Read.listMax, Wire.depthMax, Wire.rowMax]

/-- What the volume keeps always prints. -/
theorem keptText_some (r : Ring) (t : ByteArray) : (keptText r t).isSome = true := by
  obtain ⟨hn, hw⟩ := bytesSx_flat t
  obtain ⟨hn', hw'⟩ := bytesSx_flat r.text
  have h1 : Wire.labelOk "text" = true := by decide
  have h2 : Wire.labelOk "answer" = true := by decide
  have h3 : Wire.labelOk "ringer" = true := by decide
  have h4 : Wire.labelOk "notBefore" = true := by decide
  simp only [keptText, keptDatum, Print.data, Print.dataSx, Print.dataFieldsSx, Print.label, h1, h2, h3, h4]
  simp [Print.fits, Print.fitsB]
  unfold Print.list Print.digestSx Print.atom
  simp only [Print.need, Print.needs, Print.width, Print.widths, hn, hw, hn', hw']
  constructor <;> simp [Read.depthMax, Read.listMax, Wire.depthMax, Wire.rowMax]

theorem exit_codes_nodup : (Exit.all.map Exit.code).Nodup := by decide

end Nanodregg.Hosting.Proofs.Resident
