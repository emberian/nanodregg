/-
# Protocol.Proofs.Rows — no operation without a row

The deletion rule as a theorem: an operation that no row drives is not part of the system. Adding
an operation to `Op` without a row that exercises it breaks this proof by name.

The rows' writer serves every event the kernel admits (PROTOCOL-55): `Writer.walkTurnsAt_serves`
over HOST's walk at a budget of `eventBytesMax + 5`, its tooth at `+ 4`, and both parameter sets'
budgets meeting its premise.
-/
import Protocol.Rows
import Protocol.Rows.Writer
import Protocol.Rows.Deployed
import Protocol.Proofs.Table

namespace Nanodregg.Protocol

/-- Every operation is driven by some row. -/
theorem every_op_has_a_row (op : Op) : ∃ r ∈ rows, op ∈ r.ops := by
  have h : rows.any (fun r => r.ops.contains op) = true := by cases op <;> decide
  obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, List.elem_iff.mp hc⟩

theorem row_names_distinct : (rows.map Row.name).Nodup := by decide

end Nanodregg.Protocol

namespace Nanodregg.Protocol.Rows.Writer

open Nanodregg.Kernel Nanodregg.Host

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- A page carries a step's event behind a 1-byte tag (`Host.Page.stepEvent`). -/
theorem stepEvent_size (s : Kernel.Step D) : (Page.stepEvent s).size = eventSize s + 1 := by
  cases s <;> simp only [Page.stepEvent, eventSize, ByteArray.size_append] <;> exact Nat.add_comm _ _

theorem foldl_invariant {α β : Type} (f : β → α → β) (P : β → Prop) (hf : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_invariant f P hf l (f b a) (hf b a hb)

omit [Ord D] [DecidableEq D] in
theorem walkTurnsAt_eq (E : Env D) (B start : Nat) (c : D) (h : Nat) (ts : List (Kernel.Step D × D))
    (a : Page.Acc) : Page.walkTurnsAt E B start c h ts a = ts.foldl (walkStep E B start) (a, c, h) := rfl

omit [Ord D] [DecidableEq D] in
/-- Steps at or below `start` are skipped: the walk's count moves, its served events, bytes and
`full` do not. -/
theorem skip_prefix (E : Env D) (B start : Nat) :
    ∀ (pre : List (Kernel.Step D × D)) (a : Page.Acc) (c : D) (h : Nat), h + pre.length ≤ start →
      a.full = false → ∃ a' c', pre.foldl (walkStep E B start) (a, c, h) = (a', c', h + pre.length) ∧
        a'.bytes = a.bytes ∧ a'.full = false ∧ a'.events = a.events
  | [], a, c, h, _, hf => ⟨a, c, by simp, rfl, hf, rfl⟩
  | (t, r) :: pre, a, c, h, hl, hf => by
    simp only [List.length_cons] at hl
    have hs : h + 1 ≤ start := by omega
    obtain ⟨a', c', he, hb, hf', hev⟩ := skip_prefix E B start pre
      { a with steps := h + 1, chain := E.bytes (Kernel.stepLink E c t r) } (Kernel.stepLink E c t r) (h + 1)
      (by omega) hf
    refine ⟨a', c', ?_, hb, hf', hev⟩
    rw [List.foldl_cons]
    simp only [walkStep, hf, if_neg Bool.false_ne_true, if_pos hs]
    simp only [hf] at he
    rw [he, List.length_cons, show h + 1 + pre.length = h + (pre.length + 1) by omega]

omit [Ord D] [DecidableEq D] in
/-- **A page that has served nothing serves the first step past its start** whenever the budget
holds every event the kernel admits plus the page's 4-byte event length and the event's 1-byte tag.
The record may begin with any number of steps at or below `start` (`pre`, skipped: the entry
`locate` returns is at or below `start`), and the page may arrive carrying an accumulator from
records it skipped whole (events none, bytes 0, not full). The rows' budgets meet the premise
(`Params.toy_budget_serves`, `Params.deployed_budget_serves`). This is the record-level fact.
Not proved: the lift through `Host.Page.walk` and `build` (which read the segment) to the page follow
receives (cv 01a150c0). HOST's `budget_fits_event`, the same bound stated at `+ 4` (one byte short)
about `Page.budget`, is a separate fact no theorem consumes. -/
theorem walkTurnsAt_serves (E : Env D) {B : Nat} (hB : Kernel.Bounds.eventBytesMax + 5 ≤ B)
    (start : Nat) (c : D) (h : Nat) (pre : List (Kernel.Step D × D)) (s : Kernel.Step D) (root : D)
    (rest : List (Kernel.Step D × D)) (a : Page.Acc) (hev : a.events = #[]) (hb : a.bytes = 0)
    (hf : a.full = false) (hpre : h + pre.length = start) (hs : eventSize s ≤ Kernel.Bounds.eventBytesMax) :
    0 < (Page.walkTurnsAt E B start c h (pre ++ (s, root) :: rest) a).1.events.size := by
  rw [walkTurnsAt_eq, List.foldl_append]
  obtain ⟨a', c', he, hb', hf', hev'⟩ := skip_prefix E B start pre a c h (by omega) hf
  rw [he, List.foldl_cons]
  apply foldl_invariant _ (fun st : Page.Acc × D × Nat => 0 < st.1.events.size)
  · intro ⟨a, c, h⟩ ⟨t, r⟩ hb
    simp only [walkStep]
    split
    · exact hb
    · split
      · exact hb
      · split
        · exact hb
        · simp [Array.size_push]
  · have hsz := stepEvent_size s
    simp only [walkStep, hf', if_neg Bool.false_ne_true]
    rw [if_neg (by omega),
      if_neg (by simp only [hev', hev, hb', hb, Array.size_empty, Host.recordTurnsMax]; omega)]
    simp

omit [Ord D] [DecidableEq D] in
/-- The tooth, run through the walk itself: one byte less (`+ 4`, the value HOST's
`budget_fits_event` states) and an event of the kernel's full size, first past `start`, leaves the
record's walk serving NOTHING (it is marked full and nothing after is served). -/
theorem walkTurnsAt_one_short (E : Env D) (start : Nat) (c : D) (h : Nat) (s : Kernel.Step D) (root : D)
    (rest : List (Kernel.Step D × D)) (steps : Nat) (chain : ByteArray)
    (hs : eventSize s = Kernel.Bounds.eventBytesMax) (hst : start < h + 1) :
    (Page.walkTurnsAt E (Kernel.Bounds.eventBytesMax + 4) start c h ((s, root) :: rest)
      { steps, chain }).1.events.size = 0 := by
  rw [walkTurnsAt_eq, List.foldl_cons]
  refine (foldl_invariant (walkStep E (Kernel.Bounds.eventBytesMax + 4) start)
    (fun st : Page.Acc × D × Nat => st.1.full = true ∧ st.1.events.size = 0) ?_ rest _ ?_).2
  · intro ⟨a, c, h⟩ ⟨t, r⟩ ⟨hfull, he⟩
    simp only at hfull he
    simp only [walkStep, hfull, ↓reduceIte]
    exact ⟨trivial, he⟩
  · have hsz := stepEvent_size s
    simp only [walkStep, if_neg Bool.false_ne_true]
    rw [if_neg (by omega), if_pos (Or.inr (by rw [hsz, hs]; omega))]
    simp

end Nanodregg.Protocol.Rows.Writer

namespace Nanodregg.Protocol.Rows.Params

/-- The toy rows' budget is `Writer.walkTurnsAt_serves`'s premise: a record's walk that has
served nothing serves the first step past its start, whatever event the kernel admitted there. -/
theorem toy_budget_serves : Kernel.Bounds.eventBytesMax + 5 ≤ toy.pageBudget := Nat.le_refl _

/-- The deployed rows' budget is `Writer.walkTurnsAt_serves`'s premise. -/
theorem deployed_budget_serves : Kernel.Bounds.eventBytesMax + 5 ≤ deployed.pageBudget :=
  Nat.le_refl _

end Nanodregg.Protocol.Rows.Params
