/-
# Protocol.Proofs.FollowJournal — a journal entry on follow's World is a commit follow re-derived

Follow's World journals a transaction id only when follow itself re-derived the Turn that put it
there: every Turn event of a log page is `Receive.submit` on follow's own World (`absorbStep`:
receive, then admit), and a refusal or a cancel changes no journal entry (`refuse_journalAt`).

- `JournalFrom X Q w₀ w`: follow's World `w` satisfies `Q`, its journal and rows tries are
  canonical, and each of its journal entries is `w₀`'s, or was written by admitting a Turn received
  from a call that decodes from logged bytes, at a World satisfying `Q` with canonical rows: the
  entry is that call's id and `(height + 1, turnDigest)` of that Turn.
- `absorbStep_journalFrom`: one re-derived event keeps it, for any `Q` that event keeps.
- `step_journalFrom`: every step of follow's machine keeps it, when `Q` refutes `atGenesis`
  (`step_keeps`: the step that adopts a base, the one move that is not a re-derivation, happens only
  at a World that holds nothing).

What is not claimed: that `w₀` did not hold the entry already (a base follow started from carries
its own journal), nor that the committing call is the one a caller has in mind: two calls with one
id are the hash's business (`Hosting.Proofs.Committed`, a second preimage of the caller's id).
-/
import Protocol.Proofs.FollowHead
import Kernel.Proofs.Journal
import Kernel.Proofs.Rows

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- Each journal entry of `w` is `w₀`'s or a commit follow re-derived at a `Q` World. -/
def JournalFrom (X : Ctx D) (Q : World D → Prop) (w₀ w : World D) : Prop :=
  Q w ∧ w.JournalCanon X.env ∧ w.RowsCanon X.env ∧
    ∀ k e, w.journalAt X.env k = some e → w₀.journalAt X.env k = some e ∨
      ∃ (v v' : World D) (b : ByteArray) (c : Call D) (t : Turn D), Q v ∧ v.RowsCanon X.env ∧
        X.decodeCall b = some c ∧ receive X v c = .ok t ∧ World.admit X.env v t = .ok v' ∧
        txIdOf X c = k ∧ e = (v.height + 1, turnDigest X.env t)

/-- The start: a `Q` World with canonical journal and rows holds only its own entries. -/
theorem journalFrom_refl {X : Ctx D} {Q : World D → Prop} {w₀ : World D} (hq : Q w₀)
    (hj : w₀.JournalCanon X.env) (hr : w₀.RowsCanon X.env) : JournalFrom X Q w₀ w₀ :=
  ⟨hq, hj, hr, fun _ _ h => .inl h⟩

/-- A refusal keeps the journal and the rows tries, so it keeps every entry's provenance. -/
theorem refuse_journalFrom {X : Ctx D} {Q : World D → Prop} {w₀ w w' : World D} {r : Refused D}
    (h : World.refuse X.env w r = .ok w') (hq : Q w') (hp : JournalFrom X Q w₀ w) :
    JournalFrom X Q w₀ w' := by
  obtain ⟨-, hj, hr, he⟩ := hp
  refine ⟨hq, ?_, refuse_rowsCanon hr h, fun k e hk => he k e ((refuse_journalAt h k).symm.trans hk)⟩
  unfold World.JournalCanon; rw [(refuse_frame h).2.1]; exact hj

/-- **A submitted call's commit keeps the provenance**: its own entry is that commit, every other
entry is one the World held before. -/
theorem submit_journalFrom {X : Ctx D} {Q : World D → Prop} {w₀ w w' : World D} {b : ByteArray}
    {c : Call D} {t : Turn D} (hb : X.decodeCall b = some c) (h : submit X w c = .ok (t, w'))
    (hq : Q w') (hp : JournalFrom X Q w₀ w) : JournalFrom X Q w₀ w' := by
  obtain ⟨hqw, hj, hr, he⟩ := hp
  obtain ⟨-, hrc, ha⟩ := submit_ok h
  refine ⟨hq, admit_journalCanon hj ha, admit_rowsCanon hr ha, fun k e hk => ?_⟩
  obtain ⟨posts, -, rfl⟩ := admit_ok ha
  rcases commit_journal_mem hj hk with ⟨rfl, rfl⟩ | ⟨-, hw, -⟩
  · exact .inr ⟨w, _, b, c, t, hqw, hr, hb, hrc, ha, (receive_derived hrc).txId.symm, rfl⟩
  · exact he k e hw

/-- **One re-derived event keeps the provenance** (`absorbStep`: a Turn by `submit`, a refusal or
a cancel by `World.refuse`), for any `Q` it keeps. -/
theorem absorbStep_journalFrom {X : Ctx D} {Q : World D → Prop} {w₀ w w' : World D} {e : ByteArray}
    {s : Kernel.Step D} (h : absorbStep X w e = .ok (s, w')) (hq : Q w') (hp : JournalFrom X Q w₀ w) :
    JournalFrom X Q w₀ w' := by
  unfold absorbStep at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try (obtain ⟨rfl, rfl⟩ := h))
  all_goals first
    | exact refuse_journalFrom (cancel_recorded ‹_›).2.2.2 hq hp
    | exact refuse_journalFrom (judge_recorded ‹_›).2.2.2 hq hp
    | exact submit_journalFrom ‹_› ‹_› hq hp

/-- **Every step of follow's machine keeps the provenance**, for a `Q` every re-derived event keeps
and that refutes `atGenesis`. -/
theorem step_journalFrom {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {Q : World D → Prop} {w₀ : World D} {f f' : Follow D} {p : Persist D} {kb result : ByteArray}
    {r : Reply} (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false)
    (h : step X dc B me f kb result = (f', p, r)) (hp : JournalFrom X Q w₀ f.world) :
    JournalFrom X Q w₀ f'.world :=
  step_keeps (P := JournalFrom X Q w₀) (fun hp' hs => absorbStep_journalFrom hs (hA hp'.1 hs) hp')
    (fun hp' => hG hp'.1) h hp

end Nanodregg.Protocol.Command
