/-
# Protocol.Proofs.FollowJournal — a journal entry on follow's World is a commit follow re-derived

Follow's World journals a transaction id only when follow itself re-derived the Turn that put it
there: every Turn event of a log page is `Receive.submit` on follow's own World (`absorbStep`:
receive, then admit), and a refusal or a cancel changes no journal entry (`refuse_journalAt`).

- `JournalFrom X Q L w₀ w`: follow's World `w` satisfies `Q`, its journal and rows tries are
  canonical, and each of its journal entries is `w₀`'s, or was written by admitting a Turn received
  from a call that decodes from bytes IN `L`, at a World satisfying `Q` with canonical rows: the
  entry is that call's id and `(height + 1, turnDigest)` of that Turn. `L` is an explicit list, so
  a caller can bound the commits by the frames follow was actually handed (HOSTING-47).
- `absorbStep_journalFrom`: one re-derived event whose call bytes (`eventCall`) are in `L` keeps it,
  for any `Q` that event keeps.
- `step_journalFrom`: every step of follow's machine keeps it, when `Q` refutes `atGenesis` and the
  frame's result's calls (`frameCalls`) are in `L` (`step_world`: a step absorbs only events its
  result carries; the step that adopts a base, the one move that is not a re-derivation, happens only
  at a World that holds nothing).

What is not claimed: that `w₀` did not hold the entry already (a base follow started from carries
its own journal), nor that the committing call is the one a caller has in mind: two calls with one
id are the hash's business (`Hosting.Proofs.Committed`: a collision among the bytes the frames carried).
-/
import Protocol.Proofs.FollowHead
import Kernel.Proofs.Journal
import Kernel.Proofs.Rows

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- Each journal entry of `w` is `w₀`'s or a commit follow re-derived at a `Q` World, of a call
decoded from bytes in `L`. -/
def JournalFrom (X : Ctx D) (Q : World D → Prop) (L : List ByteArray) (w₀ w : World D) : Prop :=
  Q w ∧ w.JournalCanon X.env ∧ w.RowsCanon X.env ∧
    ∀ k e, w.journalAt X.env k = some e → w₀.journalAt X.env k = some e ∨
      ∃ (v v' : World D) (b : ByteArray) (c : Call D) (t : Turn D), Q v ∧ v.RowsCanon X.env ∧ b ∈ L ∧
        X.decodeCall b = some c ∧ receive X v c = .ok t ∧ World.admit X.env v t = .ok v' ∧
        txIdOf X c = k ∧ e = (v.height + 1, turnDigest X.env t)

/-- The start: a `Q` World with canonical journal and rows holds only its own entries. -/
theorem journalFrom_refl {X : Ctx D} {Q : World D → Prop} {L : List ByteArray} {w₀ : World D} (hq : Q w₀)
    (hj : w₀.JournalCanon X.env) (hr : w₀.RowsCanon X.env) : JournalFrom X Q L w₀ w₀ :=
  ⟨hq, hj, hr, fun _ _ h => .inl h⟩

/-- More logged bytes keep the provenance. -/
theorem JournalFrom.mono {X : Ctx D} {Q : World D → Prop} {L L' : List ByteArray} {w₀ w : World D}
    (hL : ∀ b ∈ L, b ∈ L') (h : JournalFrom X Q L w₀ w) : JournalFrom X Q L' w₀ w := by
  obtain ⟨hq, hj, hr, he⟩ := h
  refine ⟨hq, hj, hr, fun k e hk => ?_⟩
  rcases he k e hk with h | ⟨v, v', b, c, t, h1, h2, hb, h3⟩
  · exact .inl h
  · exact .inr ⟨v, v', b, c, t, h1, h2, hL b hb, h3⟩

/-- A refusal keeps the journal and the rows tries, so it keeps every entry's provenance. -/
theorem refuse_journalFrom {X : Ctx D} {Q : World D → Prop} {L : List ByteArray} {w₀ w w' : World D}
    {r : Refused D} (h : World.refuse X.env w r = .ok w') (hq : Q w') (hp : JournalFrom X Q L w₀ w) :
    JournalFrom X Q L w₀ w' := by
  obtain ⟨-, hj, hr, he⟩ := hp
  refine ⟨hq, ?_, refuse_rowsCanon hr h, fun k e hk => he k e ((refuse_journalAt h k).symm.trans hk)⟩
  unfold World.JournalCanon; rw [(refuse_frame h).2.1]; exact hj

/-- **A submitted call's commit keeps the provenance**: its own entry is that commit, every other
entry is one the World held before. -/
theorem submit_journalFrom {X : Ctx D} {Q : World D → Prop} {L : List ByteArray} {w₀ w w' : World D}
    {b : ByteArray} {c : Call D} {t : Turn D} (hbL : b ∈ L) (hb : X.decodeCall b = some c)
    (h : submit X w c = .ok (t, w')) (hq : Q w') (hp : JournalFrom X Q L w₀ w) : JournalFrom X Q L w₀ w' := by
  obtain ⟨hqw, hj, hr, he⟩ := hp
  obtain ⟨-, hrc, ha⟩ := submit_ok h
  refine ⟨hq, admit_journalCanon hj ha, admit_rowsCanon hr ha, fun k e hk => ?_⟩
  obtain ⟨posts, -, rfl⟩ := admit_ok ha
  rcases commit_journal_mem hj hk with ⟨rfl, rfl⟩ | ⟨-, hw, -⟩
  · exact .inr ⟨w, _, b, c, t, hqw, hr, hbL, hb, hrc, ha, (receive_derived hrc).txId.symm, rfl⟩
  · exact he k e hw

/-- **One re-derived event keeps the provenance** (`absorbStep`: a Turn by `submit`, a refusal or
a cancel by `World.refuse`), for any `Q` it keeps, when the event's call bytes are in `L`. -/
theorem absorbStep_journalFrom {X : Ctx D} {Q : World D → Prop} {L : List ByteArray} {w₀ w w' : World D}
    {e : ByteArray} {s : Kernel.Step D} (he : eventCall e ∈ L) (h : absorbStep X w e = .ok (s, w'))
    (hq : Q w') (hp : JournalFrom X Q L w₀ w) : JournalFrom X Q L w₀ w' := by
  obtain ⟨ev, hev, hr⟩ := absorbStep_ok.mp h
  rcases rederive_ok hr with ⟨b, c, t, rfl, hb, hs, rfl⟩ | ⟨b, c, v, r, -, -, hj, rfl⟩ |
      ⟨sig, b, c, v, r, -, -, hco, rfl⟩
  · have hbe : b = eventCall e := by
      rcases eventOf_some hev with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, _, _, -, h1⟩
      · exact Kernel.Event.turn.inj h1
      · cases h1
      · cases h1
    subst hbe
    exact submit_journalFrom he hb hs hq hp
  · exact refuse_journalFrom (judge_recorded hj).2.2.2 hq hp
  · exact refuse_journalFrom (cancel_recorded hco).2.2.2 hq hp

/-- Absorbing events whose call bytes are in `L` keeps the provenance. -/
theorem absorb_journalFrom {X : Ctx D} {Q : World D → Prop} {L : List ByteArray} {w₀ : World D}
    (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w') :
    ∀ (evs : List ByteArray) {w w' : World D} {acc ts : Array (Kernel.Step D × D)},
      (∀ e ∈ evs, eventCall e ∈ L) → absorb X w acc evs = .ok (w', ts) →
      JournalFrom X Q L w₀ w → JournalFrom X Q L w₀ w'
  | [], w, w', acc, ts, _, h, hp => by
    simp only [absorb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp
  | e :: es, w, w', acc, ts, hL, h, hp => by
    unfold absorb at h
    split at h
    · rename_i s w₁ hs
      exact absorb_journalFrom hA es (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) h
        (absorbStep_journalFrom (hL e List.mem_cons_self) hs (hA hp.1 hs) hp)
    · cases h

/-- **Every step of follow's machine keeps the provenance over the frame's own bytes**: a `Q` every
re-derived event keeps and that refutes `atGenesis`, and every call the frame's result carries in
`L` (`frameCalls`; `Proofs.FollowHead.step_world`: the step absorbs only `frameEvents` of its
result). -/
theorem step_journalFrom {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {Q : World D → Prop} {L : List ByteArray} {w₀ : World D} {f f' : Follow D} {p : Persist D}
    {kb result : ByteArray} {r : Reply} (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false) (hL : ∀ b ∈ frameCalls result, b ∈ L)
    (h : step X dc B me f kb result = (f', p, r)) (hp : JournalFrom X Q L w₀ f.world) :
    JournalFrom X Q L w₀ f'.world := by
  rcases step_world h with hw | ⟨evs, steps, chain, base, ts, wb, hev, ha⟩ | hg
  · rw [hw]; exact hp
  · obtain ⟨wb', tb, ts', h₁, h₂, -, -, -⟩ := absorbPage_ok ha
    have hE : ∀ e ∈ evs, eventCall e ∈ L := fun e he =>
      hL _ (List.mem_map.mpr ⟨e, hev e he, rfl⟩)
    refine absorb_journalFrom hA _ (fun e he => hE e (List.mem_of_mem_drop he)) h₂
      (absorb_journalFrom hA _ (fun e he => hE e (List.mem_of_mem_take he)) h₁ hp)
  · rw [hG hp.1] at hg; cases hg

end Nanodregg.Protocol.Command
