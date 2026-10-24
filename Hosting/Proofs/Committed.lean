/-
# Hosting.Proofs.Committed — the journal entry at a call's id was put by committing that call

Follow's World moves only by its own frames (`Socket.Reach`), and each frame keeps
`Protocol.Command.JournalFrom` (`step_journalFrom`): every journal entry is the start World's or
the commit of a call follow decoded from a logged event and re-derived. This module turns that into
what a caller holding ONE call needs:

- `reach_journalFrom`: across any number of frames, from a start World that satisfies `Q` (kept by
  every re-derived event, refuting `atGenesis`) with canonical journal and rows.
- `journal_committed`: if follow's World journals `(h, d)` at `txIdOf X c` for a call `c` whose
  canonical bytes read back as itself, then the start World held that entry, or `c` itself was
  received at a `Q` World `v` with canonical rows and admitted there, the entry being
  `(v.height + 1, turnDigest)` of its Turn, or some other byte string `b`, decoding to a call
  received and admitted at a `Q` World, has `c`'s id: `X.env.hash domTx b = txIdOf X c` with
  `b ≠ X.callBytes c`. That last disjunct is a SECOND PREIMAGE of `c`'s id, `c` fixed by the
  premises; not a collision the statement may choose.

What is not claimed: that the start World lacked the entry (a base carries its own journal; follow's
planning World does not journal the signed call's id, but nothing here proves it), nor that `v` lies
on the particular path follow took (it satisfies `Q` and has canonical rows; `Reach` is a relation,
not a trace).
-/
import Hosting.Proofs.Socket
import Protocol.Proofs.FollowJournal

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Follow's frames keep the journal's provenance.** -/
theorem reach_journalFrom {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {Q : World D → Prop} {w₀ : World D}
    (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false) {w₁ w₂ : World D}
    (h : Reach X dc B me w₁ w₂) (hp : JournalFrom X Q w₀ w₁) : JournalFrom X Q w₀ w₂ := by
  induction h with
  | refl => exact hp
  | tail _ hm ih =>
    obtain ⟨f, f', kb, res, p, r, rfl, hs, rfl⟩ := hm
    exact step_journalFrom hA hG hs ih

/-- **The entry at a call's id is that call's commit** (or the start World's, or a second preimage
of the call's id). -/
theorem journal_committed {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {Q : World D → Prop} (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false) {w₀ w : World D} (hr : Reach X dc B me w₀ w)
    (hq : Q w₀) (hjc : w₀.JournalCanon X.env) (hrc : w₀.RowsCanon X.env)
    {c : Call D} (hc : X.decodeCall (X.callBytes c) = some c) {e : Nat × D}
    (hj : w.journalAt X.env (txIdOf X c) = some e) :
    w₀.journalAt X.env (txIdOf X c) = some e ∨
      (∃ (v v' : World D) (t : Turn D), Q v ∧ v.RowsCanon X.env ∧ receive X v c = .ok t ∧
        World.admit X.env v t = .ok v' ∧ e = (v.height + 1, turnDigest X.env t)) ∨
      ∃ (v v' : World D) (b : ByteArray) (c' : Call D) (t : Turn D), Q v ∧
        X.decodeCall b = some c' ∧ receive X v c' = .ok t ∧ World.admit X.env v t = .ok v' ∧
        b ≠ X.callBytes c ∧ X.env.hash domTx b = txIdOf X c := by
  obtain ⟨-, -, -, he⟩ := reach_journalFrom hA hG hr (journalFrom_refl hq hjc hrc)
  rcases he _ _ hj with h0 | ⟨v, v', b, c', t, hqv, hrv, hb, hrcv, ha, hk, rfl⟩
  · exact .inl h0
  have hcb := hX _ _ hb
  by_cases hbc : b = X.callBytes c
  · rw [hbc, hc] at hb
    cases hb
    exact .inr (.inl ⟨v, v', t, hqv, hrv, hrcv, ha, rfl⟩)
  · refine .inr (.inr ⟨v, v', b, c', t, hqv, hb, hrcv, ha, hbc, ?_⟩)
    rw [← hk]; unfold txIdOf; rw [hcb]

end Nanodregg.Hosting.Proofs.Socket
