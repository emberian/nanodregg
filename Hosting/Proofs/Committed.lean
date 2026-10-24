/-
# Hosting.Proofs.Committed — a journal entry a run of frames added was put by committing that call

Follow's World moves only by its own frames, and `ReachOn S` names them by their results `S`
(`Socket.ReachOn`). Each frame keeps `Protocol.Command.JournalFrom` over the call bytes its result
carries (`step_journalFrom`, `frameCalls`): every journal entry is the start World's or the commit of
a call follow decoded from bytes one of those frames handed it, and re-derived. This module turns
that into what a caller holding ONE call needs:

- `pathCalls S` (`Protocol.Command.Frames`): every call byte string the frames' results `S` carry,
  in order. A function of `S`, so of the theorem's own premise: follow's own path, not every byte
  string some World would admit.
- `reachOn_journalFrom`: across the frames `S`, from a start World that satisfies `Q` (kept by every
  re-derived event, refuting `atGenesis`) with canonical journal and rows, over `pathCalls S`.
- `journal_committed`: if the frames `S` took follow's World from `w₀`, which held NO entry at
  `txIdOf X c`, to one that journals `e` there, for a call `c` whose canonical bytes read back as
  itself, then `c`'s own bytes are among `pathCalls S` and `c` was received at a `Q` World `v` with
  canonical rows and admitted there, the entry being `(v.height + 1, turnDigest)` of its Turn; or two
  different inputs among `c`'s bytes and `pathCalls S` share one `domTx` digest
  (`CollidesAmong`, over an explicit list the premises fix: a collision someone must have FOUND and
  handed follow, never one that merely exists among unbounded inputs).

HOSTING-47: the form this replaces ended in "some byte string, decoding to a call admitted at SOME
`Q` World, has `c`'s id": an existential over an unbounded set, which a 32-byte hash satisfies by
counting (the 10-20 vacuity), and it began with "or `w₀` held the entry", its own premise when
`w₀ = w`. The freshness premise and the path list remove both.

What is not claimed: that `v` is a World on the path (it satisfies `Q` and has canonical rows; the
call's bytes are on the path).
-/
import Hosting.Proofs.Socket
import Protocol.Proofs.FollowJournal

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Follow's frames keep the journal's provenance over the calls they carried.** -/
theorem reachOn_journalFrom {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {Q : World D → Prop} {L : List ByteArray} {w₀ : World D}
    (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false) {S : List ByteArray} {w₁ w₂ : World D}
    (h : ReachOn X dc B me S w₁ w₂) (hL : ∀ b ∈ pathCalls S, b ∈ L) (hp : JournalFrom X Q L w₀ w₁) :
    JournalFrom X Q L w₀ w₂ := by
  induction h with
  | refl => exact hp
  | @tail S res _ _ _ _ hm ih =>
    obtain ⟨f, f', kb, p, r, rfl, hs, rfl⟩ := hm
    have hS : ∀ b ∈ pathCalls S, b ∈ L := fun b hb =>
      hL b (by simp only [pathCalls, List.flatMap_append, List.mem_append] at hb ⊢; exact .inl hb)
    have hr : ∀ b ∈ frameCalls res, b ∈ L := fun b hb =>
      hL b (by simp only [pathCalls, List.flatMap_append, List.mem_append]; exact .inr (by simpa using hb))
    exact step_journalFrom hA hG hr hs (ih hS hp)

/-- **The entry a run of frames added at a call's id is that call's commit**, the call's bytes among
the frames' calls, or two of those inputs collide. -/
theorem journal_committed {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {Q : World D → Prop} (hA : ∀ {w w' e s}, Q w → absorbStep X w e = .ok (s, w') → Q w')
    (hG : ∀ {w}, Q w → atGenesis w = false) {S : List ByteArray} {w₀ w : World D}
    (hr : ReachOn X dc B me S w₀ w) (hq : Q w₀) (hjc : w₀.JournalCanon X.env) (hrc : w₀.RowsCanon X.env)
    {c : Call D} (hc : X.decodeCall (X.callBytes c) = some c)
    (hfresh : w₀.journalAt X.env (txIdOf X c) = none) {e : Nat × D}
    (hj : w.journalAt X.env (txIdOf X c) = some e) :
    (X.callBytes c ∈ pathCalls S ∧ ∃ (v v' : World D) (t : Turn D), Q v ∧ v.RowsCanon X.env ∧
        receive X v c = .ok t ∧ World.admit X.env v t = .ok v' ∧ e = (v.height + 1, turnDigest X.env t)) ∨
      CollidesAmong X.env.hash ((X.callBytes c :: pathCalls S).map (domTx, ·)) := by
  obtain ⟨-, -, -, he⟩ := reachOn_journalFrom hA hG hr (fun b hb => hb)
    (journalFrom_refl (L := pathCalls S) hq hjc hrc)
  rcases he _ _ hj with h0 | ⟨v, v', b, c', t, hqv, hrv, hbS, hb, hrcv, ha, hk, rfl⟩
  · rw [hfresh] at h0; cases h0
  have hcb := hX _ _ hb
  by_cases hbc : b = X.callBytes c
  · rw [hbc, hc] at hb
    cases hb
    exact .inl ⟨hbc ▸ hbS, v, v', t, hqv, hrv, hrcv, ha, rfl⟩
  · refine .inr ⟨(domTx, b), List.mem_map.mpr ⟨b, List.mem_cons_of_mem _ hbS, rfl⟩,
      (domTx, X.callBytes c), List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩,
      fun h => hbc (Prod.mk.inj h).2, ?_⟩
    show X.env.hash domTx b = X.env.hash domTx (X.callBytes c)
    rw [← hcb]; exact hk

end Nanodregg.Hosting.Proofs.Socket
