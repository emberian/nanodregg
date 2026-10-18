/-
# Protocol.Proofs.Page — the base a log page states is the one the writer passed (PROTOCOL-47)

`Host.Page.bytes` writes the writer's newest durable base (`Host.Deployed.pager` passes
`r.sealed.steps` and `r.sealed.digest`, the Resident's `Sealed`, read off the pager: no theorem, the
pager is IO; the rows' writer the same) after the tip. A page written in range is read
(`bytes_reads`), and the follower's one reader (`Command.logPage`) reads back exactly those two values
(`bytes_states_base`), and only at or below the stated tip (`Command.logPage_base_le`). That an
honest writer's `Sealed.steps` is at most its World's is not proved here (a Host invariant): if it
failed, every page would be refused `badResult`, never misread.
-/
import Host.Page
import Protocol.Command.Machine
import Protocol.Proofs.Wire
import Protocol.Proofs.Frames
import Codec.Proofs.Stream

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec

theorem ofU64_u64 {n : Nat} (h : n < 2 ^ 64) : Text.ofU64 (Text.u64 n) = some n := by
  unfold Text.ofU64 Text.u64
  rw [Stream.decode_bytes Stream.u64_lawful]
  simp [UInt64.toNat_ofNat_of_lt' h]

/-- **A page states the base its writer passed**: whatever page `Host.Page.bytes` writes for the
base `(bs, bd)`, the follower's reader returns `bs` and `bd` as the page's base. -/
theorem bytes_states_base {a : Host.Page.Acc} {ts th bs : Nat} {bd b : ByteArray} {p : LogPage}
    (h : Host.Page.bytes a ts th bs bd = .ok b) (hbs : bs < 2 ^ 64) (hp : logPage b = some p) :
    p.baseSteps = bs ∧ p.baseDigest = bd := by
  unfold Host.Page.bytes at h
  dsimp only at h
  split at h
  · rename_i hl hh hc ht hth hb hd
    simp only [Except.ok.injEq] at h
    subst h
    unfold logPage at hp
    rw [Stream.decode_bytes logReplyFrame_lawful] at hp
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
    obtain ⟨_, -, _, -, _, -, x, hx, hp⟩ := hp
    rw [fit_val hb, ofU64_u64 hbs] at hx
    cases hx
    split at hp
    · cases hp
      exact ⟨rfl, fit_val hd⟩
    · cases hp
  · cases h

/-- **A page the Host writes in range is read**, with the step count, tip and base it was written
with: for in-range values whose page end and base are at or below its tip (the writer's own
`Sealed` and World: an honest pager), `logPage` reads it, so `bytes_states_base` is about pages
that exist. -/
theorem bytes_reads {a : Host.Page.Acc} {ts th bs : Nat} {bd b : ByteArray}
    (h : Host.Page.bytes a ts th bs bd = .ok b) (hs : a.steps < 2 ^ 64) (hts : ts < 2 ^ 64)
    (hth : th < 2 ^ 64) (hbs : bs < 2 ^ 64) (hle : a.steps ≤ ts) (hb : bs ≤ ts) :
    ∃ p, logPage b = some p ∧ p.steps = a.steps ∧ p.tipSteps = ts ∧ p.baseSteps = bs ∧
      p.baseDigest = bd := by
  unfold Host.Page.bytes at h
  dsimp only at h
  split at h
  · rename_i hl hh hc ht hth' hb' hd
    simp only [Except.ok.injEq] at h
    subst h
    unfold logPage
    rw [Stream.decode_bytes logReplyFrame_lawful]
    simp only [fit_val hh, fit_val ht, fit_val hth', fit_val hb', fit_val hd, ofU64_u64 hs,
      ofU64_u64 hts, ofU64_u64 hth, ofU64_u64 hbs, Option.bind_eq_bind, Option.bind_some, hle, hb,
      and_self, if_true]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

end Nanodregg.Protocol.Command
