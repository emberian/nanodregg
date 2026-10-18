/-
# Host.Proofs.Check — `host check --anchor` passes exactly when the Store reached the anchor
-/
import Host.Check
import Codec.Proofs.World
import Codec.Proofs.Deployed

namespace Nanodregg.Host.Check

/-- No verdict (exit 0) exactly when the Store is at or past the anchor's step count and its chain
there is the anchor's. -/
theorem Anchor.verdict_none_iff (a : Anchor) (now : Nat) (ch : ByteArray) :
    a.verdict now ch = none ↔ a.steps ≤ now ∧ ch = a.chain := by
  unfold Anchor.verdict
  by_cases h : now < a.steps
  · simp only [h, if_true, reduceCtorEq, false_iff, not_and]
    intro h'; omega
  · have hle : a.steps ≤ now := Nat.le_of_not_lt h
    by_cases hc : ch = a.chain
    · simp [h, hc, hle]
    · simp [h, hc]

/-- Below the anchor the verdict is `behindAnchor`, whatever chain was read. -/
theorem Anchor.verdict_behind (a : Anchor) (now : Nat) (ch : ByteArray) (h : now < a.steps) :
    a.verdict now ch = some .behindAnchor := by
  simp [Anchor.verdict, h]

/-- Every verdict is fatal: a Store that fails its anchor is never restarted into service. -/
theorem Anchor.verdict_fatal (a : Anchor) (now : Nat) (ch : ByteArray) (s : Status)
    (h : a.verdict now ch = some s) : s.cls = .fatal := by
  unfold Anchor.verdict at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- **The tooth of `turnsOf`'s empty arm** (HOST-54): the record of no steps, the codec's own bytes
of `[]`, is refused at its position, never read as a record of zero Turns. The open refuses it
`empty` (`Record.step_empty`); `check` reads the records before the base too, which no open folds. -/
theorem turnsOf_empty (i : Nat) (rs : List ByteArray) :
    turnsOf i ((Record.codec Codec.Deployed.digestCodec).bytes [] :: rs) = .error i := by
  unfold turnsOf Record.codec
  rw [(Codec.Kernel.batch_lawfulOn Codec.Deployed.digestCodec_lawful.on recordTurnsMax (by decide)).decode_bytes
    ⟨by simp, by simp⟩]

end Nanodregg.Host.Check
