/-
# Spec.Sim.Receipt — the inputs of §7's receipt clause: the check that believes the receipt (tooling, C9)
-/
import Spec.Sim.Foreign

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **The believing check**: it compares the receipt's transaction id and roots with the head's, then
answers what the receipt states, verifying no path (the rows harness's `trustReceipt` reading). -/
def receiptBelieve (_height : Nat) (roots txId : Digest) (_notBefore : Nat) (r : Receipt.Receipt Digest) :
    Except Receipt.Refusal (Receipt.Answer Digest) :=
  if r.txId ≠ txId then .error .otherTx
  else if rootsDigest Xd.env r.root r.jroot r.rroot r.rowsroot ≠ roots then .error .headMismatch
  else .ok r.answer

/-- **The believing system**: the deployed system whose receipt check is `receiptBelieve`. -/
def receiptBeliever (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with receiptCheck := receiptBelieve }

/-- A receipt at `w`'s roots, with its paths for `t`, stating the answer `a` (whatever `w` holds). -/
def receiptStating (w : World Digest) (t : Digest) (a : Receipt.Answer Digest) : Receipt.Receipt Digest :=
  { txId := t, root := w.root Xd.env, jroot := w.journalRoot Xd.env, rroot := w.refusalsRoot Xd.env,
    rowsroot := w.rowsRoot Xd.env, answer := a,
    jpath := w.journal.prove (journalSpec Xd.env) t,
    rpath := w.refusals.prove (refusalSpec Xd.env) (.refusal (.tx t)) }

/-- The floor's receipt: the genesis World's roots, stating the run's call committed at height 1,
which the genesis World does not journal. -/
def receiptForged : Receipt.Receipt Digest := receiptStating wGenesis wTx (.committed 1 oneDigest)

/-- `k` of the World a run reaches, `false` if the run refuses. -/
def receiptOkThen {ε : Type} (r : Except ε (World Digest)) (k : World Digest → Bool) : Bool :=
  match r with
  | .ok w => k w
  | .error _ => false

/-- Whether a check answered `committed`. -/
def receiptCommittedB : Except Receipt.Refusal (Receipt.Answer Digest) → Bool
  | .ok (.committed _ _) => true
  | _ => false

end Nanodregg.Spec
