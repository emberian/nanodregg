/-
# Spec.Sim.Agree — the refusing follower and the batch-and-page run (A1′, `Spec.Proofs.Agree`)

Tooling (closure C9). The trivial system A1′ refuses (`deafFollower`: a follower that takes no page,
answering every frame `done 0` on the World it holds) and the inputs of the deployed run: from
`wGenesis`, the writer admits a batch of one `submit` frame (the founder's rotate, `wCall`), and a
plain `sync` at its log phase is handed the `log` page of exactly what that batch staged, stating
the writer's World as its end and its tip.
-/
import Spec.Sim.Cap

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **The deaf follower**: it absorbs no page; every frame leaves its World as it was. -/
def deafFollower (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with follow := fun _ f _ _ => (f, .steps [], .done 0 .empty .empty) }

/-- The writer's batch: one `submit` frame carrying the founder's rotate. -/
def agQs : List (Host.Request Host.Frame) := [⟨0, ⟨0, Op.submit.code, Xd.callBytes wCall⟩⟩]

/-- What the deployed writer's machine keeps and stages for it, from the genesis World. -/
def agBatch : World Digest × Host.Out (Step Digest × Digest) := (Host.machine Xd).admitBatch wGenesis agQs

/-- The page events of what the batch staged. -/
def agEvents : List ByteArray := agBatch.2.staged.toList.map (Host.Page.stepEvent ∘ Prod.fst)

/-- The writer's `log` reply: the staged events, its World after the batch as the page's end and
its tip, no base. -/
def agPage : ByteArray :=
  let w := agBatch.1
  let f := Text.fit Bounds.frameBytesMax
  match Text.fitList Bounds.frameBytesMax agEvents, f (Text.u64 w.steps), f (Xd.env.bytes w.chain),
      f (Text.u64 w.steps), f (Text.u64 w.height), f (Text.u64 0), f ByteArray.empty, f ByteArray.empty with
  | some l, some n, some c, some t, some th, some b, some bd, some k =>
      ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t, th, b, bd, k, ())
  | _, _, _, _, _, _, _, _ => ByteArray.empty

/-- A plain `sync` at its log phase (2), first page. -/
def agKb : ByteArray :=
  (Command.State.bytes ⟨["sync".toUTF8], 2,
    [Text.u64 0, ByteArray.empty, Text.u64 0, Text.u64 10, Text.u64 0]⟩).getD .empty

/-- Not `init` (the one verb whose phase 2 is custody's). -/
def agNotInit : Command.Cmd Digest → Bool
  | .init _ => false
  | _ => true

def agIsOk : Status → Bool
  | .ok => true
  | _ => false

end Nanodregg.Spec
