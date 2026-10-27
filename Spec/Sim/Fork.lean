/-
# Spec.Sim.Fork — the post-blind follower and the joining run (A2′, `Spec.Proofs.Fork`)

Tooling (closure C9: no deployed module imports it). The trivial system A2′ refuses (`postBlind`: the
deployed follower with its `forkedPost` verdict dropped) and the inputs of the deployed run that
reaches A2′'s refusal: from `wGenesis`, fork B is the founder's rotate (`wLog`), fork A a page that
installs `Std.head` and creates a head object seeded with fork B's head at step 1.
-/
import Spec.Sim.Run
import Protocol.Head

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The trivial system: the follower blind to posts -/

/-- What `Command.refused (.forkedPost s m)` prints, for every `s` and `m` (the name drops them). -/
def forkedPostErr : ByteArray := "refused forkedPost\n".toUTF8

/-- A reply with a `forkedPost` end replaced by an `ok` end; every other reply as it is. -/
def unforked : Command.Reply → Command.Reply
  | .done e o err => if err = forkedPostErr then .done CommandExit.ok.code.toUInt8 o .empty else .done e o err
  | r => r

/-- **The post-blind follower**: the deployed command machine, absorbing every page as it does,
except that a page carrying a self-head post at a position its own fold passed with another chain
ends `ok` (the comparison's verdict dropped: what a follower that absorbs any post answers). No
step arm is copied. -/
def postBlind (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun me f kb res =>
      let x := (deployed d).follow me f kb res
      (x.1, x.2.1, unforked x.2.2) }

/-! ## The joining run

From the genesis World `wGenesis`, fork B is the founder's `rotate` (`wLog`, to `kB`, one step).
Fork A, the page follow absorbs from genesis: the founder installs `Std.head` (`kInstall`) and
creates a head object of this World seeded with fork B's head (`kCreate`: a seed is a post,
PROTOCOL-75), two steps. Follow's own fold passes step 1 with the install's chain, not the
rotate's. -/

def kInstall : Call Digest := fCall wGenesis [] (.install Foreign.headPackageBytes)
def kW1 : World Digest := (staged wGenesis kInstall).1
def kHead : Digest := Foreign.headPackageId Xd.env

/-- Fork B's World: the founder's rotate. -/
def kB : World Digest := match World.fold Xd.env wGenesis wLog with | .ok w => w | .error _ => wGenesis

/-- Fork B's head, as `sync --post` writes it (`Head.headText`'s record), in a seed of this World. -/
def kText : String :=
  s!"(record (head (at (record (chain #{Text.toHex (Xd.env.bytes kB.chain)}) (height {kB.height}) (roots #{Text.toHex (Xd.env.bytes (kB.roots Xd.env))}) (steps {kB.steps})))) (world #{Text.toHex (Xd.env.bytes wGenesis.origin)}))"

def kSeed : Slots := (Lang.seedOf Xd.digestOf (Command.worldLook Xd.env kW1) kHead kText).toOption.getD []
def kCreate : Call Digest := fCall kW1 [kHead] (.create (some kHead) [] kSeed)
def kW2 : World Digest := (staged kW1 kCreate).1

def kEvents : List ByteArray :=
  [eventBytes (.turn (Xd.callBytes kInstall)), eventBytes (.turn (Xd.callBytes kCreate))]

/-- The writer's `log` reply: the two events, its tip at their end, no base. -/
def kPage : ByteArray :=
  let f := Text.fit Bounds.frameBytesMax
  match Text.fitList Bounds.frameBytesMax kEvents, f (Text.u64 kW2.steps), f (Xd.env.bytes kW2.chain),
      f (Text.u64 kW2.steps), f (Text.u64 kW2.height), f (Text.u64 0), f ByteArray.empty, f ByteArray.empty with
  | some l, some n, some c, some t, some th, some b, some bd, some k =>
      ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t, th, b, bd, k, ())
  | _, _, _, _, _, _, _, _ => ByteArray.empty

/-- A plain `sync` at its log phase (2), first page. -/
def kKb : ByteArray :=
  (Command.State.bytes ⟨["sync".toUTF8], 2,
    [Text.u64 0, ByteArray.empty, Text.u64 0, Text.u64 10, Text.u64 0]⟩).getD .empty

/-- The steps a frame persists, if it persists steps. -/
def stepsOf : Command.Persist Digest → Option (List (Step Digest × Digest))
  | .steps ts => some ts
  | .adopt _ => none

/-- `Command.refused (.forkedPost _ _)`'s bytes, as a computation. -/
def forkedPostDone : Command.Reply → Bool
  | .done e o err => decide (e = CommandExit.refused.code.toUInt8) && decide (o = .empty) &&
      decide (err = forkedPostErr)
  | _ => false

/-! ## The `sync --to` arm -/

/-- A continuation whose argv parses as `sync --to STEPS:CHAIN` read as a plain `sync`; every other
continuation as it is. -/
def dropAnchor (kb : ByteArray) : ByteArray :=
  match Command.State.ofBytes kb with
  | some st =>
      match Command.parse Xd.digestOf st.argv with
      | .ok (.sync (.to _ _)) => (Command.State.bytes { st with argv := ["sync".toUTF8] }).getD kb
      | _ => kb
  | none => kb

/-- **The anchor-blind follower**: the deployed command machine, reading every `sync --to` as
`sync` (it catches up to the writer's tip without walking the page against the stated head). -/
def syncBlind (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with follow := fun me f kb res => (deployed d).follow me f (dropAnchor kb) res }

/-- The anchor a parsed command states, if it is `sync --to`. -/
def toAnchor : Except Command.ParseRefusal (Command.Cmd Digest) → Option (Nat × ByteArray)
  | .ok (.sync (.to s c)) => some (s, c)
  | _ => none

/-- `sync --to STEPS:CHAIN` at its log phase (2), first page. -/
def kToKbOf (w : World Digest) : ByteArray :=
  (Command.State.bytes ⟨["sync".toUTF8, "--to".toUTF8,
      s!"{w.steps}:{Text.toHex (Xd.env.bytes w.chain)}".toUTF8], 2,
    [Text.u64 0, ByteArray.empty, Text.u64 0, Text.u64 10, Text.u64 0]⟩).getD .empty

/-- Told fork B's head (the founder's rotate at step 1). -/
def kToKb : ByteArray := kToKbOf kB

/-- Fork A's first step (the install) and its World: fork A's own head at step 1. -/
def kLogA : List (Step Digest) := (staged wGenesis kInstall).2
def kToKbA : ByteArray := kToKbOf kW1

/-- A `sync --to` frame from `⟨g⟩`: `lg` folds from `g` to `wg`; the continuation states `wg`'s head;
the frame persists steps and moves follow from `g` to `wg`'s step count or past it, `wg` one step
past `g`. -/
def syncRunOk (S : System Digest) (me : Command.Self Digest) (g : World Digest) (kb res : ByteArray)
    (lg : List (Step Digest)) : Bool :=
  match World.fold Xd.env g lg with
  | .ok wg =>
      (match Command.State.ofBytes kb with
       | some st => decide (toAnchor (Command.parse Xd.digestOf st.argv) = some (wg.steps, Xd.env.bytes wg.chain))
       | none => false) &&
        (match S.follow me ⟨g, none, none⟩ kb res with
         | (f', p, _) => (stepsOf p).isSome && decide (wg.steps = g.steps + 1) && decide (wg.steps ≤ f'.world.steps))
  | .error _ => false

/-- The frame's first persisted step is not `lg`, and no input of the two one-step folds collides. -/
def syncRunJoins (S : System Digest) (me : Command.Self Digest) (g : World Digest) (kb res : ByteArray)
    (lg : List (Step Digest)) : Bool :=
  match S.follow me ⟨g, none, none⟩ kb res with
  | (_, p, _) =>
      let ts := (stepsOf p).getD []
      decide ((ts.take 1).map Prod.fst ≠ lg) &&
        collisionFree Xd.env.hash (foldPres Xd.env g ((ts.take 1).map Prod.fst) ++ foldPres Xd.env g lg)

end Nanodregg.Spec
