/-
# Host.Batch — the loop's whole decision, as one pure function

`admitBatch` takes the World and the batch's requests, in arrival order, and returns the World
after them, the steps to append (`staged`) and one reply per request. Every request is either
answered from the World (`reply`), deferred past the sync (`defer`), or commits a step the handler
has already taken (`commit`: the step and the World after it, from `Kernel.Receive.judge`, which
admits a Turn or records a refusal, KERNEL-44); a committed step advances the World the next request
sees, every other answer leaves it unchanged.

The loop appends `staged` as one batch record, fsyncs, and only then sends `replies`.

Generic in the World `W`, step `T`, request `Q` and note `N`, so the simulation runs the same
function the Host runs; the Host instantiates `T` with `Kernel.Step D` and `note` with
`Kernel.World.roots E` (one digest of the cells', journal's and refusals' roots). Each staged step is
paired with the note of the World right after it (HOST-29: a batch record states each step's roots,
so a page reader advances the chain without taking any step).

Theorems (`Host.Proofs.Batch`): `run_append` (batch boundaries do not change the state or
the log), `staged_rooted` (for a transition every committed step satisfies, the staged pairs are a
`Kernel.Rooted` run from the starting World to exactly the World the Host keeps: what the Host logs
means what the Host holds), and `replies_size` (one reply per request, none dropped).
-/
import Kernel.World

namespace Nanodregg.Host

/-- A reply on the wire: the connection it goes back to, a status byte, the payload. -/
structure Reply where
  conn : UInt32
  status : UInt8
  payload : ByteArray

/-- A reply built after the batch's sync, from the durable state. -/
inductive Deferred where
  /-- a page of the durable log after height `start` (`Host.Page.build`) -/
  | log (start : Nat)
  /-- a page of the newest base's World bytes from byte `start` (`Host.Page.basePage`, HOST-15) -/
  | read (start : Nat)

/-- What a request asks of the loop. -/
inductive Answer (W T : Type) where
  /-- answered from the World as it stands -/
  | reply (status : UInt8) (payload : ByteArray)
  /-- commit this step, already taken: `w'` is the World after it, and the reply is
  `(status, payload)` -/
  | commit (step : T) (w' : W) (status : UInt8) (payload : ByteArray)
  /-- answered from the durable state after the batch's sync (so it holds only durable records,
  the batch's own included) -/
  | defer (d : Deferred)

/-- One request of a batch. -/
structure Request (Q : Type) where
  conn : UInt32
  body : Q

/-- What a batch produces besides the World: `staged` holds each committed step with its note. -/
structure Out (S : Type) where
  staged : Array S := #[]
  replies : Array Reply := #[]
  /-- the replies still to be filled after the sync: (reply index, what) -/
  pages : Array (Nat × Deferred) := #[]

/-- The loop's parameters: the note a staged step carries (the World's roots after it), the request
handler (which takes every step it commits: `Host.Proofs.Batch.staged_rooted` names the transition
it must agree with), and the status of a deferred reply. -/
structure Machine (W T Q N : Type) where
  note : W → N
  handle : W → Q → Answer W T
  ok : UInt8

variable {W T Q N : Type}

/-- One request. -/
def Machine.step (m : Machine W T Q N) (acc : W × Out (T × N)) (q : Request Q) : W × Out (T × N) :=
  let (w, out) := acc
  match m.handle w q.body with
  | .reply status payload => (w, { out with replies := out.replies.push ⟨q.conn, status, payload⟩ })
  | .defer d =>
    (w, { out with replies := out.replies.push ⟨q.conn, m.ok, ByteArray.empty⟩,
                   pages := out.pages.push (out.replies.size, d) })
  | .commit t w' status payload =>
    (w', { out with staged := out.staged.push (t, m.note w'),
                    replies := out.replies.push ⟨q.conn, status, payload⟩ })

/-- A batch, in arrival order, from an accumulator. -/
def Machine.run (m : Machine W T Q N) (acc : W × Out (T × N)) (qs : List (Request Q)) : W × Out (T × N) :=
  qs.foldl m.step acc

/-- A batch from the World as it stands. -/
def Machine.admitBatch (m : Machine W T Q N) (w : W) (qs : List (Request Q)) : W × Out (T × N) :=
  m.run (w, {}) qs

end Nanodregg.Host
