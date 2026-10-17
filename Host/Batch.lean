/-
# Host.Batch — the loop's whole decision, as one pure function

`admitBatch` takes the World and the batch's requests, in arrival order, and returns the World
after them, the Turns to append (`staged`) and one reply per request. Every request is either
answered from the World (`reply`) or asks for a Turn to be admitted (`admit`); an admitted Turn
advances the World the next request sees, a refused one leaves it unchanged (`admit` is
fail-closed: it returns no World).

The loop appends `staged` as one batch record, fsyncs, and only then sends `replies`.

Generic in the World `W`, Turn `T`, refusal `R` and note `N`, so the simulation runs the same
function the Host runs; the Host instantiates `admit` with `Kernel.World.admit E` and `note` with
`Kernel.World.roots E` (the cells' and the journal's roots). Each staged Turn is paired with the note of the World right after it (HOST-29:
a batch record states each Turn's roots, so a page reader advances the chain without admitting).

Theorems (`Host.Proofs.Batch`): `admitBatch_append` (batch boundaries do not change the state or
the log), `staged_rooted` (the staged pairs are a `Kernel.Rooted` run from the starting World to
exactly the World the Host keeps: every Turn admits and every note is the one admission reached;
what the Host logs means what the Host holds), and `replies_size` (one reply per request, none
dropped).
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
  /-- admit this Turn; on success the reply is built from the World after it -/
  | admit (turn : T) (receipt : W → ByteArray)
  /-- answered from the durable state after the batch's sync (so it holds only durable records,
  the batch's own included) -/
  | defer (d : Deferred)

/-- One request of a batch. -/
structure Request (Q : Type) where
  conn : UInt32
  body : Q

/-- What a batch produces besides the World: `staged` holds each admitted Turn with its note. -/
structure Out (S : Type) where
  staged : Array S := #[]
  replies : Array Reply := #[]
  /-- the replies still to be filled after the sync: (reply index, what) -/
  pages : Array (Nat × Deferred) := #[]

/-- The loop's parameters: the one transition, the note a staged Turn carries (the World's root
after it), the request handler, and how a refusal is answered (a status byte and payload;
`replayed` answers with the original receipt). -/
structure Machine (W T R Q N : Type) where
  admit : W → T → Except R W
  note : W → N
  handle : W → Q → Answer W T
  refuse : W → T → R → UInt8 × ByteArray
  ok : UInt8

variable {W T R Q N : Type}

/-- One request. -/
def Machine.step (m : Machine W T R Q N) (acc : W × Out (T × N)) (q : Request Q) : W × Out (T × N) :=
  let (w, out) := acc
  match m.handle w q.body with
  | .reply status payload => (w, { out with replies := out.replies.push ⟨q.conn, status, payload⟩ })
  | .defer d =>
    (w, { out with replies := out.replies.push ⟨q.conn, m.ok, ByteArray.empty⟩,
                   pages := out.pages.push (out.replies.size, d) })
  | .admit t receipt =>
    match m.admit w t with
    | .ok w' => (w', { out with staged := out.staged.push (t, m.note w'),
                                replies := out.replies.push ⟨q.conn, m.ok, receipt w'⟩ })
    | .error r =>
      let (status, payload) := m.refuse w t r
      (w, { out with replies := out.replies.push ⟨q.conn, status, payload⟩ })

/-- A batch, in arrival order, from an accumulator. -/
def Machine.run (m : Machine W T R Q N) (acc : W × Out (T × N)) (qs : List (Request Q)) : W × Out (T × N) :=
  qs.foldl m.step acc

/-- A batch from the World as it stands. -/
def Machine.admitBatch (m : Machine W T R Q N) (w : W) (qs : List (Request Q)) : W × Out (T × N) :=
  m.run (w, {}) qs

end Nanodregg.Host
