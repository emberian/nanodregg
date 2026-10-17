/-
# Host.Batch — the loop's whole decision, as one pure function

`admitBatch` takes the World and the batch's requests, in arrival order, and returns the World
after them, the Turns to append (`staged`) and one reply per request. Every request is either
answered from the World (`reply`) or asks for a Turn to be admitted (`admit`); an admitted Turn
advances the World the next request sees, a refused one leaves it unchanged (`admit` is
fail-closed: it returns no World).

The loop appends `staged` as one batch record, fsyncs, and only then sends `replies`.

Generic in the World `W`, Turn `T` and refusal `R`, so the simulation runs the same function the
Host runs; the Host instantiates `admit` with `Kernel.World.admit E`.

Theorems (`Host.Proofs.Batch`): `admitBatch_append` (batch boundaries do not change the state or
the log), `staged_foldlM` (folding the staged Turns from the starting World with `admit` reaches
exactly the World the Host keeps: what the Host logs means what the Host holds), and
`replies_size` (one reply per request, none dropped).
-/
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

/-- What a batch produces besides the World. -/
structure Out (T : Type) where
  staged : Array T := #[]
  replies : Array Reply := #[]
  /-- the replies still to be filled after the sync: (reply index, what) -/
  pages : Array (Nat × Deferred) := #[]

/-- The loop's parameters: the one transition, the request handler, and how a refusal is
answered (a status byte and payload; `replayed` answers with the original receipt). -/
structure Machine (W T R Q : Type) where
  admit : W → T → Except R W
  handle : W → Q → Answer W T
  refuse : W → T → R → UInt8 × ByteArray
  ok : UInt8

variable {W T R Q : Type}

/-- One request. -/
def Machine.step (m : Machine W T R Q) (acc : W × Out T) (q : Request Q) : W × Out T :=
  let (w, out) := acc
  match m.handle w q.body with
  | .reply status payload => (w, { out with replies := out.replies.push ⟨q.conn, status, payload⟩ })
  | .defer d =>
    (w, { out with replies := out.replies.push ⟨q.conn, m.ok, ByteArray.empty⟩,
                   pages := out.pages.push (out.replies.size, d) })
  | .admit t receipt =>
    match m.admit w t with
    | .ok w' => (w', { out with staged := out.staged.push t,
                                replies := out.replies.push ⟨q.conn, m.ok, receipt w'⟩ })
    | .error r =>
      let (status, payload) := m.refuse w t r
      (w, { out with replies := out.replies.push ⟨q.conn, status, payload⟩ })

/-- A batch, in arrival order, from an accumulator. -/
def Machine.run (m : Machine W T R Q) (acc : W × Out T) (qs : List (Request Q)) : W × Out T :=
  qs.foldl m.step acc

/-- A batch from the World as it stands. -/
def Machine.admitBatch (m : Machine W T R Q) (w : W) (qs : List (Request Q)) : W × Out T :=
  m.run (w, {}) qs

end Nanodregg.Host
