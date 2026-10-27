/-
# Kernel.Turn — the one log entry

A `Turn` is deterministic data: everything the follower needs to reproduce the World from the
log with `World.admit` alone, and nothing it would have to trust. It carries

* `touches` — every existing (or pinned-absent) cell the turn names, each ONCE: the digest of
  what the signer saw (`pinOf` of its entry: a live cell with its version, a tombstone, or `none` for
  "this id holds nothing") and
  what the turn does to it (`keep`, `write ops`, `retire`). The pin is the one staleness refusal
  (`Reject.stale`); a turn writes or retires only a cell it observed, so its effect on every cell
  it changes is a function of the observation, and admit looks each cell up exactly once.
* `creates` — cells born by this turn, each with its id (D5, KERNEL-28: one birth shape). The
  receiver computes the id: a ROM cell's is its content digest (a package's identity, and
  `World.admit` checks it: `notContentId`), an account's is keyed by its owner and denomination,
  a member's is `Receive.memberId` (the digest of its join consent), any other's is derived from
  `txId` and the index. A follower re-derives the Turn (`Receive.rederive`), so a
  writer cannot choose an id its receiver did not. A born id is never also touched
  (`Reject.bornTouched`).
* `nullifiers` — one-time tokens; each may be spent once in the life of the World.
* `charge` — what the turn pays, which must equal `Turn.weight` exactly: the storage it costs,
  its log record plus everything it can add to the World (KERNEL-12). The signer signs the price.
* `event` — the ingress bytes (the signed call), opaque to the kernel, kept in the log so the
  log alone is the audit trail. No archive beside it.
* `member` and `ticks` (DESIGN-OBS §1.3) — who signed the call, and the ticks its whole tree of
  runs used. Both are re-derived by every follower from the event (`Receive.rederive`: a page
  carries the call, never the writer's Turn), so a writer cannot state another member or another
  count; the kernel meters `ticks` per member per window (`World.ticksUsed`, `ticksBudget`) as it
  counts refusals, and a receipt of a Turn names its signer as a refusal's names the member charged.
* `causal` (KERNEL-79) — the head the signer's World was at when it planned the call, when the call
  carries one: a position of the log, the third pin kind beside the cell pins and the row and range
  pins. Re-derived from the event like `member`. `World.admit` admits a pinned Turn only on a World
  whose chain at that step is the pin's (`forkedPin`, `pinAhead`, `pinExpired`).
-/
import Kernel.Cell

namespace Nanodregg.Kernel

/-- What a turn does to a cell it observed. -/
inductive Act
  | keep
  | write (ops : List Op)
  | retire
  deriving DecidableEq

/-- One observed cell: its id, the digest the signer saw, and what the turn does to it. -/
structure Touch (D : Type) where
  cell : D
  seen : D
  act : Act
  deriving DecidableEq

/-! ## Rows (KERNEL-46, LANG-44): keyed, bounded rows under an object, the FOURTH instance of the
one trie. These are the signatures LANG writes against; admission arrives with the rows day. -/

/-- A row's key: the parent object, the relation's index under it (`< 256`), and the key bytes
(`≤ Bounds.keyBytesMax`, the relation's fixed width). -/
structure RowKey (D : Type) where
  parent : D
  rel : Nat
  k : ByteArray
  deriving DecidableEq

/-- A key of the rows trie: a relation's head (born by a `declare` act with its parent), or a row. -/
inductive RowSlot (D : Type)
  | head (parent : D) (rel : Nat)
  | row (key : RowKey D)
  deriving DecidableEq

/-- What the rows trie holds: at a head, the relation's row count and `amt` sum (written by the
kernel only, `head_sum`), its row `limit`, its sum `cap` (0: no sum column), the key `width`, and
whether rows may be retracted; at a row, its `amt` (the declared sum column, a kernel field beside
the bytes: the kernel never parses Lang data) and its value bytes.
KERNEL-54: a row carries its version (its relation's floor at its insert, one more per upsert), and a
head its floor (0 at its declare, raised by each retract past the version of the row it removes, by
nothing else while its parent lives, so inserts commute). While the parent lives, a row slot's leaf and
absence-at-floor never recur, so a row or range pin observed once and stale is behind for ever; a
retired parent drops its heads (`dropHeads`, its floor reads 0 again), and its slots are dead: every
row touch and range read under it is refused before a pin is read. -/
inductive RowLeaf
  | head (count sum limit cap width : Nat) (retract : Bool) (floor : Nat)
  | row (amt : Nat) (val : ByteArray) (ver : Nat)
  deriving DecidableEq

/-- What a turn does to a row slot. `insert` is unpinned (it binds on the current World:
`keyTaken`, `relationFull`, `relationCapped`); `upsert` and `retract` pin the row; `declare` births
a head, only in the turn whose `creates` bears the parent, by its create receiver. -/
inductive RowAct
  | keep
  | insert (amt : Nat) (v : ByteArray)
  | upsert (amt : Nat) (v : ByteArray)
  | retract
  | declare (limit cap width : Nat) (retract : Bool)
  deriving DecidableEq

/-- One row slot a turn names: the slot, the row pin the signer saw (`none` for an insert or a
declare), and the act. -/
structure RowTouch (D : Type) where
  slot : RowSlot D
  seen : Option D
  act : RowAct
  deriving DecidableEq

/-- A causal pin (KERNEL-79): a position of the log, its step count and the chain there. A signed
call may carry one, the head its signer planned at; `World.admit` judges it against the World's own
chain (the current one, or the ring of recent heads `World.chainAt` reads). -/
structure CausalPin (D : Type) where
  steps : Nat
  chain : D
  deriving DecidableEq, Repr

/-- A range read (LANG-44 (c), LANG-47; the SECOND pin kind): the rows of relation `rel` under
`parent` whose key starts with `pre`, at most `most` of them, pinned by `seen = rangePin` of their
listing. Admission recomputes the listing (refused `rangeTooLong` past `most`, never truncated)
and refuses `stale` on a different pin: a row landing under a pinned range makes it stale. -/
structure RangeRead (D : Type) where
  parent : D
  rel : Nat
  pre : ByteArray
  most : Nat
  seen : D
  deriving DecidableEq


structure Turn (D : Type) where
  txId : D
  notBefore : Nat
  validUntil : Nat
  touches : List (Touch D)
  creates : List (D × Cell)
  nullifiers : List D
  charge : Nat
  event : ByteArray
  /-- the row slots the turn names (KERNEL-46/48) -/
  rows : List (RowTouch D) := []
  /-- the range reads the turn pins (LANG-44 (c), the second pin kind) -/
  ranges : List (RangeRead D) := []
  /-- the member whose signed call this is (DESIGN-OBS §1.3; re-derived from `event`) -/
  member : D
  /-- the ticks the call's tree of runs used (0 for every Body but an invoke; re-derived) -/
  ticks : Nat := 0
  /-- the signer's causal pin (KERNEL-79; re-derived from the event) -/
  causal : Option (CausalPin D) := none
  deriving DecidableEq

/-- The cells a turn bears, without their ids. -/
def Turn.born {D : Type} (t : Turn D) : List Cell := t.creates.map Prod.snd

/-- Fixed per-field costs, in bytes: a digest (the deployed 32-byte digest), a counter (u64), and
the u32 header of a list or byte string. These are the codec's sizes (`Codec.Kernel`), so a turn's
log weight is its record's byte count. -/
def digestWeight : Nat := 32
def counterWeight : Nat := 8
def headerWeight : Nat := 4

def Act.opsWeight : Act → Nat
  | .write ops => (ops.map Op.weight).sum
  | _ => 0

/-- An act in the log (`Codec.Kernel.act`): a one-byte tag, and a write's op list (its header and
its ops). The header is log bytes only: it is not World growth. -/
def Act.logWeight : Act → Nat
  | .write ops => 1 + headerWeight + (ops.map Op.weight).sum
  | _ => 1

/-- LEB128 in at most `fuel` bytes, by structural recursion on the fuel, so the kernel reduces it
(`decide` over rows keys); `natBytes` gives it fuel `n + 1`, more than it uses. -/
def natBytesFuel : Nat → Nat → ByteArray
  | 0, _ => ByteArray.empty
  | fuel + 1, n =>
      if n < 128 then ⟨#[n.toUInt8]⟩ else ⟨#[(n % 128 + 128).toUInt8]⟩ ++ natBytesFuel fuel (n / 128)

/-- A number in the rows encoding (a relation, a key's length, a width, a prefix's length): LEB128,
shortest form, for EVERY `Nat` (`Codec.Stream.varint`'s bytes, which never truncate:
`Kernel.Proofs.Bytes.natBytes_eq`). Prefix-free over all of `Nat` (`natBytes_append_inj`), so the
rows keys and the range pin are injective by construction, with no bound (cv 01a14f7e: one byte
wrapped relation 0 and 256 together). One byte below 128, two below 2^14. -/
def natBytes (n : Nat) : ByteArray := natBytesFuel (n + 1) n

/-- A rows slot in the log, exactly `rowKeyBytes`: the parent, the relation (`natBytes`), the kind
byte, and a row's length (`natBytes`) and key (CODEC-9, cv 01a14f7e). -/
def RowSlot.weight {D : Type} : RowSlot D → Nat
  | .head _ rel => digestWeight + (natBytes rel).size + 1
  | .row key => digestWeight + (natBytes key.rel).size + 1 + (natBytes key.k.size).size + key.k.size

/-- A row act in the log: a tag byte; insert and upsert their amt (u64) and value (u32 length);
declare its limit, cap and width (u64 each) and the retract flag. -/
def RowAct.logWeight : RowAct → Nat
  | .insert _ v | .upsert _ v => 1 + counterWeight + headerWeight + v.size
  | .declare .. => 1 + 3 * counterWeight + 1
  | _ => 1

/-- A row touch in the log: the slot, the optional pin (a tag byte, then the digest), the act. -/
def RowTouch.weight {D : Type} (x : RowTouch D) : Nat :=
  x.slot.weight + (if x.seen.isSome then 1 + digestWeight else 1) + x.act.logWeight

/-- A range read in the log: parent, relation byte, the prefix (a length byte and its bytes), most
(u64), the pin. -/
def RangeRead.weight {D : Type} (q : RangeRead D) : Nat :=
  2 * digestWeight + 2 + counterWeight + q.pre.size

/-- What a rows leaf holds in the World beyond its key (`Kernel.rowEntryWeight`): a head its kind
byte, five counters, the retract flag and its floor; a row its kind byte, its amt, its version and its
length-prefixed value. -/
def RowLeaf.weight : RowLeaf → Nat
  | .head .. => 1 + 5 * counterWeight + 1 + counterWeight
  | .row _ v _ => 1 + 2 * counterWeight + headerWeight + v.size

/-- The most a row touch adds to the World (KERNEL-46 amendment 5): a declare its head, an insert or
an upsert its whole row with its key. An upsert of a row that exists, and a retract, give back the
row they replace or remove (`Kernel.rowFreed`), as a touch gives back what a cell does not grow. -/
def RowTouch.growth {D : Type} (x : RowTouch D) : Nat :=
  match x.act with
  | .declare l c w r => x.slot.weight + (RowLeaf.head 0 0 l c w r 0).weight
  | .insert a v | .upsert a v => x.slot.weight + (RowLeaf.row a v 0).weight
  | _ => 0

/-- A touch in the log: id, seen digest and the act. -/
def Touch.weight {D : Type} (x : Touch D) : Nat := 2 * digestWeight + x.act.logWeight

/-- What a turn's log record costs, field by field in the codec's order (`Codec.Kernel.turn`):
txId, the window, the touches, the born cells with their ids, the nullifiers (each list with its
header), the charge and the event (with its length), the rows, the ranges, the member, the
ticks and the causal pin (a tag byte, then the step count and the chain). At the deployed digest this is the record's byte count: CODEC proves
`(Codec.Kernel.turn dc).size t = t.logWeight`. -/
def Turn.logWeight {D : Type} (t : Turn D) : Nat :=
  digestWeight + 2 * counterWeight
    + headerWeight + (t.touches.map Touch.weight).sum
    + headerWeight + (t.creates.map fun p => digestWeight + p.2.weight).sum
    + headerWeight + digestWeight * t.nullifiers.length
    + counterWeight
    + headerWeight + t.event.size
    + headerWeight + (t.rows.map RowTouch.weight).sum
    + headerWeight + (t.ranges.map RangeRead.weight).sum
    + digestWeight + counterWeight
    + (if t.causal.isSome then 1 + counterWeight + digestWeight else 1)

/-- The most a turn can add to the World (`Kernel.Proofs.Weight.admit_world_weight`): each born
cell with its id, each write's ops, each spent nullifier, each row touch's growth (KERNEL-46
amendment 5). A retirement and an overwrite only shrink or keep a cell; an upsert of an existing
row and a retract are credited back. Its journal entry is not growth: the journal is pruned to the
window (KERNEL-33), a bounded overhead of every World. -/
def Turn.growth {D : Type} (t : Turn D) : Nat :=
  (t.creates.map fun p => digestWeight + counterWeight + p.2.weight).sum
    + (t.touches.map fun x => x.act.opsWeight).sum
    + digestWeight * t.nullifiers.length
    + (t.rows.map RowTouch.growth).sum

/-- The exact charge of a turn: the storage it costs, its log record plus its World growth.
Independent of the charge's value, so a turn can state its own price. -/
def Turn.weight {D : Type} (t : Turn D) : Nat := t.logWeight + t.growth


end Nanodregg.Kernel
