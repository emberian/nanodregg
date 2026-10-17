/-
# Kernel.Sim — the seeded simulation's TOY parameters (the generator is `Kernel.Sim.Gen`)

`lake exe sim --seeds N` runs N seeded scenarios. Each drives the REAL receive path
(`Receive.receive` then `World.admit`) with honest and adversarial calls, checks every verdict
against the one the generator built the call to get (by refusal NAME), restarts the "Host" from
a fold of its own log prefix at random points, and at the end requires

* the follower (`World.fold` from genesis over the admitted log) to reach the Host's World,
* the auditor (`Receive.audit`) to accept the same log and reach the same World,
* every planted mutation (stale pin, replay, wrong charge, stolen-key rotation, stranger, missing
  grant, deny-all law, a revoke by a non-issuer, a write through a revoked grant) to have been
  refused by its name,
* every revocation to have handed the grant cell's weight back to the budget (KERNEL-15).

Toy PARAMETERS in the real pipeline (memory: never toy code beside it): the digest is `UInt64`,
the hash FNV-1a, a signature is the hash of key ‖ message, and the program is a two-law stub
(`deny-all` refuses, anything else admits; method 0 sets the first state slot). The encodings of
turns and cells are the toy's own serialisation until CODEC's Turn/Cell codecs land; the Sim then
runs under the deployed `Env` as well.

The Host side here is incremental `admit` plus restart-by-fold: the stand-in for HOST's loop
(KERNEL K0), replaced by plugging `Host.Loop` into `step` when it exists.
-/
import Kernel.Sim.Gen

namespace Nanodregg.Kernel.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive

abbrev D := UInt64

/-! ## Toy parameters -/

def fnv (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

def u64le (x : UInt64) : ByteArray := Gen.u64le x

def ofLe (b : ByteArray) : Option UInt64 :=
  if b.size = 8 then
    some ((List.range 8).foldl (fun acc i => acc ||| ((b.get! i).toUInt64 <<< (8 * i).toUInt64)) 0)
  else none

def nat (n : Nat) : ByteArray := Gen.nat n
def blob (b : ByteArray) : ByteArray := nat b.size ++ b
def many {α : Type} (f : α → ByteArray) (l : List α) : ByteArray :=
  l.foldl (fun acc x => acc ++ f x) (nat l.length)

def discByte : Discipline → ByteArray
  | .rom => nat 0 | .appendOnly => nat 1 | .ram => nat 2

def cellBytes (c : Cell) : ByteArray :=
  nat c.kind ++ discByte c.discipline ++ many (fun p => nat p.1 ++ blob p.2) c.slots

def opBytes : Op → ByteArray
  | .set k v => nat 0 ++ nat k ++ blob v
  | .erase k => nat 1 ++ nat k

def actBytes : Act → ByteArray
  | .keep => nat 0 | .write ops => nat 1 ++ many opBytes ops | .retire => nat 2

def touchBytes (x : Touch D) : ByteArray := u64le x.cell ++ u64le x.seen ++ actBytes x.act

def turnBytes (t : Turn D) : ByteArray :=
  u64le t.txId ++ nat t.notBefore ++ nat t.validUntil ++
  many touchBytes t.touches ++ many cellBytes t.creates ++ many u64le t.nullifiers ++ nat t.charge ++ blob t.event

def env : Env D :=
  { hash := fun dom b => fnv (dom.toUTF8 ++ b), bytes := u64le, turnBytes, cellBytes }

def rightBytes : Right → ByteArray
  | .observe => nat 0 | .mutate => nat 1 | .invoke m => nat 2 ++ nat m | .enroll n => nat 3 ++ nat n

def optD : Option D → ByteArray
  | none => nat 0 | some d => nat 1 ++ u64le d

def bodyBytes : Body D → ByteArray
  | .enroll k n p v => nat 0 ++ blob k ++ u64le n ++ blob p ++ u64le v
  | .rotate k n => nat 1 ++ blob k ++ u64le n
  | .install p => nat 2 ++ blob p
  | .create p ls st => nat 3 ++ optD p ++ many u64le ls ++ many (fun q => nat q.1 ++ blob q.2) st
  | .write o es v => nat 4 ++ u64le o ++
      many (fun e => nat e.1 ++ match e.2 with | none => nat 0 | some b => nat 1 ++ blob b) es ++ optD v
  | .law o ls v => nat 5 ++ u64le o ++ many u64le ls ++ optD v
  | .invoke o m a b v => nat 6 ++ u64le o ++ nat m ++ blob a ++ nat b ++ optD v
  | .grant t g rs p => nat 7 ++ u64le t ++ u64le g ++ many rightBytes rs ++ optD p
  | .revoke g => nat 9 ++ u64le g

def unsignedBytes (u : Unsigned D) : ByteArray :=
  u64le u.member ++ blob u.key ++ nat u.notBefore ++ nat u.validUntil ++
  many (fun p => u64le p.1 ++ u64le p.2) u.pins ++ nat u.maxCharge ++ bodyBytes u.body

def toySign (key msg : ByteArray) : ByteArray := u64le (fnv (key ++ msg))

def program : Program D := Gen.program

abbrev Registry := Gen.Registry D

def ctx (reg : Registry) : Ctx D :=
  { env, unsignedBytes, callBytes := fun c => unsignedBytes c.unsigned ++ blob c.signature,
    decodeCall := fun b => (reg.calls.find? fun p => p.1 = fnv b).map Prod.snd
    digestOf := ofLe, verify := fun key msg sig => toySign key msg == sig, program }

/-- The toy parameters: a secret IS its public key, and its "signature" is a hash. -/
def toy : Gen.Params D :=
  { name := "toy parameters (UInt64 digest, FNV-1a, hash signatures)", env, ctx,
    pub := fun k => k, sign := toySign, regKey := fnv, zero := 0 }

/-! The generator under the toy parameters, by the names `lang-journey` uses. -/

abbrev Member := Gen.Member D
abbrev State := Gen.State D
abbrev Expect := Gen.Expect

def nameOf {α : Type} [Repr α] (a : α) : String := Gen.nameOf a
def worldName : ByteArray := Gen.worldName
def same (a b : World D) : Bool := Gen.same a b
def S.pinsFor (w : World D) (ids : List D) : List (D × D) := Gen.S.pinsFor env w ids
def signed (st : State) (m : Member) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D := Gen.signed toy st m key pins body

end Nanodregg.Kernel.Sim
