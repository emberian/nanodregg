/-
# Host.Sim.Join — carried invitations through the deployed CLI decision
-/
import Host.Cli
import Protocol.Rows.Deployed

namespace Nanodregg.Host.Sim.Join

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed
open Nanodregg.Protocol

/-- Run the actual CLI decision with observable Store writes and a matching reopen. -/
def trial (inv key : ByteArray) (input : Option String) (file : ByteArray) :
    IO (UInt32 × String × Nat × Option (World D)) := do
  let writes ← IO.mkRef 0
  let made ← IO.mkRef (none : Option (World D))
  let why ← IO.mkRef ""
  let status ← Cli.joinWith
    { nonce := pure (.ok "unused".toUTF8), readIn := pure (.ok file), key := pure (some Digest.zero)
      genesis := fun _ w => do
        writes.modify (· + 1)
        made.set (some w)
        pure (.ok ())
      reopen := fun _ => do
        match ← made.get with
        | none => pure (.error (.missing .base))
        | some w => pure (.ok w)
      refuse := fun s n => do why.set n; pure s.code.toUInt32
      report := fun _ => pure () }
    (Text.toHex inv) (Text.toHex key) input
  return (status, ← why.get, ← writes.get, ← made.get)

/-- The plant inputs are honest signed starts with one changed field, never forged parser output. -/
def checks : IO (List (String × Bool)) := do
  let R := Rows.Params.deployed
  let secret := "host-join-plant".toUTF8
  let key := R.pub secret
  let fs := [(key, Receive.nextKeyDigest X (R.pub "host-join-next".toUTF8))]
  let name := "join-plant".toUTF8
  let nonce := "signed-nonce".toUTF8
  let .ok g := Receive.genesis X name "first".toUTF8 10000 fs Receive.Authority.none |
    throw (IO.userError "join plant genesis")
  let .ok file := Carry.exportFile X.env Codec.Deployed.digestCodec g |
    throw (IO.userError "join plant export")
  let auth : Receive.Authority := ⟨[ByteArray.mk (Array.replicate 32 0xc3)], 1⟩
  let .ok (w, r) := Carry.importWorld X Codec.Deployed.digestCodec name nonce (.digest (Carry.digestOf file)) (some auth) file |
    throw (IO.userError "join plant import")
  let invitation (start : Invite.Start D) : IO ByteArray := do
    let some u := Invite.unsignedBytes X (Invite.startBytes X start)
        ⟨w.steps, R.keys.worldDigest (R.world.bytes w)⟩ (Receive.founderId X g.origin 0) key |
      throw (IO.userError "join plant unsigned")
    let some b := Invite.bytes u (R.sign secret (Invite.message u)) |
      throw (IO.userError "join plant invitation")
    return b
  let start (a : Receive.Authority) (height : Nat) : Receive.CarryStart D :=
    { Receive.carryStartOf X name nonce r.head.fromOrigin r.carried a with height }
  let good := Invite.Start.carried (start auth r.head.height) r.head.chain
  let inv ← invitation good
  let (ok, _, writes, made) ← trial inv key (some "in") file
  let (_, missing, mw, _) ← trial inv key none file
  -- a start whose trie root is not the file's names another origin: the import is another World
  let (_, wrong, ww, _) ← trial (← invitation (.carried { start auth r.head.height with trieRoot := r.head.fromOrigin } r.head.chain))
    key (some "in") file
  -- the anchor's chain in the start is not the file's
  let (_, anchor, aw, _) ← trial (← invitation (.carried (start auth r.head.height) r.head.fromOrigin))
    key (some "in") file
  let (_, arity, gw, _) ← trial (← invitation (.genesis name "first".toUTF8 10000 fs Receive.Authority.none)) key (some "in") file
  return [
    ("join-carried: signed nonce/origin reaches genesis and reopens", ok == 0 && writes == 1 &&
      (made.map fun m => R.world.bytes m == R.world.bytes w).getD false),
    ("join-carried-missing-input: usage in before writes", missing == "in" && mw == 0),
    ("join-carried-wrong-root: a start naming another trie root names another origin: carryMismatch wrongWorld before writes",
      wrong == "carryMismatch wrongWorld" && ww == 0),
    ("join-carried-anchor: carryMismatch anchor before writes", anchor == "carryMismatch anchor" && aw == 0),
    ("join-genesis-extra-input: usage in before writes", arity == "in" && gw == 0)]

end Nanodregg.Host.Sim.Join
