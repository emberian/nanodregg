/-
# Ops.Founder — a test World's founder and its signed calls, under DEPLOYED signing

Ops drivers (the backup plants, THE BAR) need calls the real `host serve` admits: deployed Ctx,
real Ed25519. The founder's seed is RFC 8032 §7.1 TEST 1's secret key and the precommitted next
key is TEST 2's public key: published test vectors, not key material. Nothing deployed imports
Ops (closure rule), and no real seed is ever written here.
-/
import Host.Deployed
import Host.Wire

namespace Nanodregg.Ops.Founder

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Codec

def hex (s : String) : ByteArray := (Protocol.Text.ofHex s).getD ByteArray.empty

/-- RFC 8032 §7.1 TEST 1, secret key (published). -/
def seed : ByteArray := hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
/-- RFC 8032 §7.1 TEST 2, secret key (published); only its public key is used, as `next`. -/
def nextSeed : ByteArray := hex "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"

def key : ByteArray := Ed25519.publicKey seed
def next : ByteArray := Ed25519.publicKey nextSeed

/-- `host genesis STORE NAME KEY NEXT`'s founder arguments. -/
def genesisArgs : List String := [Protocol.Text.toHex key, Protocol.Text.toHex next]

/-- The genesis World `host genesis STORE name …genesisArgs` writes (the same `Receive.genesis`). -/
def world (name : String) : World D :=
  Receive.genesis X name.toUTF8 allowanceMax [(key, nextKeyDigest X next)]

/-- The `i`-th call: founder 0 creates an empty data object, pinned on its own member cell as it
is in `w` (distinct `i < windowMax / 2`, distinct `validUntil`, distinct txId). -/
def create (name : String) (w : World D) (i : Nat) : Call D :=
  let me := founderId X name.toUTF8 0
  let u : Unsigned D :=
    { member := me, key, notBefore := 0, validUntil := Bounds.windowMax / 2 + i,
      pins := [(me, pinOf X.env (w.live me))], maxCharge := 1 <<< 40, body := .create none [] [] }
  { unsigned := u, signature := Ed25519.sign seed (X.unsignedBytes u) }

/-- A `submit` frame toward `host serve`. -/
def submitFrame (c : Call D) : ByteArray :=
  encodeFrame { conn := 1, op := Protocol.Op.submit.code, payload := X.callBytes c }

end Nanodregg.Ops.Founder
