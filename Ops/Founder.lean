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

/-- The test World's genesis nonce (KERNEL-24): fixed, so the driver can rebuild the World `host
genesis --nonce` writes; a real genesis draws it from the OS. -/
def nonce : ByteArray := hex "6e616e6f64726567672f6f70732f74657374206e6f6e63652f76312e2e2e2e2e"

/-- `host genesis STORE NAME --nonce N KEY NEXT`'s arguments after NAME. -/
def genesisArgs : List String :=
  ["--nonce", Protocol.Text.toHex nonce, Protocol.Text.toHex key, Protocol.Text.toHex next]

/-- The genesis World `host genesis STORE name …genesisArgs` writes (the same `Receive.genesis`),
or its refusal. -/
def world (name : String) : Except GenesisRefusal (World D) :=
  Receive.genesis X name.toUTF8 nonce allowanceMax [(key, nextKeyDigest X next)]

/-- `create` as the member `me`: after a carry (KERNEL-29) the members keep their old ids, keyed by
the EXPORTED World's origin, while every call names the new World (`Unsigned.world`). -/
def createAs (me : D) (w : World D) (i : Nat) (state : Slots := []) : Call D :=
  let u : Unsigned D :=
    { world := w.origin, member := me, key, notBefore := 0, validUntil := Bounds.windowMax / 2 + i,
      pins := [(me, pinOf X.env (w.live X.env me))], maxCharge := 1 <<< 40, body := .create none [] state }
  { unsigned := u, signature := Ed25519.sign seed (X.unsignedBytes u) }

/-- The `i`-th call: founder 0 creates an empty data object, pinned on its own member cell as it
is in `w` (distinct `i < windowMax / 2`, distinct `validUntil`, distinct txId), holding `state`
(empty by default; the sealed-Store plants fill one slot to reach a seal in few calls). -/
def create (w : World D) (i : Nat) (state : Slots := []) : Call D :=
  createAs (founderId X w.origin 0) w i state

/-- A `lookup` frame toward `host serve`: the same call bytes (Protocol.Op.lookup). -/
def lookupFrame (c : Call D) : ByteArray :=
  encodeFrame { conn := 1, op := Protocol.Op.lookup.code, payload := X.callBytes c }

/-- A `submit` frame toward `host serve`. -/
def submitFrame (c : Call D) : ByteArray :=
  encodeFrame { conn := 1, op := Protocol.Op.submit.code, payload := X.callBytes c }

end Nanodregg.Ops.Founder
