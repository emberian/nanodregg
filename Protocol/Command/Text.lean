/-
# Protocol.Command.Text — the text forms the command language reads and prints

Digests and opaque tokens are lowercase hex; numbers are decimal. Layout values are built from
plain bytes here, refusing anything past the layout's bound. Round trips: `Protocol.Proofs.Text`.
-/
import Codec.Layout

namespace Nanodregg.Protocol.Text

open Nanodregg.Codec

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase hex, two digits a byte (`Command.toHex_utf8ByteSize`). A fold over the bytes' array, so
its size is a fact about a list fold. -/
def toHex (b : ByteArray) : String :=
  b.data.foldl (fun (s : String) (x : UInt8) => (s.push (hexDigit (x >>> 4))).push (hexDigit (x &&& 15))) ""

def hexVal (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87).toUInt8
  else none

def unhex (acc : ByteArray) : List Char → Option ByteArray
  | [] => some acc
  | [_] => none
  | a :: b :: rest => do unhex (acc.push ((← hexVal a) * 16 + (← hexVal b))) rest

/-- Lowercase hex only: an uppercase or odd-length spelling is refused, so each byte string has
one spelling. -/
def ofHex (s : String) : Option ByteArray := unhex ByteArray.empty s.toList

/-- A byte string inside a layout's bound. -/
def fit (max : Nat) (b : ByteArray) : Option (Bytes max) :=
  if h : b.size ≤ max then some ⟨b, h⟩ else none

def fitList (max : Nat) (l : List ByteArray) : Option (Bounded max (Bytes max)) := do
  let a ← l.toArray.mapM (fit max)
  if h : a.size ≤ max then some ⟨a, h⟩ else none

def unlist {max : Nat} (v : Bounded max (Bytes max)) : List ByteArray := v.1.toList.map (·.1)

def u64 (n : Nat) : ByteArray := Stream.u64.bytes n.toUInt64

def ofU64 (b : ByteArray) : Option Nat :=
  match Stream.u64.decode b with
  | .ok v => some v.toNat
  | .error _ => none

end Nanodregg.Protocol.Text
