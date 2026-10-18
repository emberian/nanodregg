/-
# Hosting.Reply — the provider's answer, read by Lean: the reply TEXT, never the provider's JSON (HOSTING-29)

keybroker hands its decider the upstream's status and body (a `reply` request); `Broker.reply`
answers with the reply's text, the upstream's status when it is not 200, or `replyMalformed`.
So the resident receives text and never parses provider bytes, and the one reader of the
provider's JSON is this module.

The reader is `Json.value` over the body's bytes (a `ByteArray` and an index, law 3): a JSON value
parser (RFC 8259) whose strings are
read by `Json.unstr`, the same reader `Proofs.Broker.unstr_str` proves reads back every string
`Json.str` prints. A value nested deeper than `Bounds.depthMax` is refused (the reader recurses
once per level), and every recursion is bounded by a fuel of three steps per byte. Numbers and the
literals `true`, `false`, `null` are skipped, not kept: a number is a sign or digit followed by any
run of number bytes (`numByte`), which cannot hold a structural byte, so a lenient number never
moves where a value ends.

The reply is the text of the body's `content` blocks of type `text`, concatenated in order. The
body must be one object; `content` must occur in it exactly once and be an array; each block must
be an object with exactly one `type`, a string; a `text` block must have exactly one `text`, a
string; a block of any other type contributes nothing. A key that occurs twice in any object of
the body, at any depth, is ambiguous (a reader and the provider may disagree on which one counts),
so the body is refused. No text block (an empty `content`, or only other types) is the empty
reply, `.reply ""`: what to do with it is the resident's. The text must be UTF-8 and at most
`Bounds.replyMax` bytes.
-/
import Hosting.Broker

namespace Nanodregg.Hosting.Broker

namespace Bounds

/-- The deepest JSON nesting the reply reader accepts. -/
def depthMax : Nat := 64

/-- The longest reply text: a `reply` verdict or answer frame of it fits `frameMax`
(`Proofs.Reply.reply_encodes`). -/
def replyMax : Nat := frameMax - 64

end Bounds

namespace Json

/-- The byte at `i`, if `i` is inside `b`. -/
def byteAt (b : ByteArray) (i : Nat) : Option UInt8 := if h : i < b.size then some b[i] else none

/-- The value of one hexadecimal digit, either case. -/
def hexVal (h : UInt8) : Option Nat :=
  if 48 ≤ h && h ≤ 57 then some (h.toNat - 48)
  else if 97 ≤ h && h ≤ 102 then some (h.toNat - 87)
  else if 65 ≤ h && h ≤ 70 then some (h.toNat - 55)
  else none

/-- Four hexadecimal digits as a number below 65536. -/
def quad (a b c d : UInt8) : Option Nat := do
  let a ← hexVal a
  let b ← hexVal b
  let c ← hexVal c
  let d ← hexVal d
  pure (((a * 16 + b) * 16 + c) * 16 + d)

/-- The four hexadecimal digits at `i`. -/
def quadAt (b : ByteArray) (i : Nat) : Option Nat := do
  let a ← byteAt b i
  let c ← byteAt b (i + 1)
  let d ← byteAt b (i + 2)
  let e ← byteAt b (i + 3)
  quad a c d e

/-- The UTF-8 bytes of a Unicode scalar value (`c < 0x110000`, never a surrogate). -/
def utf8Of (c : Nat) : ByteArray :=
  if c < 0x80 then ⟨#[c.toUInt8]⟩
  else if c < 0x800 then ⟨#[(0xC0 + c / 64).toUInt8, (0x80 + c % 64).toUInt8]⟩
  else if c < 0x10000 then
    ⟨#[(0xE0 + c / 4096).toUInt8, (0x80 + c / 64 % 64).toUInt8, (0x80 + c % 64).toUInt8]⟩
  else
    ⟨#[(0xF0 + c / 262144).toUInt8, (0x80 + c / 4096 % 64).toUInt8, (0x80 + c / 64 % 64).toUInt8,
       (0x80 + c % 64).toUInt8]⟩

def isHigh (c : Nat) : Bool := 0xD800 ≤ c && c < 0xDC00
def isLow (c : Nat) : Bool := 0xDC00 ≤ c && c < 0xE000

/-- A JSON string's contents from index `i` (just after its opening quote), appended to `acc`:
the contents and the index just after the closing quote. Every RFC 8259 escape is read (`\"`,
`\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`, `\uXXXX` as UTF-8, a surrogate pair as one scalar
value); a raw control byte, an unknown escape, a lone or reversed surrogate, no closing quote, or
fuel `n` spent (one step per character) is `none`. Tail-recursive: a long string costs no stack. -/
def unstrAcc (b : ByteArray) : Nat → Nat → ByteArray → Option (ByteArray × Nat)
  | 0, _, _ => none
  | n + 1, i, acc =>
    match byteAt b i with
    | none => none
    | some x =>
      if x == 34 then some (acc, i + 1)
      else if x == 92 then
        match byteAt b (i + 1) with
        | some 34 => unstrAcc b n (i + 2) (acc.push 34)
        | some 92 => unstrAcc b n (i + 2) (acc.push 92)
        | some 47 => unstrAcc b n (i + 2) (acc.push 47)
        | some 98 => unstrAcc b n (i + 2) (acc.push 8)
        | some 102 => unstrAcc b n (i + 2) (acc.push 12)
        | some 110 => unstrAcc b n (i + 2) (acc.push 10)
        | some 114 => unstrAcc b n (i + 2) (acc.push 13)
        | some 116 => unstrAcc b n (i + 2) (acc.push 9)
        | some 117 =>
          match quadAt b (i + 2) with
          | none => none
          | some hi =>
            if isHigh hi then
              if byteAt b (i + 6) == some 92 && byteAt b (i + 7) == some 117 then
                match quadAt b (i + 8) with
                | some lo =>
                  if isLow lo then
                    unstrAcc b n (i + 12) (acc ++ utf8Of (0x10000 + (hi - 0xD800) * 1024 + (lo - 0xDC00)))
                  else none
                | none => none
              else none
            else if isLow hi then none
            else unstrAcc b n (i + 6) (acc ++ utf8Of hi)
        | _ => none
      else if x < 32 then none
      else unstrAcc b n (i + 1) (acc.push x)

/-- A JSON string's contents from index `i` (after its opening quote), and the index after its
closing quote. -/
def unstr (b : ByteArray) (i : Nat) : Option (ByteArray × Nat) := unstrAcc b b.size i .empty

/-- JSON whitespace. -/
def isWs (x : UInt8) : Bool := x == 32 || x == 9 || x == 10 || x == 13

/-- The first index at or after `i` that is not whitespace (at most `n` steps). -/
def ws (b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i =>
    match byteAt b i with
    | some x => if isWs x then ws b n (i + 1) else i
    | none => i

/-- A byte a JSON number may hold. -/
def numByte (x : UInt8) : Bool :=
  (48 ≤ x && x ≤ 57) || x == 45 || x == 43 || x == 46 || x == 101 || x == 69

/-- The first index at or after `i` that is not a number byte (at most `n` steps). -/
def dropNum (b : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i =>
    match byteAt b i with
    | some x => if numByte x then dropNum b n (i + 1) else i
    | none => i

/-- Whether `s` occurs in `b` at `i`. -/
def litAt (b : ByteArray) (i : Nat) (s : ByteArray) : Bool := b.extract i (i + s.size) == s

/-- `true`, `false`, `null`, or a number (a sign or digit, then number bytes) at `i`: the index after it. -/
def atom (b : ByteArray) (i : Nat) : Option Nat :=
  if litAt b i "true".toUTF8 then some (i + 4)
  else if litAt b i "false".toUTF8 then some (i + 5)
  else if litAt b i "null".toUTF8 then some (i + 4)
  else
    match byteAt b i with
    | some x => if (48 ≤ x && x ≤ 57) || x == 45 then some (dropNum b b.size (i + 1)) else none
    | none => none

/-- A JSON value as the reply reader keeps it: strings, arrays and objects; numbers and literals
are `atom`. -/
inductive Value where
  | str (s : ByteArray)
  | arr (vs : List Value)
  | obj (kvs : List (ByteArray × Value))
  | atom

mutual
/-- One value at index `i`, fuel `n` and remaining depth `d`, and the index after it. -/
def value (b : ByteArray) : Nat → Nat → Nat → Option (Value × Nat)
  | 0, _, _ => none
  | _ + 1, 0, _ => none
  | n + 1, d + 1, i =>
    let i := ws b b.size i
    match byteAt b i with
    | some 34 => (unstr b (i + 1)).map fun p => (.str p.1, p.2)
    | some 91 =>
      let j := ws b b.size (i + 1)
      match byteAt b j with
      | some 93 => some (.arr [], j + 1)
      | _ => (elems b n d j []).map fun p => (.arr p.1, p.2)
    | some 123 =>
      let j := ws b b.size (i + 1)
      match byteAt b j with
      | some 125 => some (.obj [], j + 1)
      | _ => (members b n d j []).map fun p => (.obj p.1, p.2)
    | _ => (atom b i).map fun j => (.atom, j)

/-- An array's elements from index `i` (after `[`, at least one), `acc` reversed; the index after `]`. -/
def elems (b : ByteArray) : Nat → Nat → Nat → List Value → Option (List Value × Nat)
  | 0, _, _, _ => none
  | n + 1, d, i, acc =>
    match value b n d i with
    | none => none
    | some (v, j) =>
      let j := ws b b.size j
      match byteAt b j with
      | some 44 => elems b n d (j + 1) (v :: acc)
      | some 93 => some ((v :: acc).reverse, j + 1)
      | _ => none

/-- An object's members from index `i` (after `{`, at least one), `acc` reversed; the index after
`}`. A key that occurs twice in one object, at any depth, is `none`. -/
def members (b : ByteArray) : Nat → Nat → Nat → List (ByteArray × Value) →
    Option (List (ByteArray × Value) × Nat)
  | 0, _, _, _ => none
  | n + 1, d, i, acc =>
    let i := ws b b.size i
    match byteAt b i with
    | some 34 =>
      match unstr b (i + 1) with
      | none => none
      | some (k, j) =>
        let j := ws b b.size j
        match byteAt b j with
        | some 58 =>
          match value b n d (j + 1) with
          | none => none
          | some (v, j) =>
            if acc.any (·.1 == k) then none else
            let j := ws b b.size j
            match byteAt b j with
            | some 44 => members b n d (j + 1) ((k, v) :: acc)
            | some 125 => some (((k, v) :: acc).reverse, j + 1)
            | _ => none
        | _ => none
    | _ => none
end

/-- The value of key `k`, or `none` when absent. A parsed object holds each key at most once
(`members` refuses a repeat), so there is no choice of copy to make here. -/
def field (k : String) (kvs : List (ByteArray × Value)) : Option Value :=
  (kvs.find? (·.1 == k.toUTF8)).map (·.2)

/-- One content block: `some (some t)` for a `text` block with text `t`, `some none` for a block of
another type, `none` for a malformed one. -/
def blockText : Value → Option (Option ByteArray)
  | .obj kvs =>
    match field "type" kvs with
    | some (.str ty) =>
      if ty == "text".toUTF8 then
        match field "text" kvs with
        | some (.str t) => some (some t)
        | _ => none
      else some none
    | _ => none
  | _ => none

/-- The reply text of a provider's body: its `text` blocks' texts, concatenated. -/
def replyText (body : ByteArray) : Option ByteArray :=
  match value body (3 * body.size + 3) Bounds.depthMax 0 with
  | some (.obj kvs, j) =>
    if ws body body.size j = body.size then
      match field "content" kvs with
      | some (.arr bs) => (bs.mapM blockText).map fun ts => ts.foldl (fun acc t => acc ++ t.getD .empty) .empty
      | _ => none
    else none
  | _ => none

end Json

/-- THE decision on an upstream answer: a status other than 200 is passed on as a status (its body
withheld: the provider's text never reaches the resident); a 200 body is read for its reply text,
which must be UTF-8 and at most `replyMax` bytes, else `replyMalformed`. -/
def reply (status : UInt32) (body : ByteArray) : Verdict :=
  if status ≠ 200 then .status status
  else
    match Json.replyText body with
    | some t => if utf8 t && Decidable.decide (t.size ≤ Bounds.replyMax) then .reply t else .refuse .replyMalformed
    | none => .refuse .replyMalformed

end Nanodregg.Hosting.Broker
