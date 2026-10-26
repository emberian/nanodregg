/-
# Lang.Proofs.WireTeeth — the codecs on concrete values

The canonicity theorems (`decodePackage_eq_ok_iff`, `decodeData_eq_ok_iff`) would hold vacuously for
an encoder that writes nothing and a decoder that refuses everything; these pin that the encoders
write, and name the values and trees the codecs refuse, each by the kernel evaluating the codec.
(`Codec.Tree.getD` is well-founded recursion, which the kernel does not unfold, so the package
decoder is reached through `decodePackage_eq_ok_iff`, not evaluated.)
-/
import Lang.Proofs.Wire
import Lang.Proofs.Data

namespace Nanodregg.Lang.Teeth

open Nanodregg.Codec Nanodregg.Lang.Wire

/-- The smallest package: no state, an empty interface and body. -/
private def tiny : Package :=
  { imports := [], state := .record [], iface := .record [], body := .record [], methods := [], laws := [] }

private def isOk {α : Type} : Except Refusal α → Bool
  | .ok _ => true
  | .error _ => false

private def isRejected {α : Type} (name : String) : Except Refusal α → Bool
  | .error (.rejected _ n) => n == name
  | _ => false

/-- The package encoder writes. -/
theorem tiny_encodes : (encodePackage tiny).isSome = true := by decide +kernel

/-- A package touching every constructor: an import, a state field, methods and laws, function, record
and sum types, and a body using all fifteen term constructors. An encoder or reader that dropped any
one of them (paired with a `*Wire` tightened to match, which the inverse proofs would not see) turns
this red. -/
private def rich : Package :=
  { imports := [⟨Array.replicate 32 7⟩], state := .record [("n", .nat)],
    iface := .record [("law", lawTy (.record [("n", .nat)])), ("m", methodTy (.record [("n", .nat)]) .bool)],
    body := .record [("a", .lam (.sum [("x", .bytes), ("y", .nat)])
        (.case (.var 0) [("x", .prim .cat (.var 0) (.bytes ⟨#[1, 2]⟩)), ("y", .ref 0)])),
      ("b", .app (.fix (.var 0)) (.extend (.record [("f", .bool true)]) [("f", .nat 3)])),
      ("c", .ite (.get (.var 1) "n") (.inj (.sum [("z", .nat)]) "z" (.nat 9)) (.var 2))],
    methods := ["m"], laws := ["law"] }

theorem rich_encodes : (encodePackage rich).isSome = true := by decide +kernel

/-- So, by canonicity, its bytes decode to it. -/
theorem tiny_decodes : ∃ b, encodePackage tiny = some b ∧ decodePackage b = .ok tiny := by
  cases e : encodePackage tiny with
  | none => have h := tiny_encodes; rw [e] at h; simp at h
  | some b => exact ⟨b, rfl, decodePackage_eq_ok_iff.mpr e⟩

/-- A literal natural past `2^64` has no bytes (a `u64` would wrap it to 0). -/
theorem big_literal_unencodable : encodePackage { tiny with body := .nat (2 ^ 64) } = none := by
  decide +kernel

/-- A 65-byte label has no bytes. -/
theorem long_label_unencodable :
    encodePackage { tiny with methods := [String.ofList (List.replicate 65 'a')] } = none := by
  decide +kernel

/-- LANG-51: `refuse` is tag 17 with its reason as the payload and its type as the one child, and
reads back; a tag-17 node without its type child is refused. `len<=` is primitive code 11; the three
payload writers are 12–14 (LANG-87); 15 is no primitive. -/
theorem refuse_round_trip :
    termOf (termTree (.refuse .nat ⟨#[108, 97, 116, 101]⟩)) = some (.refuse .nat ⟨#[108, 97, 116, 101]⟩) :=
  termOf_termTree _ (by decide +kernel)

theorem refuse_untyped_refused : (termOf (.node 17 ⟨#[108]⟩ [])).isNone = true := by decide +kernel

theorem prim_codes : primOf 11 = some .lenLe ∧ primOf 12 = some .u64be ∧ primOf 13 = some .sized ∧
    primOf 14 = some .dsized ∧ primOf 15 = none := by decide

/-- A type's tree is not a package's. -/
theorem ty_tree_not_package : packageOf (tyTree .nat) = none := by decide +kernel

/-- An index payload of three bytes is not a `u32`. -/
theorem short_index_refused : termOf (.node 0 ⟨#[0, 0, 0]⟩ []) = none := by decide +kernel

/-- A field node under a type with a payload where a type node has none. -/
theorem ty_payload_refused : tyOf (.node 0 ⟨#[0]⟩ []) = none := by decide +kernel

/-- Data: a natural round-trips at `nat`; a bool byte other than 0 or 1 is refused. -/
theorem nat_round_trip :
    (match encodeData .nat (.nat 5) with | some b => isOk (decodeData .nat b) | none => false) = true := by
  decide +kernel

theorem bool_two_refused : isRejected "bool" (decodeData .bool ⟨#[2]⟩) = true := by decide +kernel

/-- Sum data encodes, at a later arm too (a `DataAt (.sum _) := Empty` codec would fail here). -/
theorem refused_verdict_encodes :
    (encodeData verdictTy (.inj "refused" (.bytes ⟨#[1]⟩))).isSome = true := by decide +kernel

/-- One tag byte names the arm (`Stream.choice`): `refused` is arm 1, then the bytes' `u32` length and
the byte. A unary or `u32` arm index turns this red. -/
theorem refused_verdict_bytes :
    encodeData verdictTy (.inj "refused" (.bytes ⟨#[7]⟩)) = some ⟨#[1, 1, 0, 0, 0, 7]⟩ := by decide +kernel

/-- A sum of 257 arms has no data codec (one tag byte names at most 256). -/
theorem wide_sum_refused :
    isRejected "lang/data: type"
      (decodeData (.sum ((List.range 257).map fun i => (toString (1000 + i), Ty.nat))) ⟨#[0]⟩) = true := by
  decide +kernel

/-- A label the sum does not have is not data of it. -/
theorem foreign_arm_unencodable : encodeData verdictTy (.inj "maybe" (.record [])) = none := by
  decide +kernel

/-- A sum with a repeated label is not canonical: it has no data codec (two arms would name one
value). -/
theorem dup_arm_refused :
    isRejected "lang/data: type" (decodeData (.sum [("a", .nat), ("a", .nat)]) ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) = true := by
  decide +kernel

end Nanodregg.Lang.Teeth
