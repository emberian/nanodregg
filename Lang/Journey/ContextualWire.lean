/- Malformed encodings and width bounds for the new contextual wire forms. -/
import Lang.Journey.ContextualChecks

namespace Nanodregg.Lang.Journey.Contextual
open Nanodregg.Codec

def badPayload : Tree → Tree
  | .node tag _ children => .node tag "x".toUTF8 children

def badChildPayload (n : Nat) : Tree → Tree
  | .node tag payload children => .node tag payload
      (children.zipIdx.map fun (t, i) => if i = n then badPayload t else t)

def wireRows : List (String × Bool) :=
  let h := minimalPackage.holes[0]!
  let pin := factPinAt 1
  let c : HoleCode := ⟨.var 1, [pin]⟩
  let tree := Wire.holeROMTree h
  [("wire-option-none-payload", (Wire.supportOptPinOf (badPayload (Wire.supportOptPinTree none))).isNone),
   ("wire-option-some-payload", (Wire.supportOptPinOf (badPayload (Wire.supportOptPinTree (some pin)))).isNone),
   ("wire-code-payload", (Wire.holeCodeOf (badPayload (Wire.holeCodeTree c))).isNone),
   ("wire-support-wrapper", (Wire.holeCodeOf (badChildPayload 1 (Wire.holeCodeTree c))).isNone),
   ("wire-context-wrapper", (Wire.holeROMOf (badChildPayload 0 tree)).isNone),
   ("wire-candidates-wrapper", (Wire.holeROMOf (badChildPayload 2 tree)).isNone),
   ("wire-hypotheses-wrapper", (Wire.holeROMOf (badChildPayload 4 tree)).isNone),
   ("wire-substitution-width", (Wire.termOf (.node 18 (Wire.u32Bytes 0)
     (List.replicate (Wire.rowMax + 1) (Wire.termTree (.nat 0))))).isNone),
   ("wire-name-width", !Wire.holeROMWire { h with name := 2^32 }),
   ("wire-selection-width", !Wire.holeROMWire { h with selectionRel := 2^32 }),
   ("wire-pin-rel-width", !Wire.supportPinWire (.row (2^32) (factKeyAt 1) 1)),
   ("wire-pin-version-width", !Wire.supportPinWire (.row 2 (factKeyAt 1) (2^64))),
   ("wire-cell-pin-reads", Wire.supportPinOf (Wire.supportPinTree (.cell (factKeyAt 1))) == some (.cell (factKeyAt 1))),
   ("wire-cell-pin-children", (Wire.supportPinOf (.node 1 (factKeyAt 1) [.node 0 .empty []])).isNone),
   ("wire-pin-unknown-tag", (Wire.supportPinOf (.node 2 (factKeyAt 1) [])).isNone)]

end Nanodregg.Lang.Journey.Contextual
