/- The ROM signature section (version 4; a cell pin since version 5). All numbers retain the existing u32/u64 bounds. -/
import Lang.Wire
import Lang.HoleROM

namespace Nanodregg.Lang.Wire
open Nanodregg.Codec

/-- A row pin is `node 0 key [rel ver]` (its version-4 bytes); a cell pin `node 1 id []` (version 5, E1). -/
def supportPinTree : SupportPin → Tree
  | .row rel key ver => .node 0 key [.node 0 (u32Bytes rel) [], .node 0 (u64Bytes ver) []]
  | .cell id => .node 1 id []

def supportPinOf : Tree → Option SupportPin
  | .node 0 key [.node 0 r [], .node 0 v []] =>
      match u32Of r, u64Of v with
      | some rel, some ver => some (.row rel key ver)
      | _, _ => none
  | .node 1 id [] => some (.cell id)
  | _ => none

def supportPinWire : SupportPin → Bool
  | .row rel _ ver => decide (rel < 2^32) && decide (ver < 2^64)
  | .cell _ => true

def supportOptPinTree : Option SupportPin → Tree
  | none => .node 0 .empty []
  | some p => .node 1 .empty [supportPinTree p]

def supportOptPinOf : Tree → Option (Option SupportPin)
  | .node 0 e [] => if e = .empty then some none else none
  | .node 1 e [p] => if e = .empty then (supportPinOf p).map some else none
  | _ => none

def holeCodeTree (c : HoleCode) : Tree :=
  .node 0 .empty [termTree c.body, .node 0 .empty (c.supports.map supportPinTree)]

def holeCodeOf : Tree → Option HoleCode
  | .node 0 e [t, .node 0 es ps] =>
      if e = .empty ∧ es = .empty then
        match termOf t, ps.mapM supportPinOf with
        | some body, some supports => some ⟨body, supports⟩
        | _, _ => none
      else none
  | _ => none

def holeCodeWire (c : HoleCode) : Bool :=
  termWire c.body && c.supports.all supportPinWire

/-- Node 3: name u32, context node0, result type, code node0, selection node0
(key payload and u32 relation child), hypotheses node0, optional guard pin,
guard term. All wrapper payloads except the stated name/key are empty. -/
def holeROMTree (h : HoleROM) : Tree :=
  .node 3 (u32Bytes h.name)
    [.node 0 .empty (h.ctx.map tyTree), tyTree h.ty,
     .node 0 .empty (h.code.map holeCodeTree),
     .node 0 h.selectionKey [.node 0 (u32Bytes h.selectionRel) []],
     .node 0 .empty (h.hypotheses.map supportOptPinTree),
     supportOptPinTree h.guardPin, termTree h.guard]

def holeROMOf : Tree → Option HoleROM
  | .node 3 n [.node 0 ec cs, ty, .node 0 ek ks,
      .node 0 selectionKey [.node 0 sr []], .node 0 eh hs, gp, g] =>
    if ec = .empty ∧ ek = .empty ∧ eh = .empty then
      match u32Of n, cs.mapM tyOf, tyOf ty, ks.mapM holeCodeOf,
            u32Of sr, hs.mapM supportOptPinOf, supportOptPinOf gp, termOf g with
      | some name, some ctx, some ty, some code, some selectionRel,
        some hypotheses, some guardPin, some guard =>
        some { name, ctx, ty, code, selectionRel, selectionKey, hypotheses, guardPin, guard }
      | _, _, _, _, _, _, _, _ => none
    else none
  | _ => none

def holeROMWire (h : HoleROM) : Bool :=
  decide (h.name < 2^32) && h.ctx.all tyWire && tyWire h.ty &&
  h.code.all holeCodeWire && decide (h.selectionRel < 2^32) &&
  h.hypotheses.all (Option.all supportPinWire) && h.guardPin.all supportPinWire && termWire h.guard

end Nanodregg.Lang.Wire
