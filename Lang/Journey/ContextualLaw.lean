/-
# Lang.Journey.ContextualLaw — a hole filled under a CONTRACT on another object (DESIGN-CTX §2.5a, S2; LANG-84)

A candidate that links to another member's object may demand what that object IS, read off the
cell the kernel holds: `SupportPin.cellLaw g L` (the object `g` is live AND governed by the law
package `L`) and `SupportPin.cellPackage o P` (the object `o` is live AND runs package `P`). A
data object's laws can change (`law`, judged by the old regime and the new), so a contract by law
is DEFEASIBLE in exactly the slot's way: the `law g []` that drops `L` withdraws every
justification that cited it, and the next demand of the hole is refused `holeSupportDead 0
cellLaw:<g>:<L>` by name. A programmed object's package never changes today
(`audit_package_fixed`), so a contract by package is permanent until the package is a slot
(DESIGN-CTX §2.5c).

Rows LG0–LG8, through `Receive.submit` and `World.admit`: a law package `L` (one law, admits every
act) is installed; a data object `g` is created under `L` and an object `o` of `L`; a contextual ROM
with three candidates is installed — code 0 cites `cellLaw g L`, code 1 cites `cellPackage o L`,
code 2 cites `cellPackage o g` (a package `o` does not run) — and its hole object created; code 0
executes (value 7) while `g` is governed by `L`; A relaws `g` to no laws; the same execute is refused
`holeSupportDead 0 cellLaw:<g>:<L>`; code 1 executes; code 2 is refused `holeSupportDead 0
cellPackage:<o>:<g>`.
-/
import Lang.Journey
import Lang.Journey.Contextual

namespace Nanodregg.Lang.Journey.Law
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang.Journey

/-- A law package with one law that admits every act: the contract `cellLaw g L` names it. -/
def openLaw : Package :=
  { imports := [], state := .record [], iface := .record [("open", lawTy (.record []))],
    body := .record [("open", Std.lawOf (.record []) (fun _ => Std.okT) (fun _ => Std.okT)
      (fun _ => Std.okT) (fun _ => Std.okT))],
    methods := [], laws := ["open"] }

/-- The ROM: context `[bool, nat]`, result `nat`, three candidates `var 1` (the nat argument), each
under one contract support; no hypothesis pins, no guard pin (the guard passes its `present`
through). -/
def declaration (g L o : ByteArray) : HoleROM :=
  { name := 0, ctx := [.bool, .nat], ty := .nat,
    code := [⟨.var 1, [.cellLaw g L]⟩, ⟨.var 1, [.cellPackage o L]⟩, ⟨.var 1, [.cellPackage o g]⟩],
    selectionRel := 0, selectionKey := .empty,
    hypotheses := [none, none], guardPin := none, guard := .var 0 }

def lawRows (r0 : Run) (a : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let X := ctxWith prog
  let mut r := r0
  -- LG0 the law package and the two objects the contracts name
  let some lb := Wire.encodePackage openLaw | return note r "LG0 the law package has no bytes" false
  let (r0', v0, t0) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install lb))
  let some L := t0.bind fun t => (createdIds t).head? | return note r0' s!"LG0 install the law package: {v0}" false
  r := note r0' s!"LG0 A installs the law package L ({lb.size} bytes, law open): {v0}" (v0 == "admitted")
  let (rg, vg, tg) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, L]) (.create none [L] []))
  let some g := tg.bind fun t => (createdIds t).head? | return note rg s!"LG0 create g under L: {vg}" false
  r := note rg s!"LG0 A creates a data object g governed by L: {vg}" (vg == "admitted")
  let (ro, vo, to) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, L]) (.create (some L) [] []))
  let some o := to.bind fun t => (createdIds t).head? | return note ro s!"LG0 create o of L: {vo}" false
  r := note ro s!"LG0 A creates an object o running L: {vo}" (vo == "admitted")
  let (gB, LB, oB) := (Sim.dc.bytes g, Sim.dc.bytes L, Sim.dc.bytes o)
  -- LG1 the contextual ROM: helpers, then the root citing g, L and o
  let bundle ← match Std.contextualHole .nat (declaration gB LB oB) [.bool true, .var 1] Contextual.clause with
    | .ok b => pure b
    | .error e => return note r s!"LG1 generate: {e}" false
  let mut ids : List D := []
  for lib in bundle.libraries do
    let some bytes := Wire.encodePackage lib | return note r "LG1 helper wire" false
    let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rr s!"LG1 install helper {bytes.size}: {verdict}" (verdict == "admitted")
    let some id := turn.bind fun t => (createdIds t).head? | return r
    ids := ids ++ [id]
  let p ← match bundle.linkContextual (ids.map Sim.dc.bytes) with
    | .ok p => pure p
    | .error e => return note r s!"LG1 link: {e}" false
  let some text := Print.package p | return note r "LG1 print" false
  let .ok back := Surface.readPackage text | return note r "LG1 read" false
  r := note r "LG1 the contract pins survive the resident text" (decide (back = p))
  let some bytes := Wire.encodePackage p | return note r "LG1 wire" false
  let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, g, L, o] ++ ids)) (.install bytes))
  r := note rr s!"LG1 install the contextual ROM ({bytes.size} bytes; its supports name g, L and o): {verdict}" (verdict == "admitted")
  let some pkg := turn.bind fun t => (createdIds t).head? | return r
  let some seed := stateSlots (recordRow p.state)
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes a.id)), ("cap", .nat 10),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000),
     ("selected", .inj "none" (.record []))] 0 | return note r "LG1 seed" false
  let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ ids)) (.create (some pkg) [] seed))
  r := note rr s!"LG1 create the hole object: {verdict}" (verdict == "admitted")
  let some obj := turn.bind fun t => (createdIds t).head? | return r
  let choiceKey := Data.record [("hole", .nat 0)]
  -- the rows an execute reads (the selection row and the computed row) and the cells the contracts name
  let rowPins (r : Run) :=
    hole_pinAt obj r.st.host 5 Std.codeSelection choiceKey ++
    hole_pinAt obj r.st.host 1 (Std.codeOutput .nat) choiceKey
  let call (r : Run) (method : Label) (args : ByteArray) :=
    signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, obj, pkg, g, L, o] ++ ids))
      (.invoke obj (p.methods.idxOf method) args 100000 none)
      r.st.host.height (r.st.host.height + 1024) (rowPins r)
  let exec (r : Run) := call r "execute" (argBytes .nat (.nat 7))
  let choose (r : Run) (i : Nat) := call r "choose_code"
    (argBytes (.record [("hole", .nat), ("index", .nat)])
      (.record [("hole", .nat 0), ("index", .nat i)]))
  let value (r : Run) := match storyRow r.st.host obj 1 (Std.codeOutput .nat) choiceKey with
    | some (.nat n) => some n | _ => none
  let lawsOfG (r : Run) : Option Nat := (r.st.host.live X.env g).map fun c => (lawSlotsOf c).length
  -- LG2 code 0, under `cellLaw g L`, executes while g is governed by L
  let (rr, v, _) := go prog r (choose r 0)
  r := note rr s!"LG2 A chooses code 0 (contract: g governed by L): {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LG2 execute under the contract (g has {lawsOfG r} law): {v}; value {value rr}" (v == "admitted" && value rr == some 7)
  -- LG3 A relaws g to no laws (judged by L's law as relaw; nothing incoming): the contract is withdrawn
  let (rr, v, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, g, L]) (.law g [] none))
  r := note rr s!"LG3 A relaws g to no laws: {v}; g now has {lawsOfG rr} law" (v == "admitted" && lawsOfG rr == some 0)
  let (_, v, _) := go prog r (exec r)
  r := note r s!"LG4 execute after the relaw: {v}"
    (refusedBy v "execute" s!"holeSupportDead 0 {(SupportPin.cellLaw gB LB).wire}")
  -- LG5 code 1, under `cellPackage o L`, executes: o runs L
  let (rr, v, _) := go prog r (choose r 1)
  r := note rr s!"LG5 A chooses code 1 (contract: o runs L): {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LG5 execute under the package contract: {v}; value {value rr}" (v == "admitted" && value rr == some 7)
  -- LG6 code 2, under `cellPackage o g` (a package o does not run), is refused by name
  let (rr, v, _) := go prog r (choose r 2)
  r := note rr s!"LG6 A chooses code 2 (contract: o runs g, which it does not): {v}" (v == "admitted")
  let (_, v, _) := go prog r (exec r)
  r := note r s!"LG6 execute under a package contract the object does not meet: {v}"
    (refusedBy v "execute" s!"holeSupportDead 0 {(SupportPin.cellPackage oB gB).wire}")
  return r

def lawSession : Run :=
  let X := ctxWith langProgram
  let fk := [("lw-a".toUTF8, "lw-a-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 12) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"LG genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    lawRows { st := { rng := ⟨1⟩, host := g, members := ms } } (ms.headD ⟨0, .empty, .empty⟩)

initialize register { name := "law", run := pure lawSession, contextual := true }

end Nanodregg.Lang.Journey.Law
