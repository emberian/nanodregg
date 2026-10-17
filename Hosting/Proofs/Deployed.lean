/-
# Hosting.Proofs.Deployed — the grain package on the deployed path: slots in, slots out

`Hosting.Proofs.Package` evaluates the package BODY on `Data` values. This is the path the kernel
actually takes: `Lang.program`'s `run` (load the package cell through the pinned view, decode the
state slots at the state type, run method `m` = `p.methods[m]?` under the call's budget, re-encode)
and then its `judge` (every law of the package, under `lawTicks`). Toy digest (`Kernel.Sim`'s
UInt64), the deployed codecs.

`invoke_slots`: for every phase and event, from a grain's slots, the method runs, its result is
admitted exactly when `step p e` is some, its phase slot decodes to `target p e`, and its entry and
kind slots are the old ones. The compiler evaluates it (the slot codecs do not reduce in the
kernel), recorded in gates/axioms-allow.tsv.
-/
import Hosting.Package
import Hosting.Controller
import Lang.Program
import Kernel.Sim

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang
open Nanodregg.Hosting Nanodregg.Hosting.Grain

private abbrev D := Kernel.Sim.D

private def prog : Program D := Lang.program Kernel.Sim.dc.bytes Kernel.Sim.digestOf

/-- The installed package cell, its id, and the pinned view that holds exactly it. -/
private def pkgCell : Option Cell := (Grain.lifecycle?.toOption.bind Wire.encodePackage).map Controller.packageCell
private def pkgId : Option D := pkgCell.map (romIdOf Kernel.Sim.env)
private def look (id : D) (c : Cell) : Pinned D := fun i => if i = id then .ok (some c) else .ok none

private def owner : D := 7

private def reqFor (e : Event) : Req D :=
  { agent := owner, principal := owner, notBefore := 0, validUntil := 0, occasion := .invoke e.index }

private def slotsAt (k : Kind) (p : Phase) : Option Slots := do
  let s ← seed k "app.bin".toUTF8
  let b ← Wire.encodeData phaseTy (.inj p.label unitD)
  pure (s.set slotPhase b)

/-- One case of `invoke_slots`. -/
private def slotCase (k : Kind) (p : Phase) (e : Event) : Bool :=
  match pkgCell, pkgId, slotsAt k p, noArgs with
  | some c, some id, some s, some args =>
    match prog.run (look id c) id s e.index args (reqFor e) 100000 with
    | .error _ => false
    | .ok s' =>
      (prog.judge (look id c) (some id) [] s s' (reqFor e) matches .ok ()) == (step p e).isSome &&
      phaseOf s' == some (target p e) && entryOf s' == entryOf s && kindOf s' == kindOf s &&
      s'.length == s.length
  | _, _, _, _ => false

theorem invoke_slots :
    ∀ k ∈ Kind.all, ∀ p ∈ Phase.all, ∀ e ∈ Event.all, slotCase k p e = true := by
  native_decide

end Nanodregg.Hosting.Proofs
