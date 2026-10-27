/-
# Web.Sim.Resident — the Bell's resident, run in the tab (CLIENT-54)

The testground's inbox demo runs the deployed resident's tick: `Hosting.Resident.tickP`, the term of
the open calculus with its two holes (`serve`, `use`), filled by `Hosting.Resident.fill`. Only the
effects are the tab's. The tick runs in `Co`, the free monad over the resident's effects: each effect
SUSPENDS the run and is handed to the page, which performs it and hands back the result:

* a member command (`Cmd.argv`): the page runs it as the resident's member, through the same client
  every terminal uses, and returns the exit, stdout and stderr;
* an ask: the page's scripted answerer returns a text (no model is called in the tab);
* keep, forget, note: the tab's volume is the page's memory, and each always holds;
* say: one log line, shown as the deployed resident prints it (`resident: …`).

The holes are filled one at a time, as `Lang.Contextual.Slot.interp` fills them: the run goes to its
first hole (`interp` at depth 0 ends `bound` there), the page is shown that hole's candidates, each
with the supports it cites and whether each holds at what the run has read (`Slot.evidence`,
`Slot.usable`), and the run goes on with `fill` of that hole. At most `holesMax` holes per tick, as
the deployed `Prog.interp`.

Tooling, like `Web.Sim.Testground`: no deployed module imports it.

Exports (each answers `ok ‖ LINES` or `refused ‖ NAME`):
* `tg_res_start BELL GRANT` (32 bytes each): a fresh resident for that Bell, invoking through GRANT,
  with an empty memory (as a first start on an empty volume).
* `tg_res_tick ()`: start one tick. `tg_res_answer RESULT`: the result of the effect the tick waits on.
  Each answers the hole views the run passed, then `op …` (the effect it now waits on) or `end …`
  (how the tick ended, then the memory: `kept RING`, `withdrawn RING CELL`).
-/
import Web.Sim.Testground
import Hosting.Resident.Run

namespace Nanodregg.Web.Sim.Resident

open Nanodregg.Hosting Nanodregg.Hosting.Resident
open Nanodregg.Lang.Contextual.Slot (Out Slot)

/-- A run suspended at each of the resident's effects: the free monad over `Eff`. -/
inductive Co (α : Type) where
  | done (a : α)
  | call (op : Eff) (k : Eff.Resp op → Co α)

def Co.bind {α β : Type} : Co α → (α → Co β) → Co β
  | .done a, f => f a
  | .call op k, f => .call op fun r => Co.bind (k r) f

instance : Monad Co where
  pure := .done
  bind := Co.bind

/-- The handler that performs nothing: every effect suspends the run. -/
def suspend : Handler Co where
  cmd c := .call (.cmd c) .done
  keep r t := .call (.keep r t) .done
  forget := .call .forget .done
  note l := .call (.note l) .done
  ask r q := .call (.ask r q) .done
  say s := .call (.say s) .done

abbrev Ended := Out (Ix := Unit) (fun _ => Hole) (fun _ => Tick) Empty

/-- The term run to its first hole: `Slot.interp` at depth 0, every effect suspended. -/
def toHole (p : Prog Tick) : Co Ended :=
  Lang.Contextual.Slot.interp (W := Empty) (fun op => suspend.call op) (fun hl => .ok (fill hl)) 0 p

structure Live where
  w : Where
  m : Mem
  /-- the tick in flight, waiting on an effect; none between ticks -/
  cur : Option (Co Ended) := none
  /-- holes filled in this tick -/
  holes : Nat := 0
  /-- the resident ended (`Tick.stop`); a new start is needed -/
  ended : Bool := false

initialize live : IO.Ref (Option Live) ← IO.mkRef none

def hx (b : ByteArray) : String := Lang.Print.hex b

/-- A ring as the page shows it: notBefore, ringer, text (hex), and the aim's `via` and target when
it has one. -/
def ringText (r : Ring) : String :=
  s!"{r.notBefore} {hx r.ringer} {hx r.text}" ++ match r.to with
    | some a => s!" via {hx a.via} target {hx a.target}"
    | none => ""

def actText : Act → String
  | .idle => "idle"
  | .ask r => s!"ask {ringText r}"
  | .answer r _ => s!"answer {ringText r}"

def serveFactText : ServeFact → String
  | .pending _ => "pending"
  | .stands _ => "stands"

def useCandText : UseCand → String
  | .closed => "closed"
  | .withdraw c => s!"withdraw {hx c}"
  | .stop => "stop"

def useFactText : UseFact → String
  | .left => "left"
  | .waits => "waits"
  | .gone c => s!"gone {hx c}"

def holdsWord (b : Bool) : String := if b then "holds" else "dead"
def usableWord (b : Bool) : String := if b then "usable" else "blocked"

/-- One candidate of a slot: its line, then each support it cites and whether it holds. -/
def candLines {F C : Type} (S : Slot F C) (holds : F → Bool) (cText : C → String) (fText : F → String)
    (c : C) : List String :=
  s!"cand {cText c} {usableWord (S.usable holds c)}" ::
    (S.evidence holds c).map fun (f, h) => s!"support {fText f} {holdsWord h}"

/-- What a hole shows when the run reaches it: the slot's candidates in the chooser's order, each
with its supports at the run's read, and the candidate `fill` takes. The serve slot is filled on the
memory with the withdrawn rings that left `pending` dropped, as `fill` fills it. -/
def holeView : Hole → List String
  | .serve _ _ m pending =>
    let m := m.prune pending
    ["hole serve"] ++ (serveOrder m pending).flatMap (candLines serveSlot (serveHolds m pending) actText serveFactText)
      ++ [s!"chose {actText (serveChoice m pending)}"]
  | .use _ _ ring _ line pending gone =>
    [s!"hole use {ringText ring} refused {hx line.toUTF8}"] ++
      (useOrder ring).flatMap (candLines useSlot (useHolds ring pending gone) useCandText useFactText)
      ++ [s!"chose {useCandText (useChoice ring pending gone)}"]

/-- The effect a run waits on, as one line: a command's argv in hex, the rest by name. -/
def opLine (w : Where) : Eff → String
  | .cmd c => "op cmd " ++ " ".intercalate ((c.argv w.conf).map hx)
  | .keep r t => s!"op keep {ringText r} {hx t}"
  | .forget => "op forget"
  | .note l => s!"op note {l.length}"
  | .ask r _ => s!"op ask {ringText r}"
  | .say s => s!"op say {hx s.toUTF8}"

def memLines (m : Mem) : List String :=
  (match m.kept with
   | some (r, t) => [s!"kept {ringText r} {hx t}"]
   | none => []) ++ m.withdrawn.map fun (r, c) => s!"withdrawn {ringText r} {c}"

/-- Run on from `co` until the next effect or the tick's end; at a hole, its view, then `fill`. -/
def advance : Nat → Live → List String → Co Ended → List String × Live
  | _, st, pre, .call op k => (pre ++ [opLine st.w op], { st with cur := some (.call op k) })
  | _, st, pre, .done (.done _ (.next m)) =>
    (pre ++ ["end next"] ++ memLines m, { st with m, cur := none, holes := 0 })
  | _, st, pre, .done (.done _ (.stop e d)) =>
    (pre ++ [s!"end stop {e.name} {d}"] ++ memLines st.m, { st with cur := none, holes := 0, ended := true })
  | 0, st, pre, .done (.bound _ _) =>
    (pre ++ ["end stop bellShape holes"], { st with cur := none, holes := 0, ended := true })
  | n + 1, st, pre, .done (.bound _ h) =>
    if st.holes < holesMax then advance n { st with holes := st.holes + 1 } (pre ++ holeView h) (toHole (fill h))
    else (pre ++ ["end stop bellShape holes"], { st with cur := none, holes := 0, ended := true })
  | _, _, _, .done (.withdrawn _ _ e) => nomatch e

def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 0x100 + b[i+2]!.toNat * 0x10000 + b[i+3]!.toNat * 0x1000000

def textOf (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

/-- The page's result for effect `op`, or why it does not read:
* a command: `1 EXIT(u32) OUTLEN(u32) STDOUT STDERR`, or `0 WHY` for a transport failure;
* keep, forget, note: one byte, 1 held;
* an ask: `0 TEXT` answered, `1 WHY` not sent, `2 WHY` lost;
* say: nothing. -/
def respOf : (op : Eff) → ByteArray → Option (Eff.Resp op)
  | .cmd _, b =>
    if b.size ≥ 9 ∧ b[0]! = 1 then
      let n := u32At b 5
      if 9 + n ≤ b.size then
        some (.ok { exit := u32At b 1, stdout := b.extract 9 (9 + n), stderr := b.extract (9 + n) b.size })
      else none
    else if b.size ≥ 1 ∧ b[0]! = 0 then some (.error (textOf (b.extract 1 b.size)))
    else none
  | .keep _ _, b | .forget, b | .note _, b => if b.size = 1 then some (b[0]! == 1) else none
  | .ask _ _, b =>
    if b.size = 0 then none else
    let rest := b.extract 1 b.size
    if b[0]! = 0 then some (.answered (.reply rest))
    else if b[0]! = 1 then some (.notSent (textOf rest))
    else if b[0]! = 2 then some (.lost (textOf rest))
    else none
  | .say _, _ => some ()

def okLines (ls : List String) : ByteArray :=
  Testground.reply Protocol.Status.ok.code (String.join (ls.map (· ++ "\n"))).toUTF8

@[export tg_res_start] def tgResStart (bell grant : ByteArray) : IO ByteArray := do
  if bell.size ≠ 32 ∨ grant.size ≠ 32 then return Testground.refusedText "badId"
  let conf : Conf := { bell, grant, maxTokens := 0, model := "scripted".toUTF8, system := ByteArray.empty }
  let w : Where := { conf, member := "tab", broker := "tab", vol := "tab", kept := "tab/kept", noted := "tab/withdrawn" }
  live.set (some { w, m := { shape := none, kept := none } })
  return okLines [s!"serving bell {hx bell}"]

@[export tg_res_tick] def tgResTick (_ : Unit) : IO ByteArray := do
  let some st ← live.get | return Testground.refusedText "noResident"
  if st.ended then return Testground.refusedText "ended"
  if st.cur.isSome then return Testground.refusedText "busy"
  let (ls, st) := advance (holesMax + 1) st [] (toHole (tickP st.w st.m))
  live.set (some st)
  return okLines ls

@[export tg_res_answer] def tgResAnswer (b : ByteArray) : IO ByteArray := do
  let some st ← live.get | return Testground.refusedText "noResident"
  let some (.call op k) := st.cur | return Testground.refusedText "notWaiting"
  let some r := respOf op b | return Testground.refusedText "badResult"
  let (ls, st) := advance (holesMax + 1 - st.holes) st [] (k r)
  live.set (some st)
  return okLines ls

end Nanodregg.Web.Sim.Resident
