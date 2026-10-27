/-
# Web.Sim.Teach — what the testground's teaching windows ask the kernel

The page's object inspector, package editor, term REPL and Turn view (CLIENT-50) show the language;
every answer here is the language's own function, never a second implementation:

* `tg_ob TEXT` — `Lang.Resident.run`: the resident's checker (`(check P)` names the line a surface
  refusal is about, `(core P)` the core text a surface package lowers to, `(type T)`, `(eval TICKS
  T)` the value and the ticks it used, `(law P LABEL OLD NEW REQ)` one law judging one change).
* `tg_grammar WHICH` — the grammar a window shows: `core` (`Lang.Read.grammar`, what a term and a
  core package are) or `surface` (`Lang.Surface.grammar`, what a package source is).
* `tg_source I PKG` — package `PKG` as member `I`'s follow holds it, printed by `Lang.Print.package`
  (the core text `install` reads back to the same package).
* `tg_grants I OBJ` — the live grants on `OBJ` in member `I`'s follow World: one line each.
* `tg_turn I TX` — the step with transaction id `TX`, re-derived on the World member `I`'s follow
  absorbed it onto (`Testground.Member.seen`): who, the ticks, the call, every pin and what was done
  to it, the state of each touched object before and after, the calls the run returned (each invoke
  re-run on the same pinned view, as `deriveCalls` runs it), or the refusal's name and reason.

Tooling, like `Web.Sim.Testground`: no deployed module imports it.
-/
import Web.Sim.Testground
import Lang.Resident

namespace Nanodregg.Web.Sim.Teach

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Host
open Nanodregg.Web.Sim.Testground

def okText (s : String) : ByteArray := reply Protocol.Status.ok.code s.toUTF8

/-- One `ob` form: the resident's answer line, `ok ‖ LINE` or `refused ‖ LINE` (its `refused` word
dropped: the status says it). -/
@[export tg_ob] def tgOb (text : ByteArray) : ByteArray :=
  match String.fromUTF8? text with
  | none => refusedText "notUtf8"
  | some t =>
    let a := Lang.Resident.run t
    if a.refused then reply Protocol.Status.refused.code (String.ofList (a.line.toList.drop "refused ".length)).toUTF8
    else okText a.line

@[export tg_grammar] def tgGrammar (which : ByteArray) : ByteArray :=
  match String.fromUTF8? which with
  | some "core" => okText Lang.Read.grammar
  | some "surface" => okText Lang.Surface.grammar
  | _ => refusedText "noGrammar"

/-- A digest from its hex text. -/
def digestOfHex (b : ByteArray) : Option D := (String.fromUTF8? b) >>= Text.ofHex >>= P.X.digestOf

def memberWorld (i : UInt32) : IO (Except ByteArray (Member)) := do
  let some g ← ground.get | return .error (refusedText "noWorld")
  let some m := g.members[i.toNat]? | return .error (refusedText "noMember")
  return .ok m

@[export tg_source] def tgSource (i : UInt32) (pkg : ByteArray) : IO ByteArray := do
  match ← memberWorld i with
  | .error r => return r
  | .ok m =>
    let some p := digestOfHex pkg | return refusedText "badId"
    match Lang.readPackage (Command.worldLook P.X.env m.follow.world) p with
    | .error r => return refusedText r.name
    | .ok pk => match Lang.Print.package pk with
      | some t => return okText t
      | none => return refusedText "noText"

/-! ## Grants -/

/-- A grant cell's rights, read from its slot keys (`rightKey`, `rightSlots`): the uncounted rights
by key, a counted right with the count it was granted (its ledger's slot 0). -/
def rightsOf (c : Cell) : List String :=
  c.slots.filterMap fun (k, v) =>
    if k = rightKey .observe then some "observe"
    else if k = rightKey .mutate then some "mutate"
    else if k ≥ invokeBase then some s!"invoke:{k - invokeBase}"
    else if k = enrollBase then some s!"enroll:{(countOf v).getD 0}"
    else if k = transferBase then some s!"transfer:{(countOf v).getD 0}"
    else if k = creditBase then some s!"credit:{(countOf v).getD 0}"
    else none

def slotHex (c : Cell) (k : Nat) : String := ((c.slots.get k).map Text.toHex).getD "-"

/-- `grant ID grantee HEX|anyone issuer HEX [parent HEX] rights R,…` for every live grant on OBJ. -/
@[export tg_grants] def tgGrants (i : UInt32) (obj : ByteArray) : IO ByteArray := do
  match ← memberWorld i with
  | .error r => return r
  | .ok m =>
    let some o := digestOfHex obj | return refusedText "badId"
    let ob := P.X.env.bytes o
    let anyone := P.X.env.bytes (worldId P.X)
    let lines := m.follow.world.trie.toList.filterMap fun (s, l) => match s, l with
      | .cell id, .entry (.live c _) =>
        if c.kind = kindGrant && c.slots.get grantTarget == some ob then
          let grantee := if c.slots.get grantGrantee == some anyone then "anyone" else slotHex c grantGrantee
          let parent := match c.slots.get grantParent with
            | some p => s!" parent {Text.toHex p}"
            | none => ""
          some s!"grant {hexOf id} grantee {grantee} issuer {slotHex c grantIssuer}{parent} rights {",".intercalate (rightsOf c)}"
        else none
      | _, _ => none
    return okText (String.join (lines.map (· ++ "\n")))

/-! ## The Turn view -/

def actText : Kernel.Act → String
  | .keep => "keep"
  | .retire => "retire"
  | .write ops => "write " ++ " ".intercalate (ops.map fun
      | .set k _ => s!"set:{k - stateBase}"
      | .erase k => s!"erase:{k - stateBase}")

def rowActText : RowAct → String
  | .keep => "keep" | .insert _ _ => "insert" | .upsert _ _ => "upsert" | .retract => "retract"
  | .declare limit _ _ _ => s!"declare limit {limit}"

def rowSlotText : RowSlot D → String
  | .head p r => s!"{hexOf p} rel {r} head"
  | .row k => s!"{hexOf k.parent} rel {k.rel} key {Text.toHex k.k}"

/-- The verb of a call body and what it names. -/
def bodyText : Body D → String
  | .enroll _ _ _ via => s!"enroll via {hexOf via}"
  | .rotate _ _ => "rotate"
  | .install pkg => s!"install {pkg.size} bytes"
  | .create pkg laws state => s!"create {(pkg.map hexOf).getD "data"} laws {laws.length} slots {state.length}"
  | .write obj edits _ => s!"write {hexOf obj} slots {",".intercalate (edits.map fun (k, _) => toString k)}"
  | .law obj laws _ => s!"law {hexOf obj} laws {laws.length}"
  | .invoke obj m _ budget _ => s!"invoke {hexOf obj} method {m} budget {budget}"
  | .grant t g rights _ => s!"grant {hexOf t} to {hexOf g} rights {rights.length}"
  | .revoke g => s!"revoke {hexOf g}"
  | .issue cap => s!"issue cap {cap}"
  | .account a o => s!"account {hexOf a} owner {hexOf o}"
  | .transfer _ _ amount _ _ => s!"transfer {amount}"
  | .credit w _ amount _ => s!"credit {hexOf w} {amount}"

/-- An invoke's arguments as text, at the method's argument type (`Lang.resolveMethod`), with its label. -/
def argsText (look : Pinned D) (obj : D) (m : Nat) (args : ByteArray) : String :=
  match look obj with
  | .ok (some cell) =>
    match packageOf P.X obj cell with
    | .ok (some p) =>
      match Lang.readPackage look p with
      | .ok pk => match Lang.resolveMethod (D := D) pk m with
        | .ok (ℓ, sg) => match Lang.Wire.decodeData sg.arg args with
          | .ok d => s!"{ℓ} {(Lang.Print.data d).getD s!"({args.size} bytes)"}"
          | .error _ => s!"{ℓ} ({args.size} bytes)"
        | .error _ => s!"({args.size} bytes)"
      | .error _ => s!"({args.size} bytes)"
    | _ => s!"({args.size} bytes)"
  | _ => s!"({args.size} bytes)"

/-- The calls an invoke's run returned, depth first, each invoke re-run on the same pinned view as
`deriveCalls` derives it (the actor of a call is the calling object, KERNEL-28 (b)); `d` bounds the
depth. Each line: `call DEPTH VERB …`, and for an invoke, its method's label, its arguments and the
ticks its run used. -/
def callLines (look : Pinned D) (rv : RowView D) (c : Call D) : Nat → Nat → D → D → Nat → ByteArray → Nat → Option D → List String
  | 0, _, _, _, _, _, _, _ => []
  | d + 1, depth, actor, obj, m, args, fuel, via =>
    match invokeRun P.X look c actor obj m via with
    | .error r => [s!"call {depth} refused {r.name}"]
    | .ok (cell, p, r) =>
      match P.X.program.run look rv p (stateOf cell) m args r fuel with
      | .error e => [s!"call {depth} refused {e.name}"]
      | .ok (_, calls, rows, used) =>
        s!"run {depth} {hexOf obj} method {m} {argsText look obj m args} ticks {used} row-edits {rows.length}" ::
          calls.flatMap fun b => match b with
            | .invoke o m' a budget v =>
              s!"call {depth + 1} {bodyText b}" :: callLines look rv c d (depth + 1) obj o m' a (min budget (fuel - used)) v
            | _ => [s!"call {depth + 1} {bodyText b}"]

/-- A refusal's reason (`lawDenied` and `program` carry LANG's words). -/
def refusalText : Refusal D → String
  | .lawDenied l why => s!"lawDenied law {hexOf l} {Command.oneLine why}"
  | .program why => s!"program {Command.oneLine why}"
  | r => r.name

/-- The state of `obj` on `w` as `read OBJ` prints it, on one line. -/
def stateLine (w : World D) (obj : D) : String :=
  match World.live P.X.env w obj with
  | none => "(none)"
  | some cell => match cell.kind == kindObject, Command.readText P.X w obj cell with
    | true, .ok t => Command.oneLine t
    | _, _ => "-"

/-- The lines of one step re-derived on `w`, the World before it. -/
def stepLines (w : World D) (s : Kernel.Step D) : List String :=
  let callOf (b : ByteArray) : Option (Call D) := P.X.decodeCall b
  match s with
  | .turn t =>
    let w' : World D := (rederiveStep P.X w s).toOption.getD w
    let head : List String := [s!"step turn", s!"tx {hexOf t.txId}", s!"height {w.height} -> {w'.height}", s!"member {hexOf t.member}",
      s!"ticks {t.ticks}", s!"charge {t.charge}", s!"window {t.notBefore}..{t.validUntil}"]
    let body : List String := match callOf t.event with
      | some c => [s!"call {bodyText c.unsigned.body}"] ++ match c.unsigned.body with
        | .invoke obj m args budget via =>
          let look := pinned P.X.env w c.unsigned.pins
          let rv := rowView P.X.env w c.unsigned
          [s!"args {argsText look obj m args}"] ++ callLines look rv c 4 0 c.unsigned.member obj m args budget via
        | _ => []
      | none => ["call (undecodable)"]
    let pins := t.touches.map fun x => s!"pin {hexOf x.cell} seen {hexOf x.seen} {actText x.act}"
    let writes := t.touches.filterMap fun x => match x.act with
      | .write _ => some s!"state {hexOf x.cell} before {stateLine w x.cell} after {stateLine w' x.cell}"
      | _ => none
    let creates := t.creates.map fun ((id, c) : D × Cell) => s!"create {hexOf id} kind {c.kind}"
    let rows := t.rows.map fun r => s!"row {rowSlotText r.slot} {rowActText r.act}"
    let ranges := t.ranges.map fun q => s!"range {hexOf q.parent} rel {q.rel} prefix {Text.toHex q.pre} most {q.most}"
    head ++ body ++ pins ++ writes ++ creates ++ rows ++ ranges
  | .refusal r =>
    let head : List String := [s!"step refusal", s!"tx {hexOf r.txId}", s!"height {w.height}", s!"member {hexOf r.member}",
      s!"code {r.code} {(codeName r.code).getD "?"}", s!"window {r.notBefore}..{r.validUntil}"]
    let why : List String := if r.cancel.size > 0 then ["cancel signed by the member"] else match callOf r.event with
      | none => ["call (undecodable)"]
      | some c =>
        let look := pinned P.X.env w c.unsigned.pins
        [s!"call {bodyText c.unsigned.body}"] ++
        match deriveTurn P.X look (rowView P.X.env w c.unsigned) c with
        | .error e => [s!"refusal {refusalText e}"]
        | .ok t => match World.admit P.X.env w t with
          | .error rj => [s!"refusal {rj.name} (at admission)"]
          | .ok _ => ["refusal (re-derives as admitted on this World)"]
    head ++ why

def txOf : Kernel.Step D → D
  | .turn t => t.txId
  | .refusal r => r.txId

/-- The step `TX` (hex) as member `I`'s follow absorbed it: re-derived along its batch from the World
the batch was absorbed onto, then `stepLines`. -/
@[export tg_turn] def tgTurn (i : UInt32) (tx : ByteArray) : IO ByteArray := do
  match ← memberWorld i with
  | .error r => return r
  | .ok m =>
    let some x := digestOfHex tx | return refusedText "badId"
    let some (w0, ss) := m.seen.reverse.find? (fun (_, ss) => ss.any (txOf · = x)) | return refusedText "notSeen"
    let rec walk (w : World D) : List (Kernel.Step D) → Except String (List String)
      | [] => .error "notSeen"
      | s :: rest =>
        if txOf s = x then .ok (stepLines w s) else
        match rederiveStep P.X w s with
        | .ok w' => walk w' rest
        | .error v => .error s!"rederive {v.name}"
    match walk w0 ss with
    | .ok ls => return okText (String.join (ls.map (· ++ "\n")))
    | .error e => return refusedText e

end Nanodregg.Web.Sim.Teach
