/-
# Kernel.Proofs.InvokeWitness — a signed invoke of a programmed object, derived, admitted, run again

`invoke_next_slots`, `invoke_next_run` and `invoke_next_judged` (`Kernel.Proofs.InvokeNext`) take a
`receive` that derived an invoke, a `World.admit` that admitted it and a run of the object's program.
This module shows those premises hold together, on a concrete instance, through the real language
(`Lang.program`) and the real derivation: the theorems are not true of an empty premise.

The instance. A toy `Env` over one-byte digests (the hash is its input's first byte; Poseidon2 and
cSHAKE are out of the kernel evaluator's reach), every signature accepted, a call's bytes its window
end. The `Ctx`'s program is `Lang.program` itself, at the toy digest's bytes and decoder. The World
holds three cells: member 7 (key `42`), package 9 (`counter`: state `{n : nat}`, method `bump n a`
returning `n + a`, law `cap`: the new `n` is at most 100) and object 5 (package 9, owner 7, `n = 3`). The
call: member 7 invokes method 0 (`bump`) of object 5 with argument 4, pinning all three cells. It
derives a write of `n = 7`, `World.admit` takes it, and a second call invoking `bump 2` on the
admitted World runs on `n = 7` and returns `n = 9`.

The kernel never evaluates the package decoder or `Lang.load` (both well-founded recursion:
`decide +kernel` on the decode of the empty package is stuck, measured). They enter through their
equations (`Lang.Wire.decodePackage_eq_ok_iff`, `load`'s and `loadAll`'s unfoldings); every other
step of both derivations, both runs, the law and both admissions is evaluated by the kernel. The
encoder is evaluated once (`counter_encodes`, about 20 s of the module's ~25 s); the package cell's
reads are closed by definitional unfolding, never by comparing its bytes.

Toy, and only toy: the hash, so a pin binds nothing here, and `verify`. The program, the
derivation, the sealing and the admission are the deployed definitions.

`w0` is built by hand and is not reachable from a genesis: package 9's id is not its content hash,
the cell ids are not derived from a transaction, and the chain starts at 0. The theorems witnessed
carry no reachability premise, so none is needed here.
-/
import Kernel.Proofs.InvokeNext
import Lang.Program
import Lang.Std
import Lang.Proofs.Wire

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Lang

/-! ## Assembling a derivation from its steps -/

/-- `x` succeeded with `a`, as a Boolean the kernel evaluates (a `Refusal` has no `DecidableEq`). -/
private def isOkAs {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok b, a => decide (b = a)
  | .error _, _ => false

private theorem of_isOkAs {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : isOkAs x a = true) : x = .ok a := by
  cases x with
  | ok b => simp only [isOkAs, decide_eq_true_eq] at h; rw [h]
  | error _ => cases h

/-- A run's result is `(s, [], [], used)`, as a Boolean the kernel evaluates. -/
private def runIs {ε D : Type} (x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat))
    (s : Slots) (used : Nat) : Bool :=
  match x with
  | .ok (s', [], [], u) => decide (s' = s) && decide (u = used)
  | _ => false

private theorem of_runIs {ε D : Type} {x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat)}
    {s : Slots} {used : Nat} (h : runIs x s used = true) : x = .ok (s, [], [], used) := by
  unfold runIs at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, h.2]
  · cases h

section
variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] in
/-- `invoke` from its steps: the cell read, the run, its ticks, the state's form, the laws, the
judgement, no calls returned. -/
private theorem invoke_of {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {cell : Cell} {p : D} {r : Req D} {new : Slots} {used : Nat} {laws : List D}
    (hv : obj ∉ wk.visited)
    (hr : invokeRun X look c actor obj method via = .ok (cell, p, r))
    (hp : X.program.run look rv p (stateOf cell) method args r (min budget wk.pool) = .ok (new, [], [], used))
    (hu : used ≤ min budget wk.pool) (hs : checkState (D := D) new = .ok ())
    (hl : lawsOf X obj cell = .ok laws) (hj : X.program.judge look (some p) laws (stateOf cell) new r = .ok ()) :
    invoke X look rv c sub wk actor obj method args budget via =
      .ok (⟨[], writeOf obj (diffOps (stateOf cell) new), [], []⟩,
        { wk with visited := obj :: wk.visited, pool := wk.pool - used }) := by
  unfold invoke
  have h0 : req (!wk.visited.contains obj) (Refusal.revisited obj) = (Except.ok () : Except (Refusal D) Unit) := by
    simp [req, hv]
  simp only [h0, hr, hp, hs, hl, hj, bind, Except.bind]
  simp only [req, decide_eq_true hu, forEx, deriveCalls, List.foldlM_nil]
  rfl

/-- `receive` of a signed invoke from its steps: the World, the signature, the member's key, and the
invoke's Draft, sealed. -/
private theorem receive_of {X : Ctx D} {w : World D} {c : Call D} {obj : D} {method : Nat}
    {args : ByteArray} {budget : Nat} {via : Option D} {d : Draft D} {wk : Walk D}
    (hw : c.unsigned.world = w.origin) (hs : checkSignature X c = .ok ())
    (hk : checkKey (pinned X.env w c.unsigned.pins) c.unsigned = .ok ())
    (hb : c.unsigned.body = .invoke obj method args budget via)
    (hi : invoke X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member obj method args budget via = .ok (d, wk)) :
    receive X w c = sealTurn X c d.creates d.effects d.nullifiers d.rows := by
  have h0 : req (decide (c.unsigned.world = w.origin)) Refusal.wrongWorld =
      (Except.ok () : Except (Refusal D) Unit) := by simp [req, hw]
  have hk' : keyRule (pinned X.env w c.unsigned.pins) c.unsigned = .ok () := by
    unfold keyRule; rw [hb]; exact hk
  have hd : derive X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c = .ok d := by
    unfold derive; rw [hb] at hi ⊢; simp only [dispatch, hi, Except.map]
  unfold receive receiveWith deriveTurn
  simp only [h0, hs, hk', hd, bind, Except.bind]

end

/-! ## The instance -/

private def wEnv : Env UInt8 where
  hash _ b := b.data.getD 0 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def wDigestOf (b : ByteArray) : Option UInt8 := if b.size = 1 then some (b.data.getD 0 0) else none

private def wCtx : Ctx UInt8 where
  env := wEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := ⟨#[UInt8.ofNat c.unsigned.validUntil]⟩
  decodeCall _ := none
  digestOf := wDigestOf
  verify _ _ _ := true
  program := Lang.program wEnv.bytes wDigestOf

private def cS : Ty := .record [("n", .nat)]

/-- `bump`: `λ rows n a req. {calls = {}, edits = {}, state = {n = n.n + a}}`; `cap`: `λ old new req.
if new.n ≤ 100 then ok else refused`. -/
private def counter : Package :=
  { imports := [], state := cS,
    iface := .record [("bump", methodTy cS .nat), ("cap", lawTy cS)],
    body := .record [("bump", Std.methodOf cS .nat [("n", .prim .add (.get (.var 2) "n") (.var 1))]),
                     ("cap", .lam cS (.lam cS (.lam reqTy
                       (.ite (.prim .le (.get (.var 1) "n") (.nat 100)) Std.okT (Std.refusedT "n over 100")))))],
    methods := ["bump"], laws := ["cap"] }

/-- `counter`'s canonical bytes (`counter_encodes`). -/
private def pkgBytes : ByteArray := (Wire.encodePackage counter).getD .empty
private def natBytes (n : Nat) : ByteArray := (Wire.encodeData .nat (.nat n)).getD .empty

private theorem counter_encodes : Wire.encodePackage counter = some pkgBytes := by
  have h : (Wire.encodePackage counter).isSome = true := by decide +kernel
  unfold pkgBytes
  cases he : Wire.encodePackage counter with
  | none => rw [he] at h; cases h
  | some b => rfl

private def memberCell : Cell := { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩)] }
private def pkgCell : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, pkgBytes)] }
private def objCell : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := [(slotPackage, ⟨#[9]⟩), (slotOwner, ⟨#[7]⟩), (stateBase, natBytes 3)] }

private def w0 : World UInt8 :=
  let t := Trie.T.empty.insert (trieSpec wEnv) (.cell 5) (.entry (.live objCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 7) (.entry (.live memberCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 9) (.entry (.live pkgCell 0))
  { trie := t, journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

/-- The three cells, pinned at what `w` holds. -/
private def pinsAt (w : World UInt8) : List (UInt8 × UInt8) :=
  [5, 7, 9].map fun c => (c, pinOf wEnv (w.entry wEnv c))

private def wUnsigned (w : World UInt8) (vu arg : Nat) : Unsigned UInt8 :=
  { world := 0
    member := 7
    key := ⟨#[42]⟩
    notBefore := 1
    validUntil := vu
    pins := pinsAt w
    maxCharge := 100000
    body := .invoke 5 0 (natBytes arg) 1000 none }

/-- Member 7 invokes `bump arg` on object 5, on `w`'s pins, window `[1, vu]`. -/
private def wCall (w : World UInt8) (vu arg : Nat) : Call UInt8 :=
  { unsigned := wUnsigned w vu arg, signature := ByteArray.empty }

/-! ## The language's steps, through their equations -/

private theorem readPackage_counter {look : Pinned UInt8} (h : readKind look 9 kindPackage = .ok pkgCell) :
    Lang.readPackage look 9 = .ok counter := by
  have hd : Wire.decodePackage pkgBytes = .ok counter := Wire.decodePackage_eq_ok_iff.mpr counter_encodes
  have hs : pkgCell.slots.get 0 = some pkgBytes := rfl
  unfold Lang.readPackage
  rw [h]
  simp only [bind, Except.bind, hs, hd]
  rfl

private theorem load_counter {look : Pinned UInt8} (h : readKind look 9 kindPackage = .ok pkgCell) :
    Lang.load wDigestOf look closureDepthMax (wEnv.bytes 9) ⟨[], [], []⟩ =
      admitPackage wDigestOf (wEnv.bytes 9) counter ⟨[], [], []⟩ [] := by
  rw [Lang.load.eq_def]
  simp only [indexIn, closureDepthMax]
  rw [show idOf wDigestOf (wEnv.bytes 9) = .ok 9 from rfl]
  simp only [readPackage_counter h, show counter.imports = [] from rfl]
  rw [Lang.loadAll.eq_def]

/-! ## The first call, on `w0` -/

private def c1 : Call UInt8 := wCall w0 5 4
private def req1 : Req UInt8 := reqOf c1.unsigned 5 7 (.invoke 0)
/-- What `bump 4` returns on `n = 3`. -/
private def s1 : Slots := [(stateBase, natBytes 7)]

private def dummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty }

private def t1 : Turn UInt8 :=
  ((sealTurn wCtx c1 [] (writeOf 5 (diffOps (stateOf objCell) s1)) [] []).toOption).getD dummy

private def w1 : World UInt8 := ((World.admit wEnv w0 t1).toOption).getD w0

private theorem c1_pkg : readKind (pinned wCtx.env w0 c1.unsigned.pins) 9 kindPackage = .ok pkgCell := by
  rfl

private theorem c1_invokeRun :
    invokeRun wCtx (pinned wCtx.env w0 c1.unsigned.pins) c1 c1.unsigned.member 5 0 none = .ok (objCell, 9, req1) :=
  of_isOkAs (by decide +kernel)

private theorem c1_run :
    wCtx.program.run (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) 9 (stateOf objCell)
      0 (natBytes 4) req1 (min 1000 (poolOf c1.unsigned.body)) = .ok (s1, [], [], 41) := by
  show (runMeasured wEnv.bytes wDigestOf _ _ _ _ _ _ _ _).map _ = _
  unfold runMeasured runSetup
  rw [load_counter c1_pkg]
  exact of_runIs (by decide +kernel)

private theorem c1_judgeOne :
    judgeOne wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) 9 (stateOf objCell) s1 req1 = .ok () := by
  unfold judgeOne
  rw [load_counter c1_pkg]
  exact of_isOkAs (by decide +kernel)

private theorem c1_judge :
    wCtx.program.judge (pinned wCtx.env w0 c1.unsigned.pins) (some 9) [] (stateOf objCell) s1 req1 = .ok () := by
  show Nanodregg.Lang.judge wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) (some 9) [] (stateOf objCell)
    s1 req1 = .ok ()
  unfold Nanodregg.Lang.judge
  simp only [c1_judgeOne]
  rfl

private theorem c1_receive : receive wCtx w0 c1 = .ok t1 := by
  rw [receive_of rfl (of_isOkAs (by decide +kernel)) (of_isOkAs (by decide +kernel)) rfl
    (invoke_of (by decide) c1_invokeRun c1_run (by decide) (of_isOkAs (by decide +kernel))
      (of_isOkAs (by decide +kernel)) c1_judge)]
  exact of_isOkAs (by decide +kernel)

private theorem c1_admit : World.admit wCtx.env w0 t1 = .ok w1 := by
  have h : (World.admit wEnv w0 t1).isOk = true := by decide +kernel
  show World.admit wEnv w0 t1 = Except.ok (((World.admit wEnv w0 t1).toOption).getD w0)
  cases hf : World.admit wEnv w0 t1 with
  | error e => rw [hf] at h; cases h
  | ok w' => rfl

/-! ## The second call, on `w1` -/

private def c2 : Call UInt8 := wCall w1 6 2
/-- Object 5 as `w1` holds it. -/
private def cell2 : Cell := (w1.live wEnv 5).getD objCell
private def req2 : Req UInt8 := reqOf c2.unsigned 5 7 (.invoke 0)
/-- What `bump 2` returns on `n = 7`. -/
private def s2 : Slots := [(stateBase, natBytes 9)]

private def t2 : Turn UInt8 :=
  ((sealTurn wCtx c2 [] (writeOf 5 (diffOps (stateOf cell2) s2)) [] []).toOption).getD dummy

private def w2 : World UInt8 := ((World.admit wEnv w1 t2).toOption).getD w1

private theorem c2_pkg : readKind (pinned wCtx.env w1 c2.unsigned.pins) 9 kindPackage = .ok pkgCell := by
  rfl

private theorem c2_invokeRun :
    invokeRun wCtx (pinned wCtx.env w1 c2.unsigned.pins) c2 c2.unsigned.member 5 0 none = .ok (cell2, 9, req2) :=
  of_isOkAs (by decide +kernel)

private theorem c2_run :
    wCtx.program.run (pinned wCtx.env w1 c2.unsigned.pins) (rowView wCtx.env w1 c2.unsigned) 9 (stateOf cell2)
      0 (natBytes 2) req2 (min 1000 (poolOf c2.unsigned.body)) = .ok (s2, [], [], 41) := by
  show (runMeasured wEnv.bytes wDigestOf _ _ _ _ _ _ _ _).map _ = _
  unfold runMeasured runSetup
  rw [load_counter c2_pkg]
  exact of_runIs (by decide +kernel)

private theorem c2_judgeOne :
    judgeOne wEnv.bytes wDigestOf (pinned wCtx.env w1 c2.unsigned.pins) 9 (stateOf cell2) s2 req2 = .ok () := by
  unfold judgeOne
  rw [load_counter c2_pkg]
  exact of_isOkAs (by decide +kernel)

private theorem c2_judge :
    wCtx.program.judge (pinned wCtx.env w1 c2.unsigned.pins) (some 9) [] (stateOf cell2) s2 req2 = .ok () := by
  show Nanodregg.Lang.judge wEnv.bytes wDigestOf (pinned wCtx.env w1 c2.unsigned.pins) (some 9) [] (stateOf cell2)
    s2 req2 = .ok ()
  unfold Nanodregg.Lang.judge
  simp only [c2_judgeOne]
  rfl

private theorem c2_receive : receive wCtx w1 c2 = .ok t2 := by
  rw [receive_of rfl (of_isOkAs (by decide +kernel)) (of_isOkAs (by decide +kernel)) rfl
    (invoke_of (by decide +kernel) c2_invokeRun c2_run (by decide) (of_isOkAs (by decide +kernel))
      (of_isOkAs (by decide +kernel)) c2_judge)]
  exact of_isOkAs (by decide +kernel)

private theorem c2_admit : World.admit wCtx.env w1 t2 = .ok w2 := by
  have h : (World.admit wEnv w1 t2).isOk = true := by decide +kernel
  show World.admit wEnv w1 t2 = Except.ok (((World.admit wEnv w1 t2).toOption).getD w1)
  cases hf : World.admit wEnv w1 t2 with
  | error e => rw [hf] at h; cases h
  | ok w' => rfl

/-! ## The premises, witnessed -/

/-- **The premises of `invoke_next_slots` (and `invoke_next_judged`, whose premises are the same)
hold together**, through `Lang.program`: a `Ctx` whose program IS the language at its digest's
bytes and decoder, a World, and a signed call whose body invokes a programmed object, which
`receive` derives and `World.admit` admits, whose `invokeRun` reads the object and whose run returns
a state other than the one it ran on (so the admitted act is a write, not a keep). -/
theorem invoke_next_slots_witnessed :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (c : Call UInt8) (t : Turn UInt8) (obj : UInt8) (method : Nat)
      (args : ByteArray) (budget : Nat) (via : Option UInt8) (cell : Cell) (p : UInt8) (r : Req UInt8)
      (s : Slots) (calls : List (Body UInt8)) (rows : List (RowSlot UInt8 × RowAct)) (used : Nat),
      X.program = Lang.program X.env.bytes X.digestOf ∧
      receive X w c = .ok t ∧ World.admit X.env w t = .ok w' ∧
      c.unsigned.body = .invoke obj method args budget via ∧
      invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used) ∧
      s ≠ stateOf cell :=
  ⟨wCtx, w0, w1, c1, t1, 5, 0, natBytes 4, 1000, none, objCell, 9, req1, s1, [], [], 41,
    rfl, c1_receive, c1_admit, rfl, c1_invokeRun, c1_run, by decide +kernel⟩

/-- **The premises of `invoke_next_run` hold together, and the next invoke is itself a signed call
derived and admitted**: on the instance of `invoke_next_slots_witnessed`, a second call `c'` of the
same member invokes the same object on `w'` through its own pins (`pins'` are `c'`'s), `receive`
derives it and `World.admit` admits it; its `invokeRun` reads the cell `w'` holds, and its run, on
the state the first run returned, returns yet another. -/
theorem invoke_next_run_witnessed :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (c : Call UInt8) (t : Turn UInt8) (obj : UInt8) (method : Nat)
      (args : ByteArray) (budget : Nat) (via : Option UInt8) (cell : Cell) (p : UInt8) (r : Req UInt8)
      (s : Slots) (calls : List (Body UInt8)) (rows : List (RowSlot UInt8 × RowAct)) (used : Nat)
      (pins' : List (UInt8 × UInt8)) (c' : Call UInt8) (actor' : UInt8) (method' : Nat) (via' : Option UInt8)
      (cell' : Cell) (p' : UInt8) (r' : Req UInt8)
      (args' : ByteArray) (budget' : Nat) (t' : Turn UInt8) (w'' : World UInt8)
      (s' : Slots) (calls' : List (Body UInt8)) (rows' : List (RowSlot UInt8 × RowAct)) (used' : Nat),
      X.program = Lang.program X.env.bytes X.digestOf ∧
      receive X w c = .ok t ∧ World.admit X.env w t = .ok w' ∧
      c.unsigned.body = .invoke obj method args budget via ∧
      invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used) ∧
      invokeRun X (pinned X.env w' pins') c' actor' obj method' via' = .ok (cell', p', r') ∧
      c'.unsigned.pins = pins' ∧ c'.unsigned.member = actor' ∧
      c'.unsigned.body = .invoke obj method' args' budget' via' ∧
      receive X w' c' = .ok t' ∧ World.admit X.env w' t' = .ok w'' ∧
      X.program.run (pinned X.env w' pins') (rowView X.env w' c'.unsigned) p' (stateOf cell')
        method' args' r' (min budget' (poolOf c'.unsigned.body)) = .ok (s', calls', rows', used') ∧
      s ≠ stateOf cell ∧ s' ≠ s :=
  ⟨wCtx, w0, w1, c1, t1, 5, 0, natBytes 4, 1000, none, objCell, 9, req1, s1, [], [], 41,
    c2.unsigned.pins, c2, 7, 0, none, cell2, 9, req2, natBytes 2, 1000, t2, w2, s2, [], [], 41,
    rfl, c1_receive, c1_admit, rfl, c1_invokeRun, c1_run, c2_invokeRun, rfl, rfl, rfl, c2_receive, c2_admit,
    c2_run, by decide +kernel, by decide +kernel⟩

end Nanodregg.Kernel.Receive
