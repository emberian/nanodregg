/-
# Kernel.Proofs.InvokeTreeWitness — an object invoked by another object's run, derived, admitted, run again

`invoke_tree_slots` and `invoke_tree_run` (`Kernel.Proofs.InvokeTree`) take a `receive`, a
`World.admit` and `Dispatched`: the call's walk dispatched an invoke of the object. This module shows
those premises hold together on an instance where the object is NOT the signed call's: it is invoked
by another object's run, through `tree`, with the real language (`Lang.program`) running both. Tooth
`dispatched_pins_args`: the walk's record names the arguments it ran with; the same invoke with
other arguments is not dispatched (its run returns a state the World does not hold).

The instance. The toy `Env` and `Ctx` of `Kernel.Proofs.InvokeWitness` (one-byte digests, the hash an
input's first byte, every signature accepted, `program := Lang.program`). The World holds member 7
(key `42`), two packages, `counter` (9: state `{n : nat}`, method `bump n a = n + a`, law `cap`:
`n ≤ 100`) and `relay` (10: state `{m : nat}`, method `go`, which returns ONE call, `invoke 5 bump 4`,
and `m + 1`), object A = 6 (package `relay`, owner member 7, `m = 0`) and object B = 5 (package
`counter`, owner A, `n = 3`). The signed call: member 7 invokes `go` on A, pinning all five cells.
A's run (59 ticks) returns the call; the tree derives it AS A (KERNEL-28 (b)), whose authority over B
is ownership; B's run (41 ticks, from the pool A left) returns `n = 7`; the Turn carries both writes;
`World.admit` takes it. Then an `invokeRun` of B on the admitted World, as A, reads `n = 7`.

As in `InvokeWitness`: the package decoder and `Lang.load` enter through their equations, the two
encoders are evaluated once each, and every other step (both runs, the law, the derivation of the
call under `tree`, the sealing, the admission) is evaluated by the kernel. `w0` is built by hand and
is not reachable from a genesis (the package ids are not content hashes, the cell ids are not
transaction-derived, the chain starts at 0); the theorems witnessed carry no reachability premise.
-/
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.InvokeWitness
import Lang.Program
import Lang.Std
import Lang.Proofs.Wire

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Lang

/-- `x` succeeded with `a`, as a Boolean the kernel evaluates (a `Refusal` has no `DecidableEq`). -/
private def isOkAs {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok b, a => decide (b = a)
  | .error _, _ => false

private theorem of_isOkAs {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : isOkAs x a = true) : x = .ok a := by
  cases x with
  | ok b => simp only [isOkAs, decide_eq_true_eq] at h; rw [h]
  | error _ => cases h

/-- A run's result is `(s, calls, [], used)`, as a Boolean the kernel evaluates. -/
private def runIs {ε D : Type} [DecidableEq D]
    (x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat))
    (s : Slots) (calls : List (Body D)) (used : Nat) : Bool :=
  match x with
  | .ok (s', cs, [], u) => decide (s' = s) && decide (cs = calls) && decide (u = used)
  | _ => false

private theorem of_runIs {ε D : Type} [DecidableEq D]
    {x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat)}
    {s : Slots} {calls : List (Body D)} {used : Nat} (h : runIs x s calls used = true) :
    x = .ok (s, calls, [], used) := by
  unfold runIs at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  · cases h

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
  program := Lang.program wEnv.bytes wDigestOf noReceipts

private def natBytes (n : Nat) : ByteArray := (Wire.encodeData .nat (.nat n)).getD .empty

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

private def aS : Ty := .record [("m", .nat)]

/-- `go`'s one call slot: an invoke. -/
private def K : Ty := callOf ["invoke"]

/-- `invoke 5 0 (natBytes 4) 1000 none`, as call data. -/
private def goCall : Term :=
  .inj K "invoke" (.record [("args", .bytes (natBytes 4)), ("budget", .nat 1000), ("method", .nat 0),
    ("obj", .digest ⟨#[5]⟩), ("via", .inj (optTy .digest) "none" (.record []))])

/-- `go`: `λ rows s a req. {calls = {c0 = some goCall}, edits = {}, state = {m = s.m + 1}}`. -/
private def goT : Term :=
  .lam (.record []) (.lam aS (.lam .nat (.lam reqTy (resultT (callsT [someCallT K goCall])
    (.record [("m", .prim .add (.get (.var 2) "m") (.nat 1))])))))

private def relay : Package :=
  { imports := [], state := aS, iface := .record [("go", methodTy aS .nat [K])],
    body := .record [("go", goT)], methods := ["go"], laws := [] }

private def cBytes : ByteArray := (Wire.encodePackage counter).getD .empty
private def rBytes : ByteArray := (Wire.encodePackage relay).getD .empty

private theorem counter_encodes : Wire.encodePackage counter = some cBytes := by
  have h : (Wire.encodePackage counter).isSome = true := by decide +kernel
  unfold cBytes
  cases he : Wire.encodePackage counter with
  | none => rw [he] at h; cases h
  | some b => rfl

private theorem relay_encodes : Wire.encodePackage relay = some rBytes := by
  have h : (Wire.encodePackage relay).isSome = true := by decide +kernel
  unfold rBytes
  cases he : Wire.encodePackage relay with
  | none => rw [he] at h; cases h
  | some b => rfl

private def memberCell : Cell := { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩)] }
private def cPkgCell : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, cBytes)] }
private def rPkgCell : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, rBytes)] }
/-- B: package 9 (`counter`), owner 6 (A), `n = 3`. -/
private def bCell : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := [(slotPackage, ⟨#[9]⟩), (slotOwner, ⟨#[6]⟩), (stateBase, natBytes 3)] }
/-- A: package 10 (`relay`), owner 7, `m = 0`. -/
private def aCell : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := [(slotPackage, ⟨#[10]⟩), (slotOwner, ⟨#[7]⟩), (stateBase, natBytes 0)] }

private def w0 : World UInt8 :=
  let t := Trie.T.empty.insert (trieSpec wEnv) (.cell 5) (.entry (.live bCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 6) (.entry (.live aCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 7) (.entry (.live memberCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 9) (.entry (.live cPkgCell 0))
  let t := t.insert (trieSpec wEnv) (.cell 10) (.entry (.live rPkgCell 0))
  { trie := t, journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

/-- The five cells, pinned at what `w` holds. -/
private def pinsAt (w : World UInt8) : List (UInt8 × UInt8) :=
  [5, 6, 7, 9, 10].map fun c => (c, pinOf wEnv (w.entry wEnv c))

private def wUnsigned (w : World UInt8) (vu : Nat) : Unsigned UInt8 :=
  { world := 0
    member := 7
    key := ⟨#[42]⟩
    notBefore := 1
    validUntil := vu
    pins := pinsAt w
    maxCharge := 100000
    body := .invoke 6 0 (natBytes 0) 1000 none }

/-- Member 7 invokes `go` on A, on `w`'s pins, window `[1, vu]`. -/
private def wCall (w : World UInt8) (vu : Nat) : Call UInt8 :=
  { unsigned := wUnsigned w vu, signature := ByteArray.empty }

/-! ## The language's loads, through their equations -/

/-- A one-package closure: `load` of a pinned package cell holding `b`, which decodes to the
import-free `p`, is `admitPackage` of `p` alone. -/
private theorem load_one {look : Pinned UInt8} {id : UInt8} {b : ByteArray} {p : Package}
    (h : readKind look id kindPackage = .ok { kind := kindPackage, discipline := .rom, slots := [(0, b)] })
    (hd : Wire.decodePackage b = .ok p) (hi : p.imports = []) :
    Lang.load wDigestOf look closureDepthMax (wEnv.bytes id) ⟨[], [], []⟩ =
      admitPackage wDigestOf (wEnv.bytes id) p ⟨[], [], []⟩ [] := by
  have hr : Lang.readPackage look id = .ok p := by
    have hs : Slots.get [(0, b)] 0 = some b := rfl
    unfold Lang.readPackage
    rw [h]
    simp only [bind, Except.bind, hs, hd]
    rfl
  have hid : idOf wDigestOf (wEnv.bytes id) = .ok id := rfl
  unfold Lang.load
  rw [Lang.loadUsing.eq_def]
  simp only [indexIn, closureDepthMax]
  rw [hid]
  simp only [hr, hi]
  rw [Lang.loadAllUsing.eq_def]

private theorem counter_decodes : Wire.decodePackage cBytes = .ok counter :=
  Wire.decodePackage_eq_ok_iff.mpr counter_encodes
private theorem relay_decodes : Wire.decodePackage rBytes = .ok relay :=
  Wire.decodePackage_eq_ok_iff.mpr relay_encodes

/-! ## The signed call, on `w0`: A's run, then B's under `tree` -/

private def c1 : Call UInt8 := wCall w0 5
/-- A's request: self 6, principal 7 (the signer owns A). -/
private def reqA : Req UInt8 := reqOf c1.unsigned 6 7 (.invoke 0)
/-- B's request: self 5, principal 6 (A owns B; the call is derived as A). -/
private def reqB : Req UInt8 := reqOf c1.unsigned 5 6 (.invoke 0)
/-- What `go` returns on `m = 0`, and the one call it makes. -/
private def sA : Slots := [(stateBase, natBytes 1)]
private def bodyB : Body UInt8 := .invoke 5 0 (natBytes 4) 1000 none
/-- What `bump 4` returns on `n = 3`. -/
private def sB : Slots := [(stateBase, natBytes 7)]

/-- The walk at the signed call, after A's run (59 ticks), after B's (41). -/
private def wk0 : Walk UInt8 := ⟨[], poolOf c1.unsigned.body, 0⟩
private def wkA : Walk UInt8 := { wk0 with visited := 6 :: wk0.visited, pool := wk0.pool - 59 }
private def wkB : Walk UInt8 := { wkA with visited := 5 :: wkA.visited, pool := wkA.pool - 41 }
private def ownA : Draft UInt8 := ⟨[], writeOf 6 (diffOps (stateOf aCell) sA), [], []⟩
private def ownB : Draft UInt8 := ⟨[], writeOf 5 (diffOps (stateOf bCell) sB), [], []⟩

private def dummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty }

private def t1 : Turn UInt8 :=
  ((sealTurn wCtx c1 (ownA.append ownB).creates (ownA.append ownB).effects (ownA.append ownB).nullifiers
    (ownA.append ownB).rows).toOption).getD dummy

private def w1 : World UInt8 := ((World.admit wEnv w0 t1).toOption).getD w0

private theorem c1_pkgC : readKind (pinned wCtx.env w0 c1.unsigned.pins) 9 kindPackage = .ok cPkgCell := by
  rfl
private theorem c1_pkgR : readKind (pinned wCtx.env w0 c1.unsigned.pins) 10 kindPackage = .ok rPkgCell := by
  rfl

private theorem c1_readC : readPackage (pinned wCtx.env w0 c1.unsigned.pins) 9 = .ok counter :=
  readPackage_installed c1_pkgC (by rfl) counter_encodes

private theorem c1_readR : readPackage (pinned wCtx.env w0 c1.unsigned.pins) 10 = .ok relay :=
  readPackage_installed c1_pkgR (by rfl) relay_encodes

private theorem c1_invokeRunA :
    invokeRun wCtx (pinned wCtx.env w0 c1.unsigned.pins) c1 7 6 0 none = .ok (aCell, 10, reqA) :=
  of_isOkAs (by decide +kernel)

private theorem c1_runA :
    wCtx.program.run (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) 10 (stateOf aCell)
      0 (natBytes 0) reqA (min 1000 wk0.pool) = .ok (sA, [bodyB], [], 59) := by
  show (runMeasuredLive wEnv.bytes wDigestOf noReceipts _ _ _ _ _ _ _ _).map _ = _
  rw [runMeasuredLive_leaf_closed (show wDigestOf (wEnv.bytes 10) = some 10 from rfl) c1_readR rfl rfl]
  unfold runMeasured runMeasuredWith runSetup runSetupWith
  rw [load_one c1_pkgR relay_decodes rfl]
  exact of_runIs (by decide +kernel)

private theorem c1_judgeOneA :
    judgeOne wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) 10 (stateOf aCell) sA reqA = .ok () := by
  unfold judgeOne judgeOneWith
  rw [load_one c1_pkgR relay_decodes rfl]
  exact of_isOkAs (by decide +kernel)

private theorem c1_judgeA :
    wCtx.program.judge (pinned wCtx.env w0 c1.unsigned.pins) (some 10) [] (stateOf aCell) sA reqA = .ok () := by
  show Nanodregg.Lang.judgeContextual wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) (some 10) [] (stateOf aCell)
    sA reqA = .ok ()
  unfold Nanodregg.Lang.judgeContextual
  simp only [judgeOneContextual_leaf_closed (show wDigestOf (wEnv.bytes 10) = some 10 from rfl) c1_readR rfl rfl]
  simp only [c1_judgeOneA]
  rfl

private theorem c1_invokeRunB :
    invokeRun wCtx (pinned wCtx.env w0 c1.unsigned.pins) c1 6 5 0 none = .ok (bCell, 9, reqB) :=
  of_isOkAs (by decide +kernel)

private theorem c1_runB :
    wCtx.program.run (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) 9 (stateOf bCell)
      0 (natBytes 4) reqB (min 1000 wkA.pool) = .ok (sB, [], [], 41) := by
  show (runMeasuredLive wEnv.bytes wDigestOf noReceipts _ _ _ _ _ _ _ _).map _ = _
  rw [runMeasuredLive_leaf_closed (show wDigestOf (wEnv.bytes 9) = some 9 from rfl) c1_readC rfl rfl]
  unfold runMeasured runMeasuredWith runSetup runSetupWith
  rw [load_one c1_pkgC counter_decodes rfl]
  exact of_runIs (by decide +kernel)

private theorem c1_judgeOneB :
    judgeOne wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) 9 (stateOf bCell) sB reqB = .ok () := by
  unfold judgeOne judgeOneWith
  rw [load_one c1_pkgC counter_decodes rfl]
  exact of_isOkAs (by decide +kernel)

private theorem c1_judgeB :
    wCtx.program.judge (pinned wCtx.env w0 c1.unsigned.pins) (some 9) [] (stateOf bCell) sB reqB = .ok () := by
  show Nanodregg.Lang.judgeContextual wEnv.bytes wDigestOf (pinned wCtx.env w0 c1.unsigned.pins) (some 9) [] (stateOf bCell)
    sB reqB = .ok ()
  unfold Nanodregg.Lang.judgeContextual
  simp only [judgeOneContextual_leaf_closed (show wDigestOf (wEnv.bytes 9) = some 9 from rfl) c1_readC rfl rfl]
  simp only [c1_judgeOneB]
  rfl

/-- B's invoke, derived AS A one level down the tree. -/
private theorem c1_invokeB :
    invoke wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1
      (tree wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1 3)
      wkA 6 5 0 (natBytes 4) 1000 none = .ok (ownB, wkB) :=
  invoke_of (by decide) c1_invokeRunB c1_runB (by decide) (of_isOkAs (by decide +kernel))
    (of_isOkAs (by decide +kernel)) c1_judgeB (by decide) rfl

/-- The one call A's run returned, derived by `tree` at the depth bound. -/
private theorem c1_treeB :
    tree wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1 Bounds.callDepthMax
      wkA 6 bodyB = .ok (ownB, wkB) := by
  rw [show Bounds.callDepthMax = 3 + 1 from rfl, tree_succ]
  exact c1_invokeB

private theorem c1_callsA :
    deriveCalls (tree wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1
      Bounds.callDepthMax) 6 ownA wkA [bodyB] = .ok (ownA.append ownB, wkB) := by
  simp only [deriveCalls, List.foldlM_cons, List.foldlM_nil, callStep, c1_treeB, bind, Except.bind, pure,
    Except.pure]

/-- The signed invoke of A: its own write, then B's, the walk past both. -/
private theorem c1_invokeA :
    invoke wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1
      (tree wCtx (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) c1 Bounds.callDepthMax)
      wk0 7 6 0 (natBytes 0) 1000 none = .ok (ownA.append ownB, wkB) :=
  invoke_of (by decide) c1_invokeRunA c1_runA (by decide) (of_isOkAs (by decide +kernel))
    (of_isOkAs (by decide +kernel)) c1_judgeA (by decide) c1_callsA

private theorem c1_receive : receive wCtx w0 c1 = .ok t1 := by
  rw [receive_of rfl (of_isOkAs (by decide +kernel)) (of_isOkAs (by decide +kernel)) rfl c1_invokeA]
  exact of_isOkAs (by decide +kernel)

private theorem c1_admit : World.admit wCtx.env w0 t1 = .ok w1 := by
  have h : (World.admit wEnv w0 t1).isOk = true := by decide +kernel
  show World.admit wEnv w0 t1 = Except.ok (((World.admit wEnv w0 t1).toOption).getD w0)
  cases hf : World.admit wEnv w0 t1 with
  | error e => rw [hf] at h; cases h
  | ok w' => rfl

/-- B's invoke is dispatched: the one call A's run returned, the first, at the walk past A, as A. -/
private theorem c1_dispatchedB : Dispatched wCtx w0 c1 3 wkA 6 bodyB :=
  Dispatched.call (m := 3) (acc := (ownA, wkA)) (calls := [bodyB]) 0 (by decide)
    (Dispatched.root (X := wCtx) (w := w0) (c := c1)) c1_invokeA c1_invokeRunA c1_runA rfl

/-- A run's resulting state is `s`, as a Boolean the kernel evaluates. -/
private def runStateIs {ε D : Type} (x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat))
    (s : Slots) : Bool :=
  match x with
  | .ok (s', _, _, _) => decide (s' = s)
  | .error _ => false

private theorem of_runStateIs {ε D : Type}
    {x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat)} {s : Slots}
    (h : runStateIs x s = true) : ∃ cs rs u, x = .ok (s, cs, rs, u) := by
  unfold runStateIs at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst h
    exact ⟨_, _, _, rfl⟩
  · cases h

/-- What `bump 5` returns on `n = 3`. -/
private def sB5 : Slots := [(stateBase, natBytes 8)]

private theorem c1_runB5 : ∃ cs rs u,
    wCtx.program.run (pinned wCtx.env w0 c1.unsigned.pins) (rowView wCtx.env w0 c1.unsigned) 9 (stateOf bCell)
      0 (natBytes 5) reqB (min 1000 wkA.pool) = .ok (sB5, cs, rs, u) := by
  show ∃ cs rs u, (runMeasuredLive wEnv.bytes wDigestOf noReceipts _ _ _ _ _ _ _ _).map _ = _
  rw [runMeasuredLive_leaf_closed (show wDigestOf (wEnv.bytes 9) = some 9 from rfl) c1_readC rfl rfl]
  unfold runMeasured runMeasuredWith runSetup runSetupWith
  rw [load_one c1_pkgC counter_decodes rfl]
  exact of_runStateIs (by decide +kernel)

/-- B as `w1` holds it. -/
private def cellB1 : Cell := (w1.live wEnv 5).getD bCell

private theorem w1_liveB : w1.live wEnv 5 = some cellB1 := by
  have h : (w1.live wEnv 5).isSome = true := by decide +kernel
  show w1.live wEnv 5 = some ((w1.live wEnv 5).getD bCell)
  cases hl : w1.live wEnv 5 with
  | none => rw [hl] at h; cases h
  | some cl => rfl

/-! ## The second invoke of B, on `w1` -/

private def c2 : Call UInt8 := wCall w1 6
private def req2 : Req UInt8 := reqOf c2.unsigned 5 6 (.invoke 0)

private theorem c2_invokeRunB :
    invokeRun wCtx (pinned wCtx.env w1 c2.unsigned.pins) c2 6 5 0 none = .ok (cellB1, 9, req2) :=
  of_isOkAs (by decide +kernel)

/-! ## The premises, witnessed -/

/-- **The premises of `invoke_tree_slots` hold together on a NESTED invoke**, through
`Lang.program`: a signed call whose body invokes A, derived and admitted, whose walk dispatched an
invoke of B, not the signed body's object, as A (A's run returned it); that invoke's run (its
`invokeRun` as A, its `X.program.run` with its arguments at the fuel the walk left it) returned a
state other than the one it ran on, and B is live in the admitted World with exactly that state. -/
theorem invoke_tree_slots_witnessed :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (c : Call UInt8) (t : Turn UInt8) (n : Nat) (wk : Walk UInt8)
      (actor obj : UInt8) (budget : Nat),
      X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧
      receive X w c = .ok t ∧ World.admit X.env w t = .ok w' ∧
      Dispatched X w c n wk actor (.invoke obj 0 (natBytes 4) budget none) ∧
      (∀ o method args budget via, c.unsigned.body = .invoke o method args budget via → o ≠ obj) ∧
      actor ≠ c.unsigned.member ∧
      ∃ (cell : Cell) (p : UInt8) (r : Req UInt8) (s : Slots) (used : Nat),
        invokeRun X (pinned X.env w c.unsigned.pins) c actor obj 0 none = .ok (cell, p, r) ∧
        X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
          0 (natBytes 4) r (min budget wk.pool) = .ok (s, [], [], used) ∧
        s ≠ stateOf cell ∧
        ∃ cell', w'.live X.env obj = some cell' ∧ stateOf cell' = s :=
  ⟨wCtx, w0, w1, c1, t1, 3, wkA, 6, 5, 1000, rfl, c1_receive, c1_admit, c1_dispatchedB,
    fun o _ _ _ _ h => by
      rw [show c1.unsigned.body = Body.invoke 6 0 (natBytes 0) 1000 none from rfl] at h
      cases h
      decide,
    by decide, bCell, 9, reqB, sB, 41, c1_invokeRunB, c1_runB, by decide +kernel, cellB1, w1_liveB,
    by decide +kernel⟩

/-- **The premises of `invoke_tree_run` hold together**: on the instance above, an `invokeRun` of B
on the admitted World (as A, through fresh pins) reads the cell whose state is what the dispatched
invoke's run of B returned. -/
theorem invoke_tree_run_witnessed :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (c : Call UInt8) (t : Turn UInt8) (n : Nat) (wk : Walk UInt8)
      (actor obj : UInt8) (budget : Nat)
      (pins' : List (UInt8 × UInt8)) (c' : Call UInt8) (actor' : UInt8) (method' : Nat) (via' : Option UInt8)
      (cell' : Cell) (p' : UInt8) (r' : Req UInt8),
      X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧
      receive X w c = .ok t ∧ World.admit X.env w t = .ok w' ∧
      Dispatched X w c n wk actor (.invoke obj 0 (natBytes 4) budget none) ∧
      (∀ o method args budget via, c.unsigned.body = .invoke o method args budget via → o ≠ obj) ∧
      invokeRun X (pinned X.env w' pins') c' actor' obj method' via' = .ok (cell', p', r') ∧
      stateOf cell' = [(stateBase, natBytes 7)] :=
  ⟨wCtx, w0, w1, c1, t1, 3, wkA, 6, 5, 1000, c2.unsigned.pins, c2, 6, 0, none, cellB1, 9, req2, rfl,
    c1_receive, c1_admit, c1_dispatchedB,
    fun o _ _ _ _ h => by
      rw [show c1.unsigned.body = Body.invoke 6 0 (natBytes 0) 1000 none from rfl] at h
      cases h
      decide,
    c2_invokeRunB, by decide +kernel⟩

/-- **Tooth: the walk's record pins the arguments.** On the instance above, the invoke of B with
`bump 5` in place of the `bump 4` A's run returned, at the same walk, actor, method and budget, is
NOT dispatched: through `invoke_tree_slots` its run (which returns `n = 8`) would be what B holds in
`w1`, and B holds `n = 7`. The existential form `invoke_tree_slots` had before cv 01a15554-cffd named
no arguments and could not refuse it. -/
theorem dispatched_pins_args :
    ¬ Dispatched wCtx w0 c1 3 wkA 6 (.invoke 5 0 (natBytes 5) 1000 none) := by
  intro hd
  obtain ⟨cell, p, r, s, calls, rows, used, laws, hir, hrun, -, -, cell', hl, hk⟩ :=
    invoke_tree_slots c1_receive c1_admit hd
  rw [c1_invokeRunB] at hir
  simp only [Except.ok.injEq, Prod.mk.injEq] at hir
  obtain ⟨rfl, rfl, rfl⟩ := hir
  obtain ⟨cs, rs, u, h5⟩ := c1_runB5
  rw [h5] at hrun
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -, -, -⟩ := hrun
  have hl' : w1.live wEnv 5 = some cell' := hl
  rw [w1_liveB] at hl'
  cases hl'
  have h7 := hk stateBase
  revert h7
  decide +kernel

end Nanodregg.Kernel.Receive
