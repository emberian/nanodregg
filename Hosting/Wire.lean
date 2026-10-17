/-
# Hosting.Wire — the frames between the controller and `grain-launch`

The controller (Lean, `Hosting.Controller`) writes ACTIONS; the launcher (Rust, `hosting/`) writes
REPORTS. Both are `Codec.Tagged` frames over the one Layout family, so the Rust reader and writer are
printed from these lists (`emit-hosting`) and the launcher holds no copy of a code, a bound or the
path rule (law 2). On the pipe each frame is `u32le len ‖ payload`, `1 ≤ len ≤ Bounds.frameMax`.

    actions  launch 1   grain, program : path, read write exec connect hidden : paths
             kill   2   grain
             refuse 3   grain, grainRefusal : Refusal
    reports  started 1  grain, atMs
             exited  2  grain, status (the raw wait status), atMs
             failed  3  grain, launchFailure : LaunchFailure, atMs

`grain` is the grain's directory name (`Controller.dirOf`): the key a later kill and every report
name the child by. Paths are relative to the operator's hosting root, except `connect`, whose paths
are relative to the operator's broker root (SOCKDIR, HOSTING-17); the launcher joins those two roots
and nothing else. This module imports no decision (not `Hosting.Plan`, not `Hosting.Controller`),
so the emitter's closure is the Codec family and these lists.
-/
import Codec.Layout

namespace Nanodregg.Hosting

open Nanodregg.Codec

namespace Bounds

/-- The largest frame payload either way, in bytes; also the bound of every field in it. A plan's
paths are at most seven components of at most `Codec.Path.componentMax` bytes. -/
def frameMax : Nat := 4096

private theorem frameMax_fits : frameMax < 2 ^ 32 := by decide

/-- The most grains one reconcile call decides (the caller pages a larger batch). -/
def grainsMax : Nat := 256

end Bounds

/-- A path below the hosting root, as components (`Codec.Path`: clean, joined by `/` on the wire). -/
abbrev Path := List ByteArray

/-- The `sandbox::Policy` a grain is launched under, field for field, plus its program. `connect`
names unix sockets the grain may connect to (CLIENT's `Policy.connect`), relative to the broker
root, not the hosting root (HOSTING-17 §6, §8). -/
structure Plan where
  program : Path
  read : List Path
  write : List Path
  exec : List Path
  connect : List Path
  hidden : List Path
  deriving DecidableEq

/-- Why the controller refuses to plan or launch a grain, by name (law 7). -/
inductive Refusal
  /-- the Store label is not one clean path component of lowercase ASCII letters, digits and `-` -/
  | labelUnclean
  /-- the grain's entry is not one clean path component -/
  | entryUnclean
  /-- the grain's id directory name is not one clean component of lowercase ASCII letters, digits and `-` -/
  | idUnclean
  /-- a lifecycle cell whose kind, entry or phase does not decode -/
  | malformedGrain
  /-- the grain exited `Controller.restartsMax` times within the restart window -/
  | crashLoop
  deriving DecidableEq, Repr

namespace Refusal

def all : List Refusal :=
  [labelUnclean, entryUnclean, idUnclean, malformedGrain, crashLoop]

def code : Refusal → UInt8
  | labelUnclean => 0 | entryUnclean => 1 | idUnclean => 2 | malformedGrain => 3 | crashLoop => 4

def name : Refusal → String
  | labelUnclean => "labelUnclean" | entryUnclean => "entryUnclean" | idUnclean => "idUnclean"
  | malformedGrain => "malformedGrain" | crashLoop => "crashLoop"

def ofCode? (b : UInt8) : Option Refusal := all.find? (·.code == b)

end Refusal

/-- Why the launcher did not start a child it was told to launch: `sandbox::ConfineError`'s cases by
name, and the spawn itself failing. The launcher maps each `ConfineError` to one of these with an
exhaustive match, so a new sandbox case does not compile until it is named here. -/
inductive LaunchFailure
  | unsupported
  | mechanismMissing
  | unnameablePath
  | pathMissing
  | programNotAbsolute
  | programOutside
  | exposed
  /-- the confined command did not start (`Command::spawn` failed) -/
  | spawnFailed
  /-- more `connect` sockets than `sandbox::CONNECT_MAX` (HOSTING-17 §5) -/
  | connectTooMany
  /-- a `connect` path is a symbolic link -/
  | connectLink
  /-- a `connect` path is not a socket -/
  | connectNotSocket
  /-- a `connect` socket is neither the euid's (0600) nor another uid's with the egid's group (0660) -/
  | connectOwner
  /-- a `connect` socket's mode is not exactly the one its owner case allows -/
  | connectMode
  /-- a directory above a `connect` socket is writable by another, or owned by a uid that is neither
  root, the euid nor the socket's owner -/
  | connectDir
  /-- a `connect` directory lies under or contains a read/write/exec entry: on Linux every directory a
  child sees is already a connect grant (CLIENT-20, HOSTING-17 §8) -/
  | connectOverlap
  /-- a read/write/exec tree holds a unix socket at launch (CLIENT-20) -/
  | socketInGrant
  /-- a directory under a read/write/exec grant cannot be listed, so a socket in it cannot be ruled out -/
  | grantUnlisted
  deriving DecidableEq, Repr

namespace LaunchFailure

def all : List LaunchFailure :=
  [unsupported, mechanismMissing, unnameablePath, pathMissing, programNotAbsolute, programOutside,
   exposed, spawnFailed, connectTooMany, connectLink, connectNotSocket, connectOwner, connectMode,
   connectDir, connectOverlap, socketInGrant, grantUnlisted]

def code : LaunchFailure → UInt8
  | unsupported => 0 | mechanismMissing => 1 | unnameablePath => 2 | pathMissing => 3
  | programNotAbsolute => 4 | programOutside => 5 | exposed => 6 | spawnFailed => 7
  | connectTooMany => 8 | connectLink => 9 | connectNotSocket => 10 | connectOwner => 11
  | connectMode => 12 | connectDir => 13 | connectOverlap => 14 | socketInGrant => 15 | grantUnlisted => 16

def name : LaunchFailure → String
  | unsupported => "unsupported" | mechanismMissing => "mechanismMissing"
  | unnameablePath => "unnameablePath" | pathMissing => "pathMissing"
  | programNotAbsolute => "programNotAbsolute" | programOutside => "programOutside"
  | exposed => "exposed" | spawnFailed => "spawnFailed"
  | connectTooMany => "connectTooMany" | connectLink => "connectLink" | connectNotSocket => "connectNotSocket"
  | connectOwner => "connectOwner" | connectMode => "connectMode" | connectDir => "connectDir"
  | connectOverlap => "connectOverlap" | socketInGrant => "socketInGrant" | grantUnlisted => "grantUnlisted"

def ofCode? (b : UInt8) : Option LaunchFailure := all.find? (·.code == b)

end LaunchFailure

/-- What to do with one grain's child. -/
inductive Verdict
  | launch (plan : Plan)
  | kill
  | refuse (why : Refusal)
  deriving DecidableEq

/-- What the controller tells the launcher: a verdict for the grain named by its directory. -/
structure Action where
  grain : ByteArray
  verdict : Verdict
  deriving DecidableEq

/-- What the launcher reports. Times are the launcher's milliseconds (advisory: HOSTING-7). -/
inductive Report
  | started (grain : ByteArray) (atMs : UInt64)
  | exited (grain : ByteArray) (status : UInt32) (atMs : UInt64)
  | failed (grain : ByteArray) (why : LaunchFailure) (atMs : UInt64)
  deriving DecidableEq

namespace Wire

def actionCases : Tagged :=
  [("launch", 1, [.bytes "grain", .path "program", .paths "read", .paths "write", .paths "exec",
     .paths "connect", .paths "hidden"]),
   ("kill", 2, [.bytes "grain"]),
   ("refuse", 3, [.bytes "grain", .oneOf "grainRefusal" (Refusal.all.map fun r => (r.name, r.code))])]

def reportCases : Tagged :=
  [("started", 1, [.bytes "grain", .u64 "atMs"]),
   ("exited", 2, [.bytes "grain", .u32 "status", .u64 "atMs"]),
   ("failed", 3, [.bytes "grain", .oneOf "launchFailure" (LaunchFailure.all.map fun r => (r.name, r.code)),
     .u64 "atMs"])]

abbrev ActionTy := Tagged.Ty Bounds.frameMax actionCases
abbrev ReportTy := Tagged.Ty Bounds.frameMax reportCases

def actionCodec : Stream ActionTy := Tagged.codec Bounds.frameMax Bounds.frameMax_fits actionCases
def reportCodec : Stream ReportTy := Tagged.codec Bounds.frameMax Bounds.frameMax_fits reportCases

abbrev WPath := Field.PathTy Bounds.frameMax

def bytes? (b : ByteArray) : Option (Bytes Bounds.frameMax) :=
  if h : b.size ≤ Bounds.frameMax then some ⟨b, h⟩ else none

def path? (p : Path) : Option WPath :=
  if h : Path.fits Bounds.frameMax p = true then some ⟨p, h⟩ else none

def paths? (ps : List Path) : Option (Bounded Bounds.frameMax WPath) := do
  let a ← ps.mapM path?
  if h : a.toArray.size ≤ Bounds.frameMax then some ⟨a.toArray, h⟩ else none

def unpaths (a : Bounded Bounds.frameMax WPath) : List Path := a.val.toList.map (·.val)

/-- A `oneOf` field's value is one of its listed codes. -/
private theorem contains_of_mem {α : Type} (f : α → String) (c : α → UInt8) (l : List α) (r : α)
    (h : r ∈ l) : ((l.map fun r => (f r, c r)).map Prod.snd).toArray.contains (c r) = true := by
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, List.map_map]
  exact List.mem_map.mpr ⟨r, h, rfl⟩

private theorem refusal_of_contains (b : UInt8)
    (h : ((Refusal.all.map fun r => (r.name, r.code)).map Prod.snd).toArray.contains b = true) :
    (Refusal.ofCode? b).isSome = true := by
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, List.map_map] at h
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
  cases r <;> rfl

private theorem failure_of_contains (b : UInt8)
    (h : ((LaunchFailure.all.map fun r => (r.name, r.code)).map Prod.snd).toArray.contains b = true) :
    (LaunchFailure.ofCode? b).isSome = true := by
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, List.map_map] at h
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
  cases r <;> rfl

/-- The wire value of an action; `none` when a field is past `frameMax` or a path is unclean (the
controller's planned actions never are: `Proofs.Wire`). -/
def actionWire? (a : Action) : Option ActionTy := do
  let g ← bytes? a.grain
  match a.verdict with
  | .launch p => do
    let prog ← path? p.program
    let r ← paths? p.read
    let w ← paths? p.write
    let x ← paths? p.exec
    let c ← paths? p.connect
    let h ← paths? p.hidden
    pure ⟨⟨0, by decide⟩, (g, prog, r, w, x, c, h, ())⟩
  | .kill => pure ⟨⟨1, by decide⟩, (g, ())⟩
  | .refuse why => pure ⟨⟨2, by decide⟩, (g, ⟨why.code, contains_of_mem _ _ _ why (by cases why <;> decide)⟩, ())⟩

def actionOf : ActionTy → Action
  | ⟨⟨0, _⟩, (g, prog, r, w, x, c, h, ())⟩ =>
    { grain := g.val, verdict := .launch { program := prog.val, read := unpaths r, write := unpaths w,
                                           exec := unpaths x, connect := unpaths c, hidden := unpaths h } }
  | ⟨⟨1, _⟩, (g, ())⟩ => { grain := g.val, verdict := .kill }
  | ⟨⟨2, _⟩, (g, why, ())⟩ =>
    { grain := g.val, verdict := .refuse ((Refusal.ofCode? why.val).get (refusal_of_contains _ why.property)) }

def reportWire? : Report → Option ReportTy
  | .started g t => do let g ← bytes? g; pure ⟨⟨0, by decide⟩, (g, t, ())⟩
  | .exited g s t => do let g ← bytes? g; pure ⟨⟨1, by decide⟩, (g, s, t, ())⟩
  | .failed g why t => do
    let g ← bytes? g
    pure ⟨⟨2, by decide⟩, (g, ⟨why.code, contains_of_mem _ _ _ why (by cases why <;> decide)⟩, t, ())⟩

def reportOf : ReportTy → Report
  | ⟨⟨0, _⟩, (g, t, ())⟩ => .started g.val t
  | ⟨⟨1, _⟩, (g, s, t, ())⟩ => .exited g.val s t
  | ⟨⟨2, _⟩, (g, why, t, ())⟩ =>
    .failed g.val ((LaunchFailure.ofCode? why.val).get (failure_of_contains _ why.property)) t

/-- The value of the `path` field named `n` in a layout value. -/
def pathNamed (n : String) : (l : Layout) → Layout.Ty Bounds.frameMax l → Option Path
  | [], _ => none
  | .path m :: fs, (v, vs) => if m = n then some v.val else pathNamed n fs vs
  | _ :: fs, (_, vs) => pathNamed n fs vs

/-- The value of the `paths` field named `n` in a layout value. -/
def pathsNamed (n : String) : (l : Layout) → Layout.Ty Bounds.frameMax l → Option (List Path)
  | [], _ => none
  | .paths m :: fs, (v, vs) => if m = n then some (unpaths v) else pathsNamed n fs vs
  | _ :: fs, (_, vs) => pathsNamed n fs vs

/-- An action's payload, when it fits one frame. -/
def encodeAction (a : Action) : Option ByteArray := do
  let w ← actionWire? a
  let b := actionCodec.bytes w
  if b.size ≤ Bounds.frameMax then some b else none

/-- A report from its payload; a refusal names the offset and the case. -/
def decodeReport (b : ByteArray) : Except Codec.Refusal Report :=
  (reportCodec.decode b).map reportOf

end Wire
end Nanodregg.Hosting
