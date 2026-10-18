/-
# Ops.LiveCalls — the calls the live harness (deploy/live/) sends through a running unit

`live-calls DIR N` writes, for the test founder (`Ops.Founder`, RFC 8032 published vectors):
`DIR/genesis.args` (one `host genesis` argument per line after STORE: the label, `--nonce`, the
nonce, the founder's key and next key), `DIR/invitation` and `DIR/sponsor.key` (founder 0's
invitation to that World and its public key, hex, one line each: `host join STORE INVITATION KEY`'s
two arguments, RUNBOOK §2b), `DIR/op` (the `submit` operation byte, decimal) and
`DIR/call-NNN.bin` (the i-th call's payload, `X.callBytes`, i < N), each a create holding one
`Plants.slotBytes` slot so a few calls cross a 1 MiB seal or an `LimitFSIZE`. The calls are pinned
in sequence on founder 0's cell, so they are sent in order and each must be admitted. The
harness frames them for a client socket (`u32le len ‖ op ‖ payload`, client/src/frame.rs); this
module decides nothing the harness judges.
-/
import Ops.Plants
import Hosting.Controller
import Hosting.Package

namespace Nanodregg.Ops.LiveCalls

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed

def label : String := "ops-live"

def pad3 (i : Nat) : String :=
  let s := toString i
  String.ofList (List.replicate (3 - s.length) '0') ++ s

/-- The resident grain the keybroker rows need (HOSTING-26): keybroker binds a socket only for a
lifecycle object of kind resident the World holds, named by `Controller.dirOf` of its id. Two calls
on the genesis World, apart from the numbered ones (`grain-000.bin` installs the lifecycle package,
`grain-001.bin` creates the grain, phase installed), and `grain.dir`, the grain's socket directory
name. `none` if a step does not admit in process or the package is not `lifecycleId`. -/
def grainCalls (w₀ : World D) : Except String (Call D × Call D × String) := do
  let me := founderId X w₀.origin 0
  let some pkgBytes := Hosting.Grain.lifecycle?.toOption.bind Lang.Wire.encodePackage | throw "no lifecycle package bytes"
  let c0 := Founder.callAs me w₀ 0 [me] (.install pkgBytes)
  let (t0, w1) ← match submit X w₀ c0 with
    | .ok r => pure r
    | .error v => throw s!"install refused {repr v}"
  let some p := (createdIds t0).head? | throw "install created nothing"
  unless some p.bytes == (Hosting.Controller.lifecycleId X.env).map (·.bytes) do throw "installed id is not lifecycleId"
  let some st := Hosting.Grain.seed .resident "ops-live-resident".toUTF8 | throw "no seed"
  let c1 := Founder.callAs me w1 1 [me, p] (.create (some p) [] st)
  let (t1, _) ← match submit X w1 c1 with
    | .ok r => pure r
    | .error v => throw s!"create refused {repr v}"
  let some g := (createdIds t1).head? | throw "create made nothing"
  pure (c0, c1, String.fromUTF8! (Hosting.Controller.dirOf g.bytes))

def run : List String → IO UInt32
  | [dir, nStr] => do
    let some n := nStr.toNat? | IO.eprintln "live-calls: N is not a number"; return 2
    if n > 999 then IO.eprintln "live-calls: N > 999"; return 2
    let d := System.FilePath.mk dir
    IO.FS.createDirAll d
    IO.FS.writeFile (d / "genesis.args") ("\n".intercalate (label :: Founder.genesisArgs) ++ "\n")
    IO.FS.writeFile (d / "op") s!"{Protocol.Op.submit.code}\n"
    let some inv := Founder.invitation label | IO.eprintln "live-calls: the invitation does not fit"; return 1
    IO.FS.writeFile (d / "invitation") (Protocol.Text.toHex inv ++ "\n")
    IO.FS.writeFile (d / "sponsor.key") (Protocol.Text.toHex Founder.key ++ "\n")
    let w₀ ← match Founder.world label with
      | .ok w => pure w
      | .error r => do IO.eprintln s!"live-calls: genesis refused {r.name}"; return 1
    let mut w := w₀
    for i in [0:n] do
      let c := Founder.create w i (Plants.bigState i)
      match submit X w c with
      | .ok (_, w') => w := w'
      | .error _ => IO.eprintln s!"live-calls: call {i} does not admit in process"; return 1
      IO.FS.writeBinFile (d / s!"call-{pad3 i}.bin") (X.callBytes c)
    let (g0, g1, dir) ← match grainCalls w₀ with
      | .ok r => pure r
      | .error e => do IO.eprintln s!"live-calls: the resident grain: {e}"; return 1
    IO.FS.writeBinFile (d / "grain-000.bin") (X.callBytes g0)
    IO.FS.writeBinFile (d / "grain-001.bin") (X.callBytes g1)
    IO.FS.writeFile (d / "grain.dir") (dir ++ "\n")
    IO.println s!"live-calls: {n} calls, anchor {Plants.anchorArg w}"
    return 0
  | _ => do IO.eprintln "usage: live-calls DIR N"; return 2

end Nanodregg.Ops.LiveCalls
