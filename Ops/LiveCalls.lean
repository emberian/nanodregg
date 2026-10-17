/-
# Ops.LiveCalls — the calls the live harness (deploy/live/) sends through a running unit

`live-calls DIR N` writes, for the test founder (`Ops.Founder`, RFC 8032 published vectors):
`DIR/genesis.args` (one `host genesis` argument per line after STORE: the label, `--nonce`, the
nonce, the founder's key and next key), `DIR/op` (the `submit` operation byte, decimal) and
`DIR/call-NNN.bin` (the i-th call's payload, `X.callBytes`, i < N), each a create holding one
`Plants.slotBytes` slot so a few calls cross a 1 MiB seal or an `LimitFSIZE`. The calls are pinned
in sequence on founder 0's cell, so they are sent in order and each must be admitted. The
harness frames them for a client socket (`u32le len ‖ op ‖ payload`, client/src/frame.rs); this
module decides nothing the harness judges.
-/
import Ops.Plants

namespace Nanodregg.Ops.LiveCalls

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed

def label : String := "ops-live"

def pad3 (i : Nat) : String :=
  let s := toString i
  String.ofList (List.replicate (3 - s.length) '0') ++ s

def run : List String → IO UInt32
  | [dir, nStr] => do
    let some n := nStr.toNat? | IO.eprintln "live-calls: N is not a number"; return 2
    if n > 999 then IO.eprintln "live-calls: N > 999"; return 2
    let d := System.FilePath.mk dir
    IO.FS.createDirAll d
    IO.FS.writeFile (d / "genesis.args") ("\n".intercalate (label :: Founder.genesisArgs) ++ "\n")
    IO.FS.writeFile (d / "op") s!"{Protocol.Op.submit.code}\n"
    let mut w := Founder.world label
    for i in [0:n] do
      let c := Founder.create label w i (Plants.bigState i)
      match submit X w c with
      | .ok (_, w') => w := w'
      | .error _ => IO.eprintln s!"live-calls: call {i} does not admit in process"; return 1
      IO.FS.writeBinFile (d / s!"call-{pad3 i}.bin") (X.callBytes c)
    IO.println s!"live-calls: {n} calls, anchor {Plants.anchorArg w}"
    return 0
  | _ => do IO.eprintln "usage: live-calls DIR N"; return 2

end Nanodregg.Ops.LiveCalls
