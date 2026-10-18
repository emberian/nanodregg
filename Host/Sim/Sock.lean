/-
# Host.Sim.Sock — `host-sock-probe`: Host.Sock's contracts, driven by a test that holds the peer

`host-sock-probe PATH MS OP…` connects to PATH with timeout MS, then runs each OP in order and
prints one line per step: `connect ok`, `wN ok` (N bytes sent), `rN M` (M bytes read, 0 = end of
stream), or `<step> err <the IO error's text>`. It stops at the first error, then prints `alive`:
that line is the evidence a write to a closed peer did not end the process by SIGPIPE.
A PATH of the form `nul:P` connects to `P`, a NUL character, then `x` (the `pathNul` contract; the
NUL is `Char.ofNat 0`, never a `\x00` literal, which Lean 4.30's C backend miscompiles).
`launcher/tests/sock.rs` holds the listener and reads the lines (HOST-52).
-/
import Host.Sock

namespace Nanodregg.Host.Sim.Sock

/-- One step on the connection: its line, and whether the probe goes on. -/
def step (c : Conn) (op : String) : IO (String × Bool) := do
  let n := (op.drop 1).toString.toNat?
  let r : Except IO.Error String ← match op.front, n with
    | 'w', some n => (do c.writeAll (ByteArray.mk (Array.replicate n 120)); pure "ok").toBaseIO
    | 'r', some n => (do pure (toString (← c.read n.toUSize).size)).toBaseIO
    | _, _ => pure (.error (IO.userError "badOp"))
  pure <| match r with
    | .ok t => (s!"{op} {t}", true)
    | .error e => (s!"{op} err {e}", false)

def run (args : List String) : IO UInt32 := do
  let path :: ms :: ops := args | IO.eprintln "usage: host-sock-probe PATH MS OP…"; return 2
  let some ms := ms.toNat? | IO.eprintln "usage: MS is a number"; return 2
  let path := match path.dropPrefix? "nul:" with
    | some p => p.toString ++ String.singleton (Char.ofNat 0) ++ "x"
    | none => path
  match ← (Conn.connect path ms.toUInt32).toBaseIO with
  | .error e => IO.println s!"connect err {e}"
  | .ok c =>
    IO.println "connect ok"
    let mut go := true
    for op in ops do
      if go then
        let (line, more) ← step c op
        IO.println line
        go := more
  IO.println "alive"
  return 0

end Nanodregg.Host.Sim.Sock
