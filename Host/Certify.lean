/-
# Host.Certify — `host serve --certify SOCK`: the writer's certificate of each base (HOST-80)

THE PRODUCER of DESIGN-TRUST §4.4b. The writer holds no signing seed: keybroker holds it (slot
`certify`), and signs only heads its decider's own fold holds (`Hosting.Certify`). After each seal
installs a base, the writer asks keybroker, on its own socket SOCK (`SOCKDIR/.writer/certify.sock`),
to certify the base World's head: one frame, `Head.certifiedBytes (headOf base)`. keybroker answers
`signed` with the certify key and its signature over `domCertify ‖ bytes`; the writer finds the key's
index in the base World's authority (`notCertifier` when the World does not list it), builds the
certificate (`Head.certificateBytes`), checks it as a joiner will (`Head.certifiesWorld` on the base
World: a certificate this writer would not take is never written), and replaces `base.cert`
atomically (`certTmpPath` → rename → sync the directory). A `read` page serves `base.cert` beside the
base (`Host.Deployed.pager`, PROTOCOL-77.1).

At each SEAL, never on request: one signature per seal, of exactly the object a thin member adopts,
and no signing oracle on the network path (an on-request signer would let any reader drive the
broker once per page). The asks run in one worker task of their own, fed by the seal through a
bounded channel and always taking the newest base queued, so a slow or absent keybroker never
delays a seal or a commit: a refusal, an absent socket or a timeout leaves the old certificate
(stale: `otherHead` until the next seal) and is one `STATUS certify` line on stderr. `notYet` (the
decider has not caught up to the base) is asked again, at most `retries` times, `retryMs` apart.
A World whose authority names nobody (`Authority.none`) has nothing to certify: no ask is made.
-/
import Host.Deployed
import Host.Sock
import Protocol.Head
import Host.Wire
import Hosting.BrokerWire

namespace Nanodregg.Host.Certify

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec Nanodregg.Host.Deployed
open Nanodregg.Protocol.Head (headOf certifiedBytes certificateBytes certifiesWorld)

/-- How long one ask may take, connect to the last byte of the answer. -/
def answerMs : Nat := 10000

/-- `notYet` answers asked again, and how far apart (the decider's tick). -/
def retries : Nat := 25
def retryMs : Nat := 200

/-- The most bases queued for the worker; past it a seal's ask is dropped (the next seal's is not). -/
def queueMax : Nat := 16

/-- Why one base was not certified, by name (one `STATUS certify` line each). -/
inductive Miss
  | unencodable
  | notCertifier
  | answer (why : Hosting.Broker.Refusal)
  /-- the certificate built from keybroker's answer is not one a joiner takes (`certifiesWorld`) -/
  | selfCheck (why : Protocol.Head.CertRefusal)
  | badAnswer
  | io (msg : String)

def Miss.name : Miss → String
  | .unencodable => "unencodable" | .notCertifier => "notCertifier"
  | .answer why => why.name | .selfCheck why => s!"selfCheck {why.name}"
  | .badAnswer => "badAnswer" | .io m => s!"io {m}"

/-- One ask on SOCK: the certified bytes, keybroker's answer. -/
def ask (sock : String) (bytes : ByteArray) : IO (Except Miss Hosting.Broker.CertifyAnswer) := do
  try
    let conn ← Conn.connect sock answerMs.toUInt32
    conn.writeAll (Log.lenBytes bytes.size ++ bytes)
    let s := conn.stream
    let some head ← readExact s 4 | return .error .badAnswer
    let some len := Log.lenAt head 0 | return .error .badAnswer
    if len = 0 ∨ Hosting.Broker.Bounds.frameMax < len then return .error .badAnswer
    let some body ← readExact s len | return .error .badAnswer
    match Hosting.Broker.Wire.decodeCertifyAnswer body with
    | .ok a => return .ok a
    | .error _ => return .error .badAnswer
  catch e => return .error (.io (toString e))

/-- The certificate of base World `w`, from keybroker: asked (again on `notYet`), assembled under
`w`'s authority, and checked as a joiner checks it. -/
def certificate (sock : String) (w : World D) : Nat → IO (Except Miss ByteArray)
  | 0 => return .error (.answer .notYet)
  | n + 1 => do
    let some bytes := certifiedBytes X.env (headOf X.env w) | return .error .unencodable
    match ← ask sock bytes with
    | .error m => return .error m
    | .ok (.refused .notYet) => IO.sleep retryMs.toUInt32; certificate sock w n
    | .ok (.refused why) => return .error (.answer why)
    | .ok (.signed key sig) =>
      let some auth := authorityOf w | return .error .notCertifier
      -- the slot the key holds (KERNEL-79): a listed certifier's, or a committed successor's
      let some i := Protocol.Head.slotOf X auth key | return .error .notCertifier
      let some cert := certificateBytes bytes [(i, key, sig)] | return .error .unencodable
      match certifiesWorld X w cert with
      | .error why => return .error (.selfCheck why)
      | .ok () => return .ok cert

/-- Replace `base.cert` by `cert`: `cert.tmp` → sync → rename → sync the directory. -/
def install (dir : System.FilePath) (cert : ByteArray) : IO Unit := do
  if ← (certTmpPath dir).pathExists then IO.FS.removeFile (certTmpPath dir)
  writeNew (certTmpPath dir) cert
  IO.FS.rename (certTmpPath dir) (certPath dir)
  syncDir dir.toString

/-- Certify one sealed base (a World with no certifier needs none), and say what happened. -/
def certifyBase (dir : System.FilePath) (sock : String) (w : World D) : IO Unit := do
  match authorityOf w with
  | some auth => if auth.threshold = 0 then return
  | none => pure ()
  let r ← try certificate sock w retries catch e => pure (.error (.io (toString e)))
  let line ← match r with
    | .ok cert =>
      try install dir cert; pure "certified" catch e => pure s!"refused=io {e}"
    | .error m => pure s!"refused={m.name}"
  IO.eprintln s!"STATUS certify steps={w.steps} chain={w.chain.toHex} {line}"

/-- The worker: take the newest queued base, certify it, until the channel closes or `fuel` runs out. -/
def worker (dir : System.FilePath) (sock : String) (ch : Std.CloseableChannel.Sync (World D)) :
    Nat → IO Unit
  | 0 => return
  | fuel + 1 => do
    let some w ← ch.recv | return
    let mut w := w
    for _ in [0:queueMax] do
      match ← ch.tryRecv with
      | some w' => w := w'
      | none => break
    certifyBase dir sock w
    worker dir sock ch fuel

/-- The seal hook: a checkpoint whose every installed base is queued for certification. -/
def certifying {W : Type} (ck : Checkpoint W) (queue : W → IO Unit) : Checkpoint W :=
  { ck with write := fun w pos es ix => do
      let r ← ck.write w pos es ix
      if let .ok _ := r then queue w
      return r }

/-- Start the worker for `host serve --certify SOCK` over the Store at `dir`; the seal hook. -/
def start (dir : System.FilePath) (sock : String) (lifetime : Nat) : IO (World D → IO Unit) := do
  let ch ← Std.CloseableChannel.Sync.new (some queueMax)
  let _ ← IO.asTask (worker dir sock ch lifetime) .dedicated
  return fun w => do let _ ← ch.trySend w

end Nanodregg.Host.Certify
