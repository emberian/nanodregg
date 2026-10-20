/-
# Protocol.Rows.Params — the parameters a member row runs under

The member rows are ONE pipeline (HOST's loop, `host follow`'s machine, custody, the attempt
store, every step through the wire codecs) generic in the digest `D`; a `Params D` is everything
that pipeline is instantiated with: the kernel's `Ctx` (with LANG's program), the digest's codec,
the World's codec, custody's key model (a secret, its public key, its signature) and the Store's
sealers. Two instances exist and both run every member row:

* `Params.toy` (here): the digest is a `UInt64` spelled by CODEC's `Stream.u64` and hashed by the
  Sim's FNV-1a, a "signature" is the Sim's `toySign` and a secret IS its public key, the Store's
  tags are the Sim's FNV sealers. Toy PARAMETERS in the real pipeline (memory: never toy code
  beside it): the fast gate.
* `Params.deployed` (`Protocol.Rows.Deployed`): `host`'s own `Ctx` (`Host.Deployed.X`: the 32-byte
  `Codec.Digest`, cSHAKE256, RFC 8032 Ed25519), its World codec, KMAC256 Store sealers
  (`Host.Keys.ofKey` under the deployed shape stamp), and custody's Ed25519 keys.

Everything else is deployed code under both: CODEC's Call/Turn/Cell codecs (`Codec.Kernel`, generic
in the digest's codec), its batch record, LANG's program, KERNEL's receivers. So a logged event the
follower decodes is exactly the bytes follow built and the Host admitted. A `Params` selects what
the HARNESS runs; nothing in admission reads which instance it is (PROTOCOL-50).
-/
import Codec.World
import Kernel.Sim
import Lang.Program
import Host.Sim.Toy

namespace Nanodregg.Protocol.Rows

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

structure Params (D : Type) [Ord D] where
  name : String
  /-- the kernel's parameters, with LANG's program -/
  ctx : Ctx D
  /-- the digest's codec -/
  dc : Stream D
  /-- the World's codec (a base's World part, CODEC-14) -/
  world : Stream (World D)
  /-- custody's public key of a secret (what a call, an envelope or an invitation carries, what a
  founder list and `nextKeyDigest` commit to) -/
  pub : ByteArray → ByteArray
  /-- custody's signature of a message under a secret -/
  sign : ByteArray → ByteArray → ByteArray
  /-- the Store's sealers and its base digest -/
  keys : Host.Keys
  /-- the rows' writer's seal threshold in bytes: small enough that a row of a few dozen turns
  seals bases, large enough that the dozen writes `thinStale` and `seal` run past a pin do not
  (a deployed writer's cadence is in bytes, its window in heights). A row's shape is in WRITES, so
  this scales with what a write costs in bytes at these parameters. -/
  sealMinBytes : Nat
  /-- the page budget the rows' writer pages with: HOST's `Page.budget` is a frame, which no row's
  log reaches, so a row would never see a page end before the tip. It must hold every event the
  kernel admits: `Protocol.Bounds.pageEventBytesMax + 4`, DERIVED from the kernel bounds (a page's 4-byte
  event length, the event's 1-byte step tag, and a cancel's signature behind its eight-byte length,
  `Host.Page.stepEvent`, PROTOCOL-60). The theorem is
  HOST's `Host.Page.walkTurnsAt_serves` (and `walk_serves`, through the segment): under such a budget a
  record's walk that has served nothing serves the first step past its start.
  `Host.Page.walkTurnsAt_one_short` is the tooth at `+ 3`. An event past the budget is never served, the follower refuses the empty page short of
  the tip `badResult`, and the attempt's confirm reads that as `uncertain`. A guess at the largest
  event the rows happen to log broke twice: 4096 (the grain row's lifecycle package) and 16384 (the
  queue Bell's install, 31.5 KB, PROTOCOL-18); the `bigEvent` row's plant is the old 16384. It still
  makes a cold follower page (`paging` writes enough for several pages). -/
  pageBudget : Nat

namespace Params

def worldName : ByteArray := "rows".toUTF8
def allowance : Nat := 2 ^ 40
/-- The rows' genesis nonce (KERNEL-24): fixed, a test parameter; a real genesis draws it. -/
def nonce : ByteArray := "rows-nonce".toUTF8

/-- The toy parameters: the Kernel Sim's `Ctx` with LANG's program, a secret is its own public
key, the Host Sim's FNV sealers. -/
def toy : Params UInt64 :=
  { name := "toy parameters (UInt64 digest, FNV-1a, hash signatures, FNV Store tags)"
    ctx := Kernel.Sim.ctxWith (Lang.program Kernel.Sim.dc.bytes Kernel.Sim.digestOf)
    dc := Kernel.Sim.dc
    world := Codec.Kernel.world Kernel.Sim.env Kernel.Sim.dc
    pub := fun k => k
    sign := Kernel.Sim.toySign
    keys := Host.Sim.keys
    sealMinBytes := 8192
    pageBudget := Protocol.Bounds.pageEventBytesMax + 4 }

/-- The widths of what a parameter set's functions produce, measured by calling them: a digest's
bytes, a public key, a signature, a base's digest and a Store tag. -/
structure Widths where
  digest : Nat
  pub : Nat
  sig : Nat
  baseDigest : Nat
  tag : Nat
  deriving Repr, DecidableEq

def widths {D : Type} [Ord D] (P : Params D) : Widths :=
  let s := "nanodregg/rows/width-probe".toUTF8
  { digest := (P.ctx.env.bytes (P.ctx.env.hash "nanodregg/rows/width-probe" s)).size
    pub := (P.pub s).size
    sig := (P.sign s s).size
    baseDigest := (P.keys.worldDigest s).size
    tag := (P.keys.segment.tag s).size }

/-- The deployment's widths: a 32-byte digest, an Ed25519 public key (32) and signature (64), a
32-byte base digest and a 32-byte KMAC256 tag. -/
def deployedWidths : Widths := ⟨32, 32, 64, 32, 32⟩

/-- A run that claims the deployed parameters must measure the deployed widths: the first width
off, by name, else `ok`. The toy fails it (`digest 8≠32`), which is the plant that this check
reads the parameters at all. -/
def atDeployed {D : Type} [Ord D] (P : Params D) : Except String Unit :=
  let w := P.widths
  let d := deployedWidths
  match [("digest", w.digest, d.digest), ("pub", w.pub, d.pub), ("sig", w.sig, d.sig),
      ("baseDigest", w.baseDigest, d.baseDigest), ("tag", w.tag, d.tag)].find? (fun (_, a, b) => a ≠ b) with
  | some (n, a, b) => .error s!"{n} {a}≠{b}"
  | none => .ok ()

end Params

end Nanodregg.Protocol.Rows
