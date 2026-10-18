/-
# Hosting.Proofs.Residents — what `hosting-broker` answers keybroker is what the theorems speak of

HOSTING-26, VACUITY-READER-H8b's H2–H4: the IO loop's links, each a theorem. `absorbTurns_tracks`:
a catch-up leaves `Follow.grains` exactly the World's resident grains (given they were before);
`residents_mem`: the names answered are exactly `dirOf` of those grains' ids; `answer_encodes`: the
answer `serve` writes for at most `residentsMax` grains always has a frame (a deployed id is 32 bytes,
its name 64); `decodeRequest_residents` / `decodeRequest_decide`: the request keybroker encodes is
the request the decider reads, its clock included.
-/
import Hosting.BrokerCli
import Hosting.Proofs.Broker
import Hosting.Proofs.Controller
import Hosting.Proofs.Allowance

namespace Nanodregg.Hosting.Proofs.Residents

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Hosting Nanodregg.Hosting.BrokerCli

/-- A catch-up keeps the followed resident grains exactly the World's: if `f.grains` held exactly
what `residentOf` reads of `w`, and the Turns absorbed fold `w` to the World the tail reached, the
grains after `absorbTurns` are exactly what it reads of that World. -/
theorem absorbTurns_tracks {f : Follow} {t : Host.Tail (World D)} {w : World D} {ts : List (Step D)}
    (hc : ∀ i x, (i, x) ∈ f.grains ↔ Track.readAt Host.Deployed.X.env (Controller.residentOf f.lifeId) w i = some x)
    (h : World.fold Host.Deployed.X.env w ts = .ok t.world) :
    ∀ i x, (i, x) ∈ (f.absorbTurns t (Step.turns ts)).grains ↔
      Track.readAt Host.Deployed.X.env (Controller.residentOf f.lifeId) t.world i = some x :=
  Proofs.Allowance.absorb_tracks hc h

/-- The names the decider answers are exactly the followed grains' directory names. -/
theorem residents_mem {f : Follow} {n : ByteArray} :
    n ∈ f.residents ↔ ∃ p ∈ f.grains, n = Controller.dirOf p.1.bytes := by
  simp [Follow.residents, eq_comm]

/-- The answer `serve` writes encodes whenever it holds at most `residentsMax` grains: each name is
the 64-byte `dirOf` of a 32-byte deployed id (`dirOf_size`, `Digest.size_eq`). -/
theorem answer_encodes {f : Follow} (hn : f.residents.length ≤ Broker.Bounds.residentsMax) :
    (Broker.Wire.encodeVerdict (.residents f.residents)).isSome = true := by
  apply Proofs.Broker.residents_encode hn
  intro n hm
  obtain ⟨p, -, rfl⟩ := residents_mem.mp hm
  rw [Proofs.dirOf_size, p.1.size_eq]
  omega

/-- A `residents` request reads back with its clock. -/
theorem decodeRequest_residents (t : UInt64) :
    Broker.Wire.decodeRequest (Broker.Wire.requestCodec.bytes ⟨⟨1, by decide⟩, (t, ())⟩) =
      .ok (.residents t.toNat) := by
  simp [Broker.Wire.decodeRequest, Stream.decode_bytes Proofs.Broker.requestCodec_lawful, Except.map]

/-- A `decide` header reads back with its resident and clock. -/
theorem decodeRequest_decide (r : Bytes Broker.Bounds.frameMax) (t : UInt64) :
    Broker.Wire.decodeRequest (Broker.Wire.requestCodec.bytes ⟨⟨0, by decide⟩, (r, t, ())⟩) =
      .ok (.decide r.val t.toNat) := by
  simp [Broker.Wire.decodeRequest, Stream.decode_bytes Proofs.Broker.requestCodec_lawful, Except.map]

end Nanodregg.Hosting.Proofs.Residents
