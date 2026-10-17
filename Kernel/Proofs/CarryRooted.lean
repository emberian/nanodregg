/-
# Kernel.Proofs.CarryRooted — a carried World stays rooted at its lineage's genesis (KERNEL-40)

Member and founder-grant ids are derived once, at the lineage's genesis, from the FIRST origin
(KERNEL-24), and a carry keeps them (ids are names: `carry_receive`). So the roots of a carried
World's grants are the first genesis's founder grants, under every later carry and audit:

* `carry_rooted`: a carry keeps `WorldRooted` with the SAME roots;
* `deployed_carry_rooted`: a World audited from genesis, carried, and audited again has every
  World grant rooted at the first genesis's founder grants (`GenesisRoot` of the first origin),
  with no premise.
-/
import Kernel.Proofs.Carry
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

variable {D : Type} [Ord D] [DecidableEq D]

/-- **A carry keeps the World rooted at the same roots.** -/
theorem carry_rooted {X : Ctx D} {R : D → Prop} {name nonce : ByteArray} {w w' : World D}
    (hw : WorldRooted X R w) (h : carry X name nonce w.origin w.carried = .ok w') : WorldRooted X R w' := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hw

/-- **Deployed: a carried lineage is rooted at its first genesis.** A World audited from genesis,
carried, and audited again: every World grant has a parent or is one of the FIRST genesis's
founder grants. The carried World's own origin roots nothing: its ids are the lineage's. -/
theorem deployed_carry_rooted (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) {name' nonce' : ByteArray} {w w' w'' : World Digest}
    {l l' : List (Turn Digest)}
    (ha : audit (ctx program) (genesisWorld (ctx program) name nonce allowance founders) l = .ok w)
    (hc : carry (ctx program) name' nonce' w.origin w.carried = .ok w')
    (ha' : audit (ctx program) w' l' = .ok w'') :
    WorldRooted (ctx program) (GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders)) w'' :=
  audit_rooted deployed_lawful (carry_rooted (deployed_audit_rooted program name nonce allowance founders ha) hc) ha'

end Nanodregg.Kernel.Receive
