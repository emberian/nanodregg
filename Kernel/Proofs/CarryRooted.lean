/-
# Kernel.Proofs.CarryRooted — a carried World stays rooted at its lineage's genesis (KERNEL-40)

Member and founder-grant ids are derived once, at the lineage's genesis, from the FIRST origin
(KERNEL-24), and a carry keeps them (ids are names: `carry_receive`). So the roots of a carried
World's grants are the first genesis's founder grants, under every later carry and honest fold:

* `carry_rooted`: a carry keeps `WorldRooted` with the SAME roots;
* `deployed_carry_rooted`: a World an honest log folds to from genesis, carried, and folded again
  by an honest log has every
  World grant rooted at the first genesis's founder grants (`GenesisRoot` of the first origin),
  with no premise.
-/
import Kernel.Proofs.Carry
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

variable {D : Type} [Ord D] [DecidableEq D]

/-- **A carry keeps the World rooted at the same roots**: the re-authored trie holds the exported
World's grants unchanged, and the one cell it adds is the authority's, not a grant. -/
theorem carry_rooted {X : Ctx D} {R : D → Prop} {name nonce : ByteArray} {auth : Authority} {w w' : World D}
    (hc : w.Canon X.env) (hw : WorldRooted X R w) (h : carry X name nonce w.origin w.carried auth = .ok w') :
    WorldRooted X R w' := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  intro id cell hl hk
  obtain ⟨v, hg⟩ := live_get hl
  change (reauthor X w.trie auth).get (trieSpec X.env) (.cell id) = _ at hg
  rw [reauthor_get hc] at hg
  split at hg
  · simp only [Option.some.injEq, Leaf.entry.injEq, Entry.live.injEq] at hg
    rw [← hg.1] at hk
    simp [authorityCell, kindAuthority, kindGrant] at hk
  · exact hw id cell (get_live (Option.filter_eq_some_iff.mp hg).1) hk

/-- **Deployed: a carried lineage is rooted at its first genesis.** A World an honest log folds to
from genesis, carried, and folded again by an honest log: every World grant has a parent or is one of the FIRST genesis's
founder grants. The carried World's own origin roots nothing: its ids are the lineage's. -/
theorem deployed_carry_rooted (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) (auth : Authority) {name' nonce' : ByteArray} {w w' w'' : World Digest}
    {l l' : List (Step Digest)}
    (hf : World.fold (ctx program).env (genesisWorld (ctx program) name nonce allowance founders auth) l = .ok w)
    (hh : Honest (ctx program) (genesisWorld (ctx program) name nonce allowance founders auth) l)
    {auth' : Authority} (hc : carry (ctx program) name' nonce' w.origin w.carried auth' = .ok w')
    (hf' : World.fold (ctx program).env w' l' = .ok w'') (hh' : Honest (ctx program) w' l') :
    WorldRooted (ctx program) (GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders auth)) w'' :=
  honest_rooted deployed_lawful
    (carry_rooted (fold_canon (receive_genesis_canon _ name nonce allowance founders auth) hf)
      (deployed_honest_rooted program name nonce allowance founders auth hf hh) hc) hf' hh'

end Nanodregg.Kernel.Receive
