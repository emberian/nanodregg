/-
# Host.Proofs.Size — what a Store's log holds, in bytes (HOST-57's framing half; KERNEL-55 Q5)

The segment is the origin frame, then one frame per record (`size_encodeAll_sum`: its bytes are the
frames' sizes). A frame is its record plus 36 bytes (`frameSize`: a u32 length and a 32-byte tag).
A record is a u32 count, then each step with the 32-byte roots digest beside it: 33 bytes of framing
per step (its tag and that digest), and the step's own bytes (`record_size_eq`). A Turn's own bytes
are exactly its `logWeight` (CODEC's `turn_size_logWeight`). `index.log` is `entryBytes` per record
before the newest base (`entriesSeq_read`), and every record holds at least one step (HOST-49).

What bounds them:
* `turns_logWeight_le`: over any admitted fold, the Turns' log bytes sum to at most the starting
  World's weight plus allowance (KERNEL's `fold_conserves`: the log bytes are paid from the allowance
  and never credited back). `turn_logWeight_ge`: every Turn's log bytes are at least 80, so the Turn
  count is bounded too.
* `budget_store_le`: at a World `budgetFault` admits (HOST-56), that weight plus allowance is at most
  `genesisWeightMax + allowanceMax`.
* `store_turns_le`: so every Store this binary creates holds at most `genesisWeightMax + allowanceMax`
  bytes of Turns, and at most a 1/80 of that many Turns, over its whole life.

The honest edge: recorded REFUSALS are not paid from the allowance. Their steps are bounded per
window, not per life: at most `refusalsPerWindowMax` per window World-wide (KERNEL-55 R1), each
`refusedBytes` (two digests, three counters and the call's bytes) plus its 33 bytes of framing. A
Store's disk over its life is therefore the Turns' bound above plus that per-window bound times the
windows it lives through.
-/
import Host.Proofs.Deployed
import Host.Proofs.Cli
import Codec.Proofs.WorldSize
import Kernel.Proofs.RefusalsBound
import Kernel.Proofs.Journal

namespace Nanodregg.Host.Size

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed Nanodregg.Host.Cli

/-- **A record's bytes, exactly**: its u32 count, then per step 33 bytes of framing (the step's tag
and the roots digest beside it) and the step's own bytes. -/
theorem record_size_eq {r : ByteArray} {ps : List (Step D × D)}
    (h : (Record.codec Codec.Deployed.digestCodec).decode r = .ok ps) :
    r.size = 4 + (ps.map fun p => 33 + Record.stepBytes Codec.Deployed.digestCodec p.1).sum := by
  have hl := Codec.Kernel.batch_lawfulOn Codec.Deployed.digestCodec_lawful.on recordTurnsMax (by decide)
  have hb := (hl.eq_bytes_of_decode h).2
  have hs : r.size = (Codec.Kernel.batch recordTurnsMax Codec.Deployed.digestCodec).size ps := by
    rw [hb, ← hl.size_eq]
  have e : (Codec.Kernel.batch recordTurnsMax Codec.Deployed.digestCodec).size ps =
      ps.foldl (fun n x => n + (Codec.Stream.product (Codec.Kernel.step Codec.Deployed.digestCodec)
        Codec.Deployed.digestCodec).size x) 4 := rfl
  have hpt : ∀ x : Step D × D, (Codec.Stream.product (Codec.Kernel.step Codec.Deployed.digestCodec)
      Codec.Deployed.digestCodec).size x = 33 + Record.stepBytes Codec.Deployed.digestCodec x.1 := by
    intro x
    obtain ⟨s, d⟩ := x
    cases s with
    | turn t =>
      show (1 + (Codec.Kernel.turn Codec.Deployed.digestCodec).size t) + 32 = 33 + t.logWeight
      rw [Codec.Kernel.turn_size_logWeight (fun _ => rfl)]
      omega
    | refusal x =>
      show (1 + (Codec.Kernel.refused Codec.Deployed.digestCodec).size x) + 32 = 33 + _
      simp only [Record.stepBytes]
      omega
  rw [hs, e, foldl_add_eq, List.map_congr_left (fun x _ => hpt x)]

/-- **A record frame's bytes, exactly**: the record and 36 bytes (length and tag). -/
theorem frame_size_eq {r : ByteArray} {ps : List (Step D × D)}
    (h : (Record.codec Codec.Deployed.digestCodec).decode r = .ok ps) :
    frameSize r = 40 + (ps.map fun p => 33 + Record.stepBytes Codec.Deployed.digestCodec p.1).sum := by
  unfold frameSize
  rw [record_size_eq h]
  show 4 + (4 + _) + 32 = _
  omega

/-- **Every Turn's log bytes are at least 80**: its id, its two window bounds, its charge and six
list headers. -/
theorem turn_logWeight_ge (t : Turn D) : 80 ≤ t.logWeight := by
  unfold Turn.logWeight digestWeight counterWeight headerWeight
  omega

/-- **The Turns of an admitted fold carry at most the starting weight plus allowance in log bytes**
(KERNEL's `fold_conserves`): log bytes are paid from the allowance and never credited back. -/
theorem turns_logWeight_le {w w' : World D} {l : List (Step D)} (hc : w.Canon X.env)
    (hf : w.Slotted X.env) (hr : w.RowsCanon X.env) (h : World.fold X.env w l = .ok w') :
    ((Step.turns l).map Turn.logWeight).sum ≤ w.weight + w.allowance := by
  have := fold_conserves hc hf hr h
  omega

/-- **A World the budget admits starts with at most `genesisWeightMax + allowanceMax` of weight and
allowance together** (HOST-56's two arms). -/
theorem budget_store_le {w : World D} (hb : budgetFault w = none) :
    w.weight + w.allowance ≤ genesisWeightMax + allowanceMax := by
  unfold budgetFault at hb
  split at hb
  · cases hb
  · rename_i ha
    split at hb
    · cases hb
    · rename_i hp
      simp only [potential, potentialMax, potentialRatio] at hp
      omega

/-- **Every Store this binary creates holds, over its whole life, at most `genesisWeightMax +
allowanceMax` bytes of Turns, and at most an 80th of that many Turns** (KERNEL-55 Q5, the Turn
half). The World it starts from is a genesis, join or import the budget admits (premises
discharged by `genesis_budget_reaches`' and HOST-59's lemmas). -/
theorem store_turns_le {w w' : World D} {l : List (Step D)} (hb : budgetFault w = none)
    (hc : w.Canon X.env) (hf : w.Slotted X.env) (hr : w.RowsCanon X.env) (h : World.fold X.env w l = .ok w') :
    ((Step.turns l).map Turn.logWeight).sum ≤ genesisWeightMax + allowanceMax ∧
      80 * (Step.turns l).length ≤ genesisWeightMax + allowanceMax := by
  have h1 := turns_logWeight_le hc hf hr h
  have h2 := budget_store_le hb
  have h3 := sum_map_ge Turn.logWeight 80 turn_logWeight_ge (Step.turns l)
  omega

/-- **The derived World bound is 91,914,346 bytes**: about 34% of the 2^28 it replaced, whose reopen
PERF-2 measured at 120.7 s against THE BAR's 60 s. -/
theorem worldBytesDerived_eq : worldBytesDerived = 91914346 := by decide

/-- Under `refusalsFits`, CODEC's transaction count is KERNEL's: a transaction key holds a refused
leaf. -/
theorem refusalItemTx_eq {H : Nat} {l : List (RefusalSlot D × RefusalLeaf D)} (h : refusalsFits H l = true) :
    (l.map Codec.Kernel.refusalItemTx).sum = (l.map refusedOne).sum := by
  rw [List.map_congr_left (g := refusedOne) (fun p hp => ?_)]
  have hq := List.all_eq_true.mp h p hp
  obtain ⟨k, v⟩ := p
  cases k <;> cases v <;> simp_all [refusalFits, Codec.Kernel.refusalItemTx, refusedOne]

/-- **Every World the deployed writer reaches is in the World codec's domain**: it is `Kept`
(`kept_fold`), and its three listings are within `worldMax`. Each cell leaf weighs at least 32 and
each rows entry at least 1, so `budget_reaches` bounds both listings, and R1's `refusals_bounded`
bounds the third. So the live World a seal encodes needs no `CodecFits` premise. -/
theorem reached_codecFits {w w' : World D} {l : List (Step D)} (hb : budgetFault w = none) (hk : Kept w)
    (h : World.fold X.env w l = .ok w') :
    Codec.Kernel.World.CodecFits X.env (fun _ => True) w' := by
  have hk' := kept_fold hk h
  have hw := budget_reaches hb hk.canon hk.slotted hk.rowsCanon h
  have hc := sum_map_ge (fun p : Slot D × Leaf => p.2.weight) 32 (fun p => by
    obtain ⟨_, l⟩ := p
    cases l <;> simp only [Leaf.weight, digestWeight] <;> omega) w'.trie.toList
  have hr := sum_map_ge rowEntryWeight 1 (fun p => by
    obtain ⟨s, l⟩ := p
    cases l <;> simp only [rowEntryWeight, RowLeaf.weight] <;> omega) w'.rows.toList
  have hf := refusals_length_le hk'.refusalsOk hk'.counted
  simp only [World.weight, cellsWeight, rowsWeight, potentialMax, potentialRatio, genesisWeightMax,
    allowanceMax, Kernel.Bounds.refusalsPerWindowMax] at hw hc hr hf
  exact codecFits_of_kept hk' (by unfold Codec.Kernel.worldMax; omega) (by unfold Codec.Kernel.worldMax; omega)
    (by unfold Codec.Kernel.worldMax; omega)

/-- **Every World the deployed writer reaches encodes within `worldBytesMax`** (HOST-57, KERNEL-55):
from a World `budgetFault` admits (genesis, join or import; their `Kept` from KERNEL's genesis and
carry theorems and HOST-59's lemmas), every admitted fold reaches a World whose World-codec bytes are
within `Cadence.deployed.worldBytesMax`, with no premise on the reached World (`reached_codecFits`). Its weight is at most `worldWeightMax` (`budget_reaches`),
its journal fewer than three windows (`journal_bounded`), its refusals within R1's cap
(`refusals_bounded`), and CODEC's size bound (`world_size_le_div`) turns those into bytes. So the
seal's `worldTooLarge` never fires on the writer path. -/
theorem reached_size_le {w w' : World D} {l : List (Step D)} (hb : budgetFault w = none) (hk : Kept w)
    (h : World.fold X.env w l = .ok w') :
    ((Codec.Kernel.world X.env Codec.Deployed.digestCodec).bytes w').size ≤ Cadence.deployed.worldBytesMax := by
  have hfit := reached_codecFits hb hk h
  have hk' := kept_fold hk h
  have hs := Codec.Kernel.world_size_le_div Codec.Deployed.digestCodec_lawful.on (fun _ => rfl) hfit
  have hw := budget_reaches hb hk.canon hk.slotted hk.rowsCanon h
  have hj := journal_bounded hk'.journalOk
  obtain ⟨h1, h2, h3, h4⟩ := refusals_bounded hk'.refusalsOk hk'.counted
  have hrb := Codec.Kernel.refusalsBytes_le_of_fits hfit.refusalsFits
  rw [refusalItemTx_eq hfit.refusalsFits] at hrb
  unfold Codec.Kernel.journalBytes at hs
  simp only [Cadence.deployed, worldBytesDerived, worldWeightMax, journalBytesMax, refusalsBytesMax,
    potentialMax, Codec.Kernel.entrySlack, Codec.Kernel.worldFixed, potentialRatio, genesisWeightMax,
    allowanceMax, Kernel.Bounds.windowMax, Kernel.Bounds.refusalsPerWindowMax] at hs hw hj h1 h2 h3 ⊢
  omega

end Nanodregg.Host.Size
