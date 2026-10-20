> record copy of redregg/work/GATES-21-PROPOSED.md, 2026-10-19; the lane logs stay in redregg

# GATES-21 (PROPOSED, not to be built yet): a merge-train for tied landers

GATES-8, 2026-10-19. ROOT ruling: write it up with its price, and build it only if the tie tail stays
long once GATES-20's traced reuse has landed. The trigger is a day of queue records under GATES-20 in
which landers still take 4+ passes.

## The problem (measured)

- k landers that are ready and twice-displaced at the same moment must land serially. Each lands by CAS
  onto the tip its predecessor produced, so the youngest re-bases k−1 more times: 2 + k passes.
- First day under GATES-19, 13 landers. By displacements: 0 → 5, 1 → 1, 2 → 6, 3 → 1. Ties of 2 and of 4
  landers were seen (decisions/gates.md, GATES-19's measured first day).
- Under GATES-20 each re-base re-runs only the units whose traced key changed (about 58% of a judge
  today, by replay). That makes each pass cheaper but does not reduce the number of passes.

## The design

When k ≥ 2 landers are ready and tied, ordered by ticket A < B < C …, the oldest twice-displaced lander
becomes the train's head and takes the next k−1 ready landers, in ticket order, into the train.

- The judge builds stacked candidates: C_A = main + A; C_AB = C_A + B (B's change merged by GATES-19's
  3-way merge onto C_A); C_ABC = C_AB + C; and so on.
- Each stacked candidate is judged in its own slot, all in parallel. Each is judged against its parent
  in the stack (C_AB against C_A), so PRE-EXISTING keeps meaning "red in the parent".
- The verdicts are read in order. The longest green prefix lands: one CAS per member, main → C_A →
  C_AB → …, each CAS the ordinary GATES-19 proof that main is still the base.
- The first red member, and everything stacked on it, does not land. The red member gets its ordinary
  red. The members stacked above it re-base onto the new tip and re-enter as ordinary landers. Their
  displacement counts are not raised, because the train, not a race, displaced them.

## Price

- **The stacked judge's cost.** k slots for one pass instead of k serial passes. With 4 slots a train is
  capped at 4.
  - In the best case, wall time falls from k passes to 1. In box work, slot-judges fall from
    (2 + k)·k/2 to k for the youngest's chain.
  - The cost is that k slots are held at once, so no other lander judges during a train. Head-of-line
    blocking moves from "wait for a re-base" to "wait for a slot".
  - Under GATES-20 the stacked judges reuse within the train: C_AB carries C_A's verdict for every unit
    whose traced key is the same on C_AB. A member that touches disjoint read-sets therefore costs
    mostly its own units.
- **What a red in B does to C.**
  - C_ABC was judged on top of B's change, so its verdict says nothing about C on C_A. C re-bases onto
    whatever landed, A alone, and is judged again.
  - A red in B therefore costs C one extra pass. That is no worse than today, where C would have
    re-based after A and after B anyway.
  - B's red is judged against C_A: PRE-EXISTING means red in C_A. That is the same rule as for any
    lander, read against the parent it would land on.
- **The fail-closed rules it must keep.**
  - Every member's verdict comes from a judge of the exact tree it lands as. A stacked candidate is
    never landed on a verdict about a different tree.
  - Each CAS still refuses a moved main. If main moves outside the train (it cannot while a train holds
    the head under the age bound, but a crash could leave it so), the train aborts and every member
    re-enters.
  - GATES-15/16/17/18 per member: the known-red controls, NOT JUDGED on a timeout or kill (that member
    and all above it do not land), standing-only rows, and owners per member's own message and paths.
  - A conflict in the stacked 3-way merge (B onto C_A) refuses B by name, as at entry. B leaves the
    train; C is re-stacked onto C_A.
  - A carried verdict needs a byte-identical traced key on the stacked tree, which `rebase.py verify`
    re-keys exactly as for a re-base.
  - The age bound still applies: a member displaced out of a train keeps its count.

## Open questions for ROOT

- **Train membership.** Only twice-displaced landers, or every ready lander behind the head? Only the
  tied ones is the smallest change. Every ready lander gives more throughput, but holds more slots.
- **One slot reserved.** Should one slot stay free for a lander that is not in the train? That would
  cap a train at 3.
