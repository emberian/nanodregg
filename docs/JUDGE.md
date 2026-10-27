# Landing and checking changes

A landing rebases on origin/main, builds the changed modules and their dependents, runs the affected tests and journeys, then pushes to main. Documentation-only changes require no build. The commit message explains what changed and what the system can do because of it.

`scripts/commit` does this from the lane's own worktree: commit with git, then run it (or name paths: `scripts/commit -F MESSAGE PATH...`). It replays the commit onto origin/main, builds what the change touched and runs the rows it reaches in `~/nd-land/<worktree>/` on the home disk (the NVMe on the build host), at idle priority under swarm-build, and pushes. A conflict stops it and names the paths; resolve it against both changes and run it again. If main moves before the push it rebases and pushes again, rebuilding only when main changed one of the same paths. A build killed by its memory cap reads NOT BUILT, never red.

Whole-system validation is a periodic report through scripts/converge or its successor. It builds the tree, runs the rows and tests, and attributes failures to the changes that introduced them. A reported failure becomes work for that change's owner to fix forward.

Nothing else judges a landing: there are no judge slots, no queue, no message-form lines. The census, the codec vector table, the TCB table and the waste ceilings are read by the convergence report. The source checks it prints (gates/check.py) cover module closure, refusal names, the 1 MB file law, paths, the runs table, the TCB table, the codec vectors and the waste ratchet.

Keep design decisions in the layer's decision ledger, with critique and meta-critique. Write an entry for a real design choice rather than for every commit.

Build with `scripts/nd-build lake build …` (or `cargo …`): it takes one of the six box-wide build slots that landings share, runs at idle priority under swarm-build at SWARM_MEM_MAX (6G a module, 24G a tree). Keep tests filtered to the affected behavior. Stop only a process identified by its own PID file; never kill by a name pattern. Do not stash shared work or delete another lane's files or caches.

[Spec](../Spec/README.md) defines the composed assurance claims and their premises. A passing build or convergence report does not establish a theorem's meaning or non-vacuity.
