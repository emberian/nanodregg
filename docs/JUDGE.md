# Landing and checking changes

A landing rebases on origin/main, builds the changed modules and their dependents, runs the affected tests and journeys, then pushes to main. Documentation-only changes require no build. The commit message explains what changed and what the system can do because of it.

Use git fetch origin, git rebase origin/main and git push origin HEAD:main from the lane's own worktree. Resolve a rebase conflict against both changes. If main moves again before the push, fetch, rebase and retry. Keep the worktree's build products and Cargo target separate from other lanes.

Whole-system validation is a periodic report through scripts/converge or its successor. It builds the tree, runs the rows and tests, and attributes failures to the changes that introduced them. A reported failure becomes work for that change's owner to fix forward.

Per-landing judge slots, displacement queues and message-form gates are not part of this workflow. Censuses, vector tables, pins, ceilings, TCB and waste measurements serve the convergence report. Existing source-check implementations cover closure, refusals, size, paths, runs, rebase, TCB, vectors, waste, owners and targets; they are evidence tools, not landing authorization.

Keep design decisions in the layer's decision ledger, with critique and meta-critique. Write an entry for a real design choice rather than for every commit.

Use the designated build host and swarm-build resource budget. Keep tests filtered to the affected behavior. Stop only a process identified by its own PID file; never kill by a name pattern. Do not stash shared work or delete another lane's files or caches.

[Spec](../Spec/README.md) defines the composed assurance claims and their premises. A passing build or convergence report does not establish a theorem's meaning or non-vacuity.
