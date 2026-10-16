# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 701 | — |
| protocol operations | unmeasured | 40 |
| refusal constructors | unmeasured | — |
| Rust lines | 686 | — |
| Rust lines (client/src) | 517 | 2000 |
| partial defs (deployed) | 0 | 0 |
| theorems | 27 | — |
| sorry | 0 | 0 |
| Lean modules | 10 | — |
| Lean proof-modules | 3 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Host) | 262 | — |
| Lean lines (Kernel) | 722 | — |
| max dependents of one module | 4 | — |
| native (extern/implemented_by) | 0 | — |
