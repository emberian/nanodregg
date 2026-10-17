# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 59 | 150 |
| Lean lines (deployed) | 7392 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Body constructors) | 9 | 10 |
| command verbs (the one command language) | 11 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 12 (Protocol/Rows.lean: 11 member rows + lang-journey; every op reached: every_op_has_a_row) | — |
| refusal constructors | 42 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 3695 | — |
| Rust lines (client/src) | 1701 | 2000 |
| Rust lines (generated) | 417 | — |
| Rust files with an unregistered generated header | 0 | 0 |
| partial defs (deployed) | 0 | 0 |
| theorems | 610 | — |
| sorry | 0 | 0 |
| Lean modules | 135 | — |
| Lean proof-modules | 54 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 4133 | — |
| Lean lines (Emit) | 351 | — |
| Lean lines (Host) | 2959 | — |
| Lean lines (Kernel) | 4268 | — |
| Lean lines (Protocol) | 2756 | — |
| max dependents of one module | 103 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 5462 | — |
| Lean lines (tooling: Sim, Rows, Journey, Census, Emit) | 3202 | — |
