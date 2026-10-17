# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 8254 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Body constructors) | 10 | 10 |
| command verbs (the one command language) | 11 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 12 (Protocol/Rows.lean: 11 member rows + lang-journey; every op reached: every_op_has_a_row) | — |
| refusal constructors | 40 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 2826 | — |
| Rust lines (client/src) | 1625 | 2000 |
| partial defs (deployed) | 0 | 0 |
| theorems | 550 | — |
| sorry | 0 | 0 |
| Lean modules | 117 | — |
| Lean proof-modules | 50 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 3841 | — |
| Lean lines (Emit) | 344 | — |
| Lean lines (Host) | 1685 | — |
| Lean lines (Kernel) | 3460 | — |
| Lean lines (Protocol) | 1754 | — |
| max dependents of one module | 85 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 5343 | — |
