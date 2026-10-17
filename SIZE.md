# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 5545 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Call constructors) | 0 | 7 |
| command verbs (the one command language) | 0 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 11 (Protocol/Rows.lean; every op reached: every_op_has_a_row) | — |
| refusal constructors | 40 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 2492 | — |
| Rust lines (client/src) | 1535 | 2000 |
| partial defs (deployed) | 0 | 0 |
| theorems | 278 | — |
| sorry | 0 | 0 |
| Lean modules | 77 | — |
| Lean proof-modules | 29 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 1392 | — |
| Lean lines (Emit) | 279 | — |
| Lean lines (Host) | 1372 | — |
| Lean lines (Kernel) | 2641 | — |
| Lean lines (Protocol) | 815 | — |
| max dependents of one module | 53 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 3047 | — |
