# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 3350 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Call constructors) | 0 | 7 |
| command verbs (the one command language) | 0 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 11 (Protocol/Rows.lean; every op reached: every_op_has_a_row) | — |
| refusal constructors | 41 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 2389 | — |
| Rust lines (client/src) | 1436 | 2000 |
| partial defs (deployed) | 0 | 0 |
| theorems | 191 | — |
| sorry | 0 | 0 |
| Lean modules | 48 | — |
| Lean proof-modules | 17 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 951 | — |
| Lean lines (Emit) | 77 | — |
| Lean lines (Host) | 1191 | — |
| Lean lines (Kernel) | 1665 | — |
| Lean lines (Protocol) | 493 | — |
| max dependents of one module | 22 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 1524 | — |
