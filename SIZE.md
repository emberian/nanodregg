# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 9081 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Body constructors) | 9 | 10 |
| command verbs (the one command language) | 11 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 12 (Protocol/Rows.lean: 11 member rows + lang-journey; every op reached: every_op_has_a_row) | — |
| refusal constructors | 42 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 3544 | — |
| Rust lines (client/src) | 1703 | 2000 |
| Rust lines (generated) | 393 | — |
| Rust files with an unregistered generated header | 0 | 0 |
| partial defs (deployed) | 0 | 0 |
| theorems | 581 | — |
| sorry | 0 | 0 |
| Lean modules | 124 | — |
| Lean proof-modules | 52 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 4131 | — |
| Lean lines (Emit) | 344 | — |
| Lean lines (Host) | 2397 | — |
| Lean lines (Kernel) | 3659 | — |
| Lean lines (Protocol) | 1790 | — |
| max dependents of one module | 92 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 5464 | — |
