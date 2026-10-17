# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 10057 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Body constructors) | 9 | 10 |
| command verbs (the one command language) | 11 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 12 (Protocol/Rows.lean: 11 member rows + lang-journey; every op reached: every_op_has_a_row) | — |
| refusal constructors | 42 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 3568 | — |
| Rust lines (client/src) | 1703 | 2000 |
| Rust lines (generated) | 417 | — |
| Rust files with an unregistered generated header | 0 | 0 |
| partial defs (deployed) | 0 | 0 |
| theorems | 608 | — |
| sorry | 0 | 0 |
| Lean modules | 130 | — |
| Lean proof-modules | 54 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 4133 | — |
| Lean lines (Emit) | 351 | — |
| Lean lines (Host) | 2420 | — |
| Lean lines (Kernel) | 4312 | — |
| Lean lines (Protocol) | 2703 | — |
| max dependents of one module | 98 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 5464 | — |
