# SIZE — the ratchet (law 12)

`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs
`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 6387 | — |
| protocol operations | 6 | 6 |
| call kinds (Receive.Body constructors) | 10 | 10 |
| command verbs (the one command language) | 0 | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 12 (Protocol/Rows.lean: 11 member rows + lang-journey; every op reached: every_op_has_a_row) | — |
| refusal constructors | 40 | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 2756 | — |
| Rust lines (client/src) | 1555 | 2000 |
| partial defs (deployed) | 0 | 0 |
| theorems | 288 | — |
| sorry | 0 | 0 |
| Lean modules | 85 | — |
| Lean proof-modules | 31 | — |
| Lean lines (Census) | 89 | — |
| Lean lines (Codec) | 1813 | — |
| Lean lines (Emit) | 322 | — |
| Lean lines (Host) | 1677 | — |
| Lean lines (Kernel) | 2641 | — |
| Lean lines (Protocol) | 801 | — |
| max dependents of one module | 61 | — |
| native (extern/implemented_by) | 8 | 8 |
| C lines | 0 | 146 |
| Lean lines (Lang) | 3302 | — |
