# SIZE — the ratchet (counts may only fall unless the commit message says why)

| metric | now | ceiling |
|---|---|---|
| Lean modules in the Host closure | 0 | 150 |
| Lean lines (deployed) | 0 | — |
| protocol operations | 6 (Protocol/Table.lean; minidregg 186) | 6 |
| call kinds (Receive.Call constructors) | 0 committed; 7 named by rows (enroll birth delegate write install invoke rotate; minidregg ~38 families) | 7 |
| command verbs (the one command language) | 0 committed; ~15 planned (minidregg: 127 mini + 116 Host CLI) | 20 |
| protocol status / step codes | 4 / 4 | — |
| conformance rows | 11 (Protocol/Rows.lean; every op reached: every_op_has_a_row) | — |
| refusal constructors | 20 (Kernel.Reject, committed) + Receive.Refusal when committed | — (ratchet: may only fall without a row that needs the new one) |
| Rust lines | 686 (client/src; +251 plant lines in client/tests) | 2,000 (client/src) |
| partial defs (deployed) | 0 | 0 |
| theorems | 0 | — |
| sorry | 0 | 0 |
