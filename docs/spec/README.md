# The Objective Bend specification

Objective Bend is the language of nanodregg's packages: the core term language, its type checker, the machine that runs it, and the rules by which a checked package is installed and its methods and laws are run inside a World.
This specification restates the Lean definitions of the language at `main` `276ded8`, chapter by chapter, in the arrangement of the WebAssembly specification.

| chapter | contents |
|---|---|
| [0 Conventions](0-conventions.md) | notation, rule format, normative source |
| [1 Introduction](1-introduction.md) | what the language is, its design goals, scope, dependencies, an overview, what is in flight |
| [2 Structure](2-structure.md) | abstract syntax: types, terms, primitives, packages, relations, holes, claims, grades, calls |
| [3 Validation](3-validation.md) | the typing rules, and the install check of a package |
| [4 Execution](4-execution.md) | the machine, ticks and the budget, installing, loading, running a method, laws judged per act, the contextual semantics |
| [5 Binary format](5-binary.md) | the package wire, version 10, byte by byte, with worked examples |
| [6 Appendix](6-appendix.md) | the soundness statements the tree proves, the bounds, the index of rules and refusals |

The kernel the language runs under is specified in [`docs/reference/kernel.md`](../reference/kernel.md), and the member protocol in [`docs/reference/protocol.md`](../reference/protocol.md).
