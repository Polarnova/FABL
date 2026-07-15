# FABL: Formal Analysis of Boolean Functions in Lean

FABL is a Lean 4 and Mathlib formalization of Ryan O'Donnell's
[*Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386), following the May 2021
edition. It develops the book's results as a reusable theorem library while preserving the domains,
normalizations, and hypotheses of the original statements.

## Status

Chapters 1--4 are complete. Open conjectures and non-dependency remarks are represented honestly as
statement-only Blueprint nodes rather than placeholder Lean declarations; neither supplies an
assumption to the production library. The production library contains no `sorry`, project-defined
axioms, or unsafe proof shortcuts.

| Chapter | Subject | Book items | Lean declarations | Dependency edges |
|---|---|---:|---:|---:|
| 1 | Boolean functions and Fourier expansion | 43 | 111 | 62 |
| 2 | Influence and noise sensitivity | 78 | 240 | 183 |
| 3 | Spectral structure and learning | 62 | 399 | 164 |
| 4 | DNF formulas and small-depth circuits | 45 | 360 | 111 |
| **Total** |  | **228** | **1110** | **520** |

The project aims to formalize the complete book. Book-item totals count complete inventory nodes;
declaration totals count their compiled Lean associations. Open or external statement-only nodes
remain visible without placeholder declarations, and every dependency edge is mathematically
reviewed.

## Using FABL

The repository pins its Lean and Mathlib versions. After cloning, obtain the precompiled Mathlib
cache and build the library:

```bash
lake exe cache get
lake build
```

The root module imports every verified production module:

```lean
import FABL
```

Source modules follow the chapters and sections of the book under `FABL/Chapter01`,
`FABL/Chapter02`, `FABL/Chapter03`, and `FABL/Chapter04`. Larger sections expose a stable
section-level import and are internally divided at mathematical boundaries.

## Book and dependency graph

The Verso Blueprint presents the book-facing statements beside their Lean declarations and records
the reviewed dependency graph. To build and serve it locally:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve
```

Then open [http://localhost:8000/](http://localhost:8000/). Generate the printable book with:

```bash
./scripts/site.sh pdf
```

The generated site, PDF, manifest, and graph live under `blueprint-verso/_out/`; they are build
artifacts and are not committed.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the statement-inventory, Mathlib-reuse, proof, Blueprint, and
verification contracts. [`DESIGN.md`](DESIGN.md) documents representation choices, the audited
Mathlib boundary, and the treatment of algorithmic complexity. Contributions should reuse Mathlib
or an earlier FABL result whenever possible and add a local theorem only for a genuine gap.

## References and prior work

- Ryan O'Donnell, [*Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386), May 2021.
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  FABL.
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint), used for the book and dependency
  graph.
- [roos-j/lean-booleanfun](https://github.com/roos-j/lean-booleanfun), cited as earlier Lean 4 work
  on Boolean-function analysis. FABL is a from-scratch implementation and does not import, vendor,
  or copy that repository.

## License

FABL is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
