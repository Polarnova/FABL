# FABL: Formal Analysis of Boolean Functions in Lean

FABL is a Lean 4 and Mathlib formalization of Ryan O'Donnell's
[*Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386), following the May 2021
edition. It develops the book's results as a reusable theorem library while preserving the domains,
normalizations, and hypotheses of the original statements.

## Status

Chapters 1--5 are complete. The Blueprint includes open conjectures and non-dependency remarks as
statement nodes. Every associated Lean declaration is proved and kernel-checked.

| Chapter | Subject | Book items | Lean declarations | Dependency edges |
|---|---|---:|---:|---:|
| 1 | Boolean functions and Fourier expansion | 43 | 111 | 62 |
| 2 | Influence and noise sensitivity | 79 | 241 | 185 |
| 3 | Spectral structure and learning | 62 | 399 | 164 |
| 4 | DNF formulas and small-depth circuits | 45 | 360 | 111 |
| 5 | Majority and threshold functions | 108 | 502 | 259 |
| **Total** |  | **337** | **1613** | **781** |

The project aims to formalize the complete book. Book-item totals count complete inventory nodes;
declaration totals count their compiled Lean associations. Open or external statement-only nodes
remain visible in the graph, and every dependency edge is mathematically reviewed.

Chapter 5 uses the latest release of
[`ProbabilityApproximation`](https://github.com/Polarnova/ProbabilityApproximation).

## Using FABL

The repository pins its Lean and Mathlib versions. After cloning, obtain the precompiled Mathlib
cache, fetch and verify the pinned precompiled probability release, and build the library:

```bash
lake exe cache get
lake build @ProbabilityApproximation:release
./scripts/verify_probability_approximation_release.sh
lake build
```

The `release` facet supplies the matching precompiled Bentkus and Berry--Esseen artifacts.

The root module imports every verified library module:

```lean
import FABL
```

## Book and dependency graph

The Verso Blueprint presents the book-facing statements beside their Lean declarations and records
the reviewed dependency graph. To build and serve it locally:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve dev
```

Then open [http://localhost:8000/](http://localhost:8000/). Generate the printable book with:

```bash
./scripts/site.sh pdf
```

The generated site, PDF, manifest, and graph live under `blueprint-verso/_out/`; they are build
artifacts and are not committed. The `dev` HTML profile retains fidelity metadata for review;
the default `release` profile omits those tags from the reader-facing pages.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the statement-inventory, Mathlib-reuse, proof, Blueprint, and
verification contracts, including representation choices and the boundary between Mathlib reuse
and local formalization. Contributions should reuse Mathlib or an earlier FABL result whenever
possible and add a local theorem only for a genuine gap.

## References and prior work

- Ryan O'Donnell, [*Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386), May 2021.
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  FABL.
- [ProbabilityApproximation](https://github.com/Polarnova/ProbabilityApproximation), containing the
  quantitative normal-approximation theorems used in Chapter 5.
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint), used for the book and dependency
  graph.
- [roos-j/lean-booleanfun](https://github.com/roos-j/lean-booleanfun), cited as earlier Lean 4 work
  on Boolean-function analysis. FABL is an independent formalization based on Mathlib.

## License

FABL is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
