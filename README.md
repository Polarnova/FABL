# FABL

**Formal Analysis of Boolean Functions in Lean** is an independent Lean 4 and Mathlib
formalization of Ryan O'Donnell's *Analysis of Boolean Functions*.

## Current objective

The first release target is complete coverage of the definitions and proved statements in Chapters
1 and 2. Results stated there whose proofs are deferred to later chapters remain explicit dependency
nodes. End-of-chapter exercises are included only when a main-text proof depends on them.

Chapter 1 is **proof-complete**. Its 34 primary nodes—31 consecutively numbered items, Parseval,
Plancherel, and the BLR Test—have book-facing Lean declarations and kernel-checked proofs. The root
project builds with no `sorry`, `admit`, project-defined `axiom`, `unsafe`, or `native_decide` in
production Lean sources. The generated Blueprint connects every complete book-facing statement to
its compiled Lean declarations. Chapter 2 remains the next coverage target.

Coverage means that every in-scope book item has:

- a source identifier and a Mathlib-style Lean declaration name;
- a fidelity classification recording whether the Lean statement is exact or more general;
- a kernel-checked proof with no unproved declarations or project-defined axioms;
- a reviewed mathematical dependency path from the book statement to the compiled Lean source.

## Architecture

The source tree follows the book rather than imposing a mature subject taxonomy prematurely:

```text
FABL/
  Chapter01/
    FunctionsAsMultilinearPolynomials.lean
    ParityBasis.lean
    BasicFourierFormulas.lean
    ProbabilityDensitiesAndConvolution.lean
    BLR.lean
  Chapter02/
    SocialChoiceFunctions.lean
    InfluencesAndDerivatives.lean
    TotalInfluence.lean
    NoiseStability.lean
    Arrow.lean
```

Each section chooses the domain representation stated by the mathematics it formalizes. FABL does
not preselect one universal Boolean cube. Bridges are introduced only when a production theorem
actually crosses representations.

`FABL.Mathlib` publicly imports the complete pinned Mathlib release. Before adding a declaration,
contributors must search Mathlib first. An exact existing result is reused directly; a more general
result proves the book-facing theorem; a representation mismatch receives a thin bridge; only a
genuine gap is implemented locally.

The Chapter 1 implementation backbone is:

- `Finset.expect` for normalized finite expectation;
- `RCLike.wInner RCLike.cWeight` for the normalized inner product;
- `AddChar` and finite-character orthogonality for Walsh characters;
- `Module.Basis` for subset-indexed real Walsh bases;
- `hammingDist` for disagreement counting;
- `PMF` for the genuine distributions induced by real densities;
- `DiscreteConvolution.addConvolution` for the unnormalized algebraic convolution core.

FABL adds only the book-specific indexing, normalization, representation bridges, and results that
Mathlib does not already provide. See `DESIGN.md` for the audited reuse boundary.

## Construction workflow

FABL uses the Blueprint pattern illustrated by the
[PFR formalization](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/):

1. transcribe every in-scope book item, including its hypotheses, quantifiers, domains, and displayed
   formulas, into the matching Verso section;
2. search Mathlib and classify each needed declaration as direct reuse, specialization, thin
   representation bridge, or genuine local theorem;
3. write and audit the exact Lean statements before starting their proofs;
4. attach each statement to compiled declarations with `lean :=` and record its reviewed
   mathematical dependencies with `uses :=`;
5. prove only dependency-ready leaves; proofs live exclusively in the production Lean library;
6. close each leaf with a narrow module build, then close the chapter with the full build, Blueprint
   validation, and a second statement-fidelity audit against the book.

Book order determines physical modules and source coverage. The Blueprint dependency graph
determines proof order; these are deliberately different concerns.

## Build

```bash
lake update
lake exe cache get
lake build
rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b' FABL FABL.lean
```

The root `FABL.lean` imports every production module, so the default build checks the entire
formalization.

The book-facing Blueprint is itself Lean source and uses the official
[Verso Blueprint](https://github.com/leanprover/verso-blueprint):

```bash
cd blueprint-verso
lake update
lake exe cache get
./scripts/site.sh build
lake exe vbp check
./scripts/site.sh serve
```

Open [http://localhost:8000/](http://localhost:8000/). Do not open the generated HTML through
`file://`; the dependency graph and other browser assets require an HTTP server. Generate the PDF
with `./scripts/site.sh pdf`.

Lake builds are incremental: the reported job count is the size of the checked dependency graph,
not the number of modules recompiled. `site.sh` performs one aggregate Lake build; Verso 4.30 then
renders the complete HTML site because its generated preview cache is an output artifact, not an
incremental renderer cache.

The maintained sources are `FABL/**/*.lean` for formal declarations and proofs, and
`blueprint-verso/FABLBlueprint/**/*.lean` for complete book-facing statements, declaration links,
and reviewed dependency metadata. Blueprint HTML, PDF, manifest, graph, summary, and status are
generated under `blueprint-verso/_out/` and must not be edited. There is no separately maintained
YAML coverage ledger, TeX Blueprint, proof-status file, or prose proof.

## Source

The normative source is the May 2021 arXiv edition of
[Analysis of Boolean Functions](https://arxiv.org/abs/2105.10386).

## Acknowledgements

FABL is a from-scratch formalization. Its design benefits from studying
[roos-j/lean-booleanfun](https://github.com/roos-j/lean-booleanfun), an earlier Lean 4
formalization of foundational results in the analysis of Boolean functions. FABL neither imports nor
depends on that repository. The reuse audit used its `main` snapshot at commit `a76446e4` only as a
reference for comparing proof architecture and Mathlib coverage; no source was copied.
