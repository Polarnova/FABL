# FABL design and Mathlib reuse boundary

## Book-first physical structure

The module tree follows O'Donnell's section sequence because coverage, proof dependencies, and
statement fidelity are the immediate engineering problem. A mature subject taxonomy can be
extracted later when two or more chapters actually share an API. This avoids speculative `Core`,
`Common`, and `Utils` modules.

Chapter 1 is split at the book's mathematical boundaries:

1. `FunctionsAsMultilinearPolynomials`: Sections 1.1–1.2, including the two cube types,
   interpolation, monomials, and the `𝔽₂` parity character.
2. `ParityBasis`: Section 1.3, including normalized inner products and Walsh bases.
3. `BasicFourierFormulas`: Section 1.4, including coefficients, Parseval, Plancherel, distance,
   variance, covariance, and spectral samples.
4. `ProbabilityDensitiesAndConvolution`: Section 1.5.
5. `BLR`: Section 1.6.

## Domains are theorem-local

FABL does not define one global “Boolean cube”. Chapter 1 uses both
`SignCube n = Fin n → ℤˣ`, an exact two-point sign alphabet, and
`F₂Cube n = Fin n → ZMod 2`, an additive vector space. Book-like scoped notations render these as
`{−1,1}^[n]` and `𝔽₂^[n]`.

The two representations receive a bridge only where a theorem crosses them. In particular, the BLR
input and acceptance predicate stay in `𝔽₂`, while its Fourier proof uses an explicit sign encoding.
This makes a domain mismatch visible in the type checker instead of hiding it behind a global
typeclass.

## Audited Mathlib reuse

The following are direct dependencies, not reimplementations:

| Book concept | Mathlib abstraction | Key declarations |
|---|---|---|
| Uniform expectation | `Finset.expect` | `Fintype.expect_eq_sum_div_card`, `Fintype.expect_equiv`, `Fintype.expect_mul_expect` |
| Normalized inner product | weighted inner product | `RCLike.wInner`, `RCLike.cWeight`, `RCLike.wInner_cWeight_eq_expect` |
| Walsh character | finite additive character | `AddChar.zmodChar`, `AddChar.expect_eq_ite`, `AddChar.wInner_cWeight_eq_boole`, `AddChar.linearIndependent` |
| Function-space basis | finite-dimensional basis | `basisOfLinearIndependentOfCardEqFinrank`, `Module.Basis.sum_repr` |
| Multilinear interpolation | finite product expansion | `Fintype.prod_boole`, `Fintype.prod_add` |
| Cardinalities | finite-type API | `Fintype.card_pi_const`, `Fintype.card_finset`, `Fintype.card_units_int` |
| Hamming distance | information theory | `hammingDist`, `hammingDist_triangle` |
| Genuine finite distribution | probability mass functions | `PMF.ofFintype`, `PMF.uniformOfFintype`, `PMF.integral_eq_sum` |
| Algebraic convolution | discrete convolution | `DiscreteConvolution.addConvolution`, `DiscreteConvolution.addConvolution_comm` |
| Finite dual and extrema | linear duality and finite orders | `AddMonoidHom.toZModLinearMap`, `dotProductEquiv`, `Finite.exists_max` |
| Sign exponentiation | `ZMod 2` action on integer units | `uzpow_add` |

The subset-indexed real Walsh family is bundled as `AddChar` first. Its basis proof should obtain
orthogonality and linear independence from Mathlib, then use cardinality to prove completeness. It
must not reproduce a coordinate-flipping orthogonality proof unless the general character theorem
is shown inadequate.

## Thin FABL adapters

FABL owns only these adapters:

- subset indexing `Finset (Fin n) ↦ AddChar (F₂Cube n) ℝ`;
- transport between the additive and sign cubes at explicit representation changes;
- the normalization factor turning Mathlib's raw discrete convolution into the book's expectation;
- the real nonnegative density relative to uniform measure and its conversion to `PMF`;
- normalization of `hammingDist` to a real relative distance.

The genuine local theorem gaps are the unique multilinear expansion, the subset-indexed real Walsh
transform API, the finite Boolean-cube Fourier–convolution theorem, and BLR.

## Reuse roadmap after Chapter 1

The reference audit found no helper layer from `lean-booleanfun` that should be copied. Chapter 1
already uses the strongest local Mathlib APIs for finite expectation, characters, bases, Hamming
distance, PMFs, duality, finite extrema, and raw convolution. The density API is connected to
Mathlib's probability semantics by point-mass and integral theorems, and Proposition 1.26 is stated
as an exact `PMF.bind`/`PMF.map` law. The remaining bridges are deliberately deferred until a
production theorem needs them:

1. Relate `uniformLpNorm` to `MeasureTheory.lpNorm` for the uniform finite measure before the first
   chapter that needs Hölder, Minkowski, or norm monotonicity.
2. Add an inverse bridge from `PMF` to `ProbabilityDensity` only if a later construction starts from
   an arbitrary PMF rather than a book-defined density.
3. Relate finite `mean`, `variance`, and `covariance` facades to Mathlib's probability-moment API
   before results need general measure-theoretic moment inequalities.

These are representation bridges, not replacements for the book-facing finite definitions. They
should be added only with an immediate downstream theorem, preserving the no-speculative-abstraction
rule.

## Reference-only use of `lean-booleanfun`

The repository `roos-j/lean-booleanfun` is cited prior art, not an upstream dependency. Its current
architecture was audited at commit `a76446e4`. FABL intentionally replaces its custom expectation
with `Finset.expect`, avoids installing new normed/inner-product instances on function types, uses
`AddChar` orthogonality instead of bit-flip proofs, uses Mathlib's `hammingDist`, and treats its
`ToMathlib` lemmas as search prompts rather than code to copy.

## Proof closure

Each Verso block contains the complete book-facing statement and uses `lean :=` to associate it with
compiled FABL declarations. The Blueprint contains no second prose proof: formal proofs live only in
the production Lean library. Reviewed `uses :=` edges describe the mathematical dependency DAG;
proof-term dependency extraction may be used as an additional audit, but does not replace that
conceptual graph.

Verso generates declaration status, source information, the manifest, dependency graph, summary,
HTML, and PDF. A declaration is complete only when its local module and the full project build, the
forbidden-token scan is empty, every external declaration resolves, the Verso site and consistency
check pass, and statement fidelity has been checked against the book.

## Maintained and generated artifacts

- Maintained: `FABL/**/*.lean` and `blueprint-verso/FABLBlueprint/**/*.lean`.
- Generated: `blueprint-verso/_out/`, including HTML, PDF, manifests, graphs, summaries, and status.
- Deliberately absent: a YAML coverage ledger, TeX Blueprint, handwritten proof-status file, and
  duplicate natural-language proofs.
