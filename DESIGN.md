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

Chapter 2 keeps one stable public module per book topic and divides only the large implementations:

1. `SocialChoiceFunctions`: Section 2.1, implemented by `Definitions`, `MayTheorem`, and `Examples`.
2. `InfluencesAndDerivatives`: Section 2.2, implemented by `BooleanInfluence`,
   `DiscreteDerivatives`, and `DegreeOneRigidity`.
3. `TotalInfluence`: Section 2.3, implemented by `Basic`, `MajorityInfluence`,
   `MajorityOptimality`, `EvenMajority`, `LaplacianAndPoincare`, and `EdgeIsoperimetric`.
4. `NoiseStability`: Section 2.4, implemented by `NoiseKernels`, `CorrelatedGaussianLimit`,
   `GaussianDisagreement`, `NoiseOperator`, `FourierFormulas`, and `StableInfluence`.
5. `Arrow`: Section 2.5 and its Condorcet-election consequences.
6. `ArrowLevelOneBound`: the level-one estimate used by Theorem 2.57.
7. `FKN`: the deferred FKN proof required by Corollary 2.60.

Chapter 3 follows the five book sections while separating pure mathematics from oracle-program
semantics at the final highlight:

1. `LowDegreeSpectralConcentration`: Section 3.1.
2. `SubspacesAndDecisionTrees`: Section 3.2, implemented by `VectorFourier`, `Subspaces`,
   `DecisionTrees`, and `DecisionTreeFourier`.
3. `Restrictions`: Section 3.3.
4. `LearningTheory`: Section 3.4, implemented by `Program`, `FourierEstimation`, `LearningModel`,
   `FiniteFamily`, and `LowDegree`.
5. `GoldreichLevin`: the pure Section 3.5 Fourier identities and estimator, implemented by
   `RestrictedWeights`, `Estimator`, `PrefixBuckets`, and `Controller`.
6. `GoldreichLevinAlgorithm`: the adaptive membership-query algorithm, implemented by `Estimation`,
   `Adaptive`, and `Resources`.
7. `QueryLearning`: membership-query simulation of the finite-family learner.
8. `KushilevitzMansour`: the two-stage composition, Theorems 3.37--3.38, and their explicit
   polynomial resource bounds.

## Module granularity and navigation

The Blueprint always follows the book's chapters and sections; implementation splits never create
new book headings. A large section keeps its original module path as a public-import aggregate, and
its implementation files live in the matching directory with mathematical names. Thus
`FABL.Chapter02.NoiseStability` remains the user-facing import even though its proofs are distributed
under `FABL/Chapter02/NoiseStability/`.

Proof modules target 150--900 lines. Files above 900 lines receive an explicit cohesion review and
remain intact when a split would obscure one mathematical construction; files approaching 1200
lines are split at a real theorem, representation, or API boundary. This keeps the library within
the ordinary size range of proof-bearing Mathlib and CSLib modules without turning the source tree
into arbitrary numbered fragments. Blueprint declaration links point to the exact implementation
file, while aggregate imports preserve predictable navigation from the book structure.

## Statement ownership and deferred proofs

The canonical public declaration belongs to the earliest chapter in which the book formally states
the result. This applies even when the book defers the proof: Theorem 2.45 is first a Chapter 2 API
although its book proof appears in Chapter 5, and FKN is first used as a Chapter 2 API although its
book proof appears in Chapter 9.

When those later chapters are formalized, their Blueprint items must associate with the same Lean
declarations. They must not restate or reprove the result under a second public name. A proof helper
is moved out of the first-statement module only when a later production theorem genuinely reuses it;
the extraction then follows the mathematical dependency DAG and preserves the public API.

## Domains are theorem-local

FABL does not define one global “Boolean cube”. Chapter 1 uses both
`SignCube n = Fin n → ℤˣ`, an exact two-point sign alphabet, and
`F₂Cube n = Fin n → ZMod 2`, an additive vector space. Book-like scoped notations render these as
`{−1,1}^[n]` and `𝔽₂^[n]`.

The two representations receive a bridge only where a theorem crosses them. In particular, the BLR
input and acceptance predicate stay in `𝔽₂`, while its Fourier proof uses an explicit sign encoding.
This makes a domain mismatch visible in the type checker instead of hiding it behind a global
typeclass.

## Computational-complexity boundary

Chapter 3 uses the oracle model stated in the book, not a Turing-machine encoding. A learner treats
the unknown Boolean function as a unit-cost random-example or membership-query oracle. FABL models
this with a finite access-indexed program syntax, constructor-derived sample and query counts,
explicit local-work charges, a `PMF` semantics, and a finite hypothesis representation. The
Goldreich--Levin implementation must impose explicit bucket and iteration caps, with an abort
outcome, so its polynomial charged-work bound is pathwise and worst-case rather than conditioned on
the estimates being accurate.

The formal cost model distinguishes facts derived from constructors from declared local-work
charges. Query counts are forced by visible `query` nodes. Deterministic finite-set bookkeeping is
charged through visible `tick` nodes; the controller charge is therefore part of the program
semantics, but is not presented as a theorem about Lean's native evaluator. The completed bounds
are target-independent and pathwise: Goldreich--Levin uses at most
`2^21 * n * (n + 1) / τ^8` queries and `2^25 * n * (n + 1)^2 / τ^8` charged work, while the
zero-safe Kushilevitz--Mansour wrapper uses at most
`2^40 * (n + 1)^2 * (M + 1)^8 / ε^10` queries and
`2^42 * (n + 1)^3 * (M + 1)^8 / ε^10` charged work. Substituting the proved
Fourier-one-norm family bound closes the advertised polynomial dependence on `n`, `s`, and
`1 / ε`.

Scheduler inputs remain finite positive rationals. Proposition 3.40 nevertheless covers the book's
arbitrary positive real accuracy and confidence parameters: rational density supplies witnesses
between one half and all of each input clipped at `1/2`, and event monotonicity transfers the
concentration result. This factor-two bridge preserves the asymptotic resource dependence without
silently narrowing the book statement. The associated theorem also gives explicit sample,
membership-query, and charged-work bounds in the original real parameters.

This is a narrow book-specific adapter. Mathlib supplies `PMF`, uniform finite distributions,
concentration inequalities, rational arithmetic, finite combinatorics, and asymptotic bounds. FABL
does not encode the target truth table as ordinary Turing-machine input: doing so changes an
oracle problem on `n` variables into an input of length `2^n` and no longer states the book's
result.

The Lean Computer Science Library, `leanprover/cslib`, was audited at its matching `v4.30.0`
release. Its governance includes Stanford representation, and it is the project most likely meant
by the Stanford TCS-library reference. It provides PAC learning definitions, `TimeM`, and
deterministic polynomial-time Turing machines, but no combined
randomized membership-query cost model; `TimeM` also treats timing annotations as trusted. It is
therefore a future adapter target, not a Chapter 3 dependency. Re-audit Mathlib, CSLib, and a
specialized complexity library such as `SamuelSchlesinger/complexitylib` at the first book item
that genuinely quantifies over a machine model, a complexity class such as `P`, `NP`, or `BPP`, or
polynomial-time reductions. At the present audit snapshot, `complexitylib` is the closer technical
match for Chapter 7: it exposes deterministic, nondeterministic, and probabilistic multi-tape
machines, standard complexity classes, reductions, circuits, and Cook--Levin. It is nevertheless a
development-branch dependency with no published releases, so pinning it years before the first use
would create needless upgrade risk. Do not add a machine model merely because a finite oracle
algorithm has a polynomial resource bound.

The first definite full-book trigger is Sections 7.3--7.4. Their CSP approximation and hardness
statements quantify over polynomial-time algorithms, NP-hardness, Circuit-Sat reductions, PCPP
reductions, and Håstad-style hardness. Before Chapter 7 construction begins, re-audit the then-pinned
versions of Mathlib, CSLib, and `complexitylib`; formalize the finite CSP mathematics independently,
then connect the book-facing hardness statements through a narrow adapter to the selected machine,
encoding, and reduction APIs. Chapter 6 learning algorithms and Chapter 8 query-complexity results
remain oracle/decision-tree mathematics unless an individual statement explicitly crosses this
boundary.

An earlier optional trigger would be a future decision to formalize Exercise 3.45's one-way
permutation, pseudorandom-generator, and efficient-adversary claims. That exercise is not part of
the locked Chapter 3 theorem/support inventory; it must not silently broaden the current dependency
surface.

Do not confuse CSLib with `Shilun-Allan-Li/tcslib`. The latter is a separate theoretical-computer-
science project whose current `main` pins Lean 4.25 and focuses on Boolean-function analysis and
error-correcting codes. It can be studied as prior art, but it neither matches FABL's 4.30 toolchain
nor supplies the machine/reduction boundary needed for Chapter 7, so it is not an upstream
dependency.

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

## Reuse roadmap after Chapters 1 and 2

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

Chapter 2 additionally reuses Mathlib's `PMF` product and bind laws for correlated pairs, finite
expectation and Fourier bases for influence identities, characteristic functions and Lévy
continuity for the bivariate central limit theorem, Portmanteau for null-boundary events, Gaussian
density measures, and the polar-coordinate change-of-variables theorem. The local work is the
book-specific finite-cube interface and the proof chains for total influence, majority noise
stability, Arrow's theorem, the level-one bound, and FKN.

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
