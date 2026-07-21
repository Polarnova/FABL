/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06.LearningAndTesting

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Applications in learning and testing" =>

:::theorem "open-problem-random-example-junta-learning" (parent := "fabl-chapter-6") (uses := "definition-2.4, definition-3.27") (tags := "section-6-4, open, problem, statement-only")
*Open problem (learning juntas from random examples).* It is not known
whether $`k`-juntas for any unbounded $`k=\omega(1)` can be learned from
random examples in $`\operatorname{poly}(n)` time. In particular, learning
$`O(\log n)`-juntas this way is a necessary prerequisite for
polynomial-time random-example learning of polynomial-size decision trees,
DNFs, or CNFs.
:::

:::lemma_ "support-k-junta-fourier-gap" (parent := "fabl-chapter-6") (lean := "FABL.inv_two_pow_card_le_abs_fourierCoeff_of_dependsOn, FABL.isRelevant_toReal_of_fourierCoeff_ne_zero, FABL.fourierCoeff_eq_zero_or_inv_two_pow_le_abs_of_isKJunta, FABL.fourierCoeff_eq_zero_or_two_zpow_neg_le_abs_of_isKJunta") (uses := "definition-2.4, proposition-3.21, support-relevant-coordinate-count") (tags := "section-6-4, support, fidelity-exact")
*Fourier gap for juntas.* If
$`f:\{-1,1\}^n\to\{-1,1\}` is a $`k`-junta, then every Fourier coefficient
$`\widehat f(S)` is either $`0` or has
$$`
|\widehat f(S)|\ge2^{-k}.
`
Whenever $`\widehat f(S)\ne0`, every coordinate $`i\in S` is relevant for
$`f`.
:::

:::theorem "theorem-6.36" (parent := "fabl-chapter-6") (lean := "FABL.lowDegreeJuntaCutoff, FABL.lowDegreeJuntaPolynomialDegree, FABL.kJuntaConceptClass, FABL.lowDegreeJuntaLearningFailure, FABL.lowDegreeJuntaHypothesisOfOutput, FABL.lowDegreeJuntaLearningProgram, FABL.lowDegreeJuntaLearningAlgorithm, FABL.lowDegreeJuntaLearningAlgorithm_successProbability_ge, FABL.lowDegreeJuntaLearningAlgorithm_learns, FABL.lowDegreeJuntaLearnerProgram, FABL.lowDegreeJuntaLearnerProgram_failureProbability_le, FABL.lowDegreeJuntaLearnerProgram_depth_le, FABL.lowDegreeJuntaLearnerProgram_cost_le, FABL.lowDegreeJuntaTotalRandomExampleBudget, FABL.lowDegreeJuntaTotalWorkBudget, FABL.lowDegreeJuntaLearnerProgram_cost_le_totalBudget, FABL.lowDegreeJuntaRuntimeExponentLedger, FABL.lowDegreeJuntaNodeBaseResourceExponent, FABL.lowDegreeJuntaNodeWorkResourceExponent, FABL.lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence, FABL.lowDegreeJuntaTotalWorkBudget_le_linearConfidence, FABL.lowDegreeJuntaTotalRandomExampleBudget_isBigO_linearConfidence, FABL.lowDegreeJuntaTotalWorkBudget_isBigO_linearConfidence, FABL.lowDegreeJuntaLearningFailure_eq_dyadicFailure, FABL.lowDegreeJuntaLearningAlgorithm_randomExampleCost_le, FABL.lowDegreeJuntaLearningAlgorithm_workCost_le, FABL.lowDegreeJuntaLearningAlgorithm_randomExampleCost_isBigO, FABL.lowDegreeJuntaLearningAlgorithm_workCost_isBigO") (uses := "definition-3.27, lemma-6.37, support-k-junta-fourier-gap, proposition-3.30, siegenthaler-theorem, support-exercise-6.30") (tags := "section-6-4, fidelity-exact-random-example-runtime")
*Theorem 6.36.* For $`k\le O(\log n)`, the concept class
$$`
\mathcal C
=\{f:\mathbb F_2^n\to\mathbb F_2:f\text{ is a }k\text{-junta}\}
`
can be learned exactly from random examples in time
$$`
n^{(3/4)k}\operatorname{poly}(n).
`
Thus the output agrees with the target on every input, with the constant
high success probability of the learning model.
:::

:::lemma_ "lemma-6.37" (parent := "fabl-chapter-6") (lean := "FABL.JuntaRelevantCoordinateFinder, FABL.recursiveJuntaLearner, FABL.DecisionTreeComputesTarget, FABL.JuntaLearnerOutputBad, FABL.recursiveJuntaLearner_failureProbability_le, FABL.recursiveJuntaLearner_depth_le, FABL.recursiveJuntaLearner_cost_le, FABL.LowDegreeJuntaRootFinderBad, FABL.lowDegreeJuntaRelevantCoordinateProgram_root_failureProbability_le, FABL.lowDegreeJuntaRelevantCoordinateProgram_cost_le, FABL.lowDegreeJuntaRelevantCoordinateFinder, FABL.lowDegreeJuntaDyadicFailure, FABL.lowDegreeJuntaDyadicNodeFailure, FABL.lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence, FABL.lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence") (uses := "definition-2.18, support-exercise-6.31") (tags := "section-6-4, fidelity-exact-random-example-reduction")
*Lemma 6.37.* Theorem 6.36 follows from an algorithm which, given random
examples from a nonconstant $`k`-junta
$`f:\mathbb F_2^n\to\mathbb F_2`, finds at least one relevant coordinate
with probability at least $`1-\delta` in time
$$`
n^{(3/4)k}\operatorname{poly}(n)\log(1/\delta).
`
:::

:::lemma_ "remark-6.36-matrix-exponent" (parent := "fabl-chapter-6") (lean := "FABL.PositiveMatrixExponent, FABL.matrixExponentJuntaBalancedExponent, FABL.matrixExponentJuntaCutoff, FABL.matrixExponentJuntaSolverExponent, FABL.matrixExponentJuntaRuntimeExponentLedger, FABL.F₂LinearSolverBackend, FABL.solveLowDegreeF₂SamplesWithBackend, FABL.solveLowDegreeF₂SamplesWithBackend_evaluate_eq, FABL.lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend_evaluate_eq, FABL.lowDegreeF₂PolynomialLearnerWorkWithBackend, FABL.F₂LinearSolverExponentCertificate, FABL.scheduledLowDegreeF₂PolynomialLearnerWorkWithBackend_le_exponentEnvelope, FABL.matrixExponentJuntaCeilSolverExponent_le_cutoff, FABL.matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff, FABL.matrixExponentBackendRuntimeLedger, FABL.cubicF₂LinearSolverBackend, FABL.cubicF₂LinearSolverExponentCertificate, FABL.cubicLowDegreeF₂PolynomialLearnerWork_le_balancedCutoff") (uses := "theorem-6.36, support-exercise-6.30") (tags := "section-6-4, external-dependency, fidelity-explicit-linear-solver-certificate-boundary")
*Matrix-exponent refinement of Theorem 6.36.* If $`n\times n` matrices can
be multiplied in time $`O(n^\omega)`, then the exponent $`3/4` in
Theorem 6.36 can be replaced by
$$`
\frac{\omega}{\omega+1}.
`

The formal runtime boundary is the exact finite consequence needed by the
proof: an executable $`\mathbb F_2` linear solver whose charged work has
exponent $`\omega`.  Such a solver is supplied through
`F₂LinearSolverExponentCertificate`; the verified balance then gives the
displayed exponent, and the existing Gaussian solver supplies the
$`\omega=3` certificate internally.  The standard complexity-theoretic
reduction from matrix multiplication to linear-system solving is not an API
of the pinned Mathlib or CSLib releases, so it remains an explicit external
adapter rather than an implicit assumption.
:::

:::lemma_ "lemma-6.38" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_mul") (uses := "definition-6.5, proposition-6.13, plancherel, support-exercise-3.9") (tags := "section-6-4, fidelity-explicit-nonnegative-bias-parameter")
*Lemma 6.38.* If $`f:\{-1,1\}^n\to\mathbb R` and
$`\varphi:\{-1,1\}^n\to\mathbb R_{\ge0}` is an
$`\epsilon`-biased density, where $`\epsilon\ge0`, then
$$`
\left|
\mathbb E_{x\sim\varphi}[f(x)]-\mathbb E[f]
\right|
\le \lVert\widehat f\rVert_1\epsilon.
`
:::

:::lemma_ "support-fourier-one-norm-product" (parent := "fabl-chapter-6") (lean := "FABL.fourierOneNorm_pointwise_mul_le, FABL.fourierOneNorm_sq_le") (uses := "theorem-1.1, definition-3.8") (tags := "section-6-4, support, fidelity-exact")
*Fourier $`1`-norm under products.* For
$`f,g:\{-1,1\}^n\to\mathbb R`,
$$`
\lVert\widehat{fg}\rVert_1
\le\lVert\widehat f\rVert_1\lVert\widehat g\rVert_1.
`
In particular,
$`\lVert\widehat{f^2}\rVert_1\le\lVert\widehat f\rVert_1^2`.
:::

:::corollary "corollary-6.39" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le") (uses := "lemma-6.38, support-fourier-one-norm-product") (tags := "section-6-4, fidelity-explicit-nonnegative-bias-parameter")
*Corollary 6.39.* If $`f:\{-1,1\}^n\to\mathbb R` and
$`\varphi:\{-1,1\}^n\to\mathbb R_{\ge0}` is an
$`\epsilon`-biased density, where $`\epsilon\ge0`, then
$$`
\left|
\mathbb E_{x\sim\varphi}[f(x)^2]-\mathbb E[f^2]
\right|
\le \lVert\widehat f\rVert_1^2\epsilon.
`
:::

:::proposition "proposition-6.40" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.IsBiased.uniformPushforward_comp_equiv, FABL.SmallBiasFourierInput, FABL.SmallBiasFourierInput.epsilon, FABL.SmallBiasFourierInput.generatorInput, FABL.SmallBiasFourierInput.generatorInput_epsilon, FABL.SmallBiasFourierInput.sampleCount, FABL.SmallBiasFourierInput.sampleCount_pos, FABL.SmallBiasFourierInput.construction, FABL.SmallBiasFourierInput.sample, FABL.SmallBiasFourierInput.sampleDensity, FABL.SmallBiasFourierInput.sample_isBiased, FABL.deterministicSmallBiasFourierEstimatorCost, FABL.deterministicSmallBiasFourierEstimatorProgram, FABL.DeterministicQueryProgram.runWithCost_deterministicSmallBiasFourierEstimatorProgram, FABL.abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le, FABL.deterministicSmallBiasFourierEstimatorCost_queries, FABL.deterministicSmallBiasFourierEstimatorCost_randomExamples, FABL.SmallBiasFourierInput.polynomialBudget, FABL.SmallBiasFourierInput.sampleCount_le_four_mul_scale_sq, FABL.deterministicSmallBiasFourierEstimatorCost_work, FABL.deterministicSmallBiasFourierEstimatorCost_resource_bounds, FABL.SmallBiasFourierTask, FABL.smallBiasFourierTaskScale, FABL.deterministicSmallBiasFourierEstimator_queries_isBigO, FABL.deterministicSmallBiasFourierEstimator_work_isBigO") (uses := "theorem-6.30, lemma-6.38, proposition-1.8") (tags := "section-6-4, fidelity-explicit-finite-rational-and-natural-bound-input")
*Proposition 6.40.* There is a deterministic algorithm which, given query
access to $`f:\{-1,1\}^n\to\mathbb R`, a set $`U\subseteq[n]`,
$`0<\epsilon\le1/2`, and $`s\ge1`, outputs an estimate
$`\widetilde f(U)` such that
$$`
|\widetilde f(U)-\widehat f(U)|\le\epsilon,
`
provided $`\lVert\widehat f\rVert_1\le s`. Its running time is
$`\operatorname{poly}(n,s,1/\epsilon)`.

The algorithm constructs an $`(\epsilon/s)`-biased multiset, enumerates it,
and queries $`f(x)\chi_U(x)` at every multiset element.

The executable interface represents $`\epsilon` by a positive rational and
$`s` by a positive natural-number upper bound. Its complete charged cost is
$`O(\lceil ns/\epsilon\rceil^8)`, while the correctness theorem interprets
both encoded parameters in $`\mathbb R`.
:::

:::lemma_ "equation-6.6" (parent := "fabl-chapter-6") (lean := "FABL.restrictedFourierWeight_equation6_6") (uses := "definition-3.20, definition-3.39, equation-3.5") (tags := "section-6-4, support, fidelity-exact")
*Equation (6.6).* For $`S\subseteq J\subseteq[n]`,
$$`
\mathbf W^{S\mid\overline J}[f]
=\sum_{T\subseteq\overline J}\widehat f(S\cup T)^2
=\mathbb E_{z\sim\{-1,1\}^{\overline J}}
  \left[\widehat{f_{J\mid z}}(S)^2\right]
=\lVert F_{S\mid\overline J}f\rVert_2^2.
\tag{6.6}
`
:::

:::lemma_ "support-restriction-fourier-one-norm" (parent := "fabl-chapter-6") (lean := "FABL.sum_abs_indexedFourierCoeff_signRestriction_le_fourierOneNorm, FABL.sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm, FABL.fixedSignCubeEquiv, FABL.fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le") (uses := "definition-3.18, proposition-3.21, definition-3.8") (tags := "section-6-4, support, fidelity-exact")
*Exercise 3.7 (Fourier $`1`-norm under restriction).* For every restriction
$`f_{J\mid z}` of $`f:\{-1,1\}^n\to\mathbb R`,
$$`
\lVert\widehat{f_{J\mid z}}\rVert_1
\le\lVert\widehat f\rVert_1.
`
The associated function $`F_{S\mid\overline J}f` also satisfies
$`\lVert\widehat{F_{S\mid\overline J}f}\rVert_1
\le\lVert\widehat f\rVert_1`.
:::

:::lemma_ "equation-6.7" (parent := "fabl-chapter-6") (lean := "FABL.restrictionFourierWeight_equation6_7") (uses := "corollary-6.39, support-restriction-fourier-one-norm, proposition-3.21") (tags := "section-6-4, support, fidelity-exact")
*Equation (6.7).* Suppose $`\lVert\widehat f\rVert_1\le s`, put
$`F=F_{S\mid\overline J}f`, and let $`\varphi` be an
$`\epsilon/(4s^2)`-biased density on
$`\{-1,1\}^{\overline J}`. Then
$$`
\left|
\mathbb E_{z\sim\varphi}[F(z)^2]
-\mathbb E_{z\sim\{-1,1\}^{\overline J}}[F(z)^2]
\right|
\le
\lVert\widehat F\rVert_1^2\frac{\epsilon}{4s^2}
\le\frac{\epsilon}{4}.
\tag{6.7}
`
:::

:::proposition "proposition-6.41" (parent := "fabl-chapter-6") (lean := "FABL.RestrictedWeightInput, FABL.RestrictedWeightInput.quarterBias, FABL.RestrictedWeightInput.quarterBias_epsilon, FABL.RestrictedWeightInput.innerInput, FABL.RestrictedWeightInput.outerInput, FABL.RestrictedWeightInput.innerInput_biasParameter, FABL.RestrictedWeightInput.outerInput_biasParameter, FABL.RestrictedWeightInput.innerCount, FABL.RestrictedWeightInput.outerCount, FABL.RestrictedWeightInput.innerCount_pos, FABL.RestrictedWeightInput.outerCount_pos, FABL.restrictedWeightFreeSample_isBiased, FABL.restrictedWeightFixedSample_isBiased, FABL.abs_restrictedFourierCoefficientEstimate_sub_le, FABL.abs_restrictionFourierCoeff_toReal_le_one, FABL.abs_restrictedFourierWeightOuterMean_sub_le, FABL.abs_restrictedFourierWeightEstimate_sub_outerMean_le, FABL.abs_restrictedFourierWeightEstimate_sub_le, FABL.deterministicRestrictedWeightQueryCount, FABL.deterministicRestrictedWeightQueryPair, FABL.deterministicRestrictedWeightLocalWork, FABL.deterministicRestrictedWeightConstructionWork, FABL.deterministicRestrictedWeightCost, FABL.DeterministicQueryProgram.runWithCost_deterministicRestrictedWeightProgram, FABL.deterministicRestrictedWeightCost_queries, FABL.deterministicRestrictedWeightCost_randomExamples, FABL.deterministicRestrictedWeightCost_work, FABL.RestrictedWeightInput.algorithmScale, FABL.RestrictedWeightInput.polynomialBudget, FABL.deterministicRestrictedWeightCost_resource_bounds, FABL.RestrictedWeightTask, FABL.restrictedWeightTaskScale, FABL.deterministicRestrictedWeight_queries_isBigO, FABL.deterministicRestrictedWeight_work_isBigO") (uses := "proposition-6.40, equation-6.6, equation-6.7, corollary-6.39") (tags := "section-6-4, fidelity-exact-deterministic-query-runtime")
*Proposition 6.41.* There is a deterministic algorithm which, given query
access to $`f:\{-1,1\}^n\to\{-1,1\}`, sets
$`S\subseteq J\subseteq[n]`, $`0<\epsilon\le1/2`, and $`s\ge1`, outputs
$`\beta` satisfying
$$`
\left|\mathbf W^{S\mid\overline J}[f]-\beta\right|\le\epsilon,
`
provided $`\lVert\widehat f\rVert_1\le s`. Its running time is
$`\operatorname{poly}(n,s,1/\epsilon)`.
:::

:::theorem "theorem-6.42" (parent := "fabl-chapter-6") (lean := "FABL.DeterministicGoldreichLevinInput, FABL.DeterministicGoldreichLevinInput.learningParameter, FABL.DeterministicGoldreichLevinInput.learningParameter_cast, FABL.deterministicGoldreichLevinLearner, FABL.deterministicGoldreichLevinLearningProgram, FABL.deterministicGoldreichLevinLearner_relativeHammingDist_le, FABL.deterministicGoldreichLevinLearningProgram_spec, FABL.deterministicGoldreichLevinQueryBudget, FABL.deterministicGoldreichLevinWorkBudget, FABL.deterministicGoldreichLevinLearner_resource_bounds, FABL.deterministicGoldreichLevinLearningProgram_resource_bounds, FABL.DeterministicGoldreichLevinInput.runtimeScale, FABL.DeterministicGoldreichLevinInput.polynomialRuntimeBound, FABL.deterministicGoldreichLevinLearner_queries_polynomial_le, FABL.deterministicGoldreichLevinLearner_work_polynomial_le, FABL.DeterministicGoldreichLevinTask, FABL.deterministicGoldreichLevinTaskScale, FABL.deterministicGoldreichLevinLearner_queries_isBigO, FABL.deterministicGoldreichLevinLearner_work_isBigO") (uses := "definition-3.27, theorem-3.38, proposition-6.40, proposition-6.41, goldreich-levin-theorem") (tags := "section-6-4, fidelity-exact-deterministic-query-runtime")
*Theorem 6.42.* Let
$$`
\mathcal C
=\left\{
f:\{-1,1\}^n\to\{-1,1\}:
\lVert\widehat f\rVert_1\le s
\right\}.
`
The class $`\mathcal C` is deterministically learnable from queries with
error $`\epsilon` in time
$`\operatorname{poly}(n,s,1/\epsilon)`.
:::

:::theorem "theorem-6.43" (parent := "fabl-chapter-6") (lean := "FABL.exactSparseSpectrumConceptClass, FABL.exactSparseSpectrumLearningProgram, FABL.runWithCost_exactSparseSpectrumLearningProgram, FABL.exactSparseSpectrumLearningAlgorithm, FABL.exactSparseSpectrumLearningAlgorithm_successProbability_eq_one, FABL.exactSparseSpectrumLearningAlgorithm_learns, FABL.exactSparseSpectrumLearningProgram_zero_error, FABL.exactSparseSpectrumLearningProgram_spec") (uses := "theorem-6.42, support-exercise-3.37c") (tags := "section-6-4, fidelity-exact-deterministic-query-runtime")
*Theorem 6.43.* Let
$$`
\mathcal C
=\left\{
f:\{-1,1\}^n\to\{-1,1\}:
\operatorname{sparsity}(\widehat f)\le2^{O(k)}
\right\}.
`
The class $`\mathcal C` is deterministically learnable exactly, with error
$`0`, from queries in time $`\operatorname{poly}(n,2^k)`.
:::

:::definition "derandomized-blr-test" (parent := "fabl-chapter-6") (lean := "FABL.boolF₂Equiv, FABL.boolVectorF₂CubeEquiv, FABL.randomBitVectorProgram, FABL.runWithCost_randomBitVectorProgram, FABL.derandomizedBLRDecision, FABL.derandomizedBLRQueryProgram, FABL.runWithCost_derandomizedBLRQueryProgram, FABL.derandomizedBLRLocalWork, FABL.derandomizedBLRCost, FABL.derandomizedBLRRandomBits, FABL.derandomizedBLRAfterInputProgram, FABL.derandomizedBLRProgram, FABL.derandomizedBLRProgramResult, FABL.runWithCost_derandomizedBLRProgram, FABL.derandomizedBLRProgram_cost_eq_of_mem_support, FABL.derandomizedBLRProgram_resources_of_mem_support, FABL.runWithCost_derandomizedBLRProgram_eq_pure_of_isF₂Linear, FABL.derandomizedBLRProgramAcceptanceProbability, FABL.derandomizedBLRProgramAcceptanceProbability_eq") (uses := "blr-test, definition-6.5, theorem-6.30") (tags := "section-6-4, fidelity-exact-query-and-random-bit-model")
*Derandomized BLR Test.* Given query access to
$`f:\mathbb F_2^n\to\mathbb F_2` and an $`\epsilon`-biased density
$`\varphi`:

1. Choose independent $`x\sim\mathbb F_2^n` and $`y\sim\varphi`.
2. Query $`f` at $`x`, $`y`, and $`x+y`.
3. Accept if $`f(x)+f(y)=f(x+y)`.

The test makes exactly three membership queries. Using the density from
Theorem 6.30, it requires
$`n+O(\log(n/\epsilon))` independent random bits. Every
$`\mathbb F_2`-linear $`f` is accepted with probability $`1`.
:::

:::theorem "theorem-6.44" (parent := "fabl-chapter-6") (lean := "FABL.exists_affine_correlation_ge_sqrt_of_derandomizedBLRAcceptanceProbability_eq") (uses := "derandomized-blr-test, corollary-6.39, theorem-1.27, parseval, proposition-6.7, definition-1.29") (tags := "section-6-4, fidelity-exact-with-real-sqrt-truncation-explicit-nonnegative-bias-parameter")
*Theorem 6.44.* Let $`\epsilon\ge0`. Suppose the Derandomized BLR Test
with an $`\epsilon`-biased density accepts
$`f:\mathbb F_2^n\to\mathbb F_2` with probability
$$`
\frac12+\frac12\theta.
`
Then there is an affine $`g:\mathbb F_2^n\to\mathbb F_2` whose sign
encoding has correlation at least $`\sqrt{\theta^2-\epsilon}` with the sign
encoding of $`f`. Equivalently,
$$`
\operatorname{dist}(f,g)
\le\frac12-\frac12\sqrt{\theta^2-\epsilon}.
`
In the formal real-valued statement, the square root is `Real.sqrt`;
therefore it is $`0` when $`\theta^2<\epsilon`, making the bound vacuous
without adding a hypothesis absent from the book.
:::

:::lemma_ "remark-6.45" (parent := "fabl-chapter-6") (tags := "section-6-4, nondependency, statement-only, fidelity-exact")
*Remark 6.45.* Theorem 6.44 is useful both when $`\theta` is close to
$`0` and when it is close to $`1`. In particular, if
$`\theta=1-2\delta`, then acceptance probability $`1-\delta` implies that
$`f` is nearly $`\delta`-close to an affine function whenever
$`\epsilon\ll\delta`.
:::

:::lemma_ "support-exercise-6.30" (parent := "fabl-chapter-6") (lean := "FABL.F₂LinearEquation, FABL.F₂SatisfiesRows, FABL.F₂EliminationResult, FABL.eliminateF₂Rows, FABL.satisfiesRows_eliminateF₂Rows_iff, FABL.solveF₂Rows, FABL.solveF₂Rows_satisfies_of_exists, FABL.LowDegreeMonomial, FABL.LowDegreeF₂Coefficients, FABL.lowDegreeF₂MonomialCount, FABL.lowDegreeF₂MonomialCount_le, FABL.lowDegreeF₂Eval, FABL.lowDegreeF₂Eval_injective, FABL.functionAlgebraicDegree_lowDegreeF₂Eval_le, FABL.lowDegreeF₂CoefficientsOfFunction, FABL.lowDegreeF₂Eval_coefficientsOfFunction, FABL.SeparatesLowDegreeF₂Coefficients, FABL.lowDegreeF₂LearningSampleCount, FABL.measure_lowDegreeF₂SeparationFailureSet_scheduled_le, FABL.lowDegreeF₂LearningSampleCount_le, FABL.LowDegreeF₂Hypothesis, FABL.solveLowDegreeF₂Samples, FABL.solveLowDegreeF₂Samples_evaluate_eq, FABL.lowDegreeF₂PolynomialLearnerWork, FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_cubicScale, FABL.scheduledLowDegreeF₂PolynomialLearnerWork_le_fixedParameterEnvelope, FABL.lowDegreeF₂PolynomialLearnerProgram, FABL.scheduledLowDegreeF₂PolynomialLearnerProgram, FABL.scheduledLowDegreeF₂PolynomialLearnerProgram_failureProbability_le, FABL.scheduledLowDegreeF₂PolynomialLearnerProgram_sampleCount") (uses := "definition-6.20, definition-3.27, support-exercise-6.11") (tags := "section-6-4, support, external-dependency, fidelity-exact-random-example-runtime")
*Exercise 6.30 (exactly learning low-degree
$`\mathbb F_2`-polynomials).* Fix $`\ell\ge1`.

(a) Let $`p:\mathbb F_2^n\to\mathbb F_2` satisfy
$`\deg_{\mathbb F_2}(p)\le\ell`, and draw
$`x^{(1)},\ldots,x^{(m)}` independently and uniformly from
$`\mathbb F_2^n`. If
$$`
m\ge C\,2^\ell\bigl(n^\ell+\log(1/\delta)\bigr),
\qquad 0<\delta\le1/2,
`
for a sufficiently large universal constant $`C`, then, except with
probability at most $`\delta`, the only
$`q:\mathbb F_2^n\to\mathbb F_2` of degree at most $`\ell` satisfying
$`q(x^{(i)})=p(x^{(i)})` for every $`i\in[m]` is $`q=p`.

(b) The class of degree-at-most-$`\ell` polynomials
$`\mathbb F_2^n\to\mathbb F_2` can be learned exactly from random examples
in time $`O(n)^{3\ell}` by solving the resulting
$`\mathbb F_2`-linear system. If matrix multiplication takes
$`O(n^\omega)` time, the bound improves to $`O(n)^{\omega\ell}`.

(c) The learner can be amplified to success probability at least
$`1-\delta` in time $`O(n)^{3\ell}\log(1/\delta)`.

The cubic solver and the amplified random-example program are verified
internally. The $`\omega\ell` refinement is represented by the explicit
`F₂LinearSolverExponentCertificate` boundary used by the matrix-exponent
refinement below; the standard reduction from matrix multiplication to
linear-system solving is not available in the pinned Mathlib or CSLib APIs
and therefore remains an external adapter.
:::

:::lemma_ "support-exercise-6.31" (parent := "fabl-chapter-6") (lean := "FABL.JuntaConstantDecision, FABL.JuntaConstantDecision.IsCorrect, FABL.JuntaConstantDecision.constantValueF₂?, FABL.juntaConstantAccuracy, FABL.juntaConstantAccuracy_cast, FABL.juntaConstantThreshold, FABL.juntaConstantThreshold_cast, FABL.decideJuntaConstant, FABL.exists_eq_const_of_isKJunta_zero, FABL.abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant, FABL.inv_two_pow_eq_four_mul_juntaConstantAccuracy, FABL.decideJuntaConstant_isCorrect_of_close, FABL.juntaConstantTestProgram, FABL.juntaConstantTestProgram_cost_eq, FABL.juntaConstantTestProgram_failureProbability_le, FABL.juntaConstantTestSampleCount_cast_le, FABL.JuntaFreeIndex, FABL.JuntaFixedAssignment, FABL.JuntaFreeAssignment, FABL.combineJuntaAssignment, FABL.juntaAssignmentSplitEquiv, FABL.juntaAssignmentSplitEquiv_symm_apply, FABL.combineJuntaAssignment_apply_fixed, FABL.combineJuntaAssignment_apply_free, FABL.juntaRestriction, FABL.juntaFixedAssignmentSignOfF₂, FABL.juntaFreeAssignmentF₂OfSign, FABL.combineJuntaF₂Assignment, FABL.binaryCubeSignEquiv_combineJuntaF₂Assignment, FABL.MatchesJuntaAssignment, FABL.juntaFreePart, FABL.juntaFixedPart, FABL.juntaFixedPart_combineJuntaAssignment, FABL.juntaFreePart_combineJuntaAssignment, FABL.combineJuntaAssignment_freePart_of_matches, FABL.MatchedJuntaExample, FABL.matchedJuntaRestrictionExample, FABL.matchedJuntaRestrictionExample_label, FABL.fixedMatchingIndices, FABL.juntaMatchingIndices, FABL.juntaMatchCount, FABL.juntaMatchCount_eq_sum, FABL.juntaMatchObservation, FABL.juntaMatchObservation_mem_Icc, FABL.expect_juntaMatchObservation, FABL.finiteUniformEmpiricalMean_juntaMatchObservation, FABL.initialFinEmbedding, FABL.fixedMatchingIndexEmbedding, FABL.juntaMatchingIndexEmbedding, FABL.juntaMatchingIndexEmbedding_matches, FABL.takeMatchingJuntaExamples, FABL.takeMatchingJuntaExamples_eq_none_iff, FABL.juntaRestrictionMatchAccuracy, FABL.juntaRestrictionMatchAccuracy_cast, FABL.juntaRestrictionSampleCount, FABL.juntaRestrictionSampleWork, FABL.juntaRestrictionSampleProgram, FABL.runWithCost_juntaRestrictionSampleProgram, FABL.juntaRestrictionFailureSet, FABL.juntaRestrictionFailureSet_subset_empiricalBad, FABL.juntaRestrictionSampleProgram_failureProbability_le, FABL.juntaRestrictionSampleProgram_success_labels, FABL.juntaRestrictionSampleProgram_cost_eq, FABL.juntaRestrictionSampleCount_cast_le, FABL.injectionVectorSplitEquiv, FABL.injectionVectorSplitEquiv_fst, FABL.map_uniformPMF_fst, FABL.map_uniformPMF_injection_projection, FABL.selectedJuntaFreeBatch, FABL.juntaRestrictionLabeledBatch, FABL.juntaLabeledSamplesFromSplit, FABL.takeMatchingJuntaExamples_from_split, FABL.map_uniformPMF_selectedJuntaRestrictionBatch, FABL.projectJuntaRestrictionBatch, FABL.juntaInputBatchSplitEquiv, FABL.juntaInputBatchSplitEquiv_symm_apply, FABL.rawProjectedJuntaRestrictionBatch, FABL.map_uniformPMF_rawProjectedJuntaRestrictionBatch, FABL.pmfToOuterMeasure_ne_top, FABL.rawProjectedJuntaRestrictionBatch_successBadProbability_le, FABL.juntaRestrictionSampleProgram_badProbability_le, FABL.IsRelevantJuntaRestriction, FABL.mem_of_isRelevantJuntaRestriction_of_dependsOn, FABL.juntaRestriction_eq_const_of_dependsOn_of_subset, FABL.JuntaNodeDecision, FABL.JuntaNodeDecision.IsCorrect, FABL.JuntaNodeDecision.IsBad, FABL.JuntaNodeDecision.isCorrect_of_not_isBad, FABL.juntaTreeCallCount, FABL.juntaTreeCallCount_zero, FABL.juntaTreeCallCount_succ, FABL.juntaTreeCallCount_pos, FABL.juntaTreePerCallFailure, FABL.juntaTreePerCallFailure_value, FABL.juntaTreeCallCount_mul_perCallFailure, FABL.insertJuntaFixedAssignment, FABL.insertJuntaFixedAssignment_apply_new, FABL.insertJuntaFixedAssignment_apply_old, FABL.matches_insertJuntaFixedAssignment_iff, FABL.F₂DecisionTree.castAvailable, FABL.F₂DecisionTree.eval_castAvailable, FABL.F₂DecisionTree.depth_castAvailable, FABL.assembleJuntaQuery, FABL.juntaNodeLeafOutput, FABL.recursiveJuntaLearnerAux, FABL.emptyJuntaFixedAssignment, FABL.F₂DecisionTree.ComputesJuntaRestriction, FABL.F₂DecisionTree.computesJuntaRestriction_leaf, FABL.JuntaTreeOutputBad, FABL.computesJuntaRestriction_of_not_outputBad, FABL.not_outputBad_assembleJuntaQuery, FABL.subset_of_card_sdiff_le_zero, FABL.card_sdiff_insert_le_of_mem_of_notMem, FABL.exists_constant_of_correctNode_of_card_sdiff_le_zero, FABL.eventProbability_map_output_eq, FABL.eventProbability_map_output_le, FABL.eventProbability_pure_eq_zero_of_not, FABL.nodeLeafOutput_bad_implies_nodeBad, FABL.recursiveJuntaLearnerAux_failureProbability_le, FABL.recursiveJuntaLearnerAux_depth_le, FABL.recursiveJuntaLearnerAux_costProjection_le, FABL.recursiveJuntaLearnerAux_randomExamples_le, FABL.recursiveJuntaLearnerAux_queries_eq_zero, FABL.recursiveJuntaLearnerAux_work_le, FABL.rootOutput_bad_implies_auxBad") (uses := "definition-2.4, definition-2.18, definition-3.27") (tags := "section-6-4, support, fidelity-exact-random-example-reduction")
*Exercise 6.31 (reduction to finding one relevant coordinate).*

(a) Give a $`\operatorname{poly}(n,2^k)\log(1/\delta)`-time algorithm
which, from random examples of a $`k`-junta
$`f:\mathbb F_2^n\to\mathbb F_2`, determines with failure probability at
most $`\delta` whether $`f` is constant and, if so, which constant it is.

(b) Let $`P\subseteq[n]` be a set of relevant coordinates of $`f` and let
$`z\in\mathbb F_2^P`. Obtain $`M` independent random examples from the
$`(k-|P|)`-junta $`f_{P\mid z}` in time
$$`
\operatorname{poly}(n,2^k)\,M\log(1/\delta),
`
except with probability at most $`\delta`.

(c) Using a relevant-coordinate finder as in Lemma 6.37, recursively build
a depth-$`k` decision tree for $`f` and thereby prove Lemma 6.37.
:::
