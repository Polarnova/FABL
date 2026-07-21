/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter03.KushilevitzMansour
import FABL.Chapter03.LearningTheory.SparseSpectrum
import FABL.Chapter06.LearningAndTesting.ExactSparseSpectrumLearning

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: the Goldreich–Levin Algorithm" =>

:::theorem "goldreich-levin-theorem" (parent := "fabl-chapter-3") (lean := "FABL.GoldreichLevinQueryState.IsCorrectOutput, FABL.goldreichLevinControllerStepWork, FABL.goldreichLevinStageStepProgram, FABL.goldreichLevinQueryBudget, FABL.goldreichLevinWorkBudget, FABL.goldreichLevinQueryProgram, FABL.goldreichLevinQueryProgram_queries_le, FABL.goldreichLevinQueryProgram_work_le, FABL.goldreichLevinQueryBudget_cast_le, FABL.goldreichLevinWorkBudget_cast_le, FABL.goldreichLevinQueryProgram_correct_of_mem_support_of_not_hasFailure, FABL.goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth, FABL.goldreichLevinQueryProgram_incorrectProbability_le_one_tenth") (uses := "definition-3.39, parseval, proposition-3.40") (tags := "section-3-5, fidelity-exact-with-explicit-rational-scheduler")
*Goldreich–Levin Theorem.* Given query access to a target
$`f:\{-1,1\}^n\to\{-1,1\}` and an input $`0<\tau\le1`, there is a
randomized algorithm running in time $`\operatorname{poly}(n,1/\tau)` which,
with probability at least $`9/10`, outputs a duplicate-free finite list
$`L=\{U_1,\ldots,U_\ell\}` of subsets of $`[n]` such that
$`|\widehat f(U)|\ge\tau` implies $`U\in L`, while $`U\in L` implies
$`|\widehat f(U)|\ge\tau/2`. Consequently, Parseval's Theorem gives
$`|L|\le\frac4{\tau^2}`. One may take
$`K=\left\lceil\frac4{\tau^2}\right\rceil` and
$`\delta_{\mathrm{call}}=\frac1{40(n+1)(K+1)}`.
The algorithm aborts before expanding an active family larger than $`K`;
the invariant shows that this branch is unreachable whenever all
queried estimates are accurate. If Proposition 3.40 schedules $`m` samples
per bucket, every execution uses at most $`n(2K)(2m)` membership queries and
at most
$`n\left(16(n+1)^2(K+1)^2+(2K)\,8(m+1)(n+1)\right)` charged local work. In
this explicit oracle/charged-work cost model these are bounded respectively
by $`\frac{2^{21}n(n+1)}{\tau^8}` and
$`\frac{2^{25}n(n+1)^2}{\tau^8}`,
which gives the asserted polynomial bound. The adaptive union bound is at most $`1/20`,
which is stronger than the theorem's required failure probability $`1/10`.
The soundness conclusion may be strengthened to the strict inequality
$`|\widehat f(U)|>\tau/2`.
:::

:::theorem "theorem-3.37" (parent := "fabl-chapter-3") (lean := "FABL.kushilevitzMansourProgramForBound, FABL.kushilevitzMansourProgramForBound_failureProbability_le_one_tenth, FABL.kushilevitzMansourProgramForBound_queries_polynomial_cast_le, FABL.kushilevitzMansourProgramForBound_work_polynomial_cast_le") (uses := "support-exercise-3.39") (tags := "section-3-5, fidelity-exact-with-rational-threshold-refinement")
*Theorem 3.37.* Let $`\mathcal C` be a concept class such that every
$`f:\{-1,1\}^n\to\{-1,1\}` in $`\mathcal C` has its Fourier spectrum
$`\epsilon/4`-concentrated on a collection of at most $`M` subsets of
$`[n]`. Then $`\mathcal C` can be learned using queries with error
$`\epsilon`, success probability at least $`9/10`, and running time
$`\operatorname{poly}(M,n,1/\epsilon)`.
The output is a finite sparse Fourier circuit representing the hypothesis.
This learning procedure is called the Kushilevitz–Mansour Algorithm.
:::

:::theorem "theorem-3.38" (parent := "fabl-chapter-3") (lean := "FABL.fourierOneNormClass_queryLearnable, FABL.fourierOneNormFamilySizeBound_add_one_cast_le, FABL.fourierOneNormClass_queries_polynomial_le, FABL.fourierOneNormClass_work_polynomial_le, FABL.fourierOneNorm_le_leafCount_of_decisionTree, FABL.decisionTreeSizeClass_queryLearnable, FABL.decisionTreeSizeClass_queries_polynomial_le, FABL.decisionTreeSizeClass_work_polynomial_le") (uses := "proposition-3.16, support-exercise-3.38") (tags := "section-3-5, fidelity-exact")
*Theorem 3.38.* Let
$$`
\mathcal C=
\left\{f:\{-1,1\}^n\to\{-1,1\}:
  \|\widehat f\|_1\le s\right\}.
`
Then $`\mathcal C` is learnable using queries with error $`\epsilon`, success
probability at least $`9/10`, and running time
$`\operatorname{poly}(n,s,1/\epsilon)`.
In particular, Proposition 3.16 implies that this concept class contains every
Boolean function computable by a decision tree of size at most $`s`.
:::

:::lemma_ "support-exercise-3.32" (parent := "fabl-chapter-3") (lean := "FABL.vectorDualEquiv, FABL.exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq, FABL.exists_nonzero_vectorFourierCoeff_hyperplaneRestriction_eq, FABL.spectralSparsityGranularity, FABL.spectralSparsityGranularity_cast, FABL.isVectorFourierGranular_signValue_spectralSparsity, FABL.spectralSparsity_not_mem_exceptional") (uses := "definition-3.9, definition-3.10, definition-3.20, parseval") (tags := "section-3-5, support, fidelity-explicit-dual-hyperplane-bridge")
*Exercise 3.32.*

1. Suppose $`f:\mathbb F_2^n\to\mathbb R` has
   $`\operatorname{sparsity}(\widehat f)<2^n`. For every
   $`\gamma\in\operatorname{supp}(\widehat f)`, there is a nonzero
   $`\beta\in\mathbb F_2^n` such that the restriction
   $`f_{\beta^\perp}` has $`\widehat f(\gamma)` as one of its Fourier
   coefficients.
2. If $`f:\mathbb F_2^n\to\{-1,1\}` has
   $`\operatorname{sparsity}(\widehat f)=s>1`, then $`\widehat f` is
   $`2^{1-\lfloor\log_2 s\rfloor}`-granular.
3. There is no Boolean function whose Fourier sparsity belongs to
   $`\{2,3,5,6,7,9\}`.

Lean identifies the book's vector $`\beta` with its dot-product functional
through `vectorDualEquiv`; hence
`ker (vectorDualEquiv n beta)` is exactly $`\beta^\perp`.  The public
hyperplane theorem returns this vector $`\beta` directly.
:::

:::lemma_ "support-exercise-3.37c" (parent := "fabl-chapter-3") (lean := "FABL.exactSparseSpectrumSparsityBound, FABL.roundSparseSpectrumHypothesis, FABL.exactSparseSpectrumLearner, FABL.exactSparseSpectrumLearner_evaluate_eq, FABL.exactSparseSpectrumQueryBudget, FABL.exactSparseSpectrumWorkBudget, FABL.exactSparseSpectrumLearner_resource_bounds, FABL.exactSparseSpectrumRuntimeScale, FABL.exactSparseSpectrumPolynomialRuntimeBound, FABL.exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound, FABL.exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound, FABL.exactSparseSpectrumLearner_queries_polynomial_le, FABL.exactSparseSpectrumLearner_work_polynomial_le") (uses := "definition-3.9, definition-3.27, theorem-3.37, support-exercise-3.32") (tags := "section-3-5, support, fidelity-exact-query-model")
*Exercise 3.37(c) (exact sparse-spectrum learning).* The class
$$`
\mathcal C
=\left\{
f:\{-1,1\}^n\to\{-1,1\}:
\operatorname{sparsity}(\widehat f)\le2^{O(k)}
\right\}
`
can be learned exactly from membership queries in
$`\operatorname{poly}(n,2^k)` time.
:::

:::definition "definition-3.39" (parent := "fabl-chapter-3") (lean := "FABL.restrictedFourierWeight") (uses := "definition-1.17, proposition-1.8") (tags := "section-3-5, fidelity-exact")
*Definition 3.39.* Let $`f:\{-1,1\}^n\to\mathbb R` and
$`S\subseteq J\subseteq[n]`. Write
$$`
\mathbf W^{S\mid\overline J}[f]
=\sum_{T\subseteq\overline J}\widehat f(S\cup T)^2
`
for the Fourier weight of $`f` on sets whose restriction to $`J` is $`S`.
Here $`\overline J=[n]\setminus J`.
:::

:::lemma_ "equation-3.5" (parent := "fabl-chapter-3") (lean := "FABL.restrictedFourierWeight_eq_expect_sq_restrictionFourierCoeff") (uses := "corollary-3.22, definition-3.20, definition-3.39") (tags := "section-3-5, support, fidelity-exact")
*Equation (3.5).* For
$`f:\{-1,1\}^n\to\mathbb R` and $`S\subseteq J\subseteq[n]`, restriction
to $`J` gives
$$`
\mathbf W^{S\mid\overline J}[f]
=\mathbb E_{z\sim\{-1,1\}^{\overline J}}
  \left[\widehat{f_{J\mid z}}(S)^2\right].
`
This is the specialization of Corollary 3.22 used by the
Goldreich–Levin Algorithm.
:::

:::proposition "proposition-3.40" (parent := "fabl-chapter-3") (lean := "FABL.restrictionCoefficientObservation, FABL.restrictedFourierWeightObservation, FABL.expect_restrictedFourierWeightObservation_eq_restrictedFourierWeight, FABL.restrictedFourierWeightObservation_mem_Icc, FABL.rationalRestrictedFourierWeightObservation, FABL.restrictedFourierWeightObservationFromInputs, FABL.expect_restrictedFourierWeightObservationFromInputs_eq_restrictedFourierWeight, FABL.restrictedFourierWeightObservationFromInputs_mem_Icc, FABL.restrictedFourierWeightObservationProgram, FABL.restrictedFourierWeightEstimatorProgram, FABL.scheduledRestrictedFourierWeightEstimatorProgram, FABL.restrictedFourierWeightEstimatorOutput, FABL.restrictedFourierWeightEstimatorOutput_cast, FABL.measure_restrictedFourierWeightTripleEmpiricalMean_failure_le, FABL.measure_restrictedFourierWeightEstimatorOutput_failure_le, FABL.runWithCost_restrictedFourierWeightEstimatorProgram, FABL.runWithCost_restrictedFourierWeightEstimatorProgram_uniformProduct, FABL.restrictedFourierWeightEstimatorProgram_cost_eq, FABL.scheduledRestrictedFourierWeightEstimatorProgram_queries_eq, FABL.restrictedFourierWeightEstimatorCost_work_le, FABL.scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le, FABL.realRestrictedFourierWeightFailureBits, FABL.fourierEstimatorFailureBits_le_realRestrictedFourierWeightFailureBits, FABL.exists_scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le, FABL.exists_scheduledRestrictedFourierWeightEstimatorProgram_with_resource_bounds") (uses := "equation-3.5, proposition-3.30") (tags := "section-3-5, fidelity-exact-with-controlled-rational-scheduler")
*Proposition 3.40.* Let $`S\subseteq J\subseteq[n]`, and let
$`\epsilon>0` and $`0<\delta\le1`. An algorithm with query access to
$`f:\{-1,1\}^n\to\{-1,1\}` can output an estimate
$`\widetilde{\mathbf W}^{S\mid\overline J}[f]` satisfying
$$`
\Pr\!\left[
 \left|\widetilde{\mathbf W}^{S\mid\overline J}[f]
       -\mathbf W^{S\mid\overline J}[f]\right|>\epsilon
\right]\le\delta.
`
Its running time is $`\operatorname{poly}(n,1/\epsilon)\log(1/\delta)`.

Concretely, one sample draws independently
$`z\sim\{-1,1\}^{\overline J}` and $`y,y'\sim\{-1,1\}^{J}`, and evaluates the
$`\{-1,1\}`-valued random variable
$`f(y,z)\chi_S(y)\,f(y',z)\chi_S(y')`. The empirical estimator uses
$`m=O\!\left(\frac{\log(1/\delta)}{\epsilon^2}\right)` independent samples,
makes exactly $`2m` membership queries, and estimates
the expectation in Equation (3.5) to the claimed accuracy and confidence.
For arbitrary positive real $`\epsilon,\delta`, choose positive rational
parameters $`\epsilon',\delta'` satisfying
$$`
\frac{\min(\epsilon,1/2)}2<\epsilon'<\min(\epsilon,1/2),
\qquad
\frac{\min(\delta,1/2)}2<\delta'<\min(\delta,1/2).
`
Event monotonicity transfers the rational concentration theorem to the
book's full positive-real parameter range. More explicitly, put
$$`
E=\min(\epsilon,1/2),
\qquad
B=\left\lceil\log_2\left\lceil\frac{4}{\min(\delta,1/2)}\right\rceil\right\rceil.
`
A scheduler using these parameters needs at most $`16B/E^2` samples. Every
execution path
makes at most $`32B/E^2` membership queries and incurs at most
$`256B(n+1)/E^2` charged local work, which proves the stated polynomial and
logarithmic resource dependence.
:::

:::lemma_ "support-exercise-3.16" (parent := "fabl-chapter-3") (lean := "FABL.fourierOneNorm, FABL.fourierOneNorm_nonneg, FABL.fourierOneNorm_eq_spectralPNorm_one, FABL.l1ConcentratingFourierFamily, FABL.mem_l1ConcentratingFourierFamily, FABL.card_l1ConcentratingFourierFamily_le, FABL.isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily") (uses := "definition-3.8, definition-3.28") (tags := "section-3-5, support, fidelity-exact-with-cube-bridge-explicit")
*Exercise 3.16.* Let $`f:\{-1,1\}^n\to\mathbb R` and let
$`\eta>0`. Prove that the Fourier spectrum of $`f` is
$`\eta`-concentrated on a collection
$`\mathcal F\subseteq2^{[n]}` satisfying
$`|\mathcal F|\le\frac{\|\widehat f\|_1^2}{\eta}`.
:::

:::lemma_ "support-exercise-3.38" (parent := "fabl-chapter-3") (lean := "FABL.fourierOneNormFamilySizeBound, FABL.fourierOneNormFamilySizeBound_pos, FABL.card_l1ConcentratingFourierFamily_le_familySizeBound") (uses := "definition-3.28, support-exercise-3.16, theorem-3.37") (tags := "section-3-5, support, fidelity-exact")
*Exercise 3.38.* Prove Theorem 3.38 in full: if every Boolean target in
$`\mathcal C` satisfies $`\|\widehat f\|_1\le s`, then $`\mathcal C` is
learnable using queries with error $`\epsilon`, success probability at least
$`9/10`, and running time $`\operatorname{poly}(n,s,1/\epsilon)`.
(Hint: use Exercise 3.16.)
:::

:::lemma_ "support-exercise-3.39" (parent := "fabl-chapter-3") (lean := "FABL.queryInputBatchProgram, FABL.runWithCost_queryInputBatchProgram, FABL.runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples_uniformMatrix, FABL.finiteFamilyCoefficientConfidenceForTotal, FABL.queriedFiniteFamilySamplesPerCoefficient, FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence, FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_failureProbability_le, FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_cast_le, FABL.queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_cast_le, FABL.oneTwentiethLearningParameter, FABL.kushilevitzMansourThreshold, FABL.isFourierSpectrumConcentratedOn_of_goldreichLevin_complete, FABL.kushilevitzMansourSecondStage, FABL.kushilevitzMansourProgram, FABL.kushilevitzMansourProgram_failureProbability_le_one_tenth, FABL.positive_familyBound_of_spectrum_concentrated, FABL.kushilevitzMansourSecondStage_cost_cases, FABL.kushilevitzMansourProgram_cost_decomposition, FABL.fourierEstimatorFailureBits_oneTwentieth_per_family_le, FABL.kushilevitzMansourSecondStage_queries_cast_le, FABL.kushilevitzMansourSecondStage_work_cast_le, FABL.kushilevitzMansourProgram_queries_cast_le, FABL.kushilevitzMansourProgram_work_cast_le, FABL.kushilevitzMansourProgram_queries_polynomial_cast_le, FABL.kushilevitzMansourProgram_work_polynomial_cast_le") (uses := "definition-3.28, goldreich-levin-theorem, parseval, theorem-3.29") (tags := "section-3-5, support, fidelity-exact-with-rational-threshold-refinement")
*Exercise 3.39.* Deduce Theorem 3.37 from the Goldreich–Levin Algorithm.
Precisely, suppose the Fourier spectrum of each Boolean target $`f` is
$`\epsilon/4`-concentrated on some collection $`\mathcal F_0` with
$`|\mathcal F_0|\le M`. For $`M\ge1`, run Goldreich–Levin with
$`\tau=\sqrt{\frac{\epsilon}{4M}}`.
Prove that the resulting list $`L` carries all but at most $`\epsilon/2`
Fourier weight, and then implement Theorem 3.29 using only membership
queries to produce a finite sparse Fourier circuit $`h` satisfying
$`\operatorname{dist}(f,h)\le\epsilon`. The complete construction must run
in $`\operatorname{poly}(M,n,1/\epsilon)` time and succeed with probability
at least $`9/10`. It is enough to use the smaller rational threshold
$`\tau=\epsilon/(4M)`; this preserves the conclusion and the polynomial
resource bound. Give each randomized stage failure budget $`1/20`. In the
nontrivial accuracy range, the concentration premise itself rules out
$`M=0`.
:::
