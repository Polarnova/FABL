/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.AC0ThresholdParitySeparation
import FABL.Chapter05.BiasedMajorityGaussianLimit
import FABL.Chapter05.CorrelationDistillation
import FABL.Chapter05.DNFSparsePolynomialThreshold
import FABL.Chapter05.FKNOptimality
import FABL.Chapter05.GaussianIsoperimetricConcavity
import FABL.Chapter05.GaussianSharpLevelOne
import FABL.Chapter05.GaussianSharpLevelOneCounterexample
import FABL.Chapter05.GotsmanLinialExtremizer
import FABL.Chapter05.KrawtchoukPolynomials
import FABL.Chapter05.LinearThresholdBias
import FABL.Chapter05.LinearThresholdInfluence
import FABL.Chapter05.LTFNoiseSensitivityDerivative
import FABL.Chapter05.MajorityFourierWeightRecovery
import FABL.Chapter05.MajorityFourierOneNorm
import FABL.Chapter05.MajorityLargestFourierCoefficient
import FABL.Chapter05.ParityThresholdDegree
import FABL.Chapter05.PolynomialThresholdInfluence
import FABL.Chapter05.PolynomialThresholdUniformStability
import FABL.Chapter05.PrescribedFourierSupport
import FABL.Chapter05.RandomBooleanFourierMaximum
import FABL.Chapter05.RobustEdgeIsoperimetry
import FABL.Chapter05.SmallLowDegreeWeightPTF
import FABL.Chapter05.SmallSetCenterOfMass
import FABL.Chapter05.ThresholdCircuits
import FABL.Chapter05.ThresholdFunctionCounting
import FABL.Chapter05.UniformNoiseStability

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Exercises and notes" =>

The exercises used in Sections 5.1--5.5 appear alongside the results they
establish. The remaining exercises are collected here.

:::lemma_ "support-exercise-5.2" (parent := "fabl-chapter-5") (lean := "FABL.homogeneousLinearThreshold_isOdd_and_isBalanced, FABL.zero_homogeneousLinearThreshold_counterexample, FABL.mean_nonneg_of_nonnegative_linearThresholdBias, FABL.nonnegative_mean_negative_bias_counterexample, FABL.exists_homogeneousLinearThresholdRepresentation_of_isBalanced") (uses := "definition-1.3, definition-2.5") (tags := "section-5-6, support, fidelity-corrected-zero-margin")
*Exercise 5.2 (bias and homogeneous representations of LTFs).* Let
$$`
f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)
`
be a linear threshold function.

(a) If $`a_0=0`, prove that $`f` is odd and hence
$`\mathbb E[f]=0`.

(b) If $`a_0\ge0`, prove that $`\mathbb E[f]\ge0`. Show by example that the
converse implication need not hold.

(c) If $`g:\{-1,1\}^n\to\{-1,1\}` is a linear threshold function satisfying
$`\mathbb E[g]=0`, prove that there are $`c_1,\ldots,c_n\in\mathbb R` such
that
$$`
g(x)=\operatorname{sgn}(c_1x_1+\cdots+c_nx_n)
`
for every $`x`.

With the book's convention $`\operatorname{sgn}(0)=1`, part (a) is false
without excluding cube points on the zero set: the all-zero homogeneous form
represents the constant $`+1` function, which is neither odd nor unbiased.
Under the necessary hypothesis that every cube-point margin is nonzero,
part (a) holds. In part (c), unbiasedness itself yields a homogeneous
representation with no ties.
:::

:::lemma_ "support-exercise-5.3" (parent := "fabl-chapter-5") (lean := "FABL.influence_le_of_abs_linearThresholdWeight_le") (uses := "definition-2.5, definition-2.13") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.3 (ordering the influences of an LTF).* Suppose
$$`
f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)
`
is a linear threshold function whose coefficients satisfy
$$`
|a_1|\ge|a_2|\ge\cdots\ge|a_n|.
`
Then
$$`
\operatorname{Inf}_1[f]\ge
\operatorname{Inf}_2[f]\ge\cdots\ge
\operatorname{Inf}_n[f].
`
It suffices to establish the comparison for two coordinates at a time.
:::

:::lemma_ "support-exercise-5.4" (parent := "fabl-chapter-5") (lean := "FABL.PolynomialThresholdFunction, FABL.LinearThresholdFunction, FABL.natCard_polynomialThresholdFunction_le_profileCount, FABL.natCard_linearThresholdFunction_le_profileCount, FABL.natCard_linearThresholdFunction_le_two_pow_sq, FABL.card_lowDegreeFourierFamily_le_leadingTerm, FABL.natCard_polynomialThresholdFunction_le_two_pow_bookBound") (uses := "theorem-1.1, theorem-5.1, theorem-5.8") (tags := "section-5-6, support, fidelity-exact-explicit-constants")
*Exercise 5.4 (counting threshold functions).*

(a) Prove that the number of linear threshold functions
$`f:\{-1,1\}^n\to\{-1,1\}` is at most
$$`
2^{\,n^2+O(n)}.
`

(b) More generally, for each fixed $`k`, prove that the number of
degree-at-most-$`k` polynomial threshold functions
$`f:\{-1,1\}^n\to\{-1,1\}` is at most
$$`
2^{\,n^{k+1}+O(n^k)}.
`
The implied constants may depend on $`k`.
:::

:::lemma_ "support-exercise-5.6" (parent := "fabl-chapter-5") (lean := "FABL.exists_one_div_sqrt_two_mul_dimension_le_influence_of_balanced_linearThreshold") (uses := "parseval, theorem-5.2, support-exercise-2.5-unate, support-exercise-2.6-ltf-unate") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.6 (a KKL improvement for LTFs).* Let $`n\ge1` and let
$`f:\{-1,1\}^n\to\{-1,1\}` be an unbiased linear threshold function. Prove
that there is an $`i\in[n]` such that
$$`
\operatorname{Inf}_i[f]\ge\frac1{\sqrt{2n}}.
`
:::

:::lemma_ "support-exercise-5.7" (parent := "fabl-chapter-5") (lean := "FABL.signPairFamilyLeft, FABL.signPairFamilyRight, FABL.pmfExpectation_apply_left_mul_right_eq_fourierCoeff_mul_correlation, FABL.hasEqualSingletonFourierCoefficients_majority, FABL.fourierCoeff_singleton_le_majority_of_equal") (uses := "definition-2.41, theorem-2.33") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.7 (correlation distillation).* Let $`n\ge1`. For each
$`i\in[n]`, let
$`\rho_i\in[-1,1]`. Let $`(a_i,b_i)` be a pair of unbiased
$`\{-1,1\}`-valued bits with
$`\mathbb E[a_ib_i]=\rho_i`, independently across coordinates, and write
$`a=(a_1,\ldots,a_n)` and $`b=(b_1,\ldots,b_n)`. For a Boolean function
$`f:\{-1,1\}^n\to\{-1,1\}`:

(a) Prove that for every $`i\in[n]`,
$$`
\mathbb E[f(a)b_i]=\widehat f(\{i\})\rho_i.
`

(b) Suppose the singleton Fourier coefficients
$`\widehat f(\{1\}),\ldots,\widehat f(\{n\})` are all equal. Prove that a
majority function maximizes their common value among all Boolean functions
with this equality constraint.
:::

:::lemma_ "support-exercise-5.8" (parent := "fabl-chapter-5") (lean := "FABL.fourierInfinityNorm, FABL.randomBooleanFourierThreshold, FABL.measure_randomBooleanFunction_fourierInfinityNorm_gt_le") (uses := "theorem-1.1") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.8 (the largest Fourier coefficient of a random function).* Let
$`n\ge2`, and choose
$`f:\{-1,1\}^n\to\{-1,1\}` uniformly at random, equivalently by choosing
the values $`f(x)` as independent uniform signs. Prove that
$$`
\lVert\widehat f\rVert_\infty
\le 2\sqrt n\,2^{-n/2}
`
except with probability at most $`2^{-n}`.
:::

:::lemma_ "support-exercise-5.10" (parent := "fabl-chapter-5") (lean := "FABL.not_isPolynomialThreshold_parityFunction_univ_pred, FABL.isPolynomialThreshold_pred_of_ne_parityFunction_univ") (uses := "theorem-1.1, definition-5.4, theorem-5.10") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.10 (parity and threshold degree).* Let $`n\ge1`.

(a) Prove that the parity function
$`\chi_{[n]}:\{-1,1\}^n\to\{-1,1\}` is not a polynomial threshold function
of degree at most $`n-1`.

(b) Conversely, if
$`f:\{-1,1\}^n\to\{-1,1\}` is neither $`\chi_{[n]}` nor
$`-\chi_{[n]}`, prove that $`f` is a polynomial threshold function of
degree at most $`n-1`. One may use the low-degree truncation
$`f^{\le n-1}` as the representing polynomial.
:::

:::lemma_ "support-exercise-5.11" (parent := "fabl-chapter-5") (lean := "FABL.allOneSignCube, FABL.onePointFlippedParity, FABL.onePointFlippedParity_isPolynomialThreshold, FABL.fourierCoeff_onePointFlippedParity, FABL.fourierWeightAtMost_onePointFlippedParity, FABL.exists_polynomialThreshold_fourierWeightAtMost_lt_two_mul_invPow") (uses := "definition-1.19, definition-5.4, support-exercise-5.10") (tags := "section-5-6, support, fidelity-exact-equivalent-power-normal-form")
*Exercise 5.11 (small low-degree weight of a PTF).* For every
$`k\in\mathbb N^+`, construct a degree-$`k` polynomial threshold function
$`f` satisfying
$$`
\mathbf W^{\le k}[f]<2^{1-k}.
`
:::

:::lemma_ "support-exercise-5.12" (parent := "fabl-chapter-5") (lean := "FABL.IsRealSumOfLinearThresholds, FABL.HasRealSumOfLinearThresholdsSizeAtMost, FABL.IsThresholdOfThresholds, FABL.HasThresholdOfThresholdsSizeAtMost, FABL.IsThresholdOfParities, FABL.symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul, FABL.parityFunction_isRealSumOfLinearThresholds, FABL.polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost, FABL.thresholdOfParities_hasThresholdOfThresholdsSizeAtMost, FABL.completeQuadraticBit, FABL.completeQuadratic, FABL.completeQuadraticBoolean, FABL.completeQuadratic_apply, FABL.completeQuadraticBoolean_binaryCubeSignEquiv, FABL.completeQuadraticBoolean_isSymmetric, FABL.completeQuadraticBoolean_hasThresholdOfThresholdsSizeAtMost_two_mul, FABL.abs_vectorFourierCoeff_completeQuadratic, FABL.completeQuadraticBoolean_toReal, FABL.abs_fourierCoeff_completeQuadraticBoolean, FABL.pow_two_half_le_polynomialSparsity_completeQuadraticBoolean_of_pos, FABL.pow_two_half_le_thresholdOfParitiesSize_completeQuadraticBoolean") (uses := "fact-1.7, theorem-1.27, equation-3.1, definition-2.5, definition-2.8, definition-5.7, theorem-5.10") (tags := "section-5-6, support, fidelity-corrected-degenerate-dimension")
*Exercise 5.12 (threshold-of-parities and threshold-of-thresholds).* A
threshold-of-parities circuit is an outer linear threshold gate applied to
parities or negated parities; a threshold-of-thresholds circuit is an outer
linear threshold gate applied to linear threshold functions. The size is
the number of gates entering the outer threshold gate.

(a) Let $`f:\{-1,1\}^n\to\{-1,1\}` be symmetric. Prove that, as a
real-valued function, $`f` is a sum of at most $`2n` linear threshold
functions and a constant.

(b) Deduce that every function computed by a size-$`s`
threshold-of-parities circuit is computed by a size-$`2ns`
threshold-of-thresholds circuit.

(c) Define the complete quadratic function by
$$`
\operatorname{CQ}_n(x)
=(-1)^{\sum_{1\le i<j\le n}x_ix_j},
\qquad x\in\mathbb F_2^n,
`
where the exponent is evaluated in $`\mathbb F_2`. Prove that
$`\operatorname{CQ}_n` is computed by a size-$`2n`
threshold-of-thresholds circuit.

(d) If $`n` is positive and even, prove that every threshold-of-parities
circuit computing $`\operatorname{CQ}_n` has size at least $`2^{n/2}`.

The condition $`n>0` in part (d) is necessary. At $`n=0`,
$`\operatorname{CQ}_0` is the constant $`+1`
function and has the zero polynomial as a threshold representation, so the
lower bound $`1\le0` would be false. The same inequality holds in arbitrary
dimension whenever the representing polynomial is nonzero.
:::

:::lemma_ "support-exercise-5.13" (parent := "fabl-chapter-5") (lean := "FABL.DNFTerm.trueIndicator, FABL.DNFTerm.trueIndicator_eq_one_iff, FABL.DNFTerm.trueIndicator_nonneg, FABL.DNFTerm.binaryBasePoint, FABL.DNFTerm.fourierOneNorm_trueIndicator, FABL.DNFFormula.satisfiedTermCount, FABL.DNFFormula.satisfiedTermCount_eq_zero_of_no_satisfied_term, FABL.DNFFormula.one_le_satisfiedTermCount_of_satisfied_term, FABL.DNFFormula.fourierOneNorm_satisfiedTermCount_le, FABL.DNFFormula.toBooleanFunction_eq_thresholdSign_satisfiedTermCount, FABL.DNFFormula.exists_polynomialThresholdRepresentation_sparsity_le_quadratic, FABL.exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic, FABL.exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_cubic") (uses := "definition-4.1, definition-5.7, proposition-3.12, theorem-5.12") (tags := "section-5-6, support, fidelity-exact-explicit-constants-positive-dimension")
*Exercise 5.13 (sparse PTFs for DNFs).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF of size $`s`.

(a) Prove that $`f` has a polynomial threshold representation of sparsity
$`O(ns^3)`.

(b) Strengthen the construction to obtain sparsity $`O(ns^2)`.

For $`n\ge1`, one may take the explicit bounds $`17ns^3` and $`17ns^2`,
respectively. The positive-dimensional condition is necessary for these finite
bounds: when $`n=0`, the one empty term computes the constant $`-1`
function, whose representing polynomial has positive sparsity while
$`ns^2=ns^3=0`.
:::

:::lemma_ "support-exercise-5.14" (parent := "fabl-chapter-5") (lean := "FABL.ac0ThresholdParityTarget, FABL.hasDepthCircuit_ac0ThresholdParityTarget, FABL.pow_two_sq_le_polynomialSparsity_ac0ThresholdParityTarget, FABL.pow_two_pow_log_le_thresholdOfParitiesSize_ac0ThresholdParityTarget") (uses := "support-exercise-1.1g-inner-product-mod-two, proposition-3.21, corollary-5.11, support-exercise-4.12, support-exercise-5.12") (tags := "section-5-6, support, fidelity-exact-explicit-subsequence")
*Exercise 5.14 (an $`\mathrm{AC}^0` separation).* For every integer
$`m\ge 7`, set $`N=2^m`. On the first $`2m^2` coordinates of
$`\{-1,1\}^N`, partition each of the two $`m^2`-coordinate halves into
$`m` blocks of size $`m`, and let $`f_m` be the product of the $`m`
inner-product-modulo-$`2` functions on the paired blocks. Then $`f_m` is
computed by an AND--OR--AND circuit of depth $`3`, size at most $`N^3`,
and bottom fan-in at most $`2m`. Every polynomial threshold
representation of $`f_m` has at least $`2^{m^2}` nonzero Fourier
monomials; consequently, every threshold-of-parities circuit computing
$`f_m` has size at least
$$`
N^{\log_2 N}=2^{m^2}.
`
This gives the asserted asymptotic construction on the infinite subsequence
$`N=2^m`; the unused coordinates are fixed only in the lower-bound
restriction argument.
:::

:::lemma_ "support-exercise-5.15" (parent := "fabl-chapter-5") (lean := "FABL.singletonIndicatorFourierProjection, FABL.prescribedFourierKernel, FABL.prescribedFourierKernel_apply_self, FABL.expect_sq_prescribedFourierKernel, FABL.prescribedFourierKernel_comm, FABL.sum_ne_sq_prescribedFourierKernel, FABL.prescribedFourierOffCenterSum, FABL.measure_prescribedFourierOffCenterSum_abs_ge_le, FABL.prescribedFourierApproximation, FABL.fourierCoeff_prescribedFourierApproximation_eq_zero, FABL.HasPrescribedFourierUniformApproximation, FABL.measure_not_hasPrescribedFourierUniformApproximation_le, FABL.typicalPolynomialThresholdCutoff, FABL.typicalPolynomialThresholdCutoff_le, FABL.card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff, FABL.measure_not_isPolynomialThreshold_typicalPolynomialThresholdCutoff_le") (uses := "theorem-1.1, parseval") (tags := "section-5-6, support, fidelity-exact-explicit-cutoff")
*Exercise 5.15 (approximating almost all functions on a prescribed Fourier
support).* Let $`\mathcal F` be a nonempty collection of subsets of $`[n]`.
For $`a\in\{-1,1\}^n`, let $`1_{\{a\}}` be the indicator of the singleton
$`\{a\}`, define its projection onto $`\mathcal F` by
$$`
1_{\{a\}}^{\mathcal F}
=\sum_{S\in\mathcal F}
  \widehat{1_{\{a\}}}(S)\chi_S,
`
and set
$$`
\psi_a=\frac{2^n}{|\mathcal F|}\,1_{\{a\}}^{\mathcal F}.
`

(a) Prove
$$`
\psi_a(a)=1,
\qquad
\mathbb E[\psi_a^2]=\frac1{|\mathcal F|}.
`
Also prove that for all $`a,x\in\{-1,1\}^n`,
$$`
\psi_a(x)=\psi_x(a),
\qquad
\sum_{a\ne x}\psi_a(x)^2
=\frac{2^n}{|\mathcal F|}-1.
`

(b) Fix $`0<\epsilon<1` and suppose
$$`
|\mathcal F|
\ge\left(1-\frac{\epsilon^2}{6n}\right)2^n.
`
Choose $`f:\{-1,1\}^n\to\{-1,1\}` uniformly at random. For each fixed
$`x\in\{-1,1\}^n`, prove that
$$`
\left|\sum_{a\ne x}f(a)\psi_a(x)\right|<\epsilon
`
except with probability at most $`4^{-n}`.

(c) Deduce that, for all but a $`2^{-n}` fraction of Boolean functions $`f`,
there is a multilinear polynomial
$`q:\{-1,1\}^n\to\mathbb R` supported on
$`\{\chi_S:S\in\mathcal F\}` such that
$$`
\lVert f-q\rVert_\infty<\epsilon.
`

(d) Deduce that all but a $`2^{-n}` fraction of Boolean functions on $`n`
variables have a polynomial threshold representation of degree at most
$$`
\frac n2+O(\sqrt{n\log n}).
`
:::

:::lemma_ "support-exercise-5.21" (parent := "fabl-chapter-5") (lean := "FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence, FABL.abs_fourierCoeff_majority_two_mul_add_one, FABL.abs_fourierCoeff_majority_next_odd_eq, FABL.abs_fourierCoeff_majority_next_odd_lt, FABL.abs_fourierCoeff_majority_le_singleton, FABL.fourierCoeff_majority_singleton_isGreatest, FABL.tendsto_oddMajorityInfluence_div_main, FABL.tendsto_fourierCoeff_majority_singleton_div_sqrt") (uses := "support-exercise-2.22, theorem-5.19, corollary-5.20") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.21 (the largest Fourier coefficient of Majority).* Fix an odd
$`n`. Using Theorem 5.19, prove that
$`|\widehat{\operatorname{Maj}_n}(S)|` is a decreasing function of $`|S|`
for odd integers
$$`
1\le |S|\le\frac{n-1}{2}.
`
Then use Corollary 5.20 to deduce
$$`
\lVert\widehat{\operatorname{Maj}_n}\rVert_\infty
=\widehat{\operatorname{Maj}_n}(\{1\})
\sim\sqrt{\frac{2}{\pi n}}.
`
:::

:::lemma_ "support-exercise-5.25" (parent := "fabl-chapter-5") (lean := "FABL.fourierWeightAtLevel_majority_oddArity_tendsto") (uses := "theorem-2.45, theorem-2.49, support-limiting-majority-fourier-weights") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.25 (recovering limiting Fourier weights from stability).* Assume
only that
$$`
\operatorname{Stab}_\rho[\operatorname{Maj}_n]
\longrightarrow\frac2\pi\arcsin\rho
\qquad(\rho\in[-1,1])
`
and that
$$`
\operatorname{Stab}_\rho[\operatorname{Maj}_n]
=\sum_{k\ge0}\mathbf W^k[\operatorname{Maj}_n]\rho^k.
`
Prove, by induction on $`k` and by taking $`|\rho|` sufficiently small at
each step, that for every $`k\in\mathbb N`,
$$`
\lim_{n\to\infty}\mathbf W^k[\operatorname{Maj}_n]
=
[\rho^k]\left(\frac2\pi\arcsin\rho\right).
`
Here $`n` tends to infinity through the positive odd integers.
:::

:::lemma_ "support-exercise-5.26" (parent := "fabl-chapter-5") (lean := "FABL.fourierOneNorm_degreePart_majority_odd, FABL.binomialHalfOddReciprocalExpectation, FABL.fourierOneNorm_majority_odd_eq_binomialExpectation, FABL.fourierOneNorm_majority_odd_isEquivalent") (uses := "definition-3.8, support-exercise-2.22, theorem-5.19") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.26 (the Fourier $`1`-norm of Majority).* Let $`m\in\mathbb N`.

(a) For every integer $`0\le j\le m`, prove
$$`
\left\lVert
  \widehat{\operatorname{Maj}_{2m+1}}^{\,=2j+1}
\right\rVert_1
=
\binom mj\frac1{2j+1}
\frac{2m+1}{2^{2m}}\binom{2m}{m}.
`

(b) If $`X\sim\operatorname{Binomial}(m,1/2)`, deduce
$$`
\left\lVert\widehat{\operatorname{Maj}_{2m+1}}\right\rVert_1
=
\mathbb E\!\left[\frac1{2X+1}\right]
\frac{2m+1}{2^m}\binom{2m}{m}.
`

(c) Deduce, as odd $`n` tends to infinity,
$$`
\left\lVert\widehat{\operatorname{Maj}_n}\right\rVert_1
\sim
\frac2{\sqrt\pi}\frac1{\sqrt n}\,2^{n/2}.
`
:::

:::lemma_ "support-exercise-5.28" (parent := "fabl-chapter-5") (lean := "FABL.negativeCoordinateCount, FABL.krawtchoukValue, FABL.krawtchoukGeneratingPolynomial, FABL.coeff_krawtchoukGeneratingPolynomial, FABL.sum_krawtchoukValue_mul_pow, FABL.sum_krawtchoukValue, FABL.sum_krawtchoukValue_mul_pow_eq_noiseKernel, FABL.krawtchoukPolynomial, FABL.krawtchoukPolynomial_natDegree, FABL.eval_krawtchoukPolynomial_eq_coeff_countGenerating, FABL.negativeCoordinateCount_le, FABL.krawtchoukGeneratingPolynomial_eq_negativeCount, FABL.krawtchoukValue_eq_coeff_negativeCount, FABL.krawtchoukPolynomial_represents") (uses := "theorem-1.1, definition-2.46, proposition-2.47") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.28 (Krawtchouk polynomials).* For integers
$`0\le j\le n`, define
$$`
K_j(x)=\sum_{\substack{S\subseteq[n]\\|S|=j}}x^S,
\qquad x\in\{-1,1\}^n.
`
Since $`K_j` is symmetric, its value depends only on the number $`z` of
coordinates of $`x` equal to $`-1`; equivalently,
$`\sum_i x_i=n-2z`. Write $`K_j(z)` for this common value.

(a) Prove that $`K_j(z)` is represented by a degree-$`j` polynomial in
$`z`. This is the Krawtchouk polynomial of degree $`j`.

(b) Prove
$$`
\sum_{j=0}^nK_j(x)
=2^n\,1_{\{(1,\ldots,1)\}}(x).
`

(c) For $`\rho\in[-1,1]`, prove
$$`
\sum_{j=0}^nK_j(x)\rho^j
=
2^n\Pr_{\boldsymbol y\sim N_\rho(x)}
  [\boldsymbol y=(1,\ldots,1)].
`

(d) Deduce the generating-function identity
$$`
K_j(z)
=
[\rho^j]\bigl((1-\rho)^z(1+\rho)^{n-z}\bigr).
`
:::

:::lemma_ "support-exercise-5.32" (parent := "fabl-chapter-5") (lean := "FABL.gaussianUpperRightQuadrant, FABL.isOpen_gaussianUpperRightQuadrant, FABL.gaussianQuadrantProbability, FABL.tendsto_noiseStability_hammingUpperTailIndicator, FABL.gaussianQuadrantProbability_one_sub_upperTail") (uses := "notation-5.14, theorem-5.38, proposition-5.25") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.32 (the Gaussian limit for biased Majority).* Fix
$`t\in\mathbb R`, and let $`f_n` be the sequence of linear threshold
functions from Proposition 5.25,
$$`
f_n(x)=1\left\{\frac1{\sqrt n}\sum_{i=1}^nx_i>t\right\}.
`
For $`\beta\in(0,1)`, let $`t_\beta` be determined by
$`\overline\Phi(t_\beta)=\beta`. For standard Gaussian variables
$`z_1,z_2` with $`\mathbb E[z_1z_2]=\rho`, define the Gaussian quadrant
probability
$$`
\Lambda_\rho(\beta)
=\Pr[z_1>t_\beta,\ z_2>t_\beta].
`
Set $`\mu=\overline\Phi(t)`.
Prove
$$`
\lim_{n\to\infty}\operatorname{Stab}_\rho[f_n]
=\Lambda_\rho(\mu).
`
Also verify that, if $`\alpha=\Phi(t)`, then
$$`
\Lambda_\rho(\alpha)
=\Pr[z_1\le t,\ z_2\le t].
`
:::

:::lemma_ "support-exercise-5.34" (parent := "fabl-chapter-5") (lean := "FABL.noiseSensitivity_le_one, FABL.noiseSensitivity_le_dimension_mul_delta, FABL.HasInputLengthAtMost, FABL.boundedInputLengthNoiseModulus, FABL.boundedInputLengthNoiseModulus_tendsto_zero, FABL.uniformlyNoiseStable_of_inputLengthAtMost") (uses := "support-exercise-2.42, example-2.30, definition-5.34") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.34 (bounded input length is vacuously stable).* Let
$`\mathcal B` be a class of Boolean-valued functions, every member of which
has input length at most $`n`. Prove that for every $`f\in\mathcal B` and
every $`\delta\in[0,1/2]`,
$$`
\operatorname{NS}_\delta[f]\le n\delta.
`
Deduce that $`\mathcal B` is uniformly noise-stable.
:::

:::lemma_ "support-exercise-5.35" (parent := "fabl-chapter-5") (lean := "FABL.exists_signedDictator_relativeHammingDist_le_of_isBalanced_totalInfluence_le") (uses := "parseval, support-exercise-2.5-unate, proposition-3.2") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.35 (robust edge isoperimetry at volume $`1/2`).* Let
$`\delta\ge0`, and let $`f:\{-1,1\}^n\to\{-1,1\}` satisfy
$$`
\mathbb E[f]=0,
\qquad
\mathbf I[f]\le1+\delta.
`
Give a direct proof that $`f` is $`O(\delta)`-close to
$`\chi_i` or $`-\chi_i` for some $`i\in[n]`. More precisely, prove that one
may achieve $`\delta`-closeness.

The suggested argument is to lower-bound
$`\sum_i\widehat f(i)^2` and then use
$$`
\sum_i\widehat f(i)^2
\le
\left(\max_i|\widehat f(i)|\right)
\sum_i|\widehat f(i)|,
`
together with Proposition 3.2 and
$`|\widehat f(i)|\le\operatorname{Inf}_i[f]`.
:::

:::lemma_ "support-exercise-5.36" (parent := "fabl-chapter-5") (lean := "FABL.fknOptimalityGaussianMass, FABL.fknOptimalityThreshold, FABL.fknOptimalityGaussianBoundary, FABL.standardGaussianUpperTail_fknOptimalityThreshold, FABL.fknOptimalityGaussianBoundary_eq_density, FABL.fknOptimalityGaussianBoundary_pos, FABL.IsFKNOptimalityApproximation, FABL.fknOptimalityDimensionIndex, FABL.fknOptimalityDimensionIndex_spec, FABL.fknOptimalityTailDimension, FABL.fknOptimalitySmallSet, FABL.fknOptimalitySmallSetMass, FABL.fknOptimalitySmallSetMass_approx, FABL.fknOptimalitySmallSetWeight_approx, FABL.fknOptimalitySmallSetMass_pos, FABL.fknOptimalityGaussianMass_lt_two_mul_smallSetMass, FABL.two_mul_fknOptimalitySmallSetMass_lt_three_mul_gaussianMass, FABL.fknOptimalitySmallSetWeight_gt_half_boundary_sq, FABL.fknOptimalityDelta, FABL.fknOptimalityDelta_pos, FABL.fknOptimalityGaussianMass_lt_delta, FABL.fknOptimalityDelta_lt_three_mul_gaussianMass, FABL.tendsto_fknOptimalityDelta, FABL.fknOptimalityFunction, FABL.fourierCoeff_fknOptimalityFunction_zero, FABL.fourierCoeff_fknOptimalityFunction_succ, FABL.fourierWeightAtLevel_one_fknOptimalityFunction, FABL.fourierWeightAtLevel_one_fknOptimalityFunction_eq_delta, FABL.fknOptimalityGaussianMain, FABL.eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower, FABL.exercise5_36") (uses := "definition-1.19, proposition-5.25, proposition-5.27") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.36 (optimality of the improved FKN bound).* Exhibit a sequence
of Boolean functions $`f:\{-1,1\}^n\to\{-1,1\}` and positive parameters
$`\delta\to0` such that
$$`
\widehat f(\{1\})=1-\frac\delta2
`
and
$$`
\mathbf W^1[f]
\ge
1-\delta+\Omega\!\left(\delta^2\log(1/\delta)\right).
`
Thus the second-order error term in Theorem 5.33 is essentially optimal.
:::

:::lemma_ "support-exercise-5.39" (parent := "fabl-chapter-5") (lean := "FABL.fourierWeightAbove_pred_le_four_div_sqrt_of_isLinearThreshold, FABL.deriv_noiseSensitivityCurve_le_sqrt_three_halves_div_sqrt_of_isLinearThreshold") (uses := "theorem-2.49, fact-2.53, peres-theorem") (tags := "section-5-6, support, fidelity-exact-explicit-universal-constant")
*Exercise 5.39 (the derivative of LTF noise sensitivity).* Prove that every
linear threshold function $`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\frac{d}{d\delta}\operatorname{NS}_\delta[f]
\le O\!\left(\frac1{\sqrt\delta}\right)
\qquad(0<\delta\le1/2),
`
with a universal implied constant. It is enough to use the consequence of
Peres's Theorem that
$$`
\mathbf W^{\ge k}[f]\le O(k^{-1/2})
`
for every $`k\ge1`.
:::

:::lemma_ "support-exercise-5.40" (parent := "fabl-chapter-5") (lean := "FABL.polynomialThresholdClass, FABL.polynomialThresholdClass_closedUnderNegatingInputVariables, FABL.polynomialThresholdClass_closedUnderIdentifyingInputVariables, FABL.HasUniformlySublinearTotalInfluence, FABL.HasUniformPolynomialThresholdNoiseSensitivitySqrtBound, FABL.HasUniformPolynomialThresholdTotalInfluenceSqrtBound, FABL.totalInfluence_le_two_div_one_sub_exp_neg_two_mul_dimension_mul_noiseModulus, FABL.polynomialThresholdClass_uniformlyNoiseStable_iff_uniformlySublinearTotalInfluence, FABL.uniformPolynomialThreshold_noiseSensitivitySqrtBound_iff_totalInfluenceSqrtBound") (uses := "support-exercise-2.43a-average-influence, definition-5.34, theorem-5.35") (tags := "section-5-6, support, fidelity-exact-explicit-uniform-constants")
*Exercise 5.40 (influence bounds are necessary for uniform noise
stability).* Let $`\mathcal P_{n,k}` be the degree-at-most-$`k` polynomial
threshold functions on $`n` variables, and let
$`\mathcal P_k=\bigcup_n\mathcal P_{n,k}`. Suppose
$$`
\operatorname{NS}_\delta[f]\le\epsilon(\delta)
`
for every $`f\in\mathcal P_k`. Prove that every
$`f\in\mathcal P_{n,k}` satisfies
$$`
\mathbf I[f]\le O\!\left(n\,\epsilon(1/n)\right).
`
Deduce both equivalences:

(a) $`\mathcal P_k` is uniformly noise-stable if and only if
$`\mathbf I[f]=o(n)` uniformly for $`f\in\mathcal P_{n,k}`.

(b) The bound
$$`
\operatorname{NS}_\delta[f]\le O(k\sqrt\delta)
\qquad(f\in\mathcal P_k)
`
holds if and only if
$$`
\mathbf I[f]\le O(k\sqrt n)
\qquad(f\in\mathcal P_{n,k}).
`
:::

:::lemma_ "support-exercise-5.41" (parent := "fabl-chapter-5") (lean := "FABL.gotsmanLinialStart, FABL.gotsmanLinialRoot, FABL.gotsmanLinialPolynomial, FABL.gotsmanLinialCubePolynomial, FABL.gotsmanLinialExtremizer, FABL.gotsmanLinialExtremizer_isSymmetric, FABL.natDegree_gotsmanLinialPolynomial, FABL.gotsmanLinialExtremizer_isPolynomialThreshold, FABL.gotsmanLinialCubePolynomial_ne_zero, FABL.gotsmanLinialExtremizer_centralLayer, FABL.totalInfluence_gotsmanLinialExtremizer, FABL.normalizedGotsmanLinialTotalInfluence, FABL.tendsto_normalizedGotsmanLinialTotalInfluence") (uses := "definition-2.8, fact-2.14, definition-2.27, definition-5.4, support-exercise-5.21") (tags := "section-5-6, support, fidelity-exact-lower-tie")
*Exercise 5.41 (the proposed Gotsman--Linial extremizer).* Estimate
carefully the asymptotics of $`\mathbf I[f]`, where
$`f\in\mathcal P_{n,k}` is the symmetric polynomial threshold function from
the strongest form of the Gotsman--Linial Conjecture:
$$`
f(x)=\operatorname{sgn}\bigl(p(x_1+\cdots+x_n)\bigr),
`
with $`p` a degree-$`k` univariate polynomial alternating sign on the
$`k+1` attainable values of $`x_1+\cdots+x_n` nearest to $`0`.

For $`n\ge1` and $`0\le k\le n`, put
$$`
a_{n,k}=\left\lfloor\frac{n-k}{2}\right\rfloor,\qquad
p_{n,k}(t)=\prod_{j=0}^{k-1}
  \left(t-\bigl(2(a_{n,k}+j)-n+1\bigr)\right),
`
and let $`f_{n,k}(x)=\operatorname{sgn}(p_{n,k}(\sum_i x_i))`.
This is the lower-tie choice when the two central blocks are equidistant.
It is a symmetric degree-$`k` polynomial threshold function, its displayed
roots are not attained on the cube, and it alternates on the selected
central layers. Its total influence is exactly
$$`
\mathbf I[f_{n,k}]
=\frac{n}{2^{n-1}}
  \sum_{j=0}^{k-1}\binom{n-1}{a_{n,k}+j}.
`
Consequently, for each fixed $`k`,
$$`
\lim_{r\to\infty}
\frac{\mathbf I[f_{k+r,k}]}{\sqrt{k+r}}
=k\sqrt{\frac{2}{\pi}},
`
equivalently $`\mathbf I[f_{n,k}]\sim
k\sqrt{2/\pi}\,\sqrt n` as $`n\to\infty` with $`k` fixed.

The exact binomial formula also holds for $`n<k`. In the degenerate case
$`(n,k)=(0,0)`, the candidate is constant and has total influence $`0`;
there is then no block of $`k+1` attainable central values.
:::

:::lemma_ "support-exercise-5.42" (parent := "fabl-chapter-5") (lean := "FABL.smallSetCenterOfMass, FABL.smallSetCenterOfMass_apply, FABL.sum_sq_smallSetCenterOfMass, FABL.exists_smallSetCenterOfMass_sqNorm_constant, FABL.exists_smallSetCenterOfMass_norm_constant") (uses := "theorem-1.1, level-1-inequality") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.42 (the center of mass of a small subset of the cube).* Let
$`A\subseteq\{-1,1\}^n` have cardinality $`\alpha2^n`, where
$`0<\alpha\le1/2`. Regard the discrete cube as a subset of $`\mathbb R^n`,
and let
$$`
\mu_A=\frac1{|A|}\sum_{x\in A}x
`
be its center of mass. Prove
$$`
\lVert\mu_A\rVert_2
\le O\!\left(\sqrt{\log(1/\alpha)}\right),
`
with a universal implied constant.
:::

:::lemma_ "support-exercise-5.43" (parent := "fabl-chapter-5") (lean := "FABL.hasDerivAt_standardGaussianUpperTail, FABL.gaussianIsoperimetricReal, FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo, FABL.gaussianIsoperimetricReal_eq_gaussianIsoperimetric, FABL.continuousOn_gaussianIsoperimetricReal, FABL.gaussianIsoperimetricReal_pos, FABL.hasDerivAt_gaussianIsoperimetricReal, FABL.gaussianIsoperimetric_second_derivative, FABL.concaveOn_gaussianIsoperimetricReal") (uses := "definition-5.26") (tags := "section-5-6, support, fidelity-exact")
*Exercise 5.43 (concavity of the Gaussian isoperimetric function).* Prove
that the Gaussian isoperimetric function $`U` satisfies
$$`
U''(\alpha)=-\frac1{U(\alpha)}
\qquad(0<\alpha<1).
`
Deduce that $`U` is concave on $`[0,1]`.
:::

:::lemma_ "support-exercise-5.44" (parent := "fabl-chapter-5") (lean := "FABL.exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular, FABL.exercise5_44, FABL.signedHammingTwoTail, FABL.fourierCoeff_signedHammingTwoTail_singleton, FABL.signedHammingTwoTail_mem_Icc, FABL.expect_abs_signedHammingTwoTail, FABL.fourierWeightAtLevel_one_signedHammingTwoTail, FABL.signedHammingTwoTailEpsilon, FABL.abs_fourierCoeff_signedHammingTwoTail_eq_epsilon, FABL.tendsto_signedHammingTwoTailEpsilon, FABL.tendsto_expect_abs_signedHammingTwoTail, FABL.tendsto_fourierWeightAtLevel_one_signedHammingTwoTail, FABL.exercise5_44_printed_false") (uses := "definition-1.19, definition-5.26, support-exercise-5.31, proposition-5.25, support-exercise-5.43") (tags := "section-5-6, support, erratum, external-probability-dependency, fidelity-corrected-false-printed-codomain")
*Exercise 5.44 (a Gaussian-sharp Level-$`1` bound, corrected).* Fix
$`\alpha\in(0,1/2)` and $`\epsilon\ge0`. Let
$`f:\{-1,1\}^n\to[0,1]` satisfy
$$`
\mathbb E[f]\le\alpha,
\qquad
|\widehat f(\{i\})|\le\epsilon
\quad\text{for every }i\in[n].
`
Prove
$$`
\mathbf W^1[f]
\le U(\alpha)^2+C_\alpha\epsilon,
`
where $`U` is the Gaussian isoperimetric function and the constant
$`C_\alpha` may depend on $`\alpha` but not on $`n`, $`f`, or
$`\epsilon`. The proof uses the nonuniform Berry--Esseen estimate from
Exercise 5.31.

The May 2021 edition instead permits the codomain $`[-1,1]` and assumes
$`\mathbb E[|f|]\le\alpha`. That version is false: signed functions can
place positive and negative mass on opposite Gaussian tails while keeping
the same absolute mean budget, exceeding the one-sided $`U(\alpha)` bound.
Indeed, for one fixed
$`\alpha\in(0,1/2)`, every proposed $`C_\alpha` is defeated by functions
whose singleton coefficients tend to zero.
:::

:::lemma_ "support-exercise-5.45" (parent := "fabl-chapter-5") (lean := "FABL.polynomialDerivativeThreshold, FABL.discreteDerivative_toReal_eq_polynomialDerivativeThreshold_of_ne_zero, FABL.expect_toReal_mul_coordinateSign_mul_polynomialDerivativeThreshold_eq_influence, FABL.totalInfluence_le_expect_abs_derivativeThresholdSum, FABL.totalInfluence_le_sqrt_dimension_add_derivativeThresholdCrossMoments, FABL.polynomialDerivativeThreshold_isPolynomialThreshold, FABL.totalInfluence_le_sqrt_dimension_add_sum_derivativeThresholdInfluence, FABL.polynomialThresholdInfluenceExponent, FABL.polynomialThresholdInfluenceExponent_zero, FABL.polynomialThresholdInfluenceExponent_nonneg, FABL.two_mul_polynomialThresholdInfluenceExponent_succ, FABL.polynomialThresholdInfluenceExponent_succ_pos, FABL.totalInfluence_toReal_le_two_mul_rpow_of_isPolynomialThreshold, FABL.polynomialThresholdNoiseExponent, FABL.polynomialThresholdNoiseExponent_pos, FABL.polynomialThresholdNoiseExponent_le_one, FABL.polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent, FABL.noiseSensitivity_le_three_mul_rpow_of_isPolynomialThreshold, FABL.polynomialThresholdNoiseModulus, FABL.polynomialThresholdNoiseModulus_tendsto_zero, FABL.polynomialThresholdClass_uniformlyNoiseStable_of_influenceBound") (uses := "proposition-2.24, definition-2.27, definition-5.4, theorem-5.35") (tags := "section-5-6, support, fidelity-exact-explicit-constants")
*Exercise 5.45 (an elementary influence bound for PTFs).* Prove by induction
on $`k` that every degree-$`k` polynomial threshold function
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\mathbf I[f]\le2\,n^{\,1-2^{-k}}.
`
The case $`k=0` is immediate. For $`k>0`, write
$`f=\operatorname{sgn}(p)`, where
$`p:\{-1,1\}^n\to\mathbb R` is a degree-$`k` polynomial which is nonzero
at every point of the cube.

(a) For every $`i\in[n]`, prove
$$`
\mathbb E\!\left[
  f(x)x_i\operatorname{sgn}(D_ip(x))
\right]
=\operatorname{Inf}_i[f].
`
First use
$`f=x_iD_if+E_if`, and prove that
$`D_if=\operatorname{sgn}(D_ip)` whenever $`D_if\ne0`.

(b) Deduce
$$`
\mathbf I[f]
\le
\mathbb E\!\left[
  \left|\sum_i x_i\operatorname{sgn}(D_ip(x))\right|
\right].
`

(c) Apply Cauchy--Schwarz to deduce
$$`
\mathbf I[f]
\le
\sqrt{
  n+
  \sum_{i\ne j}
  \mathbb E\!\left[
    x_ix_j
    \operatorname{sgn}(D_ip(x))
    \operatorname{sgn}(D_jp(x))
  \right]
}.
`

(d) Bound the cross terms and apply the arithmetic--geometric mean
inequality to obtain
$$`
\mathbf I[f]
\le
\sqrt{
  n+\sum_i\mathbf I[\operatorname{sgn}(D_ip)]
}.
`

(e) Use the induction hypothesis for the degree-at-most-$`k-1` threshold
functions $`\operatorname{sgn}(D_ip)` to prove
$`\mathbf I[f]\le2\,n^{1-2^{-k}}`.

(f) Deduce that degree-$`k` polynomial threshold functions form a uniformly
noise-stable class. More precisely, for every
$`\delta\in(0,1/2]`,
$$`
\operatorname{NS}_\delta[f]
\le3\delta^{\,2^{-k}}.
`
:::

:::theorem "conjecture-exercise-5.45b" (parent := "fabl-chapter-5") (uses := "definition-2.5, definition-5.4") (tags := "section-5-6, open, conjecture")
*Open conjecture in Exercise 5.45(b).* There should be a universal constant
$`C` such that whenever
$`p:\{-1,1\}^n\to\mathbb R` is a degree-$`2` polynomial which is nonzero
on the cube,
$$`
\mathbb E\!\left[
  \left|\sum_i x_i\operatorname{sgn}(D_ip(x))\right|
\right]
\le C\sqrt n.
`
Each $`\operatorname{sgn}(D_ip)` is a linear threshold function. This
conjecture remains open.
:::

:::lemma_ "notes-5.6-provenance" (parent := "fabl-chapter-5") (tags := "section-5-6, nondependency, bibliographic")
*Notes on sources and provenance.*

Chow's Theorem was proved independently by Chow and Tannenbaum in 1961;
Elgot gave related work. Bruck proved the PTF generalization, Theorem 5.10,
and the threshold-circuit result of Exercise 5.12. Theorems 5.2 and 5.9,
the Gotsman--Linial Conjecture, and Exercise 5.11 come from Gotsman and
Linial. Conjecture 5.3 is folklore. Bruck and Smolensky established
Corollary 5.13 and essentially Theorem 5.12. Exercise 5.13 is credited to
Krause and Pudlak, the counting bound in Exercise 5.4 is asymptotically
sharp by Zuev, and Exercise 5.15 is due to O'Donnell and Servedio.

Titsworth's work on interplanetary ranging systems contains the ideas behind
Theorem 2.33, Proposition 2.58, and the correlation-distillation problem in
Exercise 5.7. Titsworth also first computed the Fourier expansion of
Majority. Later approaches used binomial identities and Krawtchouk
polynomials; the limiting majority-weight asymptotics are attributed to
Kalai and O'Donnell, and Krawtchouk introduced the polynomials bearing his
name.

The central limit theorem used here is due independently to Berry and
Esseen. Shevtsova obtained the constant quoted in the chapter. Bikelis
proved the nonuniform version used in Exercise 5.31, and Bentkus proved the
multidimensional theorem stated as Theorem 5.38. Sheppard's formula dates
to 1899; the results collected in Theorem 5.18 appeared in work of
O'Donnell.

The Level-$`1` Inequality is folklore and was published by Talagrand. The
two halves of the $`2/\pi` Theorem are due respectively to Khot et al. and
Matulef et al. The improved FKN estimate and the optimality construction in
Exercise 5.36 are due to Jendrej, Oleszkiewicz, and Wojtaszczyk. Earlier FKN
constants come from Friedgut, Kalai, and Naor and from Kindler and Safra.
Exercise 5.35 was communicated by Eric Blais, Exercise 5.44 is due to Khot
et al., and Exercise 5.42 was suggested by Rocco Servedio.

Peres proved the linear-threshold noise-sensitivity theorem; the earlier
work of Benjamini, Kalai, and Schramm introduced uniform noise stability for
LTFs. The proof in this chapter incorporates simplifications of Gopalan and
ideas of Diakonikolas et al. Kane proved the later total-influence bound for
polynomial threshold functions, and Exercise 5.39 was suggested by Nitin
Saurabh.
:::
