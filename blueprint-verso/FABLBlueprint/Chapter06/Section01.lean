/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06.Pseudorandomness

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Notions of pseudorandomness" =>

:::proposition "proposition-6.1" (parent := "fabl-chapter-6") (lean := "FABL.pBiasedRandomFunctionPMF, FABL.measure_pBiasedRandomFunction_fourierFailure_le") (uses := "proposition-1.8") (tags := "section-6-1, fidelity-exact")
*Proposition 6.1.* Let $`n>1` and let
$`f:\{-1,1\}^n\to\{0,1\}` be a $`p`-biased random function: independently
for every $`x\in\{-1,1\}^n`, $`f(x)=1` with probability $`p` and $`f(x)=0`
with probability $`1-p`. Except with probability at most $`2^{-n}`, both
$$`
\left|\widehat f(\varnothing)-p\right|
\le 2\sqrt n\,2^{-n/2}
`
and
$$`
\left|\widehat f(S)\right|
\le 2\sqrt n\,2^{-n/2}
\qquad\text{for every nonempty }S\subseteq[n]
`
hold simultaneously.
:::

:::definition "definition-6.2" (parent := "fabl-chapter-6") (lean := "FABL.IsFourierRegular") (uses := "proposition-1.8") (tags := "section-6-1, fidelity-exact")
*Definition 6.2.* A function $`f:\{-1,1\}^n\to\mathbb R` is
*$`\epsilon`-regular* (also called *$`\epsilon`-uniform*) if
$$`
|\widehat f(S)|\le\epsilon
\qquad\text{for every nonempty }S\subseteq[n].
`
:::

:::lemma_ "remark-6.3" (parent := "fabl-chapter-6") (lean := "FABL.isFourierRegular_uniformLpNorm_one") (uses := "definition-6.2, support-exercise-3.9") (tags := "section-6-1, fidelity-exact")
*Remark 6.3.* Every $`f:\{-1,1\}^n\to\mathbb R` is
$`\lVert f\rVert_1`-regular. When $`f` takes values in $`[-1,1]`, the
interesting range is therefore $`\epsilon\le1`.
:::

:::lemma_ "example-6.4" (parent := "fabl-chapter-6") (lean := "FABL.measure_pBiasedRandomFunction_not_isFourierRegular_le, FABL.isFourierRegular_zero_iff_exists_const, FABL.isFourierRegular_setIndicator_binaryAffineSubspace_of_codimension, FABL.isFourierRegular_innerProductModTwo_zeroOne, FABL.isFourierRegular_completeQuadratic_zeroOne, FABL.parityFunction_not_isFourierRegular_of_lt_one, FABL.isFourierRegular_majority_odd") (uses := "proposition-6.1, definition-6.2, proposition-3.12, support-exercise-1.1g-inner-product-mod-two, support-exercise-5.21") (tags := "section-6-1, fidelity-exact-explicit-odd-majority-domain")
*Example 6.4.* A random $`p`-biased function is
$`2\sqrt n\,2^{-n/2}`-regular with probability at least $`1-2^{-n}`.
A function is $`0`-regular exactly when it is constant. If
$`A\subseteq\mathbb F_2^n` is an affine subspace of codimension $`k`, then
$`\mathbf1_A` is $`2^{-k}`-regular. For even $`n`, the inner-product-mod-$`2`
and complete-quadratic functions
$`\operatorname{IP}_n,\operatorname{CQ}_n:\mathbb F_2^n\to\{0,1\}` are
$`2^{-n/2-1}`-regular. A nonconstant parity $`\chi_S` is not
$`\epsilon`-regular for any $`\epsilon<1`, while for odd
$`n=2m+1`, $`\operatorname{Maj}_{2m+1}` is
$`1/\sqrt{2m+1}`-regular.
:::

:::definition "definition-6.5" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.IsBiased, FABL.ProbabilityDensity.isBiased_iff_expectation, FABL.coordinateProjectionLinear, FABL.ProbabilityDensity.coordinateMarginal, FABL.ProbabilityDensity.vectorFourierCoeff_coordinateMarginal, FABL.ProbabilityDensity.IsBiased.coordinateMarginal") (uses := "definition-1.20, definition-1.22, definition-6.2, fact-1.21") (tags := "section-6-1, fidelity-exact")
*Definition 6.5.* A probability density
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` is an
*$`\epsilon`-biased density* if it is $`\epsilon`-regular. Equivalently,
$$`
\left|\mathbb E_{\boldsymbol x\sim\varphi}[\chi_\gamma(\boldsymbol x)]\right|
\le\epsilon
\qquad\text{for every }\gamma\in\widehat{\mathbb F_2^n}\setminus\{0\}.
`
The marginal on every set of coordinates is again $`\epsilon`-biased. If
$`\varphi=\varphi_A=\mathbf1_A/\mathbb E[\mathbf1_A]` for
$`A\subseteq\mathbb F_2^n`, then $`A` is called an *$`\epsilon`-biased set*.
:::

:::lemma_ "example-6.6" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.isBiased_one, FABL.ProbabilityDensity.isBiased_zero_iff_eq_uniform, FABL.ProbabilityDensity.affineSubspaceDensity_not_isBiased_of_lt_one, FABL.ProbabilityDensity.constantPairDensity_not_isBiased_of_two_le, FABL.ProbabilityDensity.constantPairDensity_one_isBiased_zero") (uses := "definition-6.5, definition-1.22, proposition-3.12") (tags := "section-6-1, erratum, fidelity-corrected-false-book-claim")
*Example 6.6.* Every probability density is $`1`-biased. The uniform density
$`\varphi\equiv1` on $`\mathbb F_2^n` is the only $`0`-biased density. If
$`A` is a proper affine subspace, then $`\varphi_A` is not
$`\epsilon`-biased for any $`\epsilon<1`.

The book next prints that the two-point set
$`E=\{(0,\ldots,0),(1,\ldots,1)\}` is $`1/2`-biased. This conflicts with
Definition 6.5 and with the preceding affine-subspace statement. The corrected
conclusion is: if $`n\ge2`, choose a nonzero even-weight $`\gamma`; then
$$`
\mathbb E_{x\sim\varphi_E}[\chi_\gamma(x)]=1,
`
so $`E` is not $`\epsilon`-biased for any $`\epsilon<1`. For $`n=1`,
$`E=\mathbb F_2` and its density is $`0`-biased.
:::

:::proposition "proposition-6.7" (parent := "fabl-chapter-6") (lean := "FABL.vectorFourierFourthMoment, FABL.vectorFourierFourthMoment_sub_mean_pow_four_le, FABL.epsilon_pow_four_le_vectorFourierFourthMoment_sub_mean_pow_four, FABL.vectorFourierFourthMoment_eq_additiveEnergy") (uses := "definition-6.2, definition-3.8, proposition-1.13, parseval") (tags := "section-6-1, fidelity-exact")
*Proposition 6.7.* Let $`f:\mathbb F_2^n\to\mathbb R`.

(1) If $`f` is $`\epsilon`-regular, then
$$`
\lVert\widehat f\rVert_4^4-\mathbb E[f]^4
\le\epsilon^2\operatorname{Var}[f].
`

(2) If $`f` is not $`\epsilon`-regular, then
$$`
\lVert\widehat f\rVert_4^4-\mathbb E[f]^4\ge\epsilon^4.
`

Here
$$`
\lVert\widehat f\rVert_4^4
=\mathbb E_{x,y,z}
[f(x)f(y)f(z)f(x+y+z)].
`
:::

:::lemma_ "fact-6.8" (parent := "fabl-chapter-6") (lean := "FABL.pmfExpectation_uniformBooleanFunction_stableInfluence_one_sub") (uses := "support-exercise-6.2") (tags := "section-6-1, fidelity-exact")
*Fact 6.8.* Fix $`\delta\in[0,1]` and choose
$`f:\{-1,1\}^n\to\{-1,1\}` uniformly at random. For every coordinate
$`i\in[n]`,
$$`
\mathbb E_f\!\left[\operatorname{Inf}^{(1-\delta)}_i[f]\right]
=\frac{(1-\delta/2)^n}{2-\delta}.
`
:::

:::definition "definition-6.9" (parent := "fabl-chapter-6") (lean := "FABL.HasSmallStableInfluences, FABL.HasSmallInfluences, FABL.stableInfluence_one_eq_influence, FABL.hasSmallInfluences_iff") (uses := "definition-2.52, proposition-2.54") (tags := "section-6-1, fidelity-exact")
*Definition 6.9.* A function $`f:\{-1,1\}^n\to\mathbb R` has
*$`(\epsilon,\delta)`-small stable influences*, or has no
*$`(\epsilon,\delta)`-notable coordinates*, if
$$`
\operatorname{Inf}^{(1-\delta)}_i[f]\le\epsilon
\qquad\text{for every }i\in[n].
`
This property gets stronger as $`\epsilon` and $`\delta` decrease. When
$`\delta=0`, it is called having *$`\epsilon`-small influences*.
:::

:::lemma_ "example-6.10" (parent := "fabl-chapter-6") (lean := "FABL.const_hasSmallStableInfluences_zero_zero, FABL.hasSmallInfluences_zero_iff_exists_const, FABL.majority_hasSmallInfluences, FABL.stableInfluence_parityFunction, FABL.parityFunction_hasSmallStableInfluences_of_log_bound, FABL.exists_stableInfluence_ge_of_isKJunta_of_balanced, FABL.not_hasSmallStableInfluences_of_isKJunta_of_balanced, FABL.leadingCoordinateTimes, FABL.one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd") (uses := "definition-6.9, fact-2.53, definition-2.4, support-exercise-5.21") (tags := "section-6-1, fidelity-exact-explicit-odd-majority-domain")
*Example 6.10.* Constants have $`(0,0)`-small stable influences, and they are
the only functions with $`0`-small influences. Majority has
$`1/\sqrt n`-small influences. For a nonempty parity $`\chi_S`,
$$`
\operatorname{Inf}^{(1-\delta)}_i[\chi_S]
=
\begin{cases}
(1-\delta)^{|S|-1},&i\in S,\\
0,&i\notin S;
\end{cases}
`
hence it has $`(\epsilon,\delta)`-small stable influences whenever
$`|S|\ge\ln(e/\epsilon)/\delta`.

If an unbiased $`k`-junta $`f` has variance $`1`, then some coordinate has
stable influence at least $`(1-\delta)^{k-1}/k`; thus it does not have
$`((1-\delta)^k/k,\delta)`-small stable influences for
$`\delta\in(0,1)`. Finally,
For odd $`n=2m+1`, the function
$$`
f(x_0,x_1,\ldots,x_n)=x_0\operatorname{Maj}_n(x_1,\ldots,x_n)
`
satisfies
$`\operatorname{Inf}^{(1-\delta)}_0[f]\ge1-\sqrt\delta`.
:::

:::definition "definition-6.11" (parent := "fabl-chapter-6") (lean := "FABL.IsLowDegreeFourierRegular, FABL.IsFourierRegular.isLowDegreeFourierRegular, FABL.isLowDegreeFourierRegular_dimension_iff") (uses := "definition-6.2, definition-1.19, definition-1.20") (tags := "section-6-1, fidelity-exact")
*Definition 6.11.* A function $`f:\{-1,1\}^n\to\mathbb R` is
*$`(\epsilon,k)`-regular* if
$$`
|\widehat f(S)|\le\epsilon
\qquad\text{whenever }0<|S|\le k.
`
Equivalently, the degree-at-most-$`k` part $`f^{\le k}` is
$`\epsilon`-regular. For $`k=n` (or $`k=\infty`) this is ordinary
$`\epsilon`-regularity. An $`(\epsilon,k)`-regular probability density, and
its associated distribution, is also called
*$`(\epsilon,k)`-wise independent*.
:::

:::proposition "proposition-6.12" (parent := "fabl-chapter-6") (lean := "FABL.IsLowDegreeFourierRegular.abs_mean_signRestriction_sub_mean_le, FABL.exists_signRestriction_mean_change_gt_of_not_isLowDegreeFourierRegular") (uses := "definition-6.11, definition-3.18, proposition-3.21") (tags := "section-6-1, fidelity-exact")
*Proposition 6.12.* Let $`f:\{-1,1\}^n\to\mathbb R`,
$`\epsilon\ge0`, and $`k\in\mathbb N`.

(1) If $`f` is $`(\epsilon,k)`-regular, then every restriction fixing at
most $`k` coordinates changes the mean of $`f` by at most $`2^k\epsilon`.

(2) If $`f` is not $`(\epsilon,k)`-regular, then some restriction fixing at
most $`k` coordinates changes the mean of $`f` by more than $`\epsilon`.
:::

:::proposition "proposition-6.13" (parent := "fabl-chapter-6") (lean := "FABL.IsLowDegreeFourierRegular.covariance_le_fourierOneNorm_mul, FABL.IsLowDegreeFourierRegular.covariance_booleanJunta_le, FABL.exists_booleanJunta_covariance_gt_of_not_isLowDegreeFourierRegular") (uses := "support-exercise-6.8") (tags := "section-6-1, fidelity-exact")
*Proposition 6.13.* Let $`f:\{-1,1\}^n\to\mathbb R`,
$`\epsilon\ge0`, and $`k\in\mathbb N`.

(1) If $`f` is $`(\epsilon,k)`-regular, then
$$`
\operatorname{Cov}[f,h]
\le\lVert\widehat h\rVert_1\epsilon
`
for every $`h:\{-1,1\}^n\to\mathbb R` of degree at most $`k`. In particular,
$$`
\operatorname{Cov}[f,h]\le 2^{k/2}\epsilon
`
for every Boolean-valued $`k`-junta $`h`.

(2) If $`f` is not $`(\epsilon,k)`-regular, then there is a Boolean-valued
$`k`-junta $`h` such that
$`\operatorname{Cov}[f,h]>\epsilon`.
:::

:::corollary "corollary-6.14" (parent := "fabl-chapter-6") (lean := "FABL.isLowDegreeFourierRegular_zero_iff_forall_mean_signRestriction_eq, FABL.isLowDegreeFourierRegular_zero_iff_forall_covariance_booleanJunta_eq_zero, FABL.ProbabilityDensity.isLowDegreeFourierRegular_zero_iff_forall_expectation_booleanJunta_eq_mean") (uses := "proposition-6.12, proposition-6.13, fact-1.21") (tags := "section-6-1, fidelity-exact")
*Corollary 6.14.* For $`f:\{-1,1\}^n\to\mathbb R`, the following are
equivalent:

(1) $`f` is $`(0,k)`-regular.

(2) Every restriction of at most $`k` coordinates leaves $`\mathbb E[f]`
unchanged.

(3) $`\operatorname{Cov}[f,h]=0` for every Boolean-valued $`k`-junta $`h`.

If $`f` is a probability density, condition (3) is equivalent to
$$`
\mathbb E_{\boldsymbol x\sim f}[h(\boldsymbol x)]=\mathbb E[h]
`
for every Boolean-valued $`k`-junta $`h`.
:::

:::definition "definition-6.15" (parent := "fabl-chapter-6") (lean := "FABL.IsCorrelationImmune, FABL.IsResilient") (uses := "definition-6.11, definition-1.11, definition-1.20") (tags := "section-6-1, fidelity-exact")
*Definition 6.15.* A Boolean-valued $`(0,k)`-regular function is
*$`k`th-order correlation immune*. If it is also unbiased, it is
*$`k`-resilient*. A $`(0,k)`-regular probability density, and its associated
distribution, is *$`k`-wise independent*.
:::

:::lemma_ "example-6.16" (parent := "fabl-chapter-6") (lean := "FABL.parityFunction_isResilient, FABL.parityTimes, FABL.fourierCoeff_parityTimes, FABL.parityTimes_isResilient_of_dependsOn_compl, FABL.firstTwoThirds, FABL.lastTwoThirds, FABL.card_firstTwoThirds_symmDiff_lastTwoThirds, FABL.correlationImmuneAndExample, FABL.fourierCoeff_correlationImmuneAndExample, FABL.correlationImmuneAndExample_isCorrelationImmune, FABL.mean_correlationImmuneAndExample, FABL.correlationImmuneAndExample_not_isResilient, FABL.uniformProbability_correlationImmuneAndExample_eq_true") (uses := "definition-6.15, definition-2.2") (tags := "section-6-1, fidelity-exact")
*Example 6.16.* If $`|S|=k+1`, then $`\chi_S` is $`k`-resilient; more
generally, so is $`\chi_Sg` whenever $`g` does not depend on any coordinate
in $`S`. For a correlation-immune function that is not resilient, let
$`h:\{-1,1\}^{3m}\to\{-1,1\}` be
$$`
h=\chi_{\{1,\ldots,2m\}}\wedge\chi_{\{m+1,\ldots,3m\}}.
`
It is True on one quarter of its inputs, but fixing fewer than $`2m` input
bits does not change this bias. Thus $`h` is correlation immune of order
$`2m-1` and is not unbiased.
:::

:::lemma_ "support-exercise-6.2" (parent := "fabl-chapter-6") (lean := "FABL.expect_sq_fourierCoeff_uniformBooleanFunction, FABL.sum_pow_card_sub_one_filter_mem, FABL.pmfExpectation_uniformBooleanFunction_stableInfluence") (uses := "definition-2.52, theorem-2.20") (tags := "section-6-1, support, fidelity-exact")
*Exercise 6.2.* Prove Fact 6.8.
:::

:::lemma_ "support-exercise-6.8" (parent := "fabl-chapter-6") (lean := "FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset, FABL.fourierDegree_toReal_le_of_isKJunta, FABL.fourierOneNorm_toReal_le_two_rpow_half_of_isKJunta, FABL.IsLowDegreeFourierRegular.abs_covariance_le_fourierOneNorm_mul") (uses := "definition-6.11, proposition-1.16, definition-2.4, support-exercise-3.9, parseval") (tags := "section-6-1, support, fidelity-exact")
*Exercise 6.8.* Prove Proposition 6.13.
:::
