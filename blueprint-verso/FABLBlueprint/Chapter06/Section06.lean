/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Exercises and notes" =>

The eight exercises used directly by numbered or named results remain beside
those results: Exercises 6.2 and 6.8 in Section 6.1; Exercises 6.10, 6.14,
and 6.16 in Section 6.2; Exercises 6.30 and 6.31 in Section 6.4; and
Exercise 6.29 in Section 6.5. The other twenty-six exercises are collected
here in book order.

:::lemma_ "support-exercise-6.1" (parent := "fabl-chapter-6") (lean := "FABL.variance_pBiasedRandomFunction_fourierCoeff") (uses := "proposition-6.1, proposition-1.8") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.1.* For the random $`p`-biased function $`f` in
Proposition 6.1, compute
$`\operatorname{Var}[\widehat f(S)]` for every $`S\subseteq[n]`.
:::

:::lemma_ "support-exercise-6.3" (parent := "fabl-chapter-6") (lean := "FABL.inv_two_pow_pred_le_variance_of_fourierDegree_le, FABL.pow_pred_mul_variance_le_totalStableInfluence_of_fourierDegree_le, FABL.totalStableInfluence_eq_sum_of_dependsOn, FABL.exists_stableInfluence_ge_of_isKJunta_of_nonconstant") (uses := "definition-2.4, definition-6.9, fact-2.53") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.3.* Every nonconstant Boolean-valued $`k`-junta $`f` has a
coordinate $`i` satisfying
$$`
\operatorname{Inf}^{(1-\delta)}_i[f]
\ge\frac{(1/2-\delta/2)^{k-1}}{k}.
`
:::

:::lemma_ "support-exercise-6.4" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.IsBiased.convolutionPower") (uses := "definition-6.5, definition-1.24, proposition-1.26, theorem-1.27") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.4.* If
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` is an
$`\epsilon`-biased density, then for every $`d\in\mathbb N_{>0}` its
$`d`-fold convolution $`\varphi^{*d}` is an $`\epsilon^d`-biased density.
:::

:::lemma_ "support-exercise-6.5" (parent := "fabl-chapter-6") (lean := "FABL.sq_fourierCoeff_le_influence_of_mem, FABL.HasSmallInfluences.isFourierRegular_sqrt, FABL.isFourierRegular_innerProductModTwoBoolean, FABL.influence_innerProductModTwoBoolean_eq_half, FABL.exists_isFourierRegular_not_hasSmallInfluences_of_even, FABL.exists_hasSmallStableInfluences_not_isFourierRegular, FABL.fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero, FABL.stableInfluence_leadingCoordinateTimes_eq_stabilityCurve, FABL.stableInfluence_leadingCoordinateTimes_majority_odd_eq_noiseStability, FABL.one_sub_sqrt_le_of_hasSmallStableInfluences_leadingCoordinateTimes_majority_odd, FABL.isBalanced_majority_odd, FABL.IsFourierRegular.leadingCoordinateTimes_of_isBalanced, FABL.isFourierRegular_leadingCoordinateTimes_majority_odd, FABL.rho_pow_card_sub_one_mul_sq_fourierCoeff_le_stableInfluence, FABL.HasSmallStableInfluences.isLowDegreeFourierRegular, FABL.stableInfluence_zero_eq_sq_fourierCoeff_singleton, FABL.hasSmallStableInfluences_one_iff_isLowDegreeFourierRegular_one, FABL.abs_fourierCoeff_le_influence_of_monotone, FABL.IsLowDegreeFourierRegular.isFourierRegular_and_hasSmallInfluences_of_monotone") (uses := "definition-6.2, definition-6.9, definition-6.11, example-6.10, proposition-2.21, support-exercise-5.21") (tags := "section-6-6, support, fidelity-explicit-endpoint-domains")
*Exercise 6.5 (comparison of pseudorandomness notions).*

(a) If $`f:\{-1,1\}^n\to\mathbb R` has $`\epsilon`-small influences, then it
is $`\sqrt\epsilon`-regular.

(b) For every positive even $`n` there is a Boolean-valued
$`2^{-n/2}`-regular function that does not have $`\epsilon`-small influences
for any $`\epsilon<1/2`.

(c) For every $`n>0` there is a Boolean function with
$`((1-\delta)^{n-1},\delta)`-small stable influences that is not
$`\epsilon`-regular for any $`\epsilon<1`.

(d) For odd $`n=2m+1`, let
$`f(x_0,x_1,\ldots,x_n)=x_0\operatorname{Maj}_n(x_1,\ldots,x_n)` and
$`\delta\in(0,1)`,
$$`
\operatorname{Inf}^{(1-\delta)}_0[f]
=\operatorname{Stab}_{1-\delta}[\operatorname{Maj}_n],
`
so $`f` cannot have $`(\epsilon,\delta)`-small stable influences unless
$`\epsilon\ge1-\sqrt\delta`.

(e) The function in (d) is $`1/\sqrt n`-regular.

(f) If $`\delta\in[0,1)` and $`f:\{-1,1\}^n\to\mathbb R` has
$`(\epsilon,\delta)`-small stable influences, then it is
$`(\eta,k)`-regular for
$$`
\eta=\sqrt{\epsilon/(1-\delta)^{k-1}}.
`

(g) For $`\epsilon\ge0`, $`f` has $`(\epsilon,1)`-small stable influences if and only if it is
$`(\sqrt\epsilon,1)`-regular.

(h) If a monotone Boolean function is $`(\epsilon,1)`-regular, then it is
$`\epsilon`-regular and has $`\epsilon`-small influences.

The positive-dimension clauses in (b) and (c) make explicit the book's
nontrivial-cube convention: in dimension zero there is no coordinate
influence and the literal separation in (b) is false.  The majority
construction is stated at its odd arity, and the endpoint assumptions in
(f) and (g) make the square-root and denominator expressions well-defined.
:::

:::lemma_ "support-exercise-6.6" (parent := "fabl-chapter-6") (lean := "FABL.mean_signRestriction_eq_restrictionFourierCoeff_empty, FABL.variance_mean_signRestriction_eq_sum_sq_fixed, FABL.exists_signRestriction_mean_change_gt_via_variance") (uses := "corollary-3.22, proposition-6.12, parseval") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.6.* Let $`f:\{-1,1\}^n\to\mathbb R` and let
$`(J,\overline J)` partition $`[n]`.

(a) For uniformly random $`z\in\{-1,1\}^{\overline J}`, express
$$`
\operatorname{Var}_z\!\left[\mathbb E[f_{J\mid z}]\right]
`
in terms of the Fourier coefficients of $`f`.

(b) Use this identity and the probabilistic method to give another proof of
Proposition 6.12(2).
:::

:::lemma_ "support-exercise-6.7" (parent := "fabl-chapter-6") (lean := "FABL.innerProductModTwoOneSet, FABL.innerProductModTwoSupportDensity, FABL.abs_vectorFourierCoeff_innerProductModTwoSupportDensity, FABL.innerProductModTwoSupportDensity_isBiased_iff") (uses := "definition-6.5, support-exercise-1.1g-inner-product-mod-two, definition-1.22") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.7.* Let
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` be the density of the uniform
distribution on the support of
$`\operatorname{IP}_n:\mathbb F_2^n\to\{0,1\}`. Show that $`\varphi` is
$`\epsilon`-biased for
$$`
\epsilon=\frac{2^{-n/2}}{1-2^{-n/2}},
`
and is not $`\epsilon'`-biased for any smaller $`\epsilon'`.
:::

:::lemma_ "support-exercise-6.9" (parent := "fabl-chapter-6") (lean := "FABL.f₂EqualityFunction, FABL.forall_coordinate_eq_iff_eq_zero_or_eq_one, FABL.f₂EqualityFunction_eq_pointIndicators") (uses := "proposition-6.18, equation-6.3") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.9.* Compute the $`\mathbb F_2`-polynomial representation of the
equality function
$$`
\operatorname{Eq}_n:\{0,1\}^n\to\{0,1\},
\qquad
\operatorname{Eq}_n(x)=1
\ \Longleftrightarrow\
x_1=x_2=\cdots=x_n.
`
:::

:::lemma_ "support-exercise-6.11" (parent := "fabl-chapter-6") (lean := "FABL.two_pow_sub_le_hammingNorm_of_functionAlgebraicDegree_le, FABL.uniformProbability_ne_zero_eq_hammingNorm_ratio, FABL.inv_two_pow_le_uniformProbability_ne_zero_of_functionAlgebraicDegree_le") (uses := "definition-6.20, proposition-6.18, lemma-3.5") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.11.* Let $`f:\mathbb F_2^n\to\mathbb F_2` be nonzero and suppose
$`\deg_{\mathbb F_2}(f)\le k`. Then
$$`
\Pr_{\boldsymbol x\sim\mathbb F_2^n}[f(\boldsymbol x)\ne0]\ge2^{-k}.
`
:::

:::lemma_ "support-exercise-6.12" (parent := "fabl-chapter-6") (lean := "FABL.two_pow_functionAlgebraicDegree_le_spectralSparsity_booleanRealEmbedding, FABL.functionAlgebraicDegree_le_of_isVectorFourierGranular_booleanRealEmbedding") (uses := "definition-6.20, corollary-6.22, definition-3.9, definition-3.10") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.12.* Let $`f:\{-1,1\}^n\to\{0,1\}`.

(a) Prove
$$`
\deg_{\mathbb F_2}(f)
\le\log_2\!\bigl(\operatorname{sparsity}(\widehat f)\bigr).
`

(b) If $`\widehat f` is $`2^{-k}`-granular, prove
$`\deg_{\mathbb F_2}(f)\le k`.
:::

:::lemma_ "support-exercise-6.13" (parent := "fabl-chapter-6") (lean := "FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding, FABL.restrictionFourierCoeff_realSignEncodedFunction_eq_neg_two_mul, FABL.functionAlgebraicDegree_le_half_of_isBent") (uses := "definition-6.20, definition-6.26, support-exercise-6.12") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.13.* If
$`f:\{-1,1\}^n\to\{-1,1\}` is bent and $`n>2`, then
$$`
\deg_{\mathbb F_2}(f)\le n/2.
`
The estimate $`\deg_{\mathbb F_2}(f)\le n/2+1` already follows from
Exercise 6.12(b).
:::

:::lemma_ "support-exercise-6.15" (parent := "fabl-chapter-6") (lean := "FABL.booleanFunctionF₂Decoding, FABL.booleanFunctionF₂Encoding_booleanFunctionF₂Decoding, FABL.booleanFunctionF₂Decoding_toReal, FABL.booleanFunctionF₂Encoding_parityTimes, FABL.booleanFunctionF₂Decoding_anfMonomial_dependsOn, FABL.resilientSharpnessPrefix, FABL.resilientSharpnessTail, FABL.card_resilientSharpnessPrefix, FABL.card_resilientSharpnessTail, FABL.resilientDegreeSharpnessFunction, FABL.resilientDegreeSharpnessFunction_isResilient, FABL.booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction, FABL.functionAlgebraicDegree_resilientDegreeSharpnessFunction, FABL.exists_isResilient_functionAlgebraicDegree_eq_sub_sub_one, FABL.constantPairF₂Indicator, FABL.constantPairBooleanFunction, FABL.realSignEncodedFunction_constantPairF₂Indicator, FABL.constantPairBooleanFunction_toReal, FABL.constantPairBooleanFunction_isCorrelationImmune, FABL.functionAlgebraicDegree_constantPairBooleanFunction, FABL.exists_firstOrderCorrelationImmune_functionAlgebraicDegree_eq_sub_one, FABL.exists_not_isBalanced_isCorrelationImmune_two_mul_div_three_sub_one") (uses := "siegenthaler-theorem, theorem-6.25, definition-6.15, definition-6.20") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.15 (sharpness).*

(a) For every $`n` and $`k<n-1`, construct
$`f:\{0,1\}^n\to\{0,1\}` that is $`k`-resilient and satisfies
$`\deg_{\mathbb F_2}(f)=n-k-1`.

(b) For every $`n\ge3`, construct
$`f:\{0,1\}^n\to\{0,1\}` that is first-order correlation immune and satisfies
$`\deg_{\mathbb F_2}(f)=n-1`.

(c) For every $`n` divisible by $`3`, construct a biased function
$`f:\{0,1\}^n\to\{0,1\}` that is correlation immune of order $`2n/3-1`.
:::

:::lemma_ "support-exercise-6.17" (parent := "fabl-chapter-6") (lean := "FABL.vectorFourierCoeff_vectorFourierCoeff, FABL.bentDual, FABL.IsBent.isSignValued_bentDual, FABL.vectorFourierCoeff_bentDual, FABL.IsSignValued.isBent_bentDual, FABL.IsBent.bentDual") (uses := "definition-6.26, parseval") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.17.* Bent functions come in pairs: if
$`f:\mathbb F_2^n\to\{-1,1\}` is bent, then the function
$$`
\gamma\longmapsto 2^{n/2}\widehat f(\gamma)
`
on the dual group $`\widehat{\mathbb F_2^n}` is also bent.
:::

:::lemma_ "support-exercise-6.18" (parent := "fabl-chapter-6") (lean := "FABL.maioranaMcFarlandPermutation, FABL.maioranaMcFarlandPermutation_joinF₂CubeBlocks, FABL.vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks, FABL.isSignValued_maioranaMcFarlandPermutation, FABL.isBent_maioranaMcFarlandPermutation") (uses := "definition-6.26, proposition-6.29") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.18 (Maiorana--McFarland family).* If
$`\pi:\mathbb F_2^n\to\mathbb F_2^n` is any permutation and
$`g:\mathbb F_2^n\to\{-1,1\}` is arbitrary, then
$$`
f(x,y)=\operatorname{IP}_{2n}(x,\pi(y))g(y)
`
is bent.
:::

:::lemma_ "support-exercise-6.19" (parent := "fabl-chapter-6") (uses := "definition-6.20, definition-6.26, proposition-6.28, example-6.19") (tags := "section-6-6, support, external-dependency, statement-only")
*Exercise 6.19.* Dickson's Theorem says that every polynomial
$`p:\mathbb F_2^n\to\mathbb F_2` of degree at most $`2` can be written
$$`
p(x)=\ell_0(x)+\sum_{j=1}^k\ell_j(x)\ell'_j(x),
`
where $`\ell_0` is affine and
$`\ell_1,\ell'_1,\ldots,\ell_k,\ell'_k` are linearly independent linear
functions; the integer $`k`, depending only on $`p`, is its rank.
Assuming this quoted external theorem, let $`n` be even. For
$$`
g(x)=(-1)^{p(x)},
`
prove that $`g` is bent if and only if $`k=n/2`, and that this is equivalent
to $`g` arising from the inner-product-mod-$`2` function by the
transformations of Proposition 6.28.

Dickson's 1901 classification theorem is not proved in the book, so this
exercise remains statement-only and supplies no assumption to the production
library.
:::

:::lemma_ "support-exercise-6.20" (parent := "fabl-chapter-6") (lean := "FABL.exists_completeQuadraticBit_affine_independent_decomposition") (uses := "example-6.19, proposition-6.18") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.20.* Without using Dickson's Theorem, prove that the complete
quadratic polynomial
$$`
x\longmapsto\sum_{1\le i<j\le n}x_ix_j
`
can be expressed as
$$`
\ell_0(x)+\sum_{j=1}^{\lfloor n/2\rfloor}\ell_j(x)\ell'_j(x),
`
where $`\ell_0` is affine and the displayed linear forms are linearly
independent. Use induction on $`n`, with different steps according to the
parity of $`n`.
:::

:::lemma_ "support-exercise-6.21" (parent := "fabl-chapter-6") (lean := "FABL.signCoordinateIntegerSum, FABL.modThreeBoolean, FABL.modThree, FABL.modThree_apply, FABL.modThreeResidue, FABL.modThreeResidue_eq_zero_iff, FABL.modThree_eq_residueIndicator, FABL.modThree_fourier_expansion, FABL.modThreeFourierCoefficient, FABL.fourierCoeff_modThree, FABL.fourierCoeff_modThree_of_nonempty, FABL.abs_fourierCoeff_modThree_le, FABL.modThree_isFourierRegular") (uses := "definition-6.2, theorem-1.1") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.21.* Define
$`\operatorname{mod}_3:\{-1,1\}^n\to\{0,1\}` by
$`\operatorname{mod}_3(x)=1` if and only if
$`\sum_{j=1}^n x_j` is divisible by $`3`. Prove the Fourier expansion
$$`
\operatorname{mod}_3(x)
=\frac13+\frac23\left(-\frac12\right)^n
 \sum_{\substack{S\subseteq[n]\\ |S|\ {\rm even}}}
 (-1)^{(|S|\bmod4)/2}(\sqrt3)^{|S|}x^S,
`
and conclude that $`\operatorname{mod}_3` is
$$`
\frac23\left(\frac{\sqrt3}{2}\right)^n
`
-regular.
:::

:::lemma_ "support-exercise-6.22" (parent := "fabl-chapter-6") (lean := "FABL.executableBinaryDotProductState, FABL.executableBinaryDotProduct, FABL.executableBinaryDotProductState_eq_sum, FABL.executableBinaryDotProduct_eq_f₂DotProduct, FABL.executableSmallBiasOutputBit, FABL.executableSmallBiasOutputBit_eq_generator, FABL.executableBinaryDotProductWork, FABL.executableBinaryDotProductWork_eq, FABL.executableSmallBiasOutputBitWork, FABL.executableSmallBiasOutputBitWork_eq, FABL.executableSmallBiasOutputBitWork_le, FABL.executableSmallBiasOutputBit_spec, FABL.executableSmallBiasOutputBitWork_isBigO, FABL.executableSmallBiasOutputBitWork_fixedCoordinate_isBigO") (uses := "theorem-6.30, support-binary-extension-field-model") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.22.* In the construction of Theorem 6.30, once
$`r,s\in\mathbb F_{2^\ell}` are given, every fixed output bit
$$`
y_i=\left\langle\operatorname{enc}(r^i),
                        \operatorname{enc}(s)\right\rangle
`
can be computed deterministically in $`\operatorname{poly}(\ell)` time.
:::

:::lemma_ "support-exercise-6.23" (parent := "fabl-chapter-6") (lean := "FABL.fieldPairingCoefficient, FABL.fieldPairingGenerator, FABL.f₂DotProduct_fieldPairingGenerator, FABL.vectorWalshCharacter_fieldPairingGenerator, FABL.expect_fieldPairingGenerator, FABL.fieldPairingGenerator_characterExpectation_eq_rootProbability, FABL.fieldPairingDensity, FABL.vectorFourierCoeff_fieldPairingDensity_eq_rootProbability, FABL.fieldPairingDensity_isBiased_of_polynomial, FABL.dyadicFieldRatio_eq_invPow, FABL.shiftedSmallBiasFieldFamily, FABL.shiftedSmallBiasPolynomial, FABL.shiftedSmallBiasPolynomial_eval, FABL.shiftedSmallBiasPolynomial_ne_zero, FABL.shiftedSmallBiasPolynomial_natDegree_le, FABL.shiftedSmallBiasGenerator, FABL.shiftedSmallBiasGenerator_characterExpectation_eq_rootProbability, FABL.shiftedSmallBiasGeneratorDensity, FABL.shiftedSmallBiasGeneratorDensity_isBiased, FABL.shiftedSmallBias_dyadicParameter, FABL.shiftedSmallBiasGeneratorDensity_isBiased_dyadic, FABL.binaryExtensionBasisVector, FABL.basisExpandedGroupedCoefficient, FABL.basisExpandedGroupedCoefficient_eq_sum, FABL.exists_basisExpandedGroupedCoefficient_ne_zero, FABL.basisExpandedSmallBiasFieldFamily, FABL.basisExpandedSmallBiasPolynomial, FABL.basisExpandedSmallBiasPolynomial_eval, FABL.basisExpandedSmallBiasPolynomial_ne_zero, FABL.basisExpandedSmallBiasPolynomial_natDegree_le, FABL.basisExpandedSmallBiasGenerator, FABL.basisExpandedSmallBiasGenerator_characterExpectation_eq_rootProbability, FABL.basisExpandedSmallBiasGeneratorDensity, FABL.basisExpandedSmallBiasGeneratorDensity_isBiased, FABL.basisExpandedSmallBias_dyadicParameter, FABL.basisExpandedSmallBiasGeneratorDensity_isBiased_dyadic") (uses := "theorem-6.30, equation-6.5, support-binary-extension-field-model, support-finite-field-root-bound") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.23.*

(a) Modify Theorem 6.30 so that $`p_\gamma` has degree at most $`n-1`,
and obtain a $`(2^{-t}-2^{-\ell})`-biased density.

(b) Let $`v_1,\ldots,v_\ell` be a basis of
$`\mathbb F_{2^\ell}` over $`\mathbb F_2`. Modify the construction to
produce a density on $`\mathbb F_2^{n\ell}` by setting
$$`
y_{ij}
=\left\langle\operatorname{enc}(v_jr^i),
              \operatorname{enc}(s)\right\rangle,
\qquad i\in[n],\ j\in[\ell].
`
Prove that this density remains $`2^{-t}`-biased.
:::

:::lemma_ "support-exercise-6.24" (parent := "fabl-chapter-6") (lean := "FABL.randomSmallBiasConstant, FABL.randomSmallBiasSampleCount, FABL.randomSmallBiasSampleCount_pos, FABL.randomSmallBiasMultiset, FABL.IsSmallBiasedSample, FABL.isSmallBiasedSample_zero, FABL.randomSmallBiasDensity, FABL.vectorFourierCoeff_randomSmallBiasDensity, FABL.randomSmallBiasDensity_isBiased_iff, FABL.randomSmallBiasFrequencyBadSet, FABL.randomSmallBiasFailureSet, FABL.measure_randomSmallBiasFrequencyBadSet_le, FABL.measure_randomSmallBiasSample_not_isBiased_le, FABL.measure_randomSmallBiasDensity_not_isBiased_le") (uses := "definition-6.5, proposition-6.1") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.24.* Fix $`\epsilon\in(0,1)` and $`n\in\mathbb N`. Form a
random multiset $`A\subseteq\mathbb F_2^n` by drawing
$$`
\left\lceil\frac{Cn}{\epsilon^2}\right\rceil
`
elements independently and uniformly. If $`C` is a sufficiently large
universal constant, prove that $`A` is $`\epsilon`-biased except with
probability at most $`2^{-n}`.
:::

:::lemma_ "support-exercise-6.25" (parent := "fabl-chapter-6") (lean := "FABL.matrixProductVerificationPredicate, FABL.matrixProductVerificationPredicate_decidable, FABL.matrixProductVerificationDecision, FABL.matrixProductDifference, FABL.matrixProductDifferenceRow, FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero, FABL.matrixProductVerificationDecision_eq_true_iff, FABL.matrixProductVerificationPredicate_of_eq, FABL.exists_matrixProductDifferenceRow_ne_zero, FABL.f₂DotProduct_matrixProductDifferenceRow, FABL.matrixProductVerificationPredicate_imp_row_dot_eq_zero, FABL.f₂ZeroIndicator_eq, FABL.matrixProductVerificationAcceptanceProbability, FABL.matrixProductRowZeroProbability_eq, FABL.ProbabilityDensity.IsBiased.rowZeroProbability_le, FABL.matrixProductVerificationAcceptanceProbability_eq_one_of_eq, FABL.matrixProductVerificationAcceptanceProbability_le, FABL.matrixProductVerificationLocalWork, FABL.matrixProductVerificationLocalWork_le, FABL.matrixProductVerificationLocalWork_isBigO, FABL.matrixProductVerificationCost, FABL.matrixProductVerificationCost_eq, FABL.seededMatrixProductVerificationResult, FABL.seededMatrixProductVerificationResult_eq_true_iff, FABL.seededMatrixProductVerificationProgram, FABL.runWithCost_seededMatrixProductVerificationAfterSeed, FABL.runWithCost_seededMatrixProductVerificationProgram, FABL.seededMatrixProductVerificationAcceptanceProbability, FABL.seededMatrixProductVerificationAcceptanceProbability_eq, FABL.seededMatrixProductVerificationAcceptanceProbability_eq_one_of_eq, FABL.seededMatrixProductVerificationAcceptanceProbability_le, FABL.matrixProductVerificationProgram, FABL.matrixProductVerificationRandomBits, FABL.runWithCost_matrixProductVerificationProgram, FABL.uniformMatrixProductVerificationAcceptanceProbability, FABL.seededMatrixProductVerificationAcceptanceProbability_boolVector_eq, FABL.uniformPushforward_id_isBiased_zero, FABL.uniformMatrixProductVerificationAcceptanceProbability_eq_one_of_eq, FABL.uniformMatrixProductVerificationAcceptanceProbability_le_half, FABL.matrixProductVerificationAlgorithm_spec, FABL.boolSmallBiasSeedPairEquiv, FABL.matrixProductSmallBiasSeed, FABL.matrixProductSmallBiasSeed_eq_generator, FABL.matrixProductSmallBiasSeed_apply_spec, FABL.matrixProductSmallBiasSeed_isBiased, FABL.matrixProductSmallBiasVerification_complete, FABL.matrixProductSmallBiasVerification_sound, FABL.matrixProductOneThirdSmallBiasInput, FABL.matrixProductOneThirdSmallBiasInput_epsilon, FABL.matrixProductOneThirdSmallBiasInput_scale, FABL.matrixProductSmallBiasDegree, FABL.matrixProductOneThirdSmallBiasInput_fieldDegree, FABL.matrixProductSmallBiasRandomBits, FABL.matrixProductSmallBiasLogScale, FABL.matrixProductSmallBiasDegree_le, FABL.matrixProductSmallBiasRandomBits_le, FABL.matrixProductSmallBiasRandomBits_isBigO, FABL.matrixProductOneThirdSmallBiasVerificationProgram, FABL.matrixProductOneThirdSmallBiasRandomBits_eq, FABL.matrixProductOneThirdSmallBiasVerificationAlgorithm_spec") (uses := "theorem-6.30, support-exercise-6.22, fact-1.7") (tags := "section-6-6, support, fidelity-exact-random-bit-and-runtime-model")
*Exercise 6.25 (verifying matrix multiplication).* Given
$`A,B,C'\in\mathbb F_2^{n\times n}`, test whether $`C'=AB`.

(a) Give an $`O(n^2)`-time algorithm using exactly $`n` random bits which
accepts with probability $`1` if $`C'=AB` and with probability at most
$`1/2` if $`C'\ne AB`. The test compares $`C'x` and $`ABx` for uniform
$`x\in\mathbb F_2^n`.

(b) Replace the uniform $`x` by the output of the construction in
Theorem 6.30. Reduce the random-bit cost to $`O(\log n)`, retain
$`O(n^2)` running time, preserve perfect completeness, and make the soundness
error at most $`2/3`.
:::

:::lemma_ "support-exercise-6.26" (parent := "fabl-chapter-6") (lean := "FABL.nonzeroBinaryVectorEquiv, FABL.pairwiseIndependentColumn, FABL.pairwiseIndependentColumn_ne_zero, FABL.pairwiseIndependentColumn_injective, FABL.pairwiseIndependentMatrix, FABL.pairwiseIndependentMatrix_column, FABL.pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo, FABL.exists_pairwiseIndependentMatrix, FABL.pairwiseIndependentRowCount, FABL.n_le_two_pow_pairwiseIndependentRowCount_sub_one, FABL.two_pow_pairwiseIndependentRowCount_le_four_mul, FABL.exists_pairwiseIndependentSubspace_card_le") (uses := "theorem-6.32, corollary-6.33") (tags := "section-6-6, support, fidelity-exact-capacity-bound-explicit")
*Exercise 6.26.* Specialize Theorem 6.32 and Corollary 6.33 to $`k=2`,
simplify their construction and analysis, and improve
$`m=(k-1)\ell+1` to $`m=\ell`.

Concretely, the $`\ell`-row construction takes $`n\le2^\ell-1`
distinct nonzero binary columns; this capacity bound is forced by pairwise
independence. For arbitrary $`n\ge1`, choosing
$`\ell=\max\{1,\lceil\log_2(n+1)\rceil\}` gives a pairwise-independent
row-space density supported on at most $`4n` points, matching the
$`k=2` specialization of Corollary 6.33 while using one fewer row.
:::

:::lemma_ "support-exercise-6.27" (parent := "fabl-chapter-6") (lean := "FABL.ReducedVandermondeBinaryRow, FABL.reducedVandermondeBinaryRowEquiv, FABL.reducedVandermondeBinaryMatrixOfPoints, FABL.reducedVandermondeBinaryMatrixOfPoints_constantRow, FABL.reducedVandermondeBinaryMatrixOfPoints_oddPowerRow, FABL.extensionField_moments_eq_zero_of_oddMoments_eq_zero, FABL.reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo, FABL.exists_kWiseIndependentSubspace_card_le_two_mul_two_n_pow_half") (uses := "theorem-6.32, corollary-6.33") (tags := "section-6-6, support, fidelity-exact")
*Exercise 6.27.* In the matrix
$`H'\in\mathbb F_{2^\ell}^{k\times n}` from Theorem 6.32, delete every row
corresponding to an even nonzero power of the elements $`\alpha_j`. Prove
that every nonempty sum of at most $`k` columns remains nonzero, using
$$`
\left(\sum_j\beta_j\right)^2=\sum_j\beta_j^2
\qquad(\beta_j\in\mathbb F_{2^\ell}).
`
Deduce that Corollary 6.33 can be strengthened to
$$`
|A|\le 2(2n)^{\lfloor k/2\rfloor}.
`
:::

:::lemma_ "support-exercise-6.28" (parent := "fabl-chapter-6") (lean := "FABL.signMultisetDensity, FABL.IsKWiseIndependentMultiset, FABL.fourierCoeff_signMultisetDensity, FABL.IsKWiseIndependentMultiset.expect_monomial_mul, FABL.normalizedRestrictedWalshVector, FABL.normalizedRestrictedWalshVector_orthonormal, FABL.card_frequencyFamily_le_card_of_isKWiseIndependentMultiset, FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily, FABL.exists_even_kWiseFrequencyFamily, FABL.oddKWiseFrequencyExtension, FABL.mem_oddKWiseFrequencyExtension_card, FABL.card_oddKWiseFrequencyExtension, FABL.oddKWiseFrequencyFamily, FABL.disjoint_lowDegreeFourierFamily_oddKWiseFrequencyExtension, FABL.card_oddKWiseFrequencyFamily, FABL.card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily, FABL.exists_odd_kWiseFrequencyFamily, FABL.even_kWiseIndependentMultiset_card_lowerBound, FABL.odd_kWiseIndependentMultiset_card_lowerBound, FABL.choose_floor_half_le_card_of_isKWiseIndependentMultiset, FABL.kWiseIndependentMultiset_card_isOmega") (uses := "definition-6.15, theorem-1.5") (tags := "section-6-6, support, fidelity-exact-positive-dimension-explicit")
*Exercise 6.28 (lower bound for $`k`-wise independent multisets).* Let
$`A\subseteq\{-1,1\}^n` be a multiset whose density is $`k`-wise
independent.

(a) Suppose $`\mathcal F\subseteq2^{[n]}` satisfies
$`|S\cup T|\le k` for all $`S,T\in\mathcal F`. For $`S\in\mathcal F`, let
$`\chi_S^A\in\mathbb R^{|A|}` be the vector whose entry at
$`a\in A` is $`\prod_{i\in S}a_i`. Prove that
$$`
\left\{|A|^{-1/2}\chi_S^A:S\in\mathcal F\right\}
`
is orthonormal, and hence $`|A|\ge|\mathcal F|`.

(b) Construct such a family satisfying
$$`
|\mathcal F|\ge
\begin{cases}
\displaystyle\sum_{j=0}^{k/2}\binom nj,&k\text{ even},\\[1.2ex]
\displaystyle\sum_{j=0}^{(k-1)/2}\binom nj
 +\binom{n-1}{(k-1)/2},&k\text{ odd}.
\end{cases}
`
Conclude, for constant $`k`, that
$`|A|\ge\Omega(n^{\lfloor k/2\rfloor})`.
For the displayed odd-$`k` refinement the formal theorem records
$`n\ge1`, which is necessary to choose the distinguished coordinate and
excludes the degenerate $`n=0,k=1` case where that printed formula is false.
:::

:::lemma_ "support-exercise-6.32" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_sub, FABL.ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le_refined, FABL.exists_affine_correlation_ge_sqrt_div_sqrt_of_derandomizedBLRAcceptanceProbability_eq") (uses := "lemma-6.38, corollary-6.39, theorem-6.44") (tags := "section-6-6, support, fidelity-exact-with-real-sqrt-and-zero-denominator-conventions")
*Exercise 6.32.*

(a) Improve Lemma 6.38 to
$$`
\left|
\mathbb E_{x\sim\varphi}[f(x)]-\mathbb E[f]
\right|
\le
\bigl(\lVert\widehat f\rVert_1-|\widehat f(\varnothing)|\bigr)\epsilon,
`
and improve Corollary 6.39 to
$$`
\left|
\mathbb E_{x\sim\varphi}[f(x)^2]-\mathbb E[f^2]
\right|
\le
\bigl(\lVert\widehat f\rVert_1^2-\lVert f\rVert_2^2\bigr)\epsilon.
`

(b) Improve the correlation lower bound in Theorem 6.44 to
$$`
\frac{\sqrt{\theta^2-\epsilon}}{\sqrt{1-\epsilon}}.
`
For the formal real-valued statement, Mathlib's square root and field
division make the displayed ratio `0` when $`\epsilon\ge1`; the
nontrivial book regime is $`0\le\epsilon<1`.
:::

:::lemma_ "support-exercise-6.33" (parent := "fabl-chapter-6") (lean := "FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_eq_sum_sq_mul_correlation, FABL.probabilityDensityCorrelation_add_le_one_add_bias, FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq, FABL.exists_abs_vectorFourierCoeff_ge_sqrt_div_sqrt_of_near_perfect_derandomizedBLR") (uses := "derandomized-blr-test, support-exercise-6.32, theorem-6.44") (tags := "section-6-6, support, fidelity-explicit-near-perfect-threshold")
*Exercise 6.33.* Let $`0\le\epsilon<1`. Suppose $`f` passes the
Derandomized BLR Test with probability $`1-\delta` in the explicit
near-perfect regime
$$`
\frac{1+\epsilon}{2}\le(1-2\delta)^2.
`
Then there is
$`\gamma^\ast\in\widehat{\mathbb F_2^n}` such that
$$`
|\widehat f(\gamma^\ast)|
\ge
\frac{\sqrt{1-2\delta-\epsilon}}{\sqrt{1-\epsilon}}.
`
This improves the near-perfect-acceptance distance bound by a factor of
roughly $`2`.

The book qualifies this exercise only by saying that the acceptance
probability is “near $`1`”.  The displayed threshold makes that regime
quantitative: it ensures that one Fourier coefficient carries at least
half of the spectral square mass, where the unique-decoding argument
applies.  Without some such near-perfect hypothesis, the asserted bound
is false even for a uniform test in dimension $`4`.
:::

:::lemma_ "support-exercise-6.34" (parent := "fabl-chapter-6") (lean := "FABL.GowersFamily, FABL.gowersCubePoint, FABL.gowersInner, FABL.gowersDiagonalInner, FABL.gowersNorm, FABL.gowersBit, FABL.gowersPair, FABL.gowersCubePoint_insertNth, FABL.prod_f₂Cube_succ, FABL.card_f₂Cube, FABL.gowersHalfProductAt, FABL.gowersHalfExpectationAt, FABL.gowersHalfExpectation, FABL.gowersInner_split_at, FABL.gowersInner_succ, FABL.gowersDuplicateAt, FABL.gowersLastDuplicate, FABL.gowersLastDuplicate_apply, FABL.gowersInner_duplicateAt, FABL.gowersInner_duplicateAt_nonneg, FABL.gowersDiagonalInner_nonneg, FABL.gowersNorm_nonneg, FABL.gowersNorm_pow, FABL.gowers_cauchy_schwarz_at, FABL.gowers_cauchy_schwarz_last, FABL.gowersLiftFamilyAlong, FABL.gowersDuplicateAt_liftFamilyAlong, FABL.gowersCSBound, FABL.gowersInner_liftFamilyAlong_le_csBound, FABL.gowersCSBound_eq_prod_rpow, FABL.gowersCSBound_eq_prod_norm, FABL.gowers_cauchy_schwarz, FABL.gowersInner_one_eq, FABL.gowersNorm_one_sq, FABL.gowersInner_two_eq_fourier, FABL.gowersNorm_two_pow_four_eq, FABL.gowersNorm_one, FABL.gowersMonotonicityFamily, FABL.gowersNorm_mono, FABL.gowersChoiceFamily, FABL.gowersDiagonalInner_add_expansion, FABL.gowersNorm_add_le, FABL.gowersDiagonalInner_smul, FABL.gowersNorm_smul, FABL.gowersSeminorm, FABL.gowersNorm_two_le, FABL.eq_zero_of_gowersNorm_eq_zero") (uses := "proposition-6.7, theorem-1.1, parseval, plancherel") (tags := "section-6-6, support, fidelity-corrected-notation")
*Exercise 6.34 (Gowers inner products and norms).* Fix
$`k\in\mathbb N_{>0}`. Let
$`(f_s)_{s\in\{0,1\}^k}` be a family of functions
$`f_s:\mathbb F_2^n\to\mathbb R`. Define the $`k`th Gowers inner product by
$$`
\left\langle(f_s)_s\right\rangle_{U^k}
=
\mathbb E_{x,y_1,\ldots,y_k}
\left[
\prod_{s\in\{0,1\}^k}
f_s\!\left(x+\sum_{i:s_i=1}y_i\right)
\right],
`
where $`x,y_1,\ldots,y_k` are independent and uniform on
$`\mathbb F_2^n`. Define
$$`
\lVert f\rVert_{U^k}
=
\left\langle(f,f,\ldots,f)\right\rangle_{U^k}^{\,1/2^k}.
`

(a) Prove
$$`
\langle f_0,f_1\rangle_{U^1}
=\mathbb E[f_0]\mathbb E[f_1],
\qquad
\lVert f\rVert_{U^1}^2=\mathbb E[f]^2.
`

(b) Prove
$$`
\langle f_{00},f_{10},f_{01},f_{11}\rangle_{U^2}
=
\sum_{\gamma\in\widehat{\mathbb F_2^n}}
\widehat f_{00}(\gamma)
\widehat f_{10}(\gamma)
\widehat f_{01}(\gamma)
\widehat f_{11}(\gamma),
`
and consequently
$$`
\lVert f\rVert_{U^2}^4
=\lVert\widehat f\rVert_4^4.
`

(c) If $`x'` is independent of
$`x,y_1,\ldots,y_{k-1}` and uniform on $`\mathbb F_2^n`, prove the recursive
identity
$$`
\begin{aligned}
\left\langle(f_s)_s\right\rangle_{U^k}
=\mathbb E_{y_1,\ldots,y_{k-1}}
\bigg[
&\mathbb E_x
\prod_{s:s_k=0}
f_s\!\left(x+\sum_{\substack{i<k\\s_i=1}}y_i\right)\\
\cdot{}&
\mathbb E_{x'}
\prod_{s:s_k=1}
f_s\!\left(x'+\sum_{\substack{i<k\\s_i=1}}y_i\right)
\bigg].
\end{aligned}
\tag{6.9}
`
The restriction $`i<k` in the two inner sums makes explicit the bound
variables implicit in the book's displayed notation.

(d) Deduce that
$`\langle(f,f,\ldots,f)\rangle_{U^k}\ge0`.

(e) For $`b\in\{0,1\}` and $`s\in\{0,1\}^k`, put
$`f_s^{(b)}=f_{(s_1,\ldots,s_{k-1},b)}`. Using (6.9) and
Cauchy--Schwarz, prove
$$`
\left\langle(f_s)_s\right\rangle_{U^k}
\le
\sqrt{\left\langle(f_s^{(0)})_s\right\rangle_{U^k}}\,
\sqrt{\left\langle(f_s^{(1)})_s\right\rangle_{U^k}}.
`

(f) Iterating part (e), prove the Gowers--Cauchy--Schwarz inequality
$$`
\left\langle(f_s)_s\right\rangle_{U^k}
\le\prod_{s\in\{0,1\}^k}\lVert f_s\rVert_{U^k}.
\tag{6.10}
`

(g) For every $`f:\mathbb F_2^n\to\mathbb R`, prove
$$`
\lVert f\rVert_{U^k}\le\lVert f\rVert_{U^{k+1}}.
`

(h) Prove the triangle inequality
$$`
\lVert f_0+f_1\rVert_{U^k}
\le\lVert f_0\rVert_{U^k}+\lVert f_1\rVert_{U^k},
`
and hence prove that $`\lVert\cdot\rVert_{U^k}` is a seminorm. One may first
expand
$$`
\lVert f_0+f_1\rVert_{U^k}^{2^k}
=
\sum_{S\subseteq\{0,1\}^k}
\left\langle
\bigl(f_{\mathbf1[s\in S]}\bigr)_{s\in\{0,1\}^k}
\right\rangle_{U^k}
`
and then apply (6.10).

(i) For every $`k\ge2`, prove that this seminorm is a norm:
$$`
\lVert f\rVert_{U^k}=0\quad\Longrightarrow\quad f=0.
`
:::
