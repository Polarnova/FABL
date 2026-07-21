/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06.Constructions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Constructions of various pseudorandom functions" =>

:::definition "definition-6.26" (parent := "fabl-chapter-6") (lean := "FABL.IsSignValued, FABL.IsBent") (uses := "definition-1.17") (tags := "section-6-3, fidelity-exact")
*Definition 6.26.* Let $`n` be even. A function
$`f:\mathbb F_2^n\to\{-1,1\}` is *bent* if
$$`
|\widehat f(\gamma)|=2^{-n/2}
\qquad\text{for every }\gamma\in\widehat{\mathbb F_2^n}.
`
:::

:::lemma_ "support-bent-extremality" (parent := "fabl-chapter-6") (lean := "FABL.sum_sq_vectorFourierCoeff_eq_one, FABL.exists_inv_card_le_sq_vectorFourierCoeff, FABL.exists_bent_extremal_coefficient, FABL.affineSignFunction, FABL.relativeHammingDist_affineSignFunction, FABL.distanceToAffineSigns, FABL.distanceToAffineSigns_eq, FABL.distanceToAffineSigns_le_bentBound, FABL.isBent_iff_distanceToAffineSigns_eq") (uses := "definition-6.26, definition-1.29, definition-1.28, parseval") (tags := "section-6-3, support, fidelity-exact")
*Extremality of bent functions.* For every
$`f:\mathbb F_2^n\to\{-1,1\}`, Parseval's Theorem implies
$$`
\max_{\gamma}|\widehat f(\gamma)|\ge 2^{-n/2}.
`
Moreover,
$$`
\min_{\substack{\gamma\in\widehat{\mathbb F_2^n}\\ \sigma\in\{-1,1\}}}
\operatorname{dist}(f,\sigma\chi_\gamma)
=\frac12-\frac12\max_\gamma|\widehat f(\gamma)|.
`
Consequently, bent functions are exactly the Boolean functions that attain
the largest possible distance
$`\frac12-2^{-n/2-1}` from the class of affine sign functions.
:::

:::lemma_ "example-canonical-bent-functions" (parent := "fabl-chapter-6") (lean := "FABL.isSignValued_innerProductModTwo, FABL.isBent_innerProductModTwo, FABL.isSignValued_completeQuadratic, FABL.isBent_completeQuadratic") (uses := "definition-6.26, support-exercise-1.1g-inner-product-mod-two, support-exercise-5.12, proposition-6.28") (tags := "section-6-3, fidelity-exact")
*Canonical bent functions.* The inner-product-mod-$`2` function
$$`
\operatorname{IP}_{2m}(x,y)=(-1)^{x\cdot y},
\qquad x,y\in\mathbb F_2^m,
`
is bent. For $`m=1` this is the two-bit AND function in the sign encoding.
The complete quadratic function
$$`
\operatorname{CQ}_n(x)
=(-1)^{\sum_{1\le i<j\le n}x_ix_j}
`
is also bent when $`n` is even; it is obtained from the inner-product
function by an invertible linear change of variables and multiplication by
an affine sign.
:::

:::proposition "proposition-6.27" (parent := "fabl-chapter-6") (lean := "FABL.bentDirectProduct, FABL.IsSignValued.directProduct, FABL.IsBent.directProduct") (uses := "definition-6.26, support-exercise-6.16") (tags := "section-6-3, fidelity-exact")
*Proposition 6.27.* If
$`f:\mathbb F_2^n\to\{-1,1\}` and
$`g:\mathbb F_2^{n'}\to\{-1,1\}` are bent, then
$$`
(f\oplus g)(x,x')=f(x)g(x')
`
defines a bent function on $`\mathbb F_2^{n+n'}`.
:::

:::proposition "proposition-6.28" (parent := "fabl-chapter-6") (lean := "FABL.bentAffineModulation, FABL.vectorFourierCoeff_bentAffineModulation, FABL.IsSignValued.affineModulation, FABL.IsBent.affineModulation, FABL.bentLinearReindex, FABL.vectorFourierCoeff_bentLinearReindex, FABL.IsSignValued.linearReindex, FABL.IsBent.linearReindex") (uses := "definition-6.26, theorem-1.1, proposition-1.8") (tags := "section-6-3, fidelity-exact")
*Proposition 6.28.* Let $`f:\mathbb F_2^n\to\{-1,1\}` be bent.
For every $`\gamma\in\widehat{\mathbb F_2^n}`, each function
$`\pm\chi_\gamma f` is bent. If
$`M:\mathbb F_2^n\to\mathbb F_2^n` is an invertible linear
transformation, then $`f\circ M` is bent.
:::

:::proposition "proposition-6.29" (parent := "fabl-chapter-6") (lean := "FABL.maioranaMcFarland, FABL.maioranaMcFarland_joinF₂CubeBlocks, FABL.vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks, FABL.isSignValued_maioranaMcFarland, FABL.isBent_maioranaMcFarland") (uses := "definition-6.26, support-exercise-1.1g-inner-product-mod-two, fact-1.7") (tags := "section-6-3, fidelity-exact")
*Proposition 6.29 (Maiorana--McFarland family).* Let
$`g:\mathbb F_2^n\to\{-1,1\}` be arbitrary and define
$$`
f:\mathbb F_2^{2n}\to\{-1,1\},
\qquad
f(x,y)=\operatorname{IP}_{2n}(x,y)g(y).
`
Then $`f` is bent. More precisely, for every
$`(\gamma_1,\gamma_2)\in\widehat{\mathbb F_2^{2n}}`,
$$`
\widehat f(\gamma_1,\gamma_2)
=2^{-n}g(\gamma_1)\chi_{\gamma_2}(\gamma_1),
`
so every Fourier coefficient has absolute value $`2^{-n}`.
:::

:::lemma_ "support-binary-extension-field-model" (parent := "fabl-chapter-6") (lean := "FABL.BinaryExtensionField, FABL.binaryExtensionField_finrank, FABL.binaryExtensionField_natCard, FABL.binaryExtensionBasis, FABL.binaryExtensionEncode, FABL.ExecutableBinaryFieldModel, FABL.buildExecutableBinaryFieldModel, FABL.buildExecutableBinaryFieldModel_complete, FABL.binaryArithmeticWork_isBigO, FABL.binaryFieldPreprocessingWork_isBigO, FABL.buildExecutableBinaryFieldModel_resource_bounds") (tags := "section-6-3, support, fidelity-exact")
*Binary extension-field model used by the constructions.* For every
$`\ell\in\mathbb N^+` there is a finite field $`\mathbb F_{2^\ell}` with
exactly $`2^\ell` elements and a linear encoding
$$`
\operatorname{enc}:\mathbb F_{2^\ell}\longrightarrow\mathbb F_2^\ell
`
satisfying
$$`
\operatorname{enc}(0)=0,
\qquad
\operatorname{enc}(a+b)=\operatorname{enc}(a)+\operatorname{enc}(b).
`
An explicit representation, including complete addition and multiplication
tables, can be constructed deterministically in time $`2^{O(\ell)}`.
Field arithmetic can in fact be performed in deterministic
$`\operatorname{poly}(\ell)` time.
:::

:::lemma_ "support-finite-field-root-bound" (parent := "fabl-chapter-6") (lean := "FABL.ncard_rootSet_le_natDegree") (tags := "section-6-3, support, fidelity-exact")
*Finite-field root bound.* If $`\mathbb F` is a field and
$`p\in\mathbb F[X]` is a nonzero polynomial of degree at most $`d`, then
$`p` has at most $`d` roots in $`\mathbb F`.
:::

:::lemma_ "equation-6.5" (parent := "fabl-chapter-6") (lean := "FABL.smallBiasPolynomial, FABL.smallBiasPolynomial_eval, FABL.smallBiasPolynomial_ne_zero, FABL.smallBiasPolynomial_natDegree_le, FABL.smallBiasGenerator, FABL.smallBiasGenerator_characterExpectation_eq_rootProbability, FABL.smallBiasGenerator_characterExpectation_nonneg, FABL.smallBiasGenerator_characterExpectation_le") (uses := "definition-6.5, support-binary-extension-field-model, support-finite-field-root-bound, fact-1.7") (tags := "section-6-3, support, fidelity-exact")
*Equation (6.5) (small-bias character calculation).* Let
$`r,s` be independent and uniform in $`\mathbb F_{2^\ell}`, and set
$$`
y_i=\left\langle\operatorname{enc}(r^i),
                        \operatorname{enc}(s)\right\rangle,
\qquad i\in[n].
`
For $`0\ne\gamma\in\mathbb F_2^n`, define the nonzero polynomial
$$`
p_\gamma(a)=\gamma_1a+\gamma_2a^2+\cdots+\gamma_na^n.
`
Then
$$`
\mathbb E[\chi_\gamma(y)]
=\mathbb E_r\!\left[
  \mathbb E_s
  \left[(-1)^{
    \langle\operatorname{enc}(p_\gamma(r)),\operatorname{enc}(s)\rangle}
  \right]\right]
=\Pr_r[p_\gamma(r)=0].
\tag{6.5}
`
In particular,
$$`
0\le\mathbb E[\chi_\gamma(y)]
\le\frac{n}{2^\ell}.
`
:::

:::theorem "theorem-6.30" (parent := "fabl-chapter-6") (lean := "FABL.binaryLowPolynomial_injective, FABL.binaryAdjoinRootEncode_injective, FABL.binaryAdjoinRootLinearMap, FABL.binaryPowMod, FABL.binaryAdjoinRootEncode_binaryPowMod, FABL.executableSmallBiasGenerator, FABL.executableSmallBiasGeneratorList, FABL.executableSmallBiasGeneratorMultiset, FABL.length_executableSmallBiasGeneratorList, FABL.executableSmallBiasGeneratorMultiset_card, FABL.executableSmallBiasGeneratorDensity, FABL.executableSmallBiasPolynomial, FABL.executableSmallBiasPolynomial_eval, FABL.executableSmallBiasPolynomial_ne_zero, FABL.executableSmallBiasPolynomial_natDegree_le, FABL.executableSmallBiasPowerSum, FABL.binaryAdjoinRootEncode_executableSmallBiasPowerSum, FABL.ncard_executableSmallBiasPowerSum_zero_le, FABL.executableSmallBiasGenerator_characterExpectation_eq_rootProbability, FABL.executableSmallBiasGenerator_characterExpectation_nonneg, FABL.executableSmallBiasGenerator_characterExpectation_le, FABL.vectorFourierCoeff_executableSmallBiasGeneratorDensity, FABL.executableSmallBiasGeneratorDensity_isBiased, FABL.executableSmallBiasGenerator_core, FABL.executableSmallBiasPowerWork, FABL.executableSmallBiasPowerWork_eq, FABL.executableSmallBiasRowWork, FABL.executableSmallBiasRowWork_le, FABL.executableSmallBiasConstructionWork, FABL.executableSmallBiasConstructionWork_eq, FABL.ExecutableSmallBiasConstruction, FABL.buildExecutableSmallBiasConstruction, FABL.buildExecutableSmallBiasConstruction_resource_bounds, FABL.SmallBiasInput, FABL.SmallBiasInput.epsilon, FABL.SmallBiasInput.scale, FABL.SmallBiasInput.fieldDegree, FABL.SmallBiasInput.fieldDegree_pos, FABL.deterministicSmallBiasAlgorithm, FABL.deterministicSmallBiasMultiset, FABL.deterministicSmallBiasDensity, FABL.deterministicSmallBiasWork, FABL.deterministicSmallBiasMultiset_card, FABL.SmallBiasInput.epsilon_pos, FABL.SmallBiasInput.epsilon_le_half, FABL.SmallBiasInput.one_lt_scale, FABL.SmallBiasInput.fieldDegree_eq_clog, FABL.SmallBiasInput.scale_le_fieldSize, FABL.SmallBiasInput.fieldSize_le_two_scale, FABL.SmallBiasInput.dimension_le_epsilon_mul_fieldSize, FABL.SmallBiasInput.fieldSize_mul_numerator_le, FABL.SmallBiasInput.fieldSize_le_four_dimension_div_epsilon, FABL.SmallBiasInput.n_le_scale, FABL.SmallBiasInput.fieldDegree_succ_le, FABL.SmallBiasInput.polynomialBudget, FABL.deterministicSmallBiasWork_le_polynomialBudget, FABL.deterministicSmallBiasWork_isBigO, FABL.deterministicSmallBiasAlgorithm_spec, FABL.exists_smallBiasGenerator_of_real, FABL.SmallBiasInput.fieldDegree_eq_of_dyadic, FABL.smallBiasGenerator_core_powerOfTwo") (uses := "definition-6.5, equation-6.5") (tags := "section-6-3, fidelity-explicit-finite-rational-input")
*Theorem 6.30.* There is a deterministic algorithm that, given
$`n\ge1` and $`0<\epsilon\le1/2`, runs in
$`\operatorname{poly}(n/\epsilon)` time and outputs a multiset
$`A\subseteq\mathbb F_2^n` of cardinality at most
$$`
16(n/\epsilon)^2
`
such that its uniform density $`\varphi_A` is $`\epsilon`-biased.

In the power-of-two case
$`\epsilon=2^{-t}` and $`n=2^{\ell-t}`, the construction enumerates the
$`2^{2\ell}=(n/\epsilon)^2` pairs
$`(r,s)\in\mathbb F_{2^\ell}^2` and emits the string
$$`
y_i=\left\langle\operatorname{enc}(r^i),
                        \operatorname{enc}(s)\right\rangle.
`

The executable interface encodes $`\epsilon` by a positive numerator and
denominator, so its input is finite.  The arbitrary-real quantitative
statement is proved separately as a mathematical existence theorem, rather
than as an algorithm which reads an exact real number.  Both forms use the
same field-degree bounds.
:::

:::proposition "proposition-6.31" (parent := "fabl-chapter-6") (lean := "FABL.matrixRowSpan, FABL.matrixRowSpan_eq_span_rows, FABL.matrixColumnSum, FABL.HasNonzeroColumnSumsUpTo, FABL.matrixRowSpanDensity, FABL.vectorFourierCoeff_matrixRowSpanDensity, FABL.matrixRowSpanDensity_isKWiseIndependent_iff") (uses := "definition-6.15, proposition-3.11, support-orthogonal-complement-f2") (tags := "section-6-3, fidelity-exact")
*Proposition 6.31.* Let $`H\in\mathbb F_2^{m\times n}` and let
$`A\le\mathbb F_2^n` be the span of the rows of $`H`. The density
$`\varphi_A` is $`k`-wise independent if and only if every nonempty sum of
at most $`k` columns of $`H` is nonzero in $`\mathbb F_2^m`.
:::

:::lemma_ "support-vandermonde-nonsingularity" (parent := "fabl-chapter-6") (lean := "FABL.det_vandermonde_ne_zero_of_injective, FABL.eq_zero_of_vandermonde_mulVec_eq_zero, FABL.vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo") (uses := "support-binary-extension-field-model") (tags := "section-6-3, support, fidelity-exact")
*Vandermonde nonsingularity.* If
$`\alpha_1,\ldots,\alpha_k` are distinct elements of a field, then
$$`
\begin{bmatrix}
1&1&\cdots&1\\
\alpha_1&\alpha_2&\cdots&\alpha_k\\
\alpha_1^2&\alpha_2^2&\cdots&\alpha_k^2\\
\vdots&\vdots&\ddots&\vdots\\
\alpha_1^{k-1}&\alpha_2^{k-1}&\cdots&\alpha_k^{k-1}
\end{bmatrix}
`
is nonsingular. Consequently, in the matrix whose columns are
$`(1,\alpha,\ldots,\alpha^{k-1})^{\mathsf T}` as $`\alpha` ranges over a
field, every set of at most $`k` columns is linearly independent.
:::

:::theorem "theorem-6.32" (parent := "fabl-chapter-6") (lean := "FABL.vandermondeBinaryMatrix, FABL.vandermondeBinaryMatrix_hasNonzeroColumnSumsUpTo, FABL.exists_vandermondeBinaryMatrix") (uses := "support-binary-extension-field-model, support-vandermonde-nonsingularity") (tags := "section-6-3, fidelity-exact")
*Theorem 6.32.* Let $`k,\ell\in\mathbb N^+`, assume
$`n=2^\ell\ge k`, and put
$$`
m=(k-1)\ell+1.
`
There is a matrix $`H\in\mathbb F_2^{m\times n}` such that every nonempty
sum of at most $`k` columns of $`H` is nonzero.

Explicitly, enumerate $`\mathbb F_{2^\ell}` as
$`\alpha_1,\ldots,\alpha_n`, form the $`k\times n` matrix over
$`\mathbb F_{2^\ell}` with $`j`th column
$$`
(1,\alpha_j,\alpha_j^2,\ldots,\alpha_j^{k-1})^{\mathsf T},
`
and replace each nonconstant field entry by its $`\ell`-bit linear encoding.
:::

:::corollary "corollary-6.33" (parent := "fabl-chapter-6") (lean := "FABL.exists_kWiseIndependentSubspace_card_le, FABL.ExecutableVandermondeInput, FABL.ExecutableVandermondeInput.n_pos, FABL.ExecutableVandermondeInput.fieldDegree, FABL.ExecutableVandermondeInput.fieldDegree_pos, FABL.ExecutableVandermondeInput.n_le_fieldSize, FABL.ExecutableVandermondeInput.fieldSize_le_two_n, FABL.ExecutableVandermondeInput.fieldDegree_succ_le, FABL.ExecutableVandermondeInput.fieldImplementation, FABL.executableVandermondePoint, FABL.executableVandermondePoint_injective, FABL.executableVandermondeRowEquiv, FABL.executableVandermondeMatrix, FABL.executableBinaryField_finrank, FABL.executableVandermondeFieldEquiv, FABL.executableVandermondeFieldPoint, FABL.executableVandermondeFieldPoint_power, FABL.executableVandermondeFieldPoint_injective, FABL.executableVandermondeMatrix_hasNonzeroColumnSumsUpTo, FABL.executableVandermondeSubspace, FABL.executableVandermondeDensity, FABL.executableVandermondeDensity_isKWiseIndependent, FABL.card_matrixRowSpan_le_two_pow, FABL.executableVandermondeRowCount_cardBound, FABL.executableVandermondeSubspace_card_le, FABL.executableVandermondePowerRowsWork, FABL.executableVandermondePowerRowsWork_eq_sum, FABL.executableVandermondePowerRowsWork_le, FABL.executableVandermondeConstructionWork, FABL.executableVandermondeConstructionWork_eq, FABL.executableVandermondeConstructionWork_eq_sum, FABL.ExecutableVandermondeInput.scale, FABL.ExecutableVandermondeInput.polynomialBudget, FABL.executableVandermondeConstructionWork_le_polynomialBudget, FABL.executableVandermondeConstructionWork_isBigO, FABL.executableVandermondeAlgorithm_spec") (uses := "proposition-6.31, theorem-6.32") (tags := "section-6-3, fidelity-exact-deterministic-runtime")
*Corollary 6.33.* There is a deterministic algorithm that, given integers
$`1\le k\le n`, runs in $`\operatorname{poly}(n^k)` time and outputs a
subspace $`A\le\mathbb F_2^n` such that $`\varphi_A` is $`k`-wise
independent and
$$`
|A|\le 2^k n^{k-1}.
`
:::

:::lemma_ "lemma-6.34" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.pushforward, FABL.ProbabilityDensity.pushforward_expectation, FABL.matrixPushforwardDensity, FABL.vectorFourierCoeff_matrixPushforwardDensity, FABL.matrixPushforwardDensity_isApproximatelyKWiseIndependent") (uses := "definition-6.5, definition-6.11, fact-1.7") (tags := "section-6-3, fidelity-exact")
*Lemma 6.34.* Suppose $`H\in\mathbb F_2^{m\times n}` has the property that
every nonempty sum of at most $`k` columns is nonzero. Let
$`\varphi` be an $`\epsilon`-biased density on $`\mathbb F_2^m`. Draw
$`y\sim\varphi` and set
$$`
z=y^{\mathsf T}H\in\mathbb F_2^n.
`
Then the density of $`z` is $`(\epsilon,k)`-wise independent.
:::

:::theorem "theorem-6.35" (parent := "fabl-chapter-6") (lean := "FABL.AlmostKWiseInput, FABL.AlmostKWiseInput.n_pos, FABL.AlmostKWiseInput.vandermondeInput, FABL.AlmostKWiseInput.rowCount, FABL.AlmostKWiseInput.rowCount_pos, FABL.AlmostKWiseInput.smallBiasInput, FABL.AlmostKWiseInput.epsilon, FABL.AlmostKWiseInput.epsilon_pos, FABL.AlmostKWiseInput.epsilon_le_half, FABL.AlmostKWiseInput.sizeScale, FABL.AlmostKWiseInput.rowCount_le_sizeScale, FABL.AlmostKWiseInput.reciprocalScale, FABL.AlmostKWiseInput.outputScale, FABL.AlmostKWiseInput.scale, FABL.AlmostKWiseInput.n_le_scale, FABL.AlmostKWiseInput.smallBiasScale_le_outputScale, FABL.AlmostKWiseInput.smallBiasScale_le_four_scale_sq, FABL.AlmostKWiseInput.rowCount_le_four_scale_sq, FABL.almostKWiseMatrix, FABL.almostKWiseTransform, FABL.almostKWiseOutputList, FABL.almostKWiseOutputMultiset, FABL.almostKWiseDensity, FABL.almostKWiseSmallBiasOutputList_length, FABL.almostKWiseOutputList_length, FABL.almostKWiseOutputMultiset_card_eq_source, FABL.almostKWiseRandomBits, FABL.almostKWiseOutputMultiset_card_eq_two_pow_randomBits, FABL.almostKWiseDensity_isApproximatelyKWiseIndependent, FABL.almostKWiseOutputMultiset_card_le_realScale, FABL.almostKWiseOutputMultiset_card_le_smallBiasScale, FABL.almostKWiseOutputMultiset_card_le_naturalScale, FABL.almostKWiseOutputMultiset_card_isBigO_realScale, FABL.almostKWiseOutputMultiset_card_isBigO_naturalScale, FABL.binaryClog_mul_le, FABL.AlmostKWiseInput.randomBitLogScale, FABL.almostKWiseRandomBits_le_logScale, FABL.almostKWiseRandomBits_isBigO, FABL.executableMatrixVecMulWork, FABL.executableMatrixVecMulWork_eq, FABL.almostKWiseConstructionWork, FABL.almostKWiseConstructionWork_eq, FABL.almostKWiseVandermondeWork_le, FABL.almostKWiseMatrixVecMulWork_le, FABL.AlmostKWiseInput.polynomialBudget, FABL.almostKWiseConstructionWork_le_polynomialBudget, FABL.almostKWiseConstructionWork_isBigO, FABL.almostKWiseAlgorithm_spec") (uses := "theorem-6.30, theorem-6.32, lemma-6.34") (tags := "section-6-3, fidelity-exact-deterministic-runtime")
*Theorem 6.35.* There is a deterministic algorithm that, given
$`1\le k\le n` and $`0<\epsilon\le1/2`, runs in
$`\operatorname{poly}(n/\epsilon)` time and outputs a multiset
$`A\subseteq\mathbb F_2^n` whose cardinality is a power of $`2` and
satisfies
$$`
|A|=O\!\left(\left(\frac{k\log n}{\epsilon}\right)^2\right).
`
The density $`\varphi_A` is $`(\epsilon,k)`-wise independent. Equivalently,
the distribution can be sampled using
$`O(\log k+\log\log n+\log(1/\epsilon))` independent random bits.
:::
