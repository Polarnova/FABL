/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter02.TotalInfluence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Total influence" =>

:::definition "definition-2.27" (lean := "FABL.totalInfluence") (uses := "definition-2.17") (tags := "section-2-3, fidelity-exact")
*Definition 2.27.* For every $`f:\{-1,1\}^n\to\mathbb R`, the total influence
of $`f` is
$$`\mathbf I[f]=\sum_{i=1}^{n}\operatorname{Inf}_i[f].`
:::

:::proposition "proposition-2.28" (lean := "FABL.sensitivity, FABL.totalInfluence_toReal_eq_expect_sensitivity") (uses := "definition-2.12, definition-2.13, definition-2.27") (tags := "section-2-3, fidelity-exact")
*Proposition 2.28.* For every Boolean-valued function
$`f:\{-1,1\}^n\to\{-1,1\}`,
$$`\mathbf I[f]
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}
  [\operatorname{sens}_f(\boldsymbol{x})],`
where the sensitivity $`\operatorname{sens}_f(x)` of $`f` at $`x` is the
number of coordinates that are pivotal for $`f` on input $`x`.
:::

:::lemma_ "fact-2.29" (lean := "FABL.UndirectedCubeEdge, FABL.undirectedCubeBoundaryFraction, FABL.undirectedCubeBoundaryFraction_eq_totalInfluence_div") (uses := "fact-2.14, definition-2.27") (tags := "section-2-3, fidelity-exact")
*Fact 2.29.* For every $`f:\{-1,1\}^n\to\{-1,1\}`, the fraction of all
edges in the Hamming cube $`\{-1,1\}^n` that are boundary edges for $`f` is
$`\frac{1}{n}\mathbf I[f]`.
:::

:::lemma_ "example-2.30" (lean := "FABL.totalInfluence_toReal_mem_Icc, FABL.totalInfluence_const, FABL.totalInfluence_monomial, FABL.totalInfluence_neg, FABL.totalInfluence_dictator, FABL.totalInfluence_orFunction, FABL.totalInfluence_andFunction, FABL.totalInfluence_majority_odd_eq_main_add_error") (uses := "definition-2.27, example-2.15") (tags := "section-2-3, fidelity-exact")
*Example 2.30.* For Boolean-valued functions
$`f:\{-1,1\}^n\to\{-1,1\}`, total influence ranges from $`0` to $`n`.
The constant functions $`\pm1` minimize it, with total influence $`0`.
The parity function $`\chi_{[n]}` and its negation maximize it, with total
influence $`n`; every coordinate is pivotal on every input for these functions.
The dictator functions and their negations have total influence $`1`. Moreover,
$`\mathbf I[\operatorname{OR}_n]=\mathbf I[\operatorname{AND}_n]=n2^{1-n}`,
whereas, for odd $`n`,
$`\mathbf I[\operatorname{Maj}_n]=\sqrt{\frac{2}{\pi}}\sqrt n+O(n^{-1/2})`.
:::

:::proposition "proposition-2.31" (lean := "FABL.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone") (uses := "definition-2.27, proposition-2.21") (tags := "section-2-3, fidelity-exact")
*Proposition 2.31.* If $`f:\{-1,1\}^n\to\{-1,1\}` is monotone, then
$`\mathbf I[f]=\sum_{i=1}^{n}\widehat f(i)`, where $`\widehat f(i)`
abbreviates $`\widehat f(\{i\})`.
:::

:::proposition "proposition-2.32" (lean := "FABL.agreeingVoteCount, FABL.expect_agreeingVoteCount") (uses := "definition-2.11, proposition-1.8") (tags := "section-2-3, fidelity-exact")
*Proposition 2.32.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be a voting rule for a
two-candidate election. Under the impartial culture assumption, let
$`\boldsymbol{x}=(\boldsymbol{x}_1,\ldots,\boldsymbol{x}_n)` be the votes and
let $`w` be the number of votes that agree with the election outcome
$`f(\boldsymbol{x})`. Then
$$`\mathbb E[w]
=\frac n2+\frac12\sum_{i=1}^{n}\widehat f(i).`
:::

:::lemma_ "equation-2.3" (lean := "FABL.sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue") (uses := "proposition-1.8") (tags := "section-2-3, support, fidelity-exact")
*Equation (2.3).* For every $`f:\{-1,1\}^n\to\mathbb R`, with
$`\boldsymbol{x}` uniform on $`\{-1,1\}^n`,
$$`\sum_{i=1}^{n}\widehat f(i)
=\sum_{i=1}^{n}\mathbb E[f(\boldsymbol{x})\boldsymbol{x}_i]
=\mathbb E\left[
  f(\boldsymbol{x})(\boldsymbol{x}_1+\cdots+\boldsymbol{x}_n)
\right]. \tag{2.3}`
:::

:::lemma_ "support-exercise-2.22" (lean := "FABL.booleanInfluence_majority_odd_eq_oddMajorityInfluence, FABL.oddMajorityInfluence_strictAnti, FABL.oddMajorityInfluenceMain, FABL.oddMajorityInfluenceError, FABL.oddMajorityInfluenceError_mem_Icc, FABL.oddMajorityInfluenceError_isBigO, FABL.fourierWeightAtLevel_one_majority_odd, FABL.two_div_pi_le_fourierWeightAtLevel_one_majority_odd, FABL.oddMajorityLevelOneWeightError, FABL.oddMajorityLevelOneWeightError_mem_Icc, FABL.oddMajorityLevelOneWeightError_isBigO, FABL.oddMajorityTotalInfluenceError, FABL.oddMajorityTotalInfluenceError_mem_Icc, FABL.oddMajorityTotalInfluenceError_isBigO, FABL.totalInfluence_evenMajority_eq_predecessor, FABL.totalInfluence_evenMajority_exact, FABL.abs_evenMajorityTotalInfluenceError_le, FABL.evenMajorityTotalInfluenceError_isBigO") (uses := "definition-1.19, definition-2.1, definition-2.13, definition-2.27") (tags := "section-2-3, support, fidelity-exact")
*Exercise 2.22.* For odd $`n`:

1. For every $`i\in[n]`,
   $$`\operatorname{Inf}_i[\operatorname{Maj}_n]
   =\binom{n-1}{(n-1)/2}2^{1-n}.`
2. $`\operatorname{Inf}_1[\operatorname{Maj}_n]` is a decreasing function of
   odd $`n`.
3. Using Stirling's formula
   $`m!=(m/e)^m(\sqrt{2\pi m}+O(m^{-1/2}))`,
   $$`\operatorname{Inf}_1[\operatorname{Maj}_n]
   =\sqrt{\frac{2}{\pi n}}+O(n^{-3/2}),`
   where the $`O(\cdot)` terms are nonnegative.
4. Consequently,
   $$`\frac{2}{\pi}
   \le \mathbf W^1[\operatorname{Maj}_n]
   \le \frac{2}{\pi}+O(n^{-1}).`
5. Consequently,
   $$`\sqrt{\frac{2}{\pi}}\sqrt n
   \le \mathbf I[\operatorname{Maj}_n]
   \le \sqrt{\frac{2}{\pi}}\sqrt n+O(n^{-1/2}).`

If $`n` is even and $`f:\{-1,1\}^n\to\{-1,1\}` is a majority function,
then
$$`\mathbf I[f]=\mathbf I[\operatorname{Maj}_{n-1}]
=\sqrt{\frac{2}{\pi}}\sqrt n+O(n^{-1/2}).`
:::

:::theorem "theorem-2.33" (lean := "FABL.sum_fourierCoeff_singleton_le_majority, FABL.sum_fourierCoeff_singleton_eq_majority_iff, FABL.totalInfluence_toReal_le_majority_of_monotone, FABL.totalInfluence_toReal_le_majority_main_add_error_of_monotone") (uses := "equation-2.3, proposition-2.31, support-exercise-2.22") (tags := "section-2-3, fidelity-exact")
*Theorem 2.33.* Among all functions
$`f:\{-1,1\}^n\to\{-1,1\}`, the unique maximizers of
$`\sum_{i=1}^{n}\widehat f(i)` are the majority functions: $`f(x)` must equal
$`\operatorname{sgn}(x_1+\cdots+x_n)` whenever
$`x_1+\cdots+x_n\ne0`. In particular, every monotone
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`\mathbf I[f]
\le \mathbf I[\operatorname{Maj}_n]
=\sqrt{\frac{2}{\pi}}\sqrt n+O(n^{-1/2}).`
:::

:::lemma_ "equation-2.4" (lean := "FABL.totalInfluence_eq_expect_sum_sq_discreteDerivative") (uses := "definition-2.17, definition-2.27") (tags := "section-2-3, support, fidelity-exact")
*Equation (2.4).* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\mathbf I[f]
=\sum_{i=1}^{n}\operatorname{Inf}_i[f]
=\sum_{i=1}^{n}\mathbb E[D_i f(\boldsymbol{x})^2]
=\mathbb E\left[\sum_{i=1}^{n}D_i f(\boldsymbol{x})^2\right]. \tag{2.4}`
:::

:::definition "definition-2.34" (lean := "FABL.discreteGradient, FABL.norm_discreteGradient_toReal_sq_eq_sensitivity") (uses := "definition-2.16, proposition-2.28") (tags := "section-2-3, fidelity-exact")
*Definition 2.34.* The discrete gradient operator maps every
$`f:\{-1,1\}^n\to\mathbb R` to
$`\nabla f:\{-1,1\}^n\to\mathbb R^n` defined by
$$`\nabla f(x)=(D_1f(x),D_2f(x),\ldots,D_nf(x)).`
If $`f:\{-1,1\}^n\to\{-1,1\}`, then
$`\lVert\nabla f(x)\rVert_2^2=\operatorname{sens}_f(x)`,
where $`\lVert\cdot\rVert_2` is the usual Euclidean norm on $`\mathbb R^n`.
:::

:::proposition "proposition-2.35" (lean := "FABL.totalInfluence_eq_expect_norm_discreteGradient_sq") (uses := "equation-2.4, definition-2.34") (tags := "section-2-3, fidelity-exact")
*Proposition 2.35.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\mathbf I[f]
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}
  [\lVert\nabla f(\boldsymbol{x})\rVert_2^2].`
:::

:::definition "definition-2.36" (lean := "FABL.laplacian") (uses := "definition-2.25") (tags := "section-2-3, fidelity-exact")
*Definition 2.36.* The Laplacian is the linear operator on functions
$`f:\{-1,1\}^n\to\mathbb R` defined by $`L=\sum_{i=1}^{n}L_i`;
equivalently, $`Lf=\sum_{i=1}^{n}L_if`.
:::

:::lemma_ "support-exercise-2.17" (lean := "FABL.laplacian_eq_sum_sub_flip_div_two, FABL.laplacian_toReal_eq_mul_sensitivity, FABL.laplacian_eq_fourier_sum, FABL.uniformInner_laplacian_eq_totalInfluence") (uses := "theorem-1.1, proposition-2.26, definition-2.27, definition-2.36") (tags := "section-2-3, support, fidelity-exact")
*Exercise 2.17.* Prove that for every
$`f:\{-1,1\}^n\to\mathbb R`:

1. $$`Lf(x)=\frac n2\left(
     f(x)-\operatorname*{avg}_{i\in[n]}\{f(x^{\oplus i})\}
   \right).`
2. If $`f:\{-1,1\}^n\to\{-1,1\}`, then
   $`Lf(x)=f(x)\operatorname{sens}_f(x)`.
3. $`Lf=\sum_{S\subseteq[n]}|S|\widehat f(S)\chi_S`.
4. $`\langle f,Lf\rangle=\mathbf I[f]`.
:::

:::proposition "proposition-2.37" (lean := "FABL.laplacian_eq_card_mul_sub_expect_flip") (uses := "support-exercise-2.17") (tags := "section-2-3, fidelity-exact")
*Proposition 2.37.* For every $`f:\{-1,1\}^n\to\mathbb R`:

1. $$`Lf(x)=\frac n2\left(
     f(x)-\operatorname*{avg}_{i\in[n]}\{f(x^{\oplus i})\}
   \right).`
2. If $`f:\{-1,1\}^n\to\{-1,1\}`, then
   $`Lf(x)=f(x)\operatorname{sens}_f(x)`.
3. $`Lf=\sum_{S\subseteq[n]}|S|\widehat f(S)\chi_S`.
4. $`\langle f,Lf\rangle=\mathbf I[f]`.
:::

:::theorem "theorem-2.38" (lean := "FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff, FABL.totalInfluence_eq_sum_level_mul_fourierWeight, FABL.totalInfluence_toReal_eq_spectralSample_expectedCard") (uses := "definition-1.19, definition-2.27, theorem-2.20") (tags := "section-2-3, fidelity-exact")
*Theorem 2.38.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\mathbf I[f]
=\sum_{S\subseteq[n]}|S|\widehat f(S)^2
=\sum_{k=0}^{n}k\,\mathbf W^k[f]. \tag{2.5}`
If $`f:\{-1,1\}^n\to\{-1,1\}` and $`\mathcal S_f` is its spectral
distribution, then equivalently
$`\mathbf I[f]=\mathbb E_{\boldsymbol S\sim\mathcal S_f}[|\boldsymbol S|]`.
:::

:::lemma_ "support-exercise-1.19ab" (lean := "FABL.eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one, FABL.isKJunta_one_of_fourierWeightAtMost_one_eq_one") (uses := "definition-1.19, definition-2.16, equation-2.1") (tags := "section-2-3, support, fidelity-exact")
*Exercise 1.19(a),(b).* Let $`f:\{-1,1\}^n\to\{-1,1\}`.

1. If $`\mathbf W^1[f]=1`, then
   $`f(x)=\pm\chi_S(x)` for some $`S\subseteq[n]` with $`|S|=1`.
2. If $`\mathbf W^{\le1}[f]=1`, then $`f` depends on at most one input
   coordinate.
:::

:::theorem "poincare-inequality" (lean := "FABL.variance_le_totalInfluence, FABL.variance_eq_totalInfluence_iff, FABL.variance_eq_totalInfluence_iff_fourierWeightAbove_one_eq_zero, FABL.variance_eq_totalInfluence_iff_lowDegreeWeight_eq_secondMoment, FABL.variance_eq_totalInfluence_toReal_iff") (uses := "proposition-1.13, theorem-2.38, support-exercise-1.19ab") (tags := "section-2-3, fidelity-exact")
*Poincaré Inequality.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\operatorname{Var}[f]\le\mathbf I[f].`
Equality holds if and only if all Fourier weight of $`f` is on degrees $`0`
and $`1`, equivalently $`\mathbf W^{\le1}[f]=\mathbb E[f^2]`.
If $`f:\{-1,1\}^n\to\{-1,1\}` is Boolean-valued, equality holds if and only
if $`f=\pm1` or $`f=\pm\chi_i` for some $`i\in[n]`.
:::

:::theorem "theorem-2.39" (lean := "FABL.positiveProbability, FABL.negativeProbability, FABL.minorityProbability, FABL.two_mul_minorityProbability_mul_logb_inv_le_totalInfluence") (uses := "notation-1.4, definition-2.27") (tags := "section-2-3, fidelity-exact-log-base-two")
*Theorem 2.39.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and set
$$`\alpha
=\min\{\Pr[f(\boldsymbol{x})=1],\Pr[f(\boldsymbol{x})=-1]\},`
where $`\boldsymbol{x}` is uniform on $`\{-1,1\}^n`. Then
$$`2\alpha\log_2(1/\alpha)\le\mathbf I[f].`
:::
