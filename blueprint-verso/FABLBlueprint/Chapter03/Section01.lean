/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter03.LowDegreeSpectralConcentration

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Low-degree spectral concentration" =>

:::definition "definition-3.1" (lean := "FABL.fourierWeightAboveReal, FABL.IsFourierSpectrumConcentratedUpTo, FABL.fourierWeightAboveReal_natCast, FABL.spectralSample_tailMass_eq_fourierWeightAboveReal") (uses := "definition-1.18, definition-1.19") (tags := "section-3-1, fidelity-exact-real-cutoff")
*Definition 3.1.* Let $`f:\{-1,1\}^n\to\mathbb R`, let $`k\in\mathbb R`
be a degree cutoff, and let $`\epsilon\ge0`. The Fourier spectrum of $`f` is
*$`\epsilon`-concentrated on degree up to $`k`* if
$$`
\mathbf W^{>k}[f]
=\sum_{\substack{S\subseteq[n]\\|S|>k}}\widehat f(S)^2
\le\epsilon.
`
If $`f:\{-1,1\}^n\to\{-1,1\}` and $`\mathcal S_f` is its spectral
distribution, the same condition is
$$`
\Pr_{\boldsymbol S\sim\mathcal S_f}
  [|\boldsymbol S|>k]\le\epsilon.
`
:::

:::proposition "proposition-3.2" (lean := "FABL.isFourierSpectrumConcentratedUpTo_totalInfluence_div") (uses := "definition-3.1, theorem-2.38") (tags := "section-3-1, fidelity-exact")
*Proposition 3.2.* For every $`f:\{-1,1\}^n\to\mathbb R` and
$`\epsilon>0`, the Fourier spectrum of $`f` is $`\epsilon`-concentrated on
degree up to $`\mathbf I[f]/\epsilon`; equivalently,
$$`
\sum_{\substack{S\subseteq[n]\\|S|>\mathbf I[f]/\epsilon}}
  \widehat f(S)^2
\le\epsilon.
`
:::

:::lemma_ "support-noise-tail-bound" (lean := "FABL.one_sub_two_mul_pow_le_exp_neg_two, FABL.one_sub_one_sub_two_mul_pow_nonneg, FABL.monotone_one_sub_one_sub_two_mul_pow, FABL.two_div_one_sub_exp_neg_two_le_three, FABL.two_mul_noiseSensitivity_eq_sum_fourier, FABL.noiseSensitivity_nonneg") (uses := "theorem-2.49") (tags := "section-3-1, support, fidelity-exact")
*Noise-tail estimate used in Proposition 3.3.* Let
$`\delta\in(0,1/2]` and let $`m\in\mathbb N`. The function
$`m\longmapsto 1-(1-2\delta)^m` is nonnegative and nondecreasing. In
particular, whenever $`m\ge1/\delta`, one has
$`1-(1-2\delta)^m\ge1-e^{-2}`. The numerical constant also satisfies
$`\frac{2}{1-e^{-2}}\le3`.
:::

:::proposition "proposition-3.3" (lean := "FABL.isFourierSpectrumConcentratedUpTo_noiseSensitivity, FABL.two_div_one_sub_exp_neg_two_mul_noiseSensitivity_le_three") (uses := "definition-3.1, support-noise-tail-bound, theorem-2.49") (tags := "section-3-1, fidelity-exact")
*Proposition 3.3.* For every
$`f:\{-1,1\}^n\to\{-1,1\}` and $`\delta\in(0,1/2]`, the Fourier
spectrum of $`f` is $`\epsilon`-concentrated on degree up to $`1/\delta`,
where $`\epsilon=\frac{2}{1-e^{-2}}\operatorname{NS}_\delta[f]\le3\operatorname{NS}_\delta[f]`.
Thus
$$`
\sum_{\substack{S\subseteq[n]\\|S|>1/\delta}}
  \widehat f(S)^2
\le\frac{2}{1-e^{-2}}\operatorname{NS}_\delta[f].
`
:::

:::lemma_ "support-exercise-3.4" (lean := "FABL.firstCoordinateSlice, FABL.tailFrequency, FABL.monomial_tailFrequency_fin_cons, FABL.monomial_insert_zero_tailFrequency_fin_cons, FABL.fourierCoeff_tailFrequency, FABL.fourierCoeff_insert_zero_tailFrequency, FABL.uniformProbability_ne_zero_eq_firstCoordinateSlices, FABL.exists_fourierCoeff_ne_zero_of_ne_zero, FABL.fourierDegree_firstCoordinateSlice_le, FABL.fourierDegree_firstCoordinateSlice_one_le_pred_of_neg_one_eq_zero, FABL.fourierDegree_firstCoordinateSlice_neg_one_le_pred_of_one_eq_zero, FABL.degreeBound_pos_of_firstCoordinateSlice_one_ne_zero_of_neg_one_eq_zero, FABL.degreeBound_pos_of_firstCoordinateSlice_neg_one_ne_zero_of_one_eq_zero") (uses := "support-exercise-1.10-degree") (tags := "section-3-1, support, fidelity-exact")
*Exercise 3.4.* Prove by induction on $`n` that if
$`f:\{-1,1\}^n\to\mathbb R` is not identically zero and
$`\deg(f)\le k`, then
$`\Pr_{\boldsymbol x\sim\{-1,1\}^n}[f(\boldsymbol x)\ne0]\ge2^{-k}`.
For the induction step, write $`f_+(x)=f(x,1)` and $`f_-(x)=f(x,-1)`.
If one of $`f_+` and $`f_-` is identically zero, show that the other has
degree at most $`k-1`.
:::

:::lemma_ "lemma-3.5" (lean := "FABL.inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le") (uses := "support-exercise-1.10-degree, support-exercise-3.4") (tags := "section-3-1, fidelity-exact")
*Lemma 3.5.* Suppose $`f:\{-1,1\}^n\to\mathbb R` is not identically zero
and $`\deg(f)\le k`. Then, for uniform
$`\boldsymbol x\in\{-1,1\}^n`, one has
$`\Pr[f(\boldsymbol x)\ne0]\ge2^{-k}`.
:::

:::lemma_ "support-degree-discrete-derivative" (lean := "FABL.fourierDegree_discreteDerivative_le_pred, FABL.booleanInfluence_eq_uniformProbability_discreteDerivative_ne_zero") (uses := "proposition-2.19, support-exercise-1.10-degree") (tags := "section-3-1, support, fidelity-exact")
*Degree under discrete differentiation.* If
$`f:\{-1,1\}^n\to\mathbb R` satisfies $`\deg(f)\le k` and $`i\in[n]`,
then $`\deg(D_i f)\le k-1` whenever $`D_i f` is not identically zero. For
Boolean-valued $`f`,
$`\operatorname{Inf}_i[f]=\Pr_{\boldsymbol x}[D_i f(\boldsymbol x)\ne0]`.
:::

:::proposition "proposition-3.6" (lean := "FABL.booleanInfluence_eq_zero_of_fourierDegree_le_zero, FABL.booleanInfluence_eq_zero_or_two_mul_inv_two_pow_le") (uses := "definition-2.17, equation-2.1, lemma-3.5, support-degree-discrete-derivative") (tags := "section-3-1, fidelity-exact")
*Proposition 3.6.* If $`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$`\deg(f)\le k`, then for every $`i\in[n]`,
$$`
\operatorname{Inf}_i[f]=0
\quad\text{or}\quad
\operatorname{Inf}_i[f]\ge2^{1-k}.
`
:::

:::lemma_ "fact-3.7" (lean := "FABL.totalInfluence_toReal_le_fourierDegree") (uses := "parseval, support-exercise-1.10-degree, theorem-2.38") (tags := "section-3-1, fidelity-exact")
*Fact 3.7.* Every $`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$`\mathbf I[f]\le\deg(f)`.
:::

:::lemma_ "support-relevant-coordinate-count" (lean := "FABL.isRelevant_of_fourierCoeff_ne_zero, FABL.relevantCoordinates, FABL.mem_relevantCoordinates, FABL.dependsOn_relevantCoordinates, FABL.sum_influence_relevantCoordinates_eq_totalInfluence, FABL.mul_card_relevantCoordinates_le_totalInfluence, FABL.isKJunta_of_card_relevantCoordinates_le, FABL.dependsOn_toReal_iff, FABL.isKJunta_toReal_iff, FABL.isKJunta_of_card_relevantCoordinates_toReal_le") (uses := "definition-2.4, definition-2.18, definition-2.27") (tags := "section-3-1, support, fidelity-exact")
*Relevant-coordinate counting principle.* For
$`f:\{-1,1\}^n\to\{-1,1\}`, let
$`R_f=\{i\in[n]:\operatorname{Inf}_i[f]>0\}`.
The function $`f` depends only on the coordinates in $`R_f`. Moreover, if
every $`i\in R_f` has $`\operatorname{Inf}_i[f]\ge a` for some $`a>0`, then
$$`
a|R_f|\le\sum_{i\in R_f}\operatorname{Inf}_i[f]
=\mathbf I[f].
`
Consequently, a bound $`|R_f|\le r` makes $`f` an $`r`-junta.
:::

:::theorem "theorem-3.4" (lean := "FABL.relevantCoordinates_toReal_eq_empty_of_fourierDegree_eq_zero, FABL.isKJunta_zero_of_fourierDegree_eq_zero, FABL.isKJunta_mul_two_pow_pred_of_fourierDegree_le") (uses := "definition-2.4, fact-3.7, proposition-3.6, support-relevant-coordinate-count") (tags := "section-3-1, fidelity-exact-k-zero-separated")
*Theorem 3.4.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$`\deg(f)\le k`. Then $`f` is a $`k2^{k-1}`-junta.
For $`k=0`, this means that $`f` is constant and hence is a $`0`-junta;
for $`k\ge1`, the displayed integer is interpreted literally.
:::
