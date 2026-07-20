/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.FourierCoefficientsOfMajority
import FABL.Chapter05.MajorityComplementaryWeights
import FABL.Chapter05.MajorityWeightMonotonicity
import FABL.Chapter05.MajorityNoiseStability
import FABL.Chapter05.MajorityLimits
import FABL.Chapter05.LimitingMajorityWeights
import FABL.Chapter05.MajorityFourierWeightLimits
import FABL.Chapter05.MajorityFourierTailAsymptotics

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Fourier coefficients of Majority" =>

:::lemma_ "support-symmetric-fourier-coefficients" (parent := "fabl-chapter-5") (lean := "FABL.fourierCoeff_eq_of_card_eq_of_isSymmetric") (uses := "support-exercise-1.30a, definition-2.8") (tags := "section-5-3, support, fidelity-exact")
*Symmetric Fourier coefficients (from Exercise 1.30).* Let
$`f:\{-1,1\}^n\to\mathbb R` be symmetric. If $`S,T\subseteq[n]` satisfy
$`|S|=|T|`, then
$$`
\widehat f(S)=\widehat f(T).
`
Thus the Fourier coefficient of a symmetric function at a set $`S` depends
only on $`|S|`.
:::

:::lemma_ "support-exercise-1.8" (parent := "fabl-chapter-5") (lean := "FABL.fourierCoeff_eq_zero_of_odd_of_even_card") (uses := "theorem-1.1, proposition-1.8") (tags := "section-5-3, support, fidelity-exact-used-part")
*Exercise 1.8(c), odd-function consequence.* If
$`f:\{-1,1\}^n\to\mathbb R` is odd, so that $`f(-x)=-f(x)` for every $`x`,
then every even-cardinality Fourier coefficient vanishes:
$$`
|S|\text{ even}\quad\Longrightarrow\quad\widehat f(S)=0.
`
This is the exact part of Exercise 1.8 used by Theorem 5.19.
:::

:::lemma_ "support-exercise-5.18" (parent := "fabl-chapter-5") (lean := "FABL.arcsinSeriesCoefficient, FABL.arcsinOddPowerCoefficient, FABL.arcsinOddPowerCoefficient_two_mul_add_one, FABL.exercise5_18a, FABL.exercise5_18_arcsinSeries, FABL.exercise5_18") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.18 (the power series for arcsine).*

(a) The generalized Binomial Theorem gives, for $`|z|<1`,
$$`
(1-z^2)^{-1/2}
=\sum_{j=0}^{\infty}\binom{2j}{j}\frac{z^{2j}}{2^{2j}}.
`

(b) Integrating term by term gives, for $`|z|<1`,
$$`
\arcsin z
=\sum_{j=0}^{\infty}
  \frac1{2j+1}\binom{2j}{j}\frac{z^{2j+1}}{2^{2j}}
=\sum_{\substack{k\ge1\\k\ \mathrm{odd}}}
  \frac{2}{k2^k}\binom{k-1}{(k-1)/2}z^k.
\tag{5.9}
`

(c) The arcsine series in (b) also holds for $`z=\pm1`; it converges there to
$`\arcsin(1)=\pi/2` and
$`\arcsin(-1)=-\pi/2`.
:::

:::definition "support-limiting-majority-fourier-weights" (parent := "fabl-chapter-5") (lean := "FABL.limitingMajorityFourierWeight, FABL.limitingMajorityFourierWeight_eq, FABL.limitingMajorityFourierWeight_hasSum_one, FABL.limitingMajorityFourierWeightAbove, FABL.limitingMajorityFourierWeightAbove_summable") (uses := "definition-1.19, support-exercise-5.18") (tags := "section-5-3, support, fidelity-exact")
*Limiting majority Fourier weights.* For $`k\in\mathbb N`, write
$$`
\mathbf W^k(\operatorname{Maj})
:=[\rho^k]\left(\frac2\pi\arcsin\rho\right)
=
\begin{cases}
\displaystyle
\frac{4}{\pi k2^k}\binom{k-1}{(k-1)/2},
& k\text{ odd},\\[6pt]
0,& k\text{ even}.
\end{cases}
\tag{5.10}
`
Here $`[\rho^k]F(\rho)` denotes the coefficient of $`\rho^k` in the power
series $`F`. Also write
$$`
\mathbf W^{>k}(\operatorname{Maj})
=\sum_{j>k}\mathbf W^j(\operatorname{Maj}).
`
:::

:::lemma_ "support-middle-layer-fourier-calculation" (parent := "fabl-chapter-5") (lean := "FABL.middleLayerIndicator, FABL.middleLayerIndicator_eq_one_iff_negative_count, FABL.discreteDerivative_majority_odd_last_eq_middleLayerIndicator, FABL.middleLayerIndicator_isSymmetric, FABL.noiseOperator_middleLayerIndicator_allOne_eq_product, FABL.noiseOperator_middleLayerIndicator_allOne_eq, FABL.noiseOperator_middleLayerIndicator_allOne_eq_fourierSum, FABL.noiseOperator_middleLayerIndicator_allOne_eq_groupedFourierSum, FABL.fourierCoeff_middleLayerIndicator") (uses := "definition-2.1, definition-2.16, proposition-2.19, definition-2.46, proposition-2.47, support-symmetric-fourier-coefficients") (tags := "section-5-3, support, fidelity-exact")
*The middle-layer calculation, Equations (5.12)--(5.14).* For $`m\in\mathbb N`,
let
$$`
\operatorname{Half}_{2m}:\{-1,1\}^{2m}\to\{0,1\}
`
be the indicator of the strings having exactly $`m` coordinates equal to
$`-1`. Identifying a derivative that ignores its last coordinate with a
function on the remaining coordinates,
$$`
D_{2m+1}\operatorname{Maj}_{2m+1}=\operatorname{Half}_{2m}.
`
For every $`0\le j\le m` and every $`T\subseteq[2m]` with $`|T|=2j`,
$$`
\widehat{\operatorname{Half}_{2m}}(T)
=(-1)^j
  \frac{\binom mj}{\binom{2m}{2j}}
  \frac1{2^{2m}}\binom{2m}{m}.
\tag{5.12}
`
For every $`\rho\in[-1,1]`,
$$`
\begin{aligned}
T_\rho\operatorname{Half}_{2m}(1,\ldots,1)
&=\binom{2m}{m}
  \left(\frac12+\frac\rho2\right)^m
  \left(\frac12-\frac\rho2\right)^m\\
&=\frac1{2^{2m}}\binom{2m}{m}(1-\rho^2)^m,
\end{aligned}
\tag{5.13}
`
whereas symmetry and the Fourier formula for $`T_\rho` give
$$`
T_\rho\operatorname{Half}_{2m}(1,\ldots,1)
=\sum_{U\subseteq[2m]}
  \widehat{\operatorname{Half}_{2m}}(U)\rho^{|U|}
=\sum_{i=0}^{2m}\binom{2m}{i}
  \widehat{\operatorname{Half}_{2m}}(T_i)\rho^i,
\tag{5.14}
`
where $`T_i` is any $`i`-element subset of $`[2m]`. Comparing coefficients in
(5.13) and (5.14) yields (5.12).
:::

:::theorem "theorem-5.19" (parent := "fabl-chapter-5") (lean := "FABL.fourierCoeff_majority_odd_insert_last, FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card, FABL.fourierCoeff_majority_two_mul_add_one, FABL.fourierCoeff_majority_of_odd_arity_of_card_eq_odd") (uses := "support-exercise-1.8, support-symmetric-fourier-coefficients, support-middle-layer-fourier-calculation") (tags := "section-5-3, fidelity-exact")
*Theorem 5.19.* Let $`n` be odd and let $`S\subseteq[n]`. If $`|S|` is even,
then
$$`
\widehat{\operatorname{Maj}_n}(S)=0.
`
If $`|S|=k` is odd, then
$$`
\widehat{\operatorname{Maj}_n}(S)
=(-1)^{(k-1)/2}
  \frac{\binom{(n-1)/2}{(k-1)/2}}{\binom{n-1}{k-1}}
  \frac2{2^n}\binom{n-1}{(n-1)/2}.
`
Equivalently, when $`n=2m+1` and $`k=2j+1`,
$$`
\widehat{\operatorname{Maj}_{2m+1}}(S)
=(-1)^j
  \frac{\binom mj}{\binom{2m}{2j}}
  \frac1{2^{2m}}\binom{2m}{m}.
`
:::

:::lemma_ "support-exercise-5.20" (parent := "fabl-chapter-5") (lean := "FABL.fourierCoeff_majority_complementary") (uses := "theorem-5.19") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.20.* Prove that for odd $`n` and $`S,T\subseteq[n]` satisfying
$`|S|+|T|=n+1`,
$$`
\widehat{\operatorname{Maj}_n}(S)
=(-1)^{(n-1)/2}\widehat{\operatorname{Maj}_n}(T),
`
and deduce that, for $`1\le k\le n`,
$$`
\mathbf W^{n-k+1}[\operatorname{Maj}_n]
=\frac{k}{n-k+1}\mathbf W^k[\operatorname{Maj}_n].
`
:::

:::corollary "corollary-5.20" (parent := "fabl-chapter-5") (lean := "FABL.fourierWeightAtLevel_majority_complementary") (uses := "support-exercise-5.20") (tags := "section-5-3, fidelity-exact")
*Corollary 5.20.* Let $`n` be odd. Whenever $`S,T\subseteq[n]` satisfy
$`|S|+|T|=n+1`,
$$`
\widehat{\operatorname{Maj}_n}(S)
=(-1)^{(n-1)/2}\widehat{\operatorname{Maj}_n}(T).
`
Hence, for every $`1\le k\le n`,
$$`
\mathbf W^{n-k+1}[\operatorname{Maj}_n]
=\frac{k}{n-k+1}\mathbf W^k[\operatorname{Maj}_n].
`
:::

:::lemma_ "support-exercise-5.22" (parent := "fabl-chapter-5") (lean := "FABL.fourierWeightAtLevel_majority_eq_choose_mul, FABL.fourierCoeff_majority_next_odd_eq, FABL.fourierWeightAtLevel_majority_next_odd_eq, FABL.fourierWeightAtLevel_majority_next_odd_lt") (uses := "theorem-5.19") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.22.* Fix an odd positive integer $`k`. Prove that
$`\mathbf W^k[\operatorname{Maj}_n]` is a strictly decreasing function of
$`n` as $`n` ranges through the odd integers with $`n\ge k`.
:::

:::corollary "corollary-5.21" (parent := "fabl-chapter-5") (lean := "FABL.fourierWeightAtLevel_majority_odd_sequence_strictAnti, FABL.fourierWeightAtLevel_majority_strict_decreasing") (uses := "support-exercise-5.22") (tags := "section-5-3, fidelity-exact")
*Corollary 5.21.* For every fixed odd positive integer $`k`,
$`\mathbf W^k[\operatorname{Maj}_n]` is a strictly decreasing function of
$`n` as $`n` ranges through the odd integers with $`n\ge k`.
:::

:::lemma_ "support-exercise-5.23" (parent := "fabl-chapter-5") (lean := "FABL.noiseStability_majority_next_odd_le, FABL.noiseStability_majority_next_odd_lt, FABL.noiseStability_majority_odd_antitone, FABL.noiseStability_majority_odd_strictAnti, FABL.two_div_pi_mul_arcsin_le_noiseStability_majority_odd, FABL.exists_noiseStability_majority_odd_le_arcsine_add_inv_sqrt") (uses := "theorem-2.45, theorem-5.17, corollary-5.21") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.23.* Prove Theorem 5.18: for every $`\rho\in[0,1)`,
$`\operatorname{Stab}_\rho[\operatorname{Maj}_n]` decreases as $`n` ranges
through the positive odd integers, and
$$`
\frac2\pi\arcsin\rho
\le \operatorname{Stab}_\rho[\operatorname{Maj}_n]
\le \frac2\pi\arcsin\rho
  +O_\rho\left(\frac1{\sqrt{1-\rho^2}\sqrt n}\right).
`
Use Corollary 5.21 for the monotonicity.
:::

:::lemma_ "support-exercise-5.24" (parent := "fabl-chapter-5") (lean := "FABL.exercise5_24") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.24.* For integers $`n,k` satisfying $`1\le k\le n/2`, prove
$$`
\left(1-\frac{k+1}{n}+\frac{k}{n^2}\right)^{-1/2}
\le 1+\frac{2k}{n}.
`
:::

:::theorem "theorem-5.22" (parent := "fabl-chapter-5") (lean := "FABL.limitingMajorityFourierWeight_pos_of_odd, FABL.fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul, FABL.limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority, FABL.fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight, FABL.majorityFourierWeight_bounds, FABL.fourierWeightAtLevel_majority_odd_tendsto, FABL.fourierWeightAtLevel_majority_odd_strictAnti_and_tendsto") (uses := "theorem-5.19, corollary-5.21, support-limiting-majority-fourier-weights, support-exercise-5.24, support-exercise-2.22") (tags := "section-5-3, fidelity-exact")
*Theorem 5.22.* For each fixed odd positive integer $`k`,
$$`
\mathbf W^k[\operatorname{Maj}_n]
\searrow
[\rho^k]\left(\frac2\pi\arcsin\rho\right)
=\frac{4}{\pi k2^k}\binom{k-1}{(k-1)/2}
`
as $`n\ge k` tends to infinity through the odd integers. Moreover, for every
odd $`n` and odd $`k` with $`k<n/2`,
$$`
[\rho^k]\left(\frac2\pi\arcsin\rho\right)
\le \mathbf W^k[\operatorname{Maj}_n]
\le
\left(1+\frac{2k}{n}\right)
[\rho^k]\left(\frac2\pi\arcsin\rho\right).
\tag{5.15}
`
For $`k>n/2`, Corollary 5.20 converts the estimate to the complementary
Fourier level.
:::

:::lemma_ "support-exercise-5.27" (parent := "fabl-chapter-5") (lean := "FABL.majorityFourierLevelMain, FABL.majorityFourierTailMain, FABL.majorityFourierLevelMain_pos, FABL.majorityFourierTailMain_pos, FABL.limitingMajorityFourierWeight_two_mul_add_one_eq, FABL.majorityFourierLevelMain_two_mul_add_one_eq, FABL.limitingMajorityFourierWeightError, FABL.limitingMajorityFourierWeightError_mem_Icc, FABL.majorityFourierLevelMain_le_limitingMajorityFourierWeight, FABL.limitingMajorityFourierWeight_le_levelMain_mul, FABL.limitingMajorityFourierWeightError_isBigO, FABL.limitingMajorityFourierWeightAbove_eq_tsum_odd, FABL.limitingMajorityFourierWeightAbove_mem_Icc, FABL.abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le, FABL.limitingMajorityFourierWeightAbove_relativeError_isBigO, FABL.abs_fourierWeightAtLevel_majority_div_levelMain_sub_one_le, FABL.abs_fourierWeightAbove_majority_div_tailMain_sub_one_le, FABL.majorityFourierLevel_family_relativeError_isBigO, FABL.majorityFourierTail_family_relativeError_isBigO, FABL.tendsto_limitingMajorityFourierWeightAbove_odd_zero") (uses := "theorem-5.22, corollary-5.20, support-limiting-majority-fourier-weights, support-exercise-2.22") (tags := "section-5-3, support, fidelity-exact")
*Exercise 5.27.*

(a) For every odd positive integer $`k`, prove
$$`
\left(\frac2\pi\right)^{3/2}k^{-3/2}
\le
[\rho^k]\left(\frac2\pi\arcsin\rho\right)
\le
\left(\frac2\pi\right)^{3/2}k^{-3/2}
\left(1+O(1/k)\right).
`

(b) Let $`k` tend to infinity through the odd positive integers, and let
$`n=n(k)` be odd with $`n\ge2k^2`. Prove
$$`
\mathbf W^k[\operatorname{Maj}_n]
=\left(\frac2\pi\right)^{3/2}k^{-3/2}
  \left(1\pm O(1/k)\right),
`
$$`
\mathbf W^{>k}[\operatorname{Maj}_n]
=\left(\frac2\pi\right)^{3/2}k^{-1/2}
  \left(1\pm O(1/k)\right),
`
using an integral comparison for the second estimate. Deduce that the Fourier
spectrum of $`\operatorname{Maj}_n` is $`\epsilon`-concentrated up to degree
$$`
\frac8{\pi^3}\epsilon^{-2}+O_\epsilon(1).
`
:::

:::corollary "corollary-5.23" (parent := "fabl-chapter-5") (lean := "FABL.exists_majorityFourierConcentrationCutoff, FABL.corollary5_23") (uses := "support-exercise-5.27") (tags := "section-5-3, fidelity-exact")
*Corollary 5.23.* Let $`k` tend to infinity through the odd positive integers,
and let $`n=n(k)` be odd with $`n\ge2k^2`. Then
$$`
\mathbf W^k[\operatorname{Maj}_n]
=\left(\frac2\pi\right)^{3/2}k^{-3/2}
  \left(1\pm O(1/k)\right),
`
and
$$`
\mathbf W^{>k}[\operatorname{Maj}_n]
=\left(\frac2\pi\right)^{3/2}k^{-1/2}
  \left(1\pm O(1/k)\right).
`
Consequently, the Fourier spectrum of $`\operatorname{Maj}_n` is
$`\epsilon`-concentrated up to degree
$$`
\frac8{\pi^3}\epsilon^{-2}+O_\epsilon(1).
`
:::
