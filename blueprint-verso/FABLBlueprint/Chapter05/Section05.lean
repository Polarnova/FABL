/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.UnateFunctions
import FABL.Chapter05.AverageInfluence
import FABL.Chapter05.UniformNoiseStability
import FABL.Chapter05.Peres

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: Peres's Theorem and uniform noise stability" =>

:::lemma_ "support-exercise-2.5-unate" (parent := "fabl-chapter-5") (lean := "FABL.IsMonotoneInCoordinate, FABL.IsAntimonotoneInCoordinate, FABL.IsUnateInCoordinate, FABL.IsUnate, FABL.abs_fourierCoeff_singleton_le_influence, FABL.abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate, FABL.totalInfluence_toReal_le_majority_of_unate") (uses := "definition-2.16, equation-2.3, theorem-2.33") (tags := "section-5-5, support, fidelity-exact")
*Exercise 2.5 (unate functions).* A Boolean function
$`f:\{-1,1\}^n\to\{-1,1\}` is *unate in coordinate $`i`* if it is either
monotone or antimonotone in that coordinate, and it is *unate* if this holds
in every coordinate.

(a) For every $`i\in[n]`,
$$`
|\widehat f(i)|\le\operatorname{Inf}_i[f],
`
with equality if and only if $`f` is unate in the $`i`th direction.

(b) The total-influence conclusion of Theorem 2.33 extends from monotone to
unate functions: every unate $`f` satisfies
$$`
\mathbf I[f]\le\mathbf I[\operatorname{Maj}_n].
`
:::

:::lemma_ "support-exercise-2.6-ltf-unate" (parent := "fabl-chapter-5") (lean := "FABL.isUnate_of_isLinearThreshold") (uses := "definition-2.5, support-exercise-2.5-unate") (tags := "section-5-5, support, fidelity-exact")
*Exercise 2.6.* Every linear threshold function is unate.
:::

:::lemma_ "support-exercise-2.23-unate-influence" (parent := "fabl-chapter-5") (lean := "FABL.totalInfluence_toReal_le_sqrt_card_of_unate") (uses := "definition-1.19, definition-2.27, support-exercise-2.5-unate, parseval") (tags := "section-5-5, support, fidelity-exact")
*Exercise 2.23.* If $`f:\{-1,1\}^n\to\{-1,1\}` is monotone, then
$$`
\mathbf I[f]\le\sqrt n.
`
The same estimate holds for every unate Boolean function. The proof uses only
Cauchy--Schwarz and Parseval's Theorem.
:::

:::lemma_ "support-exercise-2.43a-average-influence" (parent := "fabl-chapter-5") (lean := "FABL.averageInfluence, FABL.averageCoordinateFlipProbability, FABL.averageInfluence_toReal_eq_averageCoordinateFlipProbability, FABL.averageInfluence_mul_one_sub_exp_neg_two_div_two_le_noiseSensitivity, FABL.noiseSensitivity_inverse_dimension_le_averageInfluence") (uses := "definition-2.27, definition-2.43, theorem-2.49") (tags := "section-5-5, support, fidelity-exact")
*Exercise 2.43(a) (average influence).* For $`n\ge1`, define the average
influence of $`f:\{-1,1\}^n\to\mathbb R` by
$$`
\mathbf E[f]=\frac1n\mathbf I[f].
`
If $`f` is Boolean-valued, then
$$`
\mathbf E[f]
=\Pr_{\substack{x\sim\{-1,1\}^n\\ i\sim[n]}}
  [f(x)\ne f(x^{\oplus i})],
`
and
$$`
\frac{1-e^{-2}}2\mathbf E[f]
\le\operatorname{NS}_{1/n}[f]
\le\mathbf E[f].
`
:::

:::theorem "peres-theorem" (parent := "fabl-chapter-5") (lean := "FABL.peresNoiseSensitivityBound") (uses := "theorem-5.35, support-exercise-2.6-ltf-unate, support-exercise-2.23-unate-influence") (tags := "section-5-5, fidelity-explicit-universal-constant")
*Peres's Theorem.* Every linear threshold function
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\operatorname{NS}_\delta[f]\le O(\sqrt\delta)
\qquad (0<\delta\le1/2),
`
with a universal implied constant independent of $`n` and $`f`.
:::

:::definition "definition-5.34" (parent := "fabl-chapter-5") (lean := "FABL.BooleanClass, FABL.HalfNoiseParameter, FABL.UnitProbability, FABL.IsUniformlyNoiseStable") (uses := "definition-2.43") (tags := "section-5-5, fidelity-exact")
*Definition 5.34.* Let $`\mathcal B` be a class of Boolean-valued functions.
The class $`\mathcal B` is *uniformly noise-stable* if there is a function
$`\epsilon:[0,1/2]\to[0,1]` such that
$`\epsilon(\delta)\to0` as $`\delta\to0^+` and
$$`
\operatorname{NS}_\delta[f]\le\epsilon(\delta)
`
for every $`f\in\mathcal B` and every $`\delta\in[0,1/2]`.
:::

:::theorem "theorem-5.35" (parent := "fabl-chapter-5") (lean := "FABL.negateInputVariables, FABL.identifyInputVariables, FABL.IsClosedUnderNegatingInputVariables, FABL.IsClosedUnderIdentifyingInputVariables, FABL.PositiveHalfNoiseParameter, FABL.inverseNoiseFloor, FABL.noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound") (uses := "definition-5.34, proposition-2.51, support-exercise-2.43a-average-influence") (tags := "section-5-5, fidelity-exact")
*Theorem 5.35.* Let $`\delta\in(0,1/2]`, let
$`A:\mathbb N^+\to\mathbb R`, and let $`\mathcal B` be a class of
Boolean-valued functions closed under negating and identifying input
variables. Suppose every $`f\in\mathcal B` with domain $`\{-1,1\}^r`
satisfies
$$`
\mathbf I[f]\le A(r).
`
Then every $`f\in\mathcal B` satisfies
$$`
\operatorname{NS}_\delta[f]\le\frac1m A(m),
\qquad
m=\left\lfloor\frac1\delta\right\rfloor.
`
:::

:::lemma_ "remark-5.36" (parent := "fabl-chapter-5") (lean := "FABL.noiseSensitivity_le_sqrt_inverseNoiseFloor_of_isLinearThreshold, FABL.sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt, FABL.sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO, FABL.peresMajorityUpperBound, FABL.noiseSensitivity_le_majorityInfluenceRatio_of_isLinearThreshold, FABL.noiseSensitivity_le_peresMajorityUpperBound, FABL.peresMajorityUpperBound_sub_main_isBigO") (uses := "peres-theorem, theorem-2.33, support-exercise-2.22") (tags := "section-5-5, fidelity-exact")
*Remark 5.36.* The proof of Peres's Theorem gives the explicit bound
$$`
\operatorname{NS}_\delta[f]
\le\sqrt{\frac1{\lfloor1/\delta\rfloor}}
\le\sqrt{\frac32}\,\sqrt\delta
\qquad (0<\delta\le1/2),
`
and its first expression is $`\sqrt\delta+O(\delta^{3/2})` as
$`\delta\to0^+`. Replacing Exercise 2.23 by the sharper unate bound from
Theorem 2.33 yields
$$`
\operatorname{NS}_\delta[f]
\le\sqrt{\frac2\pi}\,\sqrt\delta+O(\delta^{3/2}).
`
:::

:::theorem "majority-is-least-stable-conjecture" (parent := "fabl-chapter-5") (uses := "definition-2.1, definition-2.5, definition-2.42") (tags := "section-5-5, refuted, conjecture")
*Majority Is Least Stable Conjecture.* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be a linear threshold function with $`n` odd.
The conjecture asserted that, for every $`\rho\in[0,1]`,
$$`
\operatorname{Stab}_\rho[f]
\ge\operatorname{Stab}_\rho[\operatorname{Maj}_n].
`
The book immediately records that this conjecture is false: a counterexample
already exists for $`n=5`.
:::

:::theorem "linear-threshold-gaussian-stability-conjecture" (parent := "fabl-chapter-5") (uses := "definition-2.5, definition-2.42, theorem-2.45") (tags := "section-5-5, open, conjecture")
*Plausible replacement conjecture.* Every linear threshold function
$`f:\{-1,1\}^n\to\{-1,1\}` should satisfy
$$`
\operatorname{Stab}_\rho[f]\ge\frac2\pi\arcsin\rho
\qquad\text{for every }\rho\in[0,1].
`
This conjecture remains open.
:::

:::theorem "gotsman-linial-conjecture" (parent := "fabl-chapter-5") (uses := "definition-2.27, definition-5.4") (tags := "section-5-5, open, conjecture")
*Gotsman--Linial Conjecture.* Let $`\mathcal P_{n,k}` be the class of
degree-at-most-$`k` polynomial threshold functions on $`n` variables. Every
$`f\in\mathcal P_{n,k}` should satisfy
$$`
\mathbf I[f]\le O_k(1)\sqrt n.
`
More strongly, the factor $`O_k(1)` should be $`O(k)`. In the strongest form,
for $`0\le k\le n`, the member of $`\mathcal P_{n,k}` with maximal total
influence is the symmetric function
$$`
f(x)=\operatorname{sgn}(p(x_1+\cdots+x_n)),
`
where $`p` is a degree-$`k` univariate polynomial alternating sign on the
$`k+1` attainable values of $`x_1+\cdots+x_n` nearest to $`0`.

All forms of this statement remain open for general $`k`.
:::

:::theorem "theorem-5.37" (parent := "fabl-chapter-5") (uses := "definition-2.27, definition-5.4, theorem-5.35") (tags := "section-5-5, external-result, unformalized")
*Theorem 5.37 (Kane).* Every $`f\in\mathcal P_{n,k}` satisfies
$$`
\mathbf I[f]
\le\sqrt n\,(2^k\log n)^{O(k\log k)}.
`
Consequently, for each fixed $`k\in\mathbb N^+` and every
$`f\in\mathcal P_k=\bigcup_n\mathcal P_{n,k}`,
$$`
\operatorname{NS}_\delta[f]
\le\sqrt\delta\,\operatorname{polylog}(1/\delta).
`
The book cites this external theorem without proof.
:::
