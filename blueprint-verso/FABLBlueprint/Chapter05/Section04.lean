/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.DegreeOneWeight
import FABL.Chapter05.FKNImprovement
import FABL.Chapter05.GaussianIsoperimetric
import FABL.Chapter05.GaussianIsoperimetricAsymptotics
import FABL.Chapter05.GaussianMillsRatio
import FABL.Chapter05.HammingBallLimit
import FABL.Chapter05.ImprovedFKN
import FABL.Chapter05.LevelOneInequality
import FABL.Chapter05.NearlyConstantLevelOne
import FABL.Chapter05.SharpLevelOneInequality
import FABL.Chapter05.TwoDivPi

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Degree-1 weight" =>

:::lemma_ "support-exercise-5.29" (lean := "FABL.abs_vectorFourierCoeff_setIndicator_coordinateSubcube, FABL.expect_setIndicator_coordinateSubcube, FABL.sum_sq_vectorFourierCoeff_support_card_one_setIndicator_coordinateSubcube") (uses := "definition-1.19, support-affine-subspaces-and-subcubes, support-exercise-3.11") (tags := "section-5-4, support, fidelity-generalized-zero-codimension")
*Exercise 5.29 (Fourier weight of a subcube).* Let
$`J\subseteq[n]` have cardinality $`k\ge1`, fix values
$`a_i\in\mathbb F_2` for $`i\in J`, and let
$$`
A=\{x\in\mathbb F_2^n:x_i=a_i\text{ for every }i\in J\}.
`
If $`f=1_A`, then
$$`
|\widehat f(S)|
=
\begin{cases}
2^{-k},&S\subseteq J,\\
0,&S\not\subseteq J.
\end{cases}
`
In particular,
$$`
\widehat f(\varnothing)=2^{-k},
\qquad
\sum_{i=1}^n\widehat f(\{i\})^2=k2^{-2k}.
`
Thus $`\mathbb E[f]=2^{-k}` and
$`\mathbf W^1[f]=k2^{-2k}`.
:::

:::proposition "proposition-5.24" (lean := "FABL.expectation_and_degreeOneWeight_setIndicator_coordinateSubcube") (uses := "support-exercise-5.29") (tags := "section-5-4, fidelity-exact")
*Proposition 5.24.* Let $`f:\mathbb F_2^n\to\{0,1\}` be the indicator of a
subcube of codimension $`k\ge1`, for example the $`\operatorname{AND}_k`
function. Then
$$`
\mathbb E[f]=2^{-k},
\qquad
\mathbf W^1[f]=k2^{-2k}.
`
:::

:::lemma_ "support-exercise-5.30" (lean := "FABL.normalizedRademacherSum, FABL.hammingUpperTailIndicator, FABL.hammingUpperTailIndicator_isSymmetric, FABL.fourierCoeff_hammingUpperTailIndicator_singleton, FABL.fourierWeightAtLevel_one_hammingUpperTailIndicator, FABL.abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le, FABL.tendsto_expect_hammingUpperTailIndicator, FABL.tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum") (uses := "berry-esseen-theorem, definition-1.19, plancherel") (tags := "section-5-4, support, fidelity-exact")
*Exercise 5.30 (the Hamming-ball limit).* Fix $`t\in\mathbb R`, and for
uniform $`x\in\{-1,1\}^n` write
$$`
S_n(x)=\frac1{\sqrt n}\sum_{i=1}^n x_i,
\qquad
f_n(x)=1\{S_n(x)>t\}.
`
The symmetry of $`f_n` gives, for every $`i\in[n]`,
$$`
\widehat f_n(\{i\})
=\frac1{\sqrt n}\mathbb E[f_nS_n],
\qquad
\mathbf W^1[f_n]=\bigl(\mathbb E[f_nS_n]\bigr)^2.
`
The Central Limit Theorem and uniform integrability imply, for
$`Z\sim N(0,1)`,
$$`
\mathbb E[f_n]\longrightarrow\Pr[Z>t]=\bar\Phi(t),
\qquad
\mathbb E[f_nS_n]\longrightarrow
\mathbb E[Z1\{Z>t\}]=\phi(t).
`
Consequently
$`\mathbf W^1[f_n]\to\phi(t)^2`.
:::

:::proposition "proposition-5.25" (lean := "FABL.proposition5_25") (uses := "support-exercise-5.30") (tags := "section-5-4, fidelity-exact")
*Proposition 5.25.* Fix $`t\in\mathbb R`. For each $`n`, define the linear
threshold function $`f_n:\{-1,1\}^n\to\{0,1\}` by
$$`
f_n(x)=1
\quad\Longleftrightarrow\quad
\frac1{\sqrt n}\sum_{i=1}^n x_i>t.
`
Equivalently, $`f_n` is the indicator of the Hamming ball
$$`
\left\{
x:\Delta(x,(1,\ldots,1))<\frac n2-\frac{t\sqrt n}{2}
\right\}.
`
Then
$$`
\lim_{n\to\infty}\mathbb E[f_n]=\bar\Phi(t),
\qquad
\lim_{n\to\infty}\mathbf W^1[f_n]=\phi(t)^2.
`
:::

:::definition "definition-5.26" (lean := "FABL.standardGaussianUpperTail, FABL.standardGaussianUpperTail_eq_measureReal_Ioi, FABL.standardGaussianUpperTail_pos, FABL.standardGaussianUpperTail_lt_one, FABL.standardGaussianUpperTail_strictAnti, FABL.continuous_standardGaussianUpperTail, FABL.tendsto_standardGaussianUpperTail_atTop, FABL.tendsto_standardGaussianUpperTail_atBot, FABL.standardGaussianUpperTail_neg, FABL.standardGaussianUpperTailOpen, FABL.strictMono_standardGaussianUpperTailOpen, FABL.surjective_standardGaussianUpperTailOpen, FABL.standardGaussianUpperTailOrderIso, FABL.standardGaussianUpperTailOrderIso_apply, FABL.standardGaussianUpperQuantile, FABL.standardGaussianUpperTail_quantile, FABL.standardGaussianUpperQuantile_upperTail, FABL.standardGaussianUpperQuantile_one_sub, FABL.gaussianIsoperimetric, FABL.gaussianIsoperimetric_zero, FABL.gaussianIsoperimetric_one, FABL.gaussianIsoperimetric_apply_of_mem_Ioo, FABL.gaussianIsoperimetric_mem_Icc, FABL.gaussianIsoperimetric_symm") (uses := "notation-5.14") (tags := "section-5-4, fidelity-exact")
*Definition 5.26.* The *Gaussian isoperimetric function*
$$`
U:[0,1]\longrightarrow
\left[0,\frac1{\sqrt{2\pi}}\right]
`
is defined on $`0<\alpha<1` by
$$`
U(\alpha)
=\phi\bigl(\bar\Phi^{-1}(\alpha)\bigr),
`
and by $`U(0)=U(1)=0`. Thus
$$`
U=\phi\circ\bar\Phi^{-1}.
`
The symmetry $`\bar\Phi(t)=\Phi(-t)` and
$`\phi(t)=\phi(-t)` also give
$$`
U=\phi\circ\Phi^{-1},
\qquad
U(\alpha)=U(1-\alpha).
`
:::

:::lemma_ "support-standard-gaussian-mills-ratio" (lean := "FABL.standardGaussianUpperTail_eq_integral_density, FABL.standardGaussianUpperTail_le_density_div, FABL.density_mul_t_div_one_add_sq_le_standardGaussianUpperTail, FABL.tendsto_standardGaussianUpperTail_div_density_div, FABL.standardGaussianUpperTail_isEquivalent_density_div") (uses := "notation-5.14") (tags := "section-5-4, support, fidelity-exact")
*Standard Gaussian Mills ratio.* For every $`t>0`,
$$`
\frac{t}{1+t^2}\phi(t)
\le\bar\Phi(t)
\le\frac{\phi(t)}{t}.
`
Consequently,
$$`
\bar\Phi(t)\sim\frac{\phi(t)}{t}
\qquad\text{as }t\to+\infty.
`
:::

:::proposition "proposition-5.27" (lean := "FABL.tendsto_standardGaussianUpperQuantile_atBot, FABL.log_inv_standardGaussianUpperTail_isEquivalent_sq, FABL.tendsto_sqrt_two_mul_log_inv_standardGaussianUpperTail_div, FABL.standardGaussianUpperQuantile_isEquivalent_sqrt_log_inv, FABL.gaussianIsoperimetric_isEquivalent_probability_mul_quantile, FABL.gaussianIsoperimetric_isEquivalent_atBot") (uses := "definition-5.26, support-standard-gaussian-mills-ratio") (tags := "section-5-4, fidelity-exact")
*Proposition 5.27.* As $`\alpha\to0^+`, the Gaussian isoperimetric function
satisfies
$$`
U(\alpha)
\sim
\alpha\sqrt{2\ln(1/\alpha)}.
`
Here $`\ln` denotes the natural logarithm.
:::

:::lemma_ "lemma-5.31" (lean := "FABL.expect_abs_linearForm_indicator_gt_le") (uses := "support-exercise-5.31") (tags := "section-5-4, fidelity-exact")
*Lemma 5.31.* Let
$$`
\ell(x)=a_1x_1+\cdots+a_nx_n,
\qquad
\sum_{i=1}^n a_i^2=1.
`
For every $`s\ge1`,
$$`
\mathbb E\!\left[
  1\{|\ell(x)|>s\}\,|\ell(x)|
\right]
\le
(2s+2)\exp(-s^2/2).
`
:::

:::theorem "level-1-inequality" (lean := "FABL.fourierWeightAtLevel_one_eq_zero_of_zero_one_mean_eq_zero, FABL.exists_levelOneInequality_constant") (uses := "lemma-5.31, plancherel, definition-1.19") (tags := "section-5-4, fidelity-exact")
*Level-1 Inequality.* There is a universal constant $`C` such that if
$`f:\{-1,1\}^n\to\{0,1\}` has
$$`
\mathbb E[f]=\alpha,
\qquad
0<\alpha\le\frac12,
`
then
$$`
\mathbf W^1[f]
\le C\alpha^2\log_2(1/\alpha).
`
If $`\alpha=0`, then $`\mathbf W^1[f]=0`; for
$`\alpha\ge1/2`, the corresponding small-set estimate is obtained by
replacing $`f` with $`1-f`.
:::

:::lemma_ "remark-5.28" (lean := "FABL.sharpLevelOneInequality_eq_zero, FABL.sharpLevelOneInequality, FABL.sharpLevelOneSignedCounterexample, FABL.sharpLevelOneSignedCounterexample_mem_Icc, FABL.mean_abs_sharpLevelOneSignedCounterexample, FABL.fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample, FABL.not_sharpLevelOneInequality_signed") (uses := "level-1-inequality") (tags := "section-5-4, erratum, fidelity-corrected-false-printed-codomain")
*Remark 5.28 (sharp Level-1 Inequality).* The Level-1 bound has the sharp
form
$$`
\mathbf W^1[f]\le2\alpha^2\ln(1/\alpha).
`
More generally, this holds for every
$`f:\{-1,1\}^n\to[0,1]` with
$$`
\alpha=\mathbb E[f],
\qquad
0<\alpha\le\frac12.
`
For $`\alpha=0` the conclusion is $`\mathbf W^1[f]=0`. In particular,
Hamming balls are asymptotic maximizers of degree-$`1` Fourier weight among
sets whose volume $`\alpha` tends to $`0`. Here $`\ln` is the natural
logarithm.

The printed signed generalization is false. Already for
$`f(x_1,x_2)=(x_1+x_2)/2`, one has
$`\mathbb E[|f|]=1/2` and $`\mathbf W^1[f]=1/2`, whereas the displayed
right-hand side is $`(\ln 2)/2<1/2`.
:::

:::lemma_ "remark-5.29" (tags := "section-5-4, nondependency, bibliographic")
*Remark 5.29.* The name “Level-1 Inequality” is not standard. In additive
combinatorics the result is called *Chang's Inequality*. The terminology used
here anticipates the Level-$`k` Inequalities of Chapter 9.5.
:::

:::theorem "two-div-pi-theorem" (lean := "FABL.exists_two_div_pi_constant") (uses := "theorem-5.16, berry-esseen-theorem, remark-5.15, support-exercise-5.16, plancherel, definition-1.19") (tags := "section-5-4, fidelity-exact")
*The 2/$`\pi` Theorem.* There is a universal constant $`C` such that the
following holds. Let $`0<\epsilon\le1` and let
$`f:\{-1,1\}^n\to\{-1,1\}` satisfy
$$`
|\widehat f(\{i\})|\le\epsilon
\qquad\text{for every }i\in[n].
`
Then
$$`
\mathbf W^1[f]\le\frac2\pi+C\epsilon.
\tag{5.16}
`
Furthermore, if
$$`
\mathbf W^1[f]\ge\frac2\pi-\epsilon,
`
then
$$`
\Pr_x\!\left[
f(x)\ne\operatorname{sgn}\bigl(f^{=1}(x)\bigr)
\right]
\le C\sqrt\epsilon,
`
where
$$`
f^{=1}(x)=\sum_{i=1}^n\widehat f(\{i\})x_i.
`
Thus a near-extremizer is $`O(\sqrt\epsilon)`-close to the linear threshold
function $`\operatorname{sgn}(f^{=1})`.
:::

:::lemma_ "remark-5.30" (tags := "section-5-4, nondependency, explanatory")
*Remark 5.30.* For an unbiased Boolean function,
$$`
\operatorname{Stab}_\rho[f]
=\rho\mathbf W^1[f]+O(\rho^2),
\qquad
\frac2\pi\arcsin\rho
=\frac2\pi\rho+O(\rho^3)
`
as $`\rho\to0^+`. Hence the 2/$`\pi` Theorem is the
$`\rho\to0^+` limiting case of the Majority Is Stablest Theorem.
:::

:::lemma_ "support-exercise-5.37" (lean := "FABL.nearlyConstantMinorityIndicator, FABL.nearlyConstantMinorityIndicator_mem_Icc, FABL.mean_nearlyConstantMinorityIndicator, FABL.mean_nearlyConstantMinorityIndicator_nonneg, FABL.mean_nearlyConstantMinorityIndicator_le, FABL.fourierCoeff_nearlyConstantMinorityIndicator_singleton, FABL.fourierWeightAtLevel_one_eq_four_mul_nearlyConstantMinorityIndicator") (uses := "remark-5.28, definition-1.19") (tags := "section-5-4, support, fidelity-exact")
*Exercise 5.37 (nearly constant functions).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` satisfy
$$`
|\mathbb E[f]|\ge1-\delta\ge0.
`
Choose the sign so that
$$`
g=\frac{1\mp f}{2}
`
has mean $`\alpha\le\delta/2`. Then
$$`
\mathbf W^1[f]=4\mathbf W^1[g].
`
Applying the sharp Level-1 Inequality and converting the natural logarithm
to the book's base-$`2` logarithm gives
$$`
\mathbf W^1[f]
\le4\delta^2\log_2(2/\delta).
`
The case $`\delta=0` is interpreted by the conclusion
$`\mathbf W^1[f]=0`.
:::

:::corollary "corollary-5.32" (lean := "FABL.fourierWeightAtLevel_one_le_of_abs_mean_ge") (uses := "support-exercise-5.37") (tags := "section-5-4, fidelity-exact")
*Corollary 5.32.* Let
$`f:\{-1,1\}^n\to\{-1,1\}` satisfy
$$`
|\mathbb E[f]|\ge1-\delta\ge0.
`
Then
$$`
\mathbf W^1[f]\le4\delta^2\log_2(2/\delta).
`
For $`\delta=0`, the right-hand side is understood as $`0`.
:::

:::lemma_ "support-exercise-2.49" (lean := "FABL.balancedFKNLift, FABL.balancedFKNLift_fin_cons_one, FABL.balancedFKNLift_fin_cons_neg_one, FABL.mean_balancedFKNLift, FABL.fourierWeightAtLevel_one_balancedFKNLift, FABL.exists_isKJunta_one_relativeHammingDist_le_of_fourierWeightAtMost_one") (uses := "fkn-theorem, definition-1.19") (tags := "section-5-4, support, fidelity-exact")
*Exercise 2.49 (balanced lift for FKN).* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\mathbf W^{\le1}[f]\ge1-\delta.
`
Define $`g:\{-1,1\}^{n+1}\to\{-1,1\}` by
$$`
g(x_0,x)=x_0f(x_0x),
`
where $`x_0x=(x_0x_1,\ldots,x_0x_n)`. Then
$$`
\mathbb E[g]=0,
\qquad
\mathbf W^1[g]=\mathbf W^{\le1}[f].
`
Applying the balanced FKN Theorem to $`g` and translating its dictator or
negated-dictator conclusion back to $`f` shows that $`f` is
$`O(\delta)`-close to a $`1`-junta. The same construction preserves the
chosen FKN closeness constant.
:::

:::lemma_ "support-exercise-5.38" (lean := "FABL.fknImprovementEta, FABL.exercise5_38a, FABL.exercise5_38b, FABL.exercise5_38_nonnegative_lower_bound, FABL.exercise5_38_sqrt_lower_bound") (tags := "section-5-4, support, fidelity-exact")
*Exercise 5.38 (numerical details for Theorem 5.33).* Let $`C\ge1`,
$`\delta>0`, and
$$`
\eta
=16C^2\delta^2
  \max\!\left(\log_2\!\left(\frac1{C\delta}\right),1\right).
`
Complete the two numerical steps in the proof:

(a) If $`\delta>1/(10C)`, then
$$`
1-\frac\delta2-2\eta<0.
`

(b) If $`0<\delta\le1/(10C)`, then
$$`
1-\delta
-16C^2\delta^2\log_2\!\left(\frac1{C\delta}\right)
\ge
\left(1-\frac\delta2-2\eta\right)^2.
`
Consequently, any nonnegative number whose square is at least the left-hand
side in (b) is at least $`1-\delta/2-2\eta`.
:::

:::theorem "theorem-5.33" (lean := "FABL.improvedFKN") (uses := "fkn-theorem, support-exercise-2.49, corollary-5.32, corollary-3.22, support-exercise-5.38") (tags := "section-5-4, fidelity-explicit-positive-arity")
*Theorem 5.33.* Let $`n\ge1`. Suppose the FKN Theorem holds with closeness bound
$`C\delta`, where $`C\ge1` is a universal constant: whenever
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\mathbf W^1[f]\ge1-\delta\ge0,
`
the function $`f` is $`C\delta`-close to a dictator or negated dictator.
Then the same conclusion holds with the improved bound
$$`
\frac\delta4+\eta,
\qquad
\eta
=16C^2\delta^2
  \max\!\left(\log_2\!\left(\frac1{C\delta}\right),1\right).
`
At $`\delta=0`, this expression is understood by continuity as $`0`.
Thus FKN admits the essentially optimal closeness bound
$`\delta/4+O(\delta^2\log(1/\delta))`.
:::
