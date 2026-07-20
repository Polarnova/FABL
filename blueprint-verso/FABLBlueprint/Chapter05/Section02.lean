/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.BerryEsseenConsequences
import FABL.Chapter05.CorrelatedMajority
import FABL.Chapter05.RegularThresholdNoiseStability
import FABL.Chapter05.MajorityNoiseStability
import FABL.Chapter05.GaussianThresholds
import FABL.Chapter05.BerryEsseenIntervals
import FABL.Chapter05.BerryEsseenRescaling
import FABL.Chapter05.RademacherFirstMoment

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Majority, and the Central Limit Theorem" =>

:::definition "notation-5.14" (parent := "fabl-chapter-5") (lean := "ProbabilityTheory.gaussianPDFReal, ProbabilityTheory.gaussianReal, ProbabilityTheory.cdf, ProbabilityTheory.stdGaussian, ProbabilityTheory.multivariateGaussian") (tags := "section-5-2, fidelity-direct-mathlib")
*Notation 5.14.* We write $`Z\sim N(0,1)` when $`Z` is a standard Gaussian
random variable. Its probability density function, cumulative distribution
function, and complementary cumulative distribution function are denoted by
$$`
\phi(z)=\frac1{\sqrt{2\pi}}e^{-z^2/2},
\qquad
\Phi(t)=\int_{-\infty}^{t}\phi(z)\,dz,
\qquad
\overline\Phi(t)=\Phi(-t)=\int_t^\infty\phi(z)\,dz.
`
More generally, if $`\mu\in\mathbb R^d` and
$`\Sigma\in\mathbb R^{d\times d}` is positive semidefinite, then
$`Z\sim N(\mu,\Sigma)` means that $`Z` is a $`d`-dimensional Gaussian random
vector with mean $`\mu` and covariance matrix $`\Sigma`.
:::

:::theorem "berry-esseen-theorem" (parent := "fabl-chapter-5") (lean := "ProbabilityTheory.uniformBerryEsseen_thirdMoment") (uses := "notation-5.14") (tags := "section-5-2, external-probability-dependency, fidelity-explicit-universal-constant")
*Berry--Esseen (Central Limit) Theorem.* Let
$`X_1,\ldots,X_n` be independent real-valued random variables satisfying
$$`
\mathbb E[X_i]=0,
\qquad
\operatorname{Var}[X_i]=\sigma_i^2,
\qquad
\sum_{i=1}^n\sigma_i^2=1.
`
Set $`S=\sum_{i=1}^nX_i`, let $`Z\sim N(0,1)`, and define
$$`
\gamma=\sum_{i=1}^n\lVert X_i\rVert_3^3
      =\sum_{i=1}^n\mathbb E[|X_i|^3].
`
Then for every $`u\in\mathbb R`,
$$`
\bigl|\Pr[S\le u]-\Pr[Z\le u]\bigr|\le c\gamma,
`
where $`c` is a universal constant. For definiteness, the book permits
$`c=.56`.
:::

:::lemma_ "remark-5.15" (parent := "fabl-chapter-5") (lean := "FABL.sum_integral_abs_cube_le_of_ae_abs_le") (uses := "berry-esseen-theorem") (tags := "section-5-2")
*Remark 5.15.* In the setting of the Berry--Esseen Theorem, suppose in
addition that $`|X_i|\le\epsilon` with probability $`1` for every $`i`.
Then
$$`
\begin{aligned}
\gamma
  &=\sum_{i=1}^n\mathbb E[|X_i|^3]\\
  &\le\epsilon\sum_{i=1}^n\mathbb E[|X_i|^2]
   =\epsilon\sum_{i=1}^n\sigma_i^2
   =\epsilon.
\end{aligned}
`
:::

:::lemma_ "support-exercise-5.16" (parent := "fabl-chapter-5") (lean := "FABL.RealInterval, FABL.RealInterval.toSet, FABL.exercise5_16_strict, FABL.exercise5_16_interval") (uses := "berry-esseen-theorem") (tags := "section-5-2, support, external-probability-dependency, fidelity-exact")
*Exercise 5.16 (strict inequalities and intervals).* Under the assumptions
and notation of the Berry--Esseen Theorem:

(a) For every $`u\in\mathbb R`,
$$`
\bigl|\Pr[S<u]-\Pr[Z<u]\bigr|\le c\gamma.
`
The passage from non-strict to strict inequalities uses
$`\lim_{\delta\to0^+}\Pr[Z\le u-\delta]=\Pr[Z\le u]`.

(b) Consequently, for every interval $`I\subseteq\mathbb R`, with arbitrary
choices of open or closed endpoints and allowing unbounded intervals,
$$`
\bigl|\Pr[S\in I]-\Pr[Z\in I]\bigr|\le2c\gamma.
`
:::

:::lemma_ "support-exercise-5.17" (parent := "fabl-chapter-5") (lean := "FABL.exercise5_17") (uses := "berry-esseen-theorem") (tags := "section-5-2, support, external-probability-dependency, fidelity-exact")
*Exercise 5.17 (centering and rescaling Berry--Esseen).* Let
$`X_1,\ldots,X_n` be independent real-valued random variables with finite
means and variances. Write
$$`
S=\sum_{i=1}^nX_i,
\qquad
\mu=\sum_{i=1}^n\mathbb E[X_i],
\qquad
\sigma^2=\sum_{i=1}^n\operatorname{Var}[X_i],
`
and assume $`\sigma^2>0`. If $`Z\sim N(\mu,\sigma^2)` and
$$`
\epsilon
=\sum_{i=1}^n\lVert X_i-\mathbb E[X_i]\rVert_3^3,
`
then for every $`u\in\mathbb R`,
$$`
\bigl|\Pr[S\le u]-\Pr[Z\le u]\bigr|
\le\frac{c\epsilon}{\sigma^3},
`
where $`c` is the same universal constant as in the Berry--Esseen Theorem.
:::

:::lemma_ "support-exercise-5.31" (parent := "fabl-chapter-5") (lean := "FABL.exercise5_31a, FABL.exercise5_31b, FABL.exercise5_31c, FABL.exercise5_31d") (uses := "berry-esseen-theorem, remark-5.15, support-exercise-5.16") (tags := "section-5-2, support, external-probability-dependency, fidelity-explicit-small-parameter-range")
*Exercise 5.31 (absolute first moments).* Let
$`a_1,\ldots,a_n\in\mathbb R` satisfy
$`\sum_{i=1}^na_i^2=1` and $`|a_i|\le\epsilon` for every $`i`. For uniformly
random $`x\in\{-1,1\}^n`, set
$$`
S=\sum_{i=1}^na_ix_i,
`
and let $`Z\sim N(0,1)`.

(a) For every $`t\ge0`,
$$`
\Pr[|S|\ge t]\le2e^{-t^2/2},
\qquad
\Pr[|Z|\ge t]\le2e^{-t^2/2}.
`

(b) Using
$`\mathbb E[|Y|]=\int_0^\infty\Pr[|Y|\ge t]\,dt`, the Berry--Esseen
Theorem, Remark 5.15, and Exercise 5.16, show that for every $`T\ge1`,
$$`
\bigl|\mathbb E[|S|]-\mathbb E[|Z|]\bigr|
\le O\bigl(\epsilon T+e^{-T^2/2}\bigr),
`
with a universal implied constant.

(c) For $`0<\epsilon<1`, deduce
$$`
\left|\mathbb E[|S|]-\sqrt{\frac2\pi}\right|
\le O\left(\epsilon\sqrt{\log(1/\epsilon)}\right).
`

(d) Improve this to the universal bound
$$`
\left|\mathbb E[|S|]-\sqrt{\frac2\pi}\right|\le O(\epsilon)
`
by using the nonuniform Berry--Esseen estimate
$$`
\bigl|\Pr[S\le u]-\Pr[Z\le u]\bigr|
\le\frac{C\gamma}{1+|u|^3}
`
for a universal constant $`C`.

The estimate in part (c) holds with an explicit universal constant on the
standard neighbourhood $`0<\epsilon\le e^{-1}` of zero.
This is the literal small-parameter content of the book's estimate; reading
the displayed $`O(\epsilon\sqrt{\log(1/\epsilon)})` as a uniform bound all
the way to $`\epsilon=1` would be false.
:::

:::theorem "theorem-5.16" (parent := "fabl-chapter-5") (lean := "FABL.exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular") (uses := "support-exercise-5.31") (tags := "section-5-2, fidelity-exact")
*Theorem 5.16.* There is a universal constant $`C` such that the following
holds. If $`a_1,\ldots,a_n\in\mathbb R` satisfy
$$`
\sum_{i=1}^na_i^2=1,
\qquad
|a_i|\le\epsilon\quad\text{for every }i,
`
then
$$`
\left|
\mathbb E_{x\sim\{-1,1\}^n}
  \left[\left|\sum_{i=1}^na_ix_i\right|\right]
-\sqrt{\frac2\pi}
\right|
\le C\epsilon.
`
:::

:::lemma_ "support-exercise-5.19" (parent := "fabl-chapter-5") (lean := "FABL.exercise5_19, FABL.normalizedCorrelatedPairSum_projection_mean, FABL.normalizedCorrelatedPairSum_projection_secondMoment") (uses := "definition-2.41") (tags := "section-5-2, support, fidelity-exact")
*Exercise 5.19 (covariance of the correlated sum).* Let
$`\rho\in[-1,1]`, let $`(x,y)` be a $`\rho`-correlated pair of uniformly
random strings in $`\{-1,1\}^n`, and define the random vector
$$`
\widetilde S
=\sum_{i=1}^n
  \begin{pmatrix}x_i/\sqrt n\\y_i/\sqrt n\end{pmatrix}
\in\mathbb R^2.
\tag{5.7}
`
Then
$$`
\mathbb E[\widetilde S_1]
=\mathbb E[\widetilde S_2]=0,
\qquad
\mathbb E[\widetilde S_1^2]
=\mathbb E[\widetilde S_2^2]=1,
\qquad
\mathbb E[\widetilde S_1\widetilde S_2]=\rho.
`
Equivalently,
$$`
\mathbb E[\widetilde S]
=\begin{pmatrix}0\\0\end{pmatrix},
\qquad
\operatorname{Cov}[\widetilde S]
=\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}.
`
:::

:::theorem "sheppards-formula" (parent := "fabl-chapter-5") (lean := "FABL.sheppardsFormula") (uses := "notation-5.14") (tags := "section-5-2, fidelity-exact-canonical-law")
*Sheppard's Formula.* Let $`z_1,z_2` be standard Gaussian random variables
with correlation
$`\mathbb E[z_1z_2]=\rho\in[-1,1]`. Then
$$`
\Pr[z_1\le0,\ z_2\le0]
=\frac12-\frac12\frac{\arccos\rho}{\pi}.
`
The book defers its rotational-symmetry proof to Example 11.19.
Alternatively, the formula follows directly from the Gaussian-disagreement
identity in Theorem 2.45.
:::

:::theorem "theorem-5.38" (parent := "fabl-chapter-5") (lean := "ProbabilityTheory.exists_bentkus_convex_set_constant") (uses := "notation-5.14") (tags := "section-5-2, external-probability-dependency, fidelity-positive-definite-specialization")
*Theorem 5.38 (multidimensional Berry--Esseen).* There is a universal
constant $`C` with the following property. Let
$`X_1,\ldots,X_n` be independent $`\mathbb R^d`-valued random vectors, each
having mean zero. Set
$$`
S=\sum_{i=1}^nX_i,
\qquad
\Sigma=\operatorname{Cov}[S],
`
and assume that $`\Sigma` is invertible. Let $`Z\sim N(0,\Sigma)`. Then for
every convex set $`U\subseteq\mathbb R^d`,
$$`
\bigl|\Pr[S\in U]-\Pr[Z\in U]\bigr|
\le C d^{1/4}\gamma,
\qquad
\gamma
=\sum_{i=1}^n
  \mathbb E\!\left[
    \left\lVert\Sigma^{-1/2}X_i\right\rVert_2^3
  \right].
`
Here $`\lVert\cdot\rVert_2` is the Euclidean norm on $`\mathbb R^d`.

For a covariance matrix, invertibility is equivalent to positive
definiteness, so the hypothesis may equivalently be written $`\Sigma\succ0`.
:::

:::lemma_ "support-exercise-5.33" (parent := "fabl-chapter-5") (lean := "FABL.correlationMatrix, FABL.exercise5_33a, FABL.exercise5_33b_sameSigns, FABL.exercise5_33b_oppositeSigns, FABL.correlationMatrix_posDef, FABL.regularCorrelatedSignSummand, FABL.regularThresholdPairSummand, FABL.regularThresholdPairSum, FABL.signQuadrant, FABL.measurableSet_signQuadrant, FABL.isConvexSet_signQuadrant, FABL.exists_exercise5_33c_constant") (uses := "definition-2.42, sheppards-formula, support-exercise-5.19, theorem-5.38") (tags := "section-5-2, support, external-probability-dependency, fidelity-exact")
*Exercise 5.33 (the two-dimensional CLT calculation).* Use Theorem 5.38 to
complete the proof of Theorem 5.17.

(a) For
$$`
\Sigma=\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix},
\qquad -1<\rho<1,
`
show that
$$`
\Sigma^{-1}
=
\begin{pmatrix}1&-\rho\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\0&(1-\rho^2)^{-1}\end{pmatrix}
\begin{pmatrix}1&0\\-\rho&1\end{pmatrix}.
`

(b) If $`y=(\pm a,\pm a)^{\mathsf T}\in\mathbb R^2`, compute
$`y^{\mathsf T}\Sigma^{-1}y`. It equals
$$`
\frac{2a^2}{1+\rho}
\quad\text{when the two signs agree},
\qquad
\frac{2a^2}{1-\rho}
\quad\text{when the two signs disagree}.
`

(c) Apply the multidimensional Berry--Esseen estimate to the four quadrants,
use Sheppard's Formula, and complete the proof of Theorem 5.17.
:::

:::theorem "theorem-5.17" (parent := "fabl-chapter-5") (lean := "FABL.exists_noiseStability_sub_arcsine_le_of_regular_homogeneous_threshold") (uses := "definition-2.5, definition-2.42, support-exercise-5.33") (tags := "section-5-2, fidelity-exact")
*Theorem 5.17.* There is a universal constant $`C` such that the following
holds. Let $`f:\{-1,1\}^n\to\{-1,1\}` be an unbiased homogeneous linear
threshold function,
$$`
f(x)=\operatorname{sgn}\left(\sum_{i=1}^na_ix_i\right),
\qquad
\mathbb E[f]=0,
`
whose coefficients satisfy
$$`
\sum_{i=1}^na_i^2=1,
\qquad
|a_i|\le\epsilon\quad\text{for every }i.
`
Then for every $`\rho\in(-1,1)`,
$$`
\left|
\operatorname{Stab}_\rho[f]-\frac2\pi\arcsin\rho
\right|
\le
\frac{C\epsilon}{\sqrt{1-\rho^2}}.
`
:::

:::theorem "theorem-5.18" (parent := "fabl-chapter-5") (lean := "FABL.exists_majorityNoiseStability_constant") (uses := "definition-2.1, definition-2.42, support-exercise-5.23") (tags := "section-5-2, fidelity-exact")
*Theorem 5.18.* There is a universal constant $`C` such that for every
$`\rho\in[0,1)`, the sequence
$`\operatorname{Stab}_\rho[\operatorname{Maj}_n]` is decreasing as $`n`
ranges through the positive odd integers, and for every such $`n`,
$$`
\frac2\pi\arcsin\rho
\le
\operatorname{Stab}_\rho[\operatorname{Maj}_n]
\le
\frac2\pi\arcsin\rho
+
\frac{C}{\sqrt{1-\rho^2}\sqrt n}.
`
:::

:::theorem "majority-is-stablest-theorem" (parent := "fabl-chapter-5") (uses := "definition-2.17, definition-2.42, sheppards-formula") (tags := "section-5-2, deferred, later-chapter-dependency")
*Majority Is Stablest Theorem.* Fix $`\rho\in(0,1)`. If
$`f:\{-1,1\}^n\to[-1,1]` satisfies
$$`
\mathbb E[f]=0,
\qquad
\operatorname{MaxInf}[f]\le\tau,
`
then
$$`
\operatorname{Stab}_\rho[f]
\le\frac2\pi\arcsin\rho+o_\tau(1)
=1-\frac2\pi\arccos\rho+o_\tau(1).
`
Precisely, for every $`\eta>0` there is a $`\tau_0>0`, depending only on
$`\rho` and $`\eta`, such that whenever $`0\le\tau\le\tau_0` the first upper
bound holds with $`\eta` in place of $`o_\tau(1)`.

Section 5.4 proves only the sufficiently-small-$`\rho` case. The full theorem
is deferred to Chapter 11.
:::
