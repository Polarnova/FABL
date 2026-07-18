/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter05.LinearThresholdFunctions
import FABL.Chapter05.SparsePolynomialApproximation
import FABL.Chapter05.IntegralThresholdRepresentations
import FABL.Chapter05.InnerProductModTwo
import FABL.Chapter05.KhintchineKahane
import FABL.Chapter05.ChowTheorem
import FABL.Chapter05.LinearThresholdLevelOne

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Linear threshold functions and polynomial threshold functions" =>

:::lemma_ "support-exercise-2.55-khintchine-kahane" (lean := "FABL.rademacherNorm, FABL.two_mul_variance_le_totalInfluence_of_even, FABL.rademacherNorm_even, FABL.laplacian_rademacherNorm_le, FABL.two_mul_variance_rademacherNorm_le_secondMoment, FABL.khintchineKahane, FABL.rademacherNorm_two_equal_weights_moments, FABL.khintchineKahane_constant_le_inv_sqrt_two") (uses := "definition-1.3") (tags := "section-5-1, support, fidelity-exact")
*Exercise 2.55 (Khintchine--Kahane Inequality).* Let $`V` be a real normed
vector space, fix $`w_1,\ldots,w_n\in V`, and define
$$`
g(x)=\left\lVert\sum_{i=1}^n x_iw_i\right\rVert
\qquad (x\in\{-1,1\}^n).
`

(a) Show that the Boolean-cube Laplacian satisfies $`Lg\le g` pointwise.

(b) Deduce $`2\operatorname{Var}[g]\le\mathbb E[g^2]` and hence
$$`
\mathbb E_x\left[\left\lVert\sum_{i=1}^n x_iw_i\right\rVert\right]
\ge \frac1{\sqrt2}
\left(
  \mathbb E_x\left[\left\lVert\sum_{i=1}^n x_iw_i\right\rVert^2\right]
\right)^{1/2}.
`

(c) The constant $`1/\sqrt2` is optimal, even for $`V=\mathbb R`.
:::

:::lemma_ "support-exercise-3.9" (lean := "FABL.abs_fourierCoeff_le_uniformLpNorm_one, FABL.abs_apply_le_fourierOneNorm") (uses := "theorem-1.1, proposition-1.8, definition-3.8") (tags := "section-5-1, support, fidelity-exact")
*Exercise 3.9 (the endpoint Hausdorff--Young inequalities).* For every
$`f:\{-1,1\}^n\to\mathbb R`,
$$`
\lVert\widehat f\rVert_\infty\le\lVert f\rVert_1,
\qquad
\lVert f\rVert_\infty\le\lVert\widehat f\rVert_1.
`
:::

:::lemma_ "support-exercise-1.1g-inner-product-mod-two" (lean := "FABL.f₂CubeBlockEquiv, FABL.joinF₂CubeBlocks, FABL.f₂CubeBlockEquiv_joinF₂CubeBlocks, FABL.joinF₂CubeBlocks_castAdd, FABL.joinF₂CubeBlocks_natAdd, FABL.joinF₂CubeBlocks_addNat, FABL.innerProductModTwoBit, FABL.innerProductModTwo, FABL.innerProductModTwoBoolean, FABL.innerProductModTwoBit_joinF₂CubeBlocks, FABL.f₂DotProduct_joinF₂CubeBlocks, FABL.innerProductModTwo_joinF₂CubeBlocks, FABL.vectorWalshCharacter_joinF₂CubeBlocks, FABL.vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks, FABL.abs_vectorFourierCoeff_innerProductModTwo, FABL.innerProductModTwoBoolean_toReal, FABL.abs_fourierCoeff_innerProductModTwoBoolean") (uses := "equation-3.1, theorem-1.1") (tags := "section-5-1, support, fidelity-exact")
*Exercise 1.1(g) (inner product modulo $`2`).* Define
$$`
\operatorname{IP}_{2n}(x,y)=(-1)^{x\cdot y},
\qquad x,y\in\mathbb F_2^n.
`
For $`a,b\in\mathbb F_2^n`, its Fourier coefficients are
$$`
\widehat{\operatorname{IP}_{2n}}(a,b)
=2^{-n}(-1)^{a\cdot b}.
`
In particular every Fourier coefficient has absolute value $`2^{-n}`.
:::

:::definition "definition-5.4" (lean := "FABL.IsPolynomialThresholdRepresentation, FABL.IsPolynomialThreshold") (uses := "support-exercise-1.10-degree") (tags := "section-5-1, fidelity-exact")
*Definition 5.4.* A function $`f:\{-1,1\}^n\to\{-1,1\}` is a
*polynomial threshold function* (PTF) of degree at most $`k` if there is a
real polynomial $`p:\{-1,1\}^n\to\mathbb R` of degree at most $`k` such that
$$`
f(x)=\operatorname{sgn}(p(x))
`
for every $`x\in\{-1,1\}^n`.
:::

:::lemma_ "support-exercise-5.1" (lean := "FABL.exists_integer_linearThresholdRepresentation, FABL.exists_integer_polynomialThresholdRepresentation") (uses := "definition-2.5, definition-5.4, theorem-1.1") (tags := "section-5-1, support, fidelity-exact")
*Exercise 5.1 (integral threshold representations).* 

(a) Every linear threshold function has a representation
$$`
f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)
`
with $`a_0,a_1,\ldots,a_n\in\mathbb Z`. The representation may be chosen so
that the affine form is nonzero at every point of the discrete cube.

(b) More generally, every degree-$`d` polynomial threshold function has a
degree-$`d` representation whose polynomial coefficients are all integers;
again the representing polynomial may be chosen nonzero on the discrete
cube.
:::

:::theorem "theorem-5.1" (lean := "FABL.eq_of_isLinearThreshold_of_fourierCoeff_eq") (uses := "definition-2.5, support-exercise-5.1, plancherel") (tags := "section-5-1, fidelity-exact")
*Theorem 5.1 (Chow's Theorem).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be a linear threshold function and let
$`g:\{-1,1\}^n\to\{-1,1\}` be arbitrary. If
$$`
\widehat g(S)=\widehat f(S)
\qquad\text{for every }S\subseteq[n]\text{ with }|S|\le1,
`
then $`g=f`.
:::

:::lemma_ "support-exercise-5.5" (lean := "FABL.affineLinearForm, FABL.homogenizedAffineLinearForm, FABL.homogenizedAffineLinearForm_fin_cons, FABL.uniformLpNorm_one_homogenizedAffineLinearForm, FABL.uniformLpNorm_two_sq_homogenizedAffineLinearForm, FABL.uniformLpNorm_two_homogenizedAffineLinearForm, FABL.affineKhintchineKahane") (uses := "definition-1.3, definition-2.5, support-exercise-2.55-khintchine-kahane, support-exercise-5.1, plancherel") (tags := "section-5-1, support, fidelity-exact")
*Exercise 5.5 (homogenizing an affine form).* Let
$$`
\ell(x)=a_0+a_1x_1+\cdots+a_nx_n
`
on $`\{-1,1\}^n`, and define
$$`
\widetilde\ell(x_0,x_1,\ldots,x_n)
=a_0x_0+a_1x_1+\cdots+a_nx_n
`
on $`\{-1,1\}^{n+1}`.

(a) Show that
$`\lVert\widetilde\ell\rVert_1=\lVert\ell\rVert_1` and
$`\lVert\widetilde\ell\rVert_2^2=\lVert\ell\rVert_2^2`.

(b) Use this homogenization and the Khintchine--Kahane Inequality to complete
the proof of Theorem 5.2 for affine, rather than homogeneous, linear forms.
:::

:::theorem "theorem-5.2" (lean := "FABL.fourierDegree_affineLinearForm_le_one, FABL.one_half_le_fourierWeightAtMost_one_of_isLinearThreshold") (uses := "definition-1.19, support-exercise-5.5") (tags := "section-5-1, fidelity-exact")
*Theorem 5.2.* If $`f:\{-1,1\}^n\to\{-1,1\}` is a linear threshold
function, then
$$`
\mathbf W^{\le1}[f]\ge\frac12.
`
:::

:::theorem "conjecture-5.3" (uses := "theorem-5.2, support-exercise-2.22") (tags := "section-5-1, open, conjecture")
*Conjecture 5.3.* Every linear threshold function
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies
$$`
\mathbf W^{\le1}[f]\ge\frac2\pi.
`
This conjecture remains open.
:::

:::lemma_ "example-5.5" (lean := "FABL.fourBitEquality, FABL.fourBitEqualityPolynomial, FABL.fourBitEquality_polynomialThresholdRepresentation, FABL.fourierDegree_fourBitEqualityPolynomial_le, FABL.fourBitEquality_isPolynomialThreshold, FABL.polynomialSparsity_fourBitEqualityPolynomial") (uses := "definition-5.4") (tags := "section-5-1, fidelity-exact")
*Example 5.5.* Let $`f:\{-1,1\}^4\to\{-1,1\}` be the four-bit equality
function, equal to $`1` exactly when all four input bits are equal. Then $`f`
is a degree-$`2` polynomial threshold function, since
$$`
f(x)=\operatorname{sgn}\bigl(
-3+x_1x_2+x_1x_3+x_1x_4+x_2x_3+x_2x_4+x_3x_4
\bigr).
`
This displayed representation has sparsity $`7` in the sense of
Definition 5.7.
:::

:::proposition "proposition-5.6" (lean := "FABL.exists_polynomialThreshold_relativeHammingDist_le_three_mul_noiseSensitivity") (uses := "definition-1.29, definition-5.4, proposition-3.3, proposition-3.31") (tags := "section-5-1, fidelity-exact-natural-cutoff")
*Proposition 5.6.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and
$`\delta\in(0,1/2]`. Then $`f` is
$`3\operatorname{NS}_\delta[f]`-close to a polynomial threshold function of
degree at most $`1/\delta`.
:::

:::definition "definition-5.7" (lean := "FABL.polynomialSparsity") (uses := "definition-5.4, support-exercise-1.10-degree") (tags := "section-5-1, fidelity-exact")
*Definition 5.7.* A polynomial threshold representation
$`f(x)=\operatorname{sgn}(p(x))` has *sparsity at most $`s`* if $`p` is a
multilinear polynomial containing at most $`s` nonzero monomial terms.
:::

:::lemma_ "support-exercise-5.9" (lean := "FABL.eq_of_polynomialThresholdRepresentation_of_fourierCoeff_eq") (uses := "definition-5.4, support-exercise-5.1, plancherel") (tags := "section-5-1, support, fidelity-exact")
*Exercise 5.9 (generalized Chow argument).* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` has a degree-at-most-$`k` polynomial threshold
representation $`f=\operatorname{sgn}(p)` whose representing polynomial is
nonzero on the discrete cube. If $`g:\{-1,1\}^n\to\{-1,1\}` has
$`\widehat g(S)=\widehat f(S)` for every $`|S|\le k`, prove $`g=f` by applying
the pointwise inequality $`f(x)p(x)\ge g(x)p(x)` and Plancherel's Theorem.
:::

:::theorem "theorem-5.8" (lean := "FABL.eq_of_isPolynomialThreshold_of_fourierCoeff_eq") (uses := "support-exercise-5.9") (tags := "section-5-1, fidelity-exact")
*Theorem 5.8.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be a polynomial threshold
function of degree at most $`k`, and let
$`g:\{-1,1\}^n\to\{-1,1\}` be arbitrary. If
$$`
\widehat g(S)=\widehat f(S)
\qquad\text{for every }S\subseteq[n]\text{ with }|S|\le k,
`
then $`g=f`.
:::

:::theorem "post-theorem-9.22" (tags := "section-5-1, support, deferred, later-chapter-dependency")
*Theorem 9.22 (hypercontractive norm comparison).* If
$`p:\{-1,1\}^n\to\mathbb R` has degree at most $`k`, then
$$`
\lVert p\rVert_2\le e^k\lVert p\rVert_1.
`
More generally, for every $`1\le r\le2`,
$$`
\lVert p\rVert_2
\le \exp\bigl(k(2/r-1)\bigr)\lVert p\rVert_r.
`
The proof is deferred to Chapter 9. The full range $`1\le r\le2` is needed
below; a weaker local estimate does not suffice.
:::

:::theorem "theorem-5.9" (uses := "definition-1.19, definition-5.4, plancherel, post-theorem-9.22") (tags := "section-5-1, deferred, later-chapter-dependency")
*Theorem 5.9.* If $`f:\{-1,1\}^n\to\{-1,1\}` is a degree-$`k`
polynomial threshold function, then
$$`
\mathbf W^{\le k}[f]\ge e^{-2k}.
`
:::

:::theorem "theorem-5.10" (lean := "FABL.one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation") (uses := "definition-5.7, support-exercise-3.9, plancherel") (tags := "section-5-1, fidelity-corrected-book-omission")
*Theorem 5.10.* Let $`\mathcal F\subseteq2^{[n]}` and suppose
$`f:\{-1,1\}^n\to\{-1,1\}` has a polynomial threshold representation by a
nonzero polynomial
$$`
f(x)=\operatorname{sgn}(p(x)),
\qquad
p(x)=\sum_{S\in\mathcal F}\widehat p(S)x^S.
`
Then
$$`
\sum_{S\in\mathcal F}|\widehat f(S)|\ge1.
`

The printed statement omits the nonzero condition, although its proof cancels
$`\lVert\widehat p\rVert_\infty`. Since the book fixes
$`\operatorname{sgn}(0)=1`, the omission creates the counterexample
$`p\equiv0`, $`f\equiv1`, $`\mathcal F=\varnothing`. Thus the hypothesis
$`p\not\equiv0` is necessary.
:::

:::corollary "corollary-5.11" (lean := "FABL.pow_two_le_polynomialSparsity_innerProductModTwo, FABL.innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks, FABL.pow_two_le_polynomialSparsity_innerProductModTwo_of_pos") (uses := "definition-5.7, theorem-5.10, support-exercise-1.1g-inner-product-mod-two") (tags := "section-5-1, fidelity-exact-positive-dimension")
*Corollary 5.11.* Every polynomial threshold representation of the inner
product modulo $`2` function
$`\operatorname{IP}_{2n}:\mathbb F_2^{2n}\to\{-1,1\}` has sparsity at least
$`2^n`.

For $`n>0`,
$`\operatorname{IP}_{2n}` takes the value $`-1` and hence every representing
polynomial is automatically nonzero, so Theorem 5.10 applies directly. In
arbitrary dimension the same conclusion holds under the explicit hypothesis
that the representing polynomial is nonzero. At $`n=0`, the zero polynomial
represents the constant-one function under the convention
$`\operatorname{sgn}(0)=1`.
:::

:::theorem "theorem-5.12" (lean := "FABL.exists_sparsePolynomial_uniformApproximation") (uses := "theorem-1.1, definition-3.8, definition-5.7, support-exercise-3.9") (tags := "section-5-1, fidelity-explicit-positive-arity")
*Theorem 5.12.* Let $`n\ge1`, let $`f:\{-1,1\}^n\to\mathbb R`, let
$`\delta>0`, and let $`s` be an integer satisfying
$$`
s\ge \frac{4n\lVert\widehat f\rVert_1^2}{\delta^2}.
`
Then there is a multilinear polynomial
$`q:\{-1,1\}^n\to\mathbb R` of sparsity at most $`s` such that
$$`
\lVert f-q\rVert_\infty<\delta.
`

The positive-arity condition is necessary for the displayed integer bound:
when $`n=0`, a nonzero constant $`f`, $`s=0`, and sufficiently small
$`\delta` satisfy the printed numerical hypothesis but admit no
zero-sparsity approximation.
:::

:::corollary "corollary-5.13" (lean := "FABL.exists_polynomialThresholdRepresentation_sparsity_le_ceil, FABL.exists_parityMajorityRepresentation") (uses := "definition-5.4, definition-5.7, theorem-5.12") (tags := "section-5-1, fidelity-explicit-positive-arity")
*Corollary 5.13.* Let $`n\ge1`. Every
$`f:\{-1,1\}^n\to\{-1,1\}` has a polynomial
threshold representation of sparsity at most
$$`
s=\left\lceil4n\lVert\widehat f\rVert_1^2\right\rceil.
`
Indeed, $`f` can be represented as a majority of $`s` parities or negated
parities.
:::
