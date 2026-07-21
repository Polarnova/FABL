/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06.FoolingF₂Polynomials
import FABL.Chapter06.Pseudorandomness.InnerProductSupportDensity
import FABL.Chapter06.F₂Polynomials.Examples

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: Fooling F₂-polynomials" =>

:::definition "definition-6.46" (parent := "fabl-chapter-6") (lean := "FABL.ProbabilityDensity.Fools") (uses := "definition-1.20") (tags := "section-6-5, fidelity-exact")
*Definition 6.46.* Let
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` be a probability density and let
$`\mathcal C` be a class of functions
$`\mathbb F_2^n\to\mathbb R`. The density $`\varphi`
*$`\epsilon`-fools* $`\mathcal C` if
$$`
\left|
\mathbb E_{\boldsymbol y\sim\varphi}[f(\boldsymbol y)]
-\mathbb E_{\boldsymbol x\sim\mathbb F_2^n}[f(\boldsymbol x)]
\right|\le\epsilon
`
for every $`f\in\mathcal C`.
:::

:::lemma_ "example-6.47" (parent := "fabl-chapter-6") (lean := "FABL.expect_booleanRealEmbedding_innerProductModTwoBit, FABL.innerProductModTwoSupportDensity_expectation, FABL.innerProductModTwoSupportDensity_expectation_gap") (uses := "definition-6.46, example-6.4, support-exercise-1.1g-inner-product-mod-two, example-6.19, definition-6.20, support-exercise-6.7") (tags := "section-6-5, fidelity-strengthened-exact-value")
*Example 6.47.* Let $`n` be even, let
$`\operatorname{IP}_n:\mathbb F_2^n\to\{0,1\}` be the
inner-product-mod-$`2` function, and let $`\varphi` be the density of the
uniform distribution on its support. The function
$`\operatorname{IP}_n` has $`\mathbb F_2`-degree $`2`, and $`\varphi` is
roughly $`2^{-n/2}`-biased, but
$$`
\mathbb E_{\boldsymbol x\sim\mathbb F_2^n}
  [\operatorname{IP}_n(\boldsymbol x)]
=\frac{1-2^{-n/2}}2,
\qquad
\mathbb E_{\boldsymbol y\sim\varphi}
  [\operatorname{IP}_n(\boldsymbol y)]
=1.
`
Thus a small-biased density need not fool even all
$`\mathbb F_2`-degree-$`2` functions.
:::

:::theorem "external-lvw-fooling" (parent := "fabl-chapter-6") (uses := "definition-6.46, definition-6.20") (tags := "section-6-5, external-result, statement-only")
*Luby--Veličković--Wigderson bound.* There is a generator whose output
distribution $`\epsilon`-fools every $`n`-bit Boolean function of
$`\mathbb F_2`-degree at most $`d` and whose seed uses
$$`
\exp\!\left(
  O\!\left(\sqrt{d\log(n/d)+\log(1/\epsilon)}\right)
\right)
`
independent random bits.

The book quotes this external result for historical comparison and does not
prove it.
:::

:::theorem "external-bogdanov-viola" (parent := "fabl-chapter-6") (uses := "definition-6.46, definition-6.20") (tags := "section-6-5, external-result, statement-only")
*Bogdanov--Viola bounds.* Boolean functions of $`\mathbb F_2`-degree at most
$`2` can be $`\epsilon`-fooled using $`O(\log(n/\epsilon))` independent
random bits. Those of degree at most $`3` can be $`\epsilon`-fooled using
$$`
O(\log n)+\exp(\operatorname{poly}(1/\epsilon))
`
independent random bits.

The book quotes these external bounds without proof.
:::

:::theorem "external-lovett-convolution" (parent := "fabl-chapter-6") (uses := "definition-6.46, definition-6.5, definition-6.20, definition-1.24") (tags := "section-6-5, external-result, statement-only")
*Lovett's convolution bound.* Let
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` be an
$`\epsilon`-biased density. For every
$`f:\mathbb F_2^n\to\{-1,1\}` with
$`\deg_{\mathbb F_2}(f)\le d`,
$$`
\left|
\mathbb E_{\boldsymbol y^{(1)},\ldots,\boldsymbol y^{(2^d)}
                \mathrel{\sim}\varphi}
\!\left[
f\!\left(\boldsymbol y^{(1)}+\cdots+\boldsymbol y^{(2^d)}\right)
\right]
-\mathbb E_{\boldsymbol x\sim\mathbb F_2^n}[f(\boldsymbol x)]
\right|
\le O\!\left(\epsilon^{\,1/4^d}\right).
`
Equivalently, the $`2^d`-fold convolution
$`\varphi^{*2^d}` fools the class of
$`\mathbb F_2`-degree-at-most-$`d` Boolean functions, using
$`2^{O(d)}\log(n/\epsilon)` random bits with a standard small-bias
construction.

The book quotes this external theorem without proof.
:::

:::theorem "viola-theorem" (parent := "fabl-chapter-6") (lean := "FABL.f₂PolynomialSignClass, FABL.isTranslationClosed_f₂PolynomialSignClass, FABL.ProbabilityDensity.IsBiased.violaTheorem") (uses := "definition-6.46, definition-6.5, definition-6.20, definition-6.48, fact-6.49, proposition-6.50, support-exercise-6.29, support-viola-directional-gap, support-viola-convolution-second-moment, support-viola-error-recurrence") (tags := "section-6-5, fidelity-exact")
*Viola's Theorem.* Let
$`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` be an
$`\epsilon`-biased probability density, where $`0\le\epsilon\le1`, and let
$`d\in\mathbb N_{>0}`. Define
$$`
\epsilon_d=9\epsilon^{\,1/2^{d-1}}.
`
Then the $`d`-fold convolution $`\varphi^{*d}`
$`\epsilon_d`-fools all
$`f:\mathbb F_2^n\to\{-1,1\}` with
$`\deg_{\mathbb F_2}(f)\le d`; explicitly,
$$`
\left|
\mathbb E_{\boldsymbol y^{(1)},\ldots,\boldsymbol y^{(d)}
                \mathrel{\sim}\varphi}
\!\left[
f\!\left(\boldsymbol y^{(1)}+\cdots+\boldsymbol y^{(d)}\right)
\right]
-\mathbb E_{\boldsymbol x\sim\mathbb F_2^n}[f(\boldsymbol x)]
\right|
\le 9\epsilon^{\,1/2^{d-1}}.
`
:::

:::corollary "corollary-viola-seed-length" (parent := "fabl-chapter-6") (lean := "FABL.violaBaseBias, FABL.violaBaseBias_pos, FABL.violaBaseBias_le_half, FABL.violaError_baseBias, FABL.violaSmallBiasSeedBits, FABL.violaSmallBiasSampler, FABL.card_violaSmallBiasSamplerSeedSpace, FABL.violaSeedLogBound, FABL.logb_smallBiasSupportEnvelope_eq, FABL.violaSmallBiasSeedBits_le_of_card, FABL.exists_violaSmallBiasDistribution") (uses := "viola-theorem, theorem-6.30") (tags := "section-6-5, fidelity-exact-random-bit-bound")
*Random-bit consequence of Viola's Theorem.* For
$`d\in\mathbb N_{>0}` and $`0<\epsilon\le1`, there is an explicit
distribution that $`\epsilon`-fools every
$`f:\mathbb F_2^n\to\{-1,1\}` of
$`\mathbb F_2`-degree at most $`d` and can be sampled using
$$`
O(d\log n)+O\!\left(d\,2^d\log(1/\epsilon)\right)
`
independent random bits. This follows by applying Viola's Theorem to the
small-biased construction of Theorem 6.30 with its bias parameter chosen to
make $`9\epsilon_0^{\,1/2^{d-1}}\le\epsilon`.
:::

:::definition "definition-6.48" (parent := "fabl-chapter-6") (lean := "FABL.booleanDerivative") (uses := "definition-1.22") (tags := "section-6-5, fidelity-exact")
*Definition 6.48.* For
$`f:\mathbb F_2^n\to\mathbb F_2` and
$`y\in\mathbb F_2^n`, the *directional derivative* of $`f` in direction
$`y` is the function
$`\Delta_yf:\mathbb F_2^n\to\mathbb F_2` defined by
$$`
\Delta_yf(x)=f(x+y)-f(x)=f(x+y)+f(x).
`
The two displayed expressions agree because the codomain is
$`\mathbb F_2`.
:::

:::lemma_ "fact-6.49" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_booleanDerivative_le") (uses := "definition-6.48, definition-6.20") (tags := "section-6-5, fidelity-exact")
*Fact 6.49.* For every
$`f:\mathbb F_2^n\to\mathbb F_2` and
$`y\in\mathbb F_2^n`,
$$`
\deg_{\mathbb F_2}(\Delta_yf)
\le \deg_{\mathbb F_2}(f)-1.
`
For a constant function the right side is interpreted in the natural
truncated-degree convention.
:::

:::proposition "proposition-6.50" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_add_translates_le") (uses := "proposition-6.18, definition-6.20") (tags := "section-6-5, fidelity-exact")
*Proposition 6.50.* Let
$`f:\mathbb F_2^n\to\mathbb F_2` satisfy
$`\deg_{\mathbb F_2}(f)=d`, fix $`y,y'\in\mathbb F_2^n`, and define
$$`
g(x)=f(x+y)-f(x+y').
`
Then
$$`
\deg_{\mathbb F_2}(g)\le d-1.
`
:::

:::lemma_ "support-exercise-6.29" (parent := "fabl-chapter-6") (lean := "FABL.IsTranslationClosed, FABL.ProbabilityDensity.expectation_convolution, FABL.ProbabilityDensity.Fools.convolution_right") (uses := "definition-6.46, definition-3.24, definition-1.24, proposition-1.26") (tags := "section-6-5, support, fidelity-exact")
*Exercise 6.29.* Let $`\mathcal C` be a class of functions
$`\mathbb F_2^n\to\mathbb R` closed under translation: if
$`f\in\mathcal C` and $`z\in\mathbb F_2^n`, then the function
$$`
f^{+z}(x)=f(x+z)
`
also belongs to $`\mathcal C`. If a probability density $`\psi`
$`\epsilon`-fools $`\mathcal C`, then for every probability density
$`\varphi`, the convolution $`\psi*\varphi` also
$`\epsilon`-fools $`\mathcal C`.
:::

:::lemma_ "support-viola-directional-gap" (parent := "fabl-chapter-6") (lean := "FABL.multiplicativeDerivative, FABL.abs_mean_mul_density_gap_le_expect_abs_multiplicativeDerivative_gap") (uses := "definition-6.48, definition-1.20") (tags := "section-6-5, support, fidelity-exact")
*Directional-gap inequality used in Viola's proof.* Let
$`\psi:\mathbb F_2^n\to\mathbb R_{\ge0}` be a probability density and let
$`F:\mathbb F_2^n\to\{-1,1\}`. Define the multiplicative directional
derivative
$$`
D_yF(x)=F(x+y)F(x).
`
Then
$$`
\begin{aligned}
|\mathbb E[F]|\,
\left|
\mathbb E_{z\sim\psi}[F(z)]-\mathbb E[F]
\right|
&\le
\mathbb E_{y\sim\mathbb F_2^n}
\left[
\left|
\mathbb E_{z\sim\psi}[D_yF(z)]
-\mathbb E_{x\sim\mathbb F_2^n}[D_yF(x)]
\right|
\right].
\end{aligned}
`
If $`F(x)=(-1)^{f(x)}` for an
$`\mathbb F_2`-polynomial $`f`, then
$`D_yF(x)=(-1)^{\Delta_yf(x)}`.
:::

:::lemma_ "support-viola-convolution-second-moment" (parent := "fabl-chapter-6") (lean := "FABL.expectation_pair_correlation_eq_expect_convolution_sq, FABL.expect_convolution_sq_eq_sum_sq_vectorFourierCoeff, FABL.expect_convolution_sq_le_sq_mean_add_sq") (uses := "definition-1.24, theorem-1.27, parseval, definition-6.5") (tags := "section-6-5, support, fidelity-exact")
*Convolution second moment used in Viola's proof.* For every probability
density $`\varphi:\mathbb F_2^n\to\mathbb R_{\ge0}` and every
$`F:\mathbb F_2^n\to\mathbb R`,
$$`
\begin{aligned}
&\mathbb E_{y,y'\mathrel{\sim}\varphi}
\mathbb E_{x\sim\mathbb F_2^n}
  [F(x+y)F(x+y')]\\
&\qquad =
\mathbb E_{x\sim\mathbb F_2^n}[(\varphi*F)(x)^2]
=\sum_{\gamma\in\widehat{\mathbb F_2^n}}
  \widehat\varphi(\gamma)^2\widehat F(\gamma)^2.
\end{aligned}
`
Consequently, if $`\varphi` is $`\epsilon`-biased and
$`F:\mathbb F_2^n\to\{-1,1\}`, then
$$`
\mathbb E[(\varphi*F)^2]
\le \mathbb E[F]^2+\epsilon^2.
`
:::

:::lemma_ "support-viola-error-recurrence" (parent := "fabl-chapter-6") (lean := "FABL.violaError, FABL.violaError_succ, FABL.sqrt_violaError, FABL.sq_le_violaError") (tags := "section-6-5, support, fidelity-exact")
*Error recurrence used in Viola's proof.* Let $`0\le\epsilon\le1` and, for
$`d\ge1`, set
$$`
\epsilon_d=9\epsilon^{\,1/2^{d-1}}.
`
Then
$$`
\epsilon_{d+1}=3\sqrt{\epsilon_d},
\qquad
\sqrt{\epsilon_d}=\frac13\epsilon_{d+1},
\qquad
\epsilon^2\le\epsilon_d.
`
:::

:::theorem "external-counting-lower-bound" (parent := "fabl-chapter-6") (uses := "definition-6.46, definition-6.5, definition-6.20") (tags := "section-6-5, external-result, nondependency, statement-only, fidelity-historical-summary")
*Counting lower bound for convolution generators.* The book records the
external historical result that, for each $`d\in\mathbb N_{>0}`, there are
small-bias parameters and dimensions for which a $`d`-fold convolution of
small-biased densities fails to fool some Boolean function of
$`\mathbb F_2`-degree $`d+1`.

The book cites the counting argument establishing this sharp degree boundary
without stating its full quantified parameter theorem, and does not prove it.
This node records the historical claim only and supplies no assumption to
the production library.
:::

:::theorem "external-lovett-tzur-counterexample" (parent := "fabl-chapter-6") (uses := "definition-6.46, definition-6.5, definition-6.20") (tags := "section-6-5, external-result, statement-only")
*Lovett--Tzur explicit counterexample.* For every
$`d\in\mathbb N_{>0}` and $`\ell\ge2d+1`, there are an explicit
$`(\ell/2^n)`-biased density $`\varphi` on
$`\mathbb F_2^{(\ell+1)n}` and an explicit Boolean function
$$`
f:\mathbb F_2^{(\ell+1)n}\to\{-1,1\},
\qquad
\deg_{\mathbb F_2}(f)=d+1,
`
such that
$$`
\left|
\mathbb E_{w\sim\varphi^{*d}}[f(w)]-\mathbb E[f]
\right|
\ge1-\frac{2d}{2^n}.
`

The book quotes this external construction without proof.
:::

:::theorem "remark-6-viola-improvement-open" (parent := "fabl-chapter-6") (uses := "viola-theorem, external-lovett-tzur-counterexample") (tags := "section-6-5, open, problem, statement-only")
*Open problem (the error exponent in Viola's Theorem).* It is unknown whether
the error dependence
$`\epsilon^{\,1/2^{d-1}}` in Viola's Theorem can be improved, even for
$`d=2`. An improvement as modest as replacing it by
$`\epsilon^{\,1/1.99^d}` for degrees as large as $`\log n` would imply
progress on the correlation-bounds-for-polynomials problem.
:::
