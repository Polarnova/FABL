/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter06.F₂Polynomials
import FABL.Chapter06.F₂Polynomials.Interpolation
import FABL.Chapter06.Constructions.BentFunctions
import FABL.Chapter06.Pseudorandomness.CorrelationImmunityBounds

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "F₂-polynomials" =>

:::lemma_ "example-6.17" (parent := "fabl-chapter-6") (lean := "FABL.fourierDegree_parityFunction_univ, FABL.booleanFunctionF₂Encoding_parityFunction, FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_parityFunction_univ") (uses := "support-sign-monomial, equation-3.1") (tags := "section-6-2, erratum, fidelity-corrected-zero-dimensional-convention")
*Example 6.17.* For the parity function on $`n>0` bits, encoding
False and True by $`\pm1\in\mathbb R` gives
$$`
\chi_{[n]}(x)=x_1x_2\cdots x_n,
`
of real degree $`n`. Encoding False and True by $`0,1\in\mathbb F_2` instead
gives
$$`
\chi_{[n]}(x)=x_1+x_2+\cdots+x_n,
`
of $`\mathbb F_2`-degree $`1`.

For $`n=0`, both encodings give the empty parity, whose real and
$`\mathbb F_2` degrees are $`0`.
:::

:::lemma_ "equation-6.1" (parent := "fabl-chapter-6") (lean := "FABL.f₂PointIndicator, FABL.f₂PointIndicator_eq_ite") (uses := "definition-1.22") (tags := "section-6-2, support, fidelity-exact")
*Equation (6.1).* For $`a\in\mathbb F_2^n`, the point indicator
$`\mathbf1_{\{a\}}:\mathbb F_2^n\to\mathbb F_2` is represented by the
multilinear polynomial
$$`
\mathbf1_{\{a\}}(x)
=\prod_{i:a_i=1}x_i\prod_{i:a_i=0}(1-x_i).
`
:::

:::lemma_ "equation-6.2" (parent := "fabl-chapter-6") (lean := "FABL.f₂Interpolation") (uses := "equation-6.1") (tags := "section-6-2, support, fidelity-exact")
*Equation (6.2).* Every $`f:\mathbb F_2^n\to\mathbb F_2` has the
interpolation formula
$$`
f(x)=\sum_{a\in\mathbb F_2^n}f(a)\mathbf1_{\{a\}}(x).
`
:::

:::definition "equation-6.3" (parent := "fabl-chapter-6") (lean := "FABL.ANFCoefficients, FABL.anfMonomial, FABL.anfEval") (uses := "equation-6.2") (tags := "section-6-2, support, fidelity-exact")
*Equation (6.3) (algebraic normal form).* After multilinear simplification,
the interpolation of $`f:\mathbb F_2^n\to\mathbb F_2` has the form
$$`
f(x)=\sum_{S\subseteq[n]}c_Sx^S,
\qquad
x^S=\prod_{i\in S}x_i,
\qquad c_S\in\mathbb F_2.
`
This is called the $`\mathbb F_2`-polynomial representation, or algebraic
normal form, of $`f`.
:::

:::lemma_ "equation-6.4" (parent := "fabl-chapter-6") (lean := "FABL.threeBitParity_integer_interpolation, FABL.threeBitParity_f₂_interpolation") (uses := "example-6.17, equation-6.2") (tags := "section-6-2, support, fidelity-exact")
*Equation (6.4).* Interpolating the three-bit parity function first over the
integers gives
$$`
\begin{aligned}
\chi_{[3]}(x)
&=(1-x_1)(1-x_2)x_3+(1-x_1)x_2(1-x_3)\\
&\quad+x_1(1-x_2)(1-x_3)+x_1x_2x_3\\
&=x_1+x_2+x_3-2(x_1x_2+x_1x_3+x_2x_3)+4x_1x_2x_3.
\end{aligned}
`
Reducing the coefficients modulo $`2` yields
$`\chi_{[3]}(x)=x_1+x_2+x_3` over $`\mathbb F_2`.
:::

:::proposition "proposition-6.18" (parent := "fabl-chapter-6") (lean := "FABL.anfEval_anfCoeff, FABL.anfEval_injective, FABL.existsUnique_anfEval") (uses := "equation-6.1, equation-6.2, equation-6.3") (tags := "section-6-2, fidelity-exact")
*Proposition 6.18.* Every function
$`f:\mathbb F_2^n\to\mathbb F_2` has a unique multilinear
$`\mathbb F_2`-polynomial representation
$$`
f(x)=\sum_{S\subseteq[n]}c_Sx^S.
`
:::

:::lemma_ "example-6.19" (parent := "fabl-chapter-6") (lean := "FABL.f₂AndFunction, FABL.f₂AndFunction_apply, FABL.functionAlgebraicDegree_f₂AndFunction, FABL.innerProductModTwoBit_joinF₂CubeBlocks_eq_sum, FABL.innerProductModTwoBit_eq_sum_anfMonomial, FABL.functionAlgebraicDegree_innerProductModTwoBit") (uses := "proposition-6.18, support-exercise-1.1g-inner-product-mod-two") (tags := "section-6-2, fidelity-exact")
*Example 6.19.* The logical AND and inner-product-mod-$`2` functions have
the algebraic normal forms
$$`
\operatorname{AND}_n(x)=x_1x_2\cdots x_n
`
and
$$`
\operatorname{IP}_{2n}(x_1,\ldots,x_n,y_1,\ldots,y_n)
=x_1y_1+x_2y_2+\cdots+x_ny_n.
`
:::

:::definition "definition-6.20" (parent := "fabl-chapter-6") (lean := "FABL.algebraicDegree, FABL.functionAlgebraicDegree") (uses := "proposition-6.18, support-exercise-1.10-degree") (tags := "section-6-2, fidelity-exact")
*Definition 6.20.* The *$`\mathbb F_2`-degree* of a Boolean function $`f`,
written $`\deg_{\mathbb F_2}(f)`, is the degree of its unique
$`\mathbb F_2`-polynomial representation. The notation $`\deg(f)` remains
reserved for the degree of the real Fourier expansion.
:::

:::lemma_ "support-exercise-6.10" (parent := "fabl-chapter-6") (lean := "FABL.PseudoBooleanFunction, FABL.NumericalCoefficients, FABL.numericalMonomial, FABL.numericalEval, FABL.existsUnique_numericalEval, FABL.numericalCoeff, FABL.numericalCoeff_eq_mobius_sum") (uses := "proposition-6.18, equation-6.3") (tags := "section-6-2, support, fidelity-exact")
*Exercise 6.10 (Möbius inversion).*

(a) Let $`f:\{0,1\}^n\to\mathbb R` have the unique real multilinear
representation
$$`
q(x)=\sum_{S\subseteq[n]}c_Sx^S.
`
Identifying $`R\subseteq[n]` with its indicator string, prove
$$`
c_S=\sum_{R\subseteq S}(-1)^{|S|-|R|}f(R).
`

(b) Reduce this identity modulo $`2` to prove the coefficient formula in
Proposition 6.21.
:::

:::proposition "proposition-6.21" (parent := "fabl-chapter-6") (lean := "FABL.anfCoeff") (uses := "support-exercise-6.10") (tags := "section-6-2, fidelity-exact")
*Proposition 6.21.* If
$`f:\mathbb F_2^n\to\mathbb F_2` has algebraic normal form
$$`
f(x)=\sum_{S\subseteq[n]}c_Sx^S,
`
then
$$`
c_S=\sum_{\operatorname{supp}(x)\subseteq S}f(x)
\qquad\text{in }\mathbb F_2.
`
:::

:::corollary "corollary-6.22" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd, FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd") (uses := "proposition-6.21") (tags := "section-6-2, erratum, fidelity-corrected-zero-dimensional-convention")
*Corollary 6.22.* For $`n>0` and a Boolean function
$`f:\{\mathrm{False},\mathrm{True}\}^n
\to\{\mathrm{False},\mathrm{True}\}`,
$$`
\deg_{\mathbb F_2}(f)=n
`
if and only if $`f(x)=\mathrm{True}` for an odd number of inputs $`x`.

For $`n=0`, every function has algebraic degree $`0=n`, whereas only the
constant-True function is True on an odd number of inputs. Thus without the
$`n>0` hypothesis the exact statement is
$$`
\deg_{\mathbb F_2}(f)=n
\quad\Longleftrightarrow\quad
n=0\ \text{or}\ |\{x:f(x)=\mathrm{True}\}|\text{ is odd}.
`
:::

:::lemma_ "support-fourier-to-f2-polynomial" (parent := "fabl-chapter-6") (lean := "FABL.booleanFunctionF₂Encoding, FABL.booleanRealEmbedding, FABL.signEncode_booleanFunctionF₂Encoding, FABL.booleanRealEmbedding_booleanFunctionF₂Encoding_apply, FABL.binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding, FABL.fourierSubstitutionCoeff, FABL.fourierSubstitution, FABL.fourierToF₂Polynomial, FABL.fourierToF₂Coeff, FABL.numericalEval_fourierSubstitutionCoeff, FABL.numericalCoeff_fourierToF₂Polynomial, FABL.numericalDegree_fourierSubstitutionCoeff, FABL.numericalDegree_fourierToF₂Coeff, FABL.booleanNumericalCoeffInt, FABL.numericalCoeff_booleanRealEmbedding_eq_intCast, FABL.booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff, FABL.algebraicDegree_intCastModTwo_le_numericalDegree, FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree_viaPolynomial") (uses := "theorem-1.1, proposition-6.18, example-6.17") (tags := "section-6-2, support, fidelity-exact")
*Fourier-to-$`\mathbb F_2` representation bridge.* Let $`p` be the real
Fourier polynomial of a Boolean function under the $`\pm1` encoding. Under
the $`0,1` encoding, its unique real multilinear polynomial is
$$`
q(x)=\frac12-\frac12p(1-2x_1,\ldots,1-2x_n).
`
The coefficients of $`q` are integers, and reducing them modulo $`2` gives
the algebraic normal form of the function. The substitution preserves degree
(except that $`p\equiv1` becomes $`q\equiv0`), and coefficient reduction
cannot increase degree.
:::

:::proposition "proposition-6.23" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree") (uses := "definition-6.20, support-fourier-to-f2-polynomial") (tags := "section-6-2, fidelity-exact")
*Proposition 6.23.* For every Boolean function
$`f:\{-1,1\}^n\to\{-1,1\}`, interpreted under the canonical
$`\{\pm1\}\leftrightarrow\mathbb F_2` encoding,
$$`
\deg_{\mathbb F_2}(f)\le\deg(f).
`
:::

:::proposition "proposition-6.24" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient") (uses := "definition-6.15, proposition-6.23, corollary-6.22, theorem-1.1") (tags := "section-6-2, fidelity-exact")
*Proposition 6.24.* If
$`f:\{-1,1\}^n\to\{-1,1\}` is $`k`-resilient and $`k<n-1`, then
$$`
\deg_{\mathbb F_2}(f)\le n-k-1.
`
:::

:::theorem "siegenthaler-theorem" (parent := "fabl-chapter-6") (lean := "FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isCorrelationImmune") (uses := "proposition-6.24, definition-6.15, corollary-6.22") (tags := "section-6-2, fidelity-exact")
*Siegenthaler's Theorem.* Proposition 6.24 holds. More generally, if
$`f:\{-1,1\}^n\to\{-1,1\}` is $`k`th-order correlation immune and $`k<n`,
then
$$`
\deg_{\mathbb F_2}(f)\le n-k.
`
:::

:::lemma_ "support-exercise-6.14" (parent := "fabl-chapter-6") (lean := "FABL.fourierCoeff_pointwise_mul, FABL.fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support") (uses := "definition-6.15, theorem-1.1, parseval") (tags := "section-6-2, support, fidelity-exact")
*Exercise 6.14.*

(a) Let
$$`
p(x)=c_\varnothing+c_Sx^S+r(x)
`
be a real multilinear polynomial in $`x_1,\ldots,x_n`, where
$`c_\varnothing c_S\ne0`, $`|S|>2n/3`, and every monomial $`x^T` occurring
in $`r` has $`|T|>2n/3`. Show that, after expanding $`p(x)^2` and making the
multilinear reduction $`x_i^2\mapsto1`, the term
$`2c_\varnothing c_Sx^S` occurs and is not cancelled.

(b) Deduce Theorem 6.25.
:::

:::theorem "theorem-6.25" (parent := "fabl-chapter-6") (lean := "FABL.correlationImmune_not_resilient_three_mul_succ_le_two_mul_dimension") (uses := "support-exercise-6.14, definition-6.15") (tags := "section-6-2, erratum, fidelity-corrected-missing-nonconstant-hypothesis")
*Theorem 6.25 (corrected).* If a nonconstant
$`f:\{-1,1\}^n\to\{-1,1\}` is $`k`th-order correlation immune but is not
$`k`-resilient (equivalently, $`\mathbb E[f]\ne0`), then
$$`
k+1\le\frac23n.
`

The printed statement omits the nonconstant hypothesis. Without it, either
constant sign function is correlation immune of every order, has nonzero
mean, and gives an immediate counterexample for sufficiently large $`k`.
:::

:::lemma_ "support-exercise-6.16" (parent := "fabl-chapter-6") (lean := "FABL.vectorFourierCoeff_bentDirectProduct_append") (uses := "definition-6.26, proposition-1.8, parseval") (tags := "section-6-2, support, fidelity-exact")
*Exercise 6.16.* Prove Proposition 6.27: if
$`f:\mathbb F_2^n\to\{-1,1\}` and
$`g:\mathbb F_2^{n'}\to\{-1,1\}` are bent, then
$$`
(f\oplus g)(x,x')=f(x)g(x')
`
is bent on $`\mathbb F_2^{n+n'}`.
:::

:::theorem "open-problem-bent-classification" (parent := "fabl-chapter-6") (uses := "definition-6.26, support-exercise-6.18, support-exercise-6.19") (tags := "section-6-2, open, problem, statement-only")
*Open problem (classification of bent functions).* The inner-product,
complete-quadratic, and Maiorana--McFarland constructions give large families
of bent functions, and Dickson's Theorem classifies those of
$`\mathbb F_2`-degree at most $`2`. Classifying all bent Boolean functions is
open.
:::
