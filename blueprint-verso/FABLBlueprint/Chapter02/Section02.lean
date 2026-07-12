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

#doc (Manual) "Influences and derivatives" =>

:::definition "definition-2.12" (lean := "FABL.setCoordinate, FABL.flipCoordinate, FABL.IsPivotal, FABL.isPivotal_iff_setCoordinate_ne") (tags := "section-2-2, fidelity-exact")
*Definition 2.12.* A coordinate $`i\in[n]` is pivotal for
$`f:\{-1,1\}^n\to\{-1,1\}` on input $`x` if
$`f(x)\ne f(x^{\oplus i})`,
where
$`x^{\oplus i}=(x_1,\ldots,x_{i-1},-x_i,x_{i+1},\ldots,x_n)`.
:::

:::definition "definition-2.13" (lean := "FABL.booleanInfluence") (uses := "definition-2.12, notation-1.4") (tags := "section-2-2, fidelity-exact")
*Definition 2.13.* The influence of coordinate $`i` on
$`f:\{-1,1\}^n\to\{-1,1\}` is the probability that $`i` is pivotal for a
uniformly random input:
$$`\operatorname{Inf}_i[f]
=\Pr_{\boldsymbol{x}\sim\{-1,1\}^n}
  [f(\boldsymbol{x})\ne f(\boldsymbol{x}^{\oplus i})].`
:::

:::lemma_ "fact-2.14" (lean := "FABL.DimensionEdge, FABL.IsBoundaryDimensionEdge, FABL.dimensionEdgeBoundaryFraction, FABL.booleanInfluence_eq_dimensionEdgeBoundaryFraction") (uses := "definition-2.12, definition-2.13") (tags := "section-2-2, fidelity-exact")
*Fact 2.14.* For $`f:\{-1,1\}^n\to\{-1,1\}`,
$`\operatorname{Inf}_i[f]` equals the fraction of dimension-$`i` edges of the
Hamming cube that are boundary edges. An edge $`(x,y)` has dimension $`i`
when $`y=x^{\oplus i}`, and it is a boundary edge when $`f(x)\ne f(y)`.
:::

:::lemma_ "example-2.15" (lean := "FABL.booleanInfluence_dictator_self, FABL.booleanInfluence_dictator_of_ne, FABL.booleanInfluence_neg_dictator, FABL.booleanInfluence_const, FABL.booleanInfluence_orFunction, FABL.booleanInfluence_andFunction, FABL.booleanInfluence_majority_three, FABL.booleanInfluence_majority_odd") (uses := "definition-2.1, definition-2.2, definition-2.3, definition-2.12, definition-2.13, fact-2.14, support-exercise-2.22") (tags := "section-2-2, fidelity-exact")
*Example 2.15.* For the dictator $`\chi_i`, coordinate $`i` is pivotal on
every input, so $`\operatorname{Inf}_i[\chi_i]=1`; for $`j\ne i`,
$`\operatorname{Inf}_j[\chi_i]=0`. The same holds for the corresponding
negated dictator. Every coordinate of a constant function has influence
$`0`, and for every $`i\in[n]`,
$`\operatorname{Inf}_i[\operatorname{OR}_n]=\operatorname{Inf}_i[\operatorname{AND}_n]=2^{1-n}`.
For $`\operatorname{Maj}_3`, each influence is $`1/2`. More generally, for
odd $`n`,
$$`\operatorname{Inf}_i[\operatorname{Maj}_n]
=\Pr[\text{exactly half of }n-1\text{ independent random bits are }1]
=\binom{n-1}{(n-1)/2}2^{1-n}
=\sqrt{\frac{2}{\pi n}}+O(n^{-3/2}).`
:::

:::definition "definition-2.16" (lean := "FABL.discreteDerivative, FABL.discreteDerivative_apply, FABL.discreteDerivative_add, FABL.discreteDerivative_setCoordinate") (tags := "section-2-2, fidelity-exact")
*Definition 2.16.* The $`i`th discrete derivative operator sends
$`f:\{-1,1\}^n\to\mathbb R` to the function
$$`D_i f(x)
=\frac{f(x^{(i\mapsto1)})-f(x^{(i\mapsto-1)})}{2},`
where
$`x^{(i\mapsto b)}=(x_1,\ldots,x_{i-1},b,x_{i+1},\ldots,x_n)`.
The function $`D_i f` does not depend on $`x_i`, and $`D_i` is linear:
$`D_i(f+g)=D_i f+D_i g`.
:::

:::lemma_ "equation-2.1" (lean := "FABL.pivotalIndicator, FABL.sq_discreteDerivative_toReal_eq_pivotalIndicator") (uses := "definition-2.12, definition-2.16") (tags := "section-2-2, support, fidelity-exact")
*Equation (2.1).* If $`f:\{-1,1\}^n\to\{-1,1\}` is Boolean-valued, then
$$`D_i f(x)=
\begin{cases}
0 & \text{if coordinate }i\text{ is not pivotal for }f\text{ on }x,\\
\pm1 & \text{if coordinate }i\text{ is pivotal for }f\text{ on }x.
\end{cases}`
Consequently, $`D_i f(x)^2` is the indicator that $`i` is pivotal at $`x`.
:::

:::definition "definition-2.17" (lean := "FABL.influence, FABL.booleanInfluence_eq_influence_toReal") (uses := "definition-1.3, definition-2.16, equation-2.1") (tags := "section-2-2, fidelity-exact")
*Definition 2.17.* For $`f:\{-1,1\}^n\to\mathbb R`, the influence of
coordinate $`i` is
$$`\operatorname{Inf}_i[f]
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}
  [D_i f(\boldsymbol{x})^2]
=\lVert D_i f\rVert_2^2.`
For Boolean-valued $`f`, this agrees with Definition 2.13.
:::

:::definition "definition-2.18" (lean := "FABL.IsRelevant, FABL.isRelevant_iff_exists_setCoordinate_ne") (uses := "definition-2.17") (tags := "section-2-2, fidelity-exact")
*Definition 2.18.* A coordinate $`i\in[n]` is relevant for
$`f:\{-1,1\}^n\to\mathbb R` if and only if
$`\operatorname{Inf}_i[f]>0`; equivalently, there is an
$`x\in\{-1,1\}^n` such that
$`f(x^{(i\mapsto1)})\ne f(x^{(i\mapsto-1)})`.
:::

:::proposition "proposition-2.19" (lean := "FABL.discreteDerivative_eq_fourier_sum") (uses := "definition-2.16, theorem-1.1") (tags := "section-2-2, fidelity-exact")
*Proposition 2.19.* Let $`f:\{-1,1\}^n\to\mathbb R` have multilinear
expansion $`f(x)=\sum_{S\subseteq[n]}\widehat f(S)x^S`. Then
$$`D_i f(x)
=\sum_{\substack{S\subseteq[n]\\i\in S}}
  \widehat f(S)x^{S\setminus\{i\}}. \tag{2.2}`
:::

:::theorem "theorem-2.20" (lean := "FABL.influence_eq_sum_sq_fourierCoeff") (uses := "definition-2.17, proposition-2.19, parseval") (tags := "section-2-2, fidelity-exact")
*Theorem 2.20.* For every $`f:\{-1,1\}^n\to\mathbb R` and $`i\in[n]`,
$$`\operatorname{Inf}_i[f]
=\sum_{\substack{S\subseteq[n]\\i\in S}}\widehat f(S)^2.`
:::

:::proposition "proposition-2.21" (lean := "FABL.influence_eq_fourierCoeff_singleton_of_monotone") (uses := "definition-2.8, definition-2.17, equation-2.1, proposition-2.19, fact-1.12") (tags := "section-2-2, fidelity-exact")
*Proposition 2.21.* If $`f:\{-1,1\}^n\to\{-1,1\}` is monotone, then
$`\operatorname{Inf}_i[f]=\widehat f(i)` for every $`i\in[n]`, where
$`\widehat f(i)` abbreviates
$`\widehat f(\{i\})`.
:::

:::proposition "proposition-2.22" (lean := "FABL.influence_le_one_div_sqrt_of_transitiveSymmetric_monotone") (uses := "definition-2.10, proposition-2.21, support-exercise-1.30a, parseval") (tags := "section-2-2, fidelity-exact")
*Proposition 2.22.* If
$`f:\{-1,1\}^n\to\{-1,1\}` is transitive-symmetric and monotone, then
$`\operatorname{Inf}_i[f]\le\frac1{\sqrt n}` for every $`i\in[n]`.
:::

:::definition "definition-2.23" (lean := "FABL.coordinateExpectation") (uses := "notation-1.4") (tags := "section-2-2, fidelity-exact")
*Definition 2.23.* The $`i`th expectation operator is the linear operator on
$`f:\{-1,1\}^n\to\mathbb R` defined by
$$`E_i f(x)
=\mathbb E_{\boldsymbol{x}_i}
  [f(x_1,\ldots,x_{i-1},\boldsymbol{x}_i,x_{i+1},\ldots,x_n)],`
where $`\boldsymbol{x}_i` is uniform on $`\{-1,1\}`.
:::

:::proposition "proposition-2.24" (lean := "FABL.coordinateExpectation_apply, FABL.coordinateExpectation_eq_fourier_sum, FABL.eq_signValue_mul_discreteDerivative_add_coordinateExpectation, FABL.coordinateExpectation_setCoordinate") (uses := "definition-2.16, definition-2.23, theorem-1.1") (tags := "section-2-2, fidelity-exact")
*Proposition 2.24.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\begin{aligned}
E_i f(x)&=\frac{f(x^{(i\mapsto1)})+f(x^{(i\mapsto-1)})}{2},\\
E_i f(x)&=\sum_{\substack{S\subseteq[n]\\i\notin S}}\widehat f(S)x^S,\\
f(x)&=x_iD_i f(x)+E_i f(x).
\end{aligned}`
Neither $`D_i f` nor $`E_i f` depends on $`x_i`.
:::

:::definition "definition-2.25" (lean := "FABL.coordinateLaplacian") (uses := "definition-2.23") (tags := "section-2-2, fidelity-exact")
*Definition 2.25.* The $`i`th coordinate Laplacian is $`L_i f=f-E_i f`.
The book warns that some sources use the negated convention
$`E_i f-f`.
:::

:::proposition "proposition-2.26" (lean := "FABL.coordinateLaplacian_eq_sub_flip_div_two, FABL.coordinateLaplacian_eq_signValue_mul_discreteDerivative, FABL.coordinateLaplacian_eq_fourier_sum, FABL.uniformInner_coordinateLaplacian_eq_influence, FABL.uniformInner_coordinateLaplacian_self_eq_influence") (uses := "definition-2.16, definition-2.17, proposition-2.24, definition-2.25, plancherel") (tags := "section-2-2, fidelity-exact")
*Proposition 2.26.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\begin{aligned}
L_i f(x)&=\frac{f(x)-f(x^{\oplus i})}{2},\\
L_i f(x)&=x_iD_i f(x)
=\sum_{\substack{S\subseteq[n]\\i\in S}}\widehat f(S)x^S,\\
\langle f,L_i f\rangle&=\langle L_i f,L_i f\rangle
=\operatorname{Inf}_i[f].
\end{aligned}`
:::
