/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter03.Restrictions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Restrictions" =>

:::lemma_ "support-finite-index-sign-fourier" (parent := "fabl-chapter-3") (lean := "FABL.IndexedSignCube, FABL.indexedMonomial, FABL.indexedSignMonomialChar, FABL.indexedWalshBasis, FABL.indexedFourierCoeff, FABL.indexed_fourier_expansion, FABL.expect_eq_indexedFourierCoeff_empty, FABL.indexed_plancherel, FABL.indexed_parseval") (uses := "support-sign-monomial, theorem-1.1, theorem-1.5, parseval, fact-1.12") (tags := "section-3-3, support, fidelity-conservative-generalization")
*Finite-index sign-cube Fourier formulas.* Let $`I` be a finite set. For
$`x\in\{-1,1\}^{I}` and $`A\subseteq I`, write $`x^A=\prod_{i\in A}x_i`.
For every $`g:\{-1,1\}^{I}\to\mathbb R`, define
$$`\widehat g(A)
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^{I}}
  [g(\boldsymbol{x})\boldsymbol{x}^{A}].`
Then
$$`g(x)=\sum_{A\subseteq I}\widehat g(A)x^A,
\qquad
\mathbb E[g]=\widehat g(\varnothing),
\qquad
\mathbb E[g^2]=\sum_{A\subseteq I}\widehat g(A)^2.`
For $`I=[n]`, these are the monomials, Fourier coefficients, Fourier
expansion, constant-coefficient formula, and Parseval formula of Chapter 1.
:::

:::lemma_ "support-coordinate-split" (parent := "fabl-chapter-3") (lean := "FABL.FixedIndex, FABL.FreeSignCube, FABL.FixedSignCube, FABL.signCubeSplitEquiv, FABL.combineSignCube, FABL.liftFreeFrequency, FABL.liftFixedFrequency, FABL.freeFrequencyPart, FABL.fixedFrequencyPart, FABL.disjoint_liftFreeFrequency_liftFixedFrequency, FABL.disjoint_liftFreeFrequencyPart_liftFixedFrequencyPart, FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart, FABL.existsUnique_frequency_split, FABL.indexedMonomial_lift_union_combine, FABL.monomial_liftFreeFrequency_combine") (uses := "support-finite-index-sign-fourier") (tags := "section-3-3, support, fidelity-exact")
*Coordinate and frequency splitting.* Let $`J\subseteq[n]` and
$`\bar J=[n]\setminus J`. Every $`x\in\{-1,1\}^n` has a unique decomposition
$$`x=(y,z),
\qquad
y\in\{-1,1\}^{J},
\quad
z\in\{-1,1\}^{\bar J}.`
Every $`U\subseteq[n]` has a unique decomposition
$$`U=S\mathbin{\dot\cup}T,
\qquad
S=U\cap J\subseteq J,
\quad
T=U\cap\bar J\subseteq\bar J.`
Under these decompositions,
$`x^U=y^S z^T`.
:::

:::definition "definition-3.18" (parent := "fabl-chapter-3") (lean := "FABL.signRestriction") (uses := "support-coordinate-split") (tags := "section-3-3, fidelity-exact")
*Definition 3.18.* Let $`f:\{-1,1\}^n\to\mathbb R` and let
$`(J,\bar J)` be a partition of $`[n]`, with
$`\bar J=[n]\setminus J`. For $`z\in\{-1,1\}^{\bar J}`, write
$`f_{J\mid z}:\{-1,1\}^{J}\to\mathbb R`
for the subfunction obtained by fixing the coordinates in $`\bar J` to the
bit values $`z`. If $`y\in\{-1,1\}^{J}` and
$`z\in\{-1,1\}^{\bar J}`, write $`(y,z)\in\{-1,1\}^n` for their composite
string. Thus $`f_{J\mid z}(y)=f(y,z)`.
When the partition is understood, one may write simply $`f_{\mid z}`.
:::

:::lemma_ "example-3.19" (parent := "fabl-chapter-3") (lean := "FABL.example3_19Predicate, FABL.example3_19Function, FABL.example3_19Function_eq_one_iff, FABL.example3_19_fourier_expansion, FABL.example3_19FreeCoordinates, FABL.example3_19First, FABL.example3_19Second, FABL.example3_19FixedAssignment, FABL.example3_19TwoBitInput, FABL.example3_19_restriction_eq_orFunction, FABL.example3_19_restriction_eq_one_iff, FABL.example3_19_restriction_fourier_expansion, FABL.example3_19_restrictionFourierCoeff_first, FABL.example3_19_first_coefficient_arithmetic") (uses := "definition-3.18, theorem-1.1") (tags := "section-3-3, fidelity-exact")
*Example 3.19.* Let $`f:\{-1,1\}^4\to\{-1,1\}` be defined by
$$`f(x)=1
\quad\Longleftrightarrow\quad
x_3=x_4=-1
\ \text{or}\ x_1\ge x_2\ge x_3\ge x_4
\ \text{or}\ x_1\le x_2\le x_3\le x_4. \tag{3.2}`
Its Fourier expansion is
$$`\begin{aligned}
f(x)={}&\frac18-\frac18x_1+\frac18x_2-\frac18x_3-\frac18x_4\\
&+\frac38x_1x_2+\frac18x_1x_3-\frac38x_1x_4
  +\frac38x_2x_3-\frac18x_2x_4+\frac58x_3x_4\\
&+\frac18x_1x_2x_3+\frac18x_1x_2x_4-\frac18x_1x_3x_4
  +\frac18x_2x_3x_4-\frac18x_1x_2x_3x_4.
\end{aligned} \tag{3.3}`
Fix $`x_3=1` and $`x_4=-1`, and let
$`f'=f_{\{1,2\}\mid(1,-1)}`. Then
$`f'(x_1,x_2)=1\Longleftrightarrow x_1=x_2=1`,
so $`f'=\min_2`, with Fourier expansion
$$`f'(x_1,x_2)=\min_2(x_1,x_2)
=-\frac12+\frac12x_1+\frac12x_2+\frac12x_1x_2. \tag{3.4}`
In particular, the terms contributing to the coefficient on $`x_1` after
this restriction are
$$`-\frac18x_1,
\quad +\frac18x_1x_3,
\quad -\frac38x_1x_4,
\quad -\frac18x_1x_3x_4,`
and their restricted coefficients sum to
$`-\frac18+\frac18+\frac38+\frac18=\frac12`.
:::

:::definition "definition-3.20" (parent := "fabl-chapter-3") (lean := "FABL.restrictionFourierCoeff") (uses := "definition-3.18, support-finite-index-sign-fourier") (tags := "section-3-3, fidelity-exact")
*Definition 3.20.* Let $`f:\{-1,1\}^n\to\mathbb R`, let
$`(J,\bar J)` be a partition of $`[n]`, and let $`S\subseteq J`. Define
$`F_{S\mid J}f:\{-1,1\}^{\bar J}\to\mathbb R` by
$`F_{S\mid J}f(z)=\widehat{f_{J\mid z}}(S)`.
When the partition is understood, one may write simply $`F_{S\mid}f`.
:::

:::proposition "proposition-3.21" (parent := "fabl-chapter-3") (lean := "FABL.indexedFourierCoeff_restrictionFourierCoeff, FABL.restrictionFourierCoeff_eq_sum") (uses := "definition-3.20, theorem-1.1, support-coordinate-split, support-finite-index-sign-fourier") (tags := "section-3-3, fidelity-exact")
*Proposition 3.21.* In the setting of Definition 3.20, for every
$`z\in\{-1,1\}^{\bar J}` one has the Fourier expansion
$$`F_{S\mid J}f(z)
=\sum_{T\subseteq\bar J}\widehat f(S\cup T)z^T.`
Equivalently, for every $`T\subseteq\bar J`,
$`\widehat{F_{S\mid J}f}(T)=\widehat f(S\cup T)`.
:::

:::corollary "corollary-3.22" (parent := "fabl-chapter-3") (lean := "FABL.expect_restrictionFourierCoeff, FABL.expect_sq_restrictionFourierCoeff") (uses := "proposition-3.21, fact-1.12, parseval, support-finite-index-sign-fourier") (tags := "section-3-3, fidelity-exact")
*Corollary 3.22.* Let $`f:\{-1,1\}^n\to\mathbb R`, let
$`(J,\bar J)` be a partition of $`[n]`, and fix $`S\subseteq J`. If
$`\boldsymbol z\sim\{-1,1\}^{\bar J}` is chosen uniformly at random, then
$`\mathbb E_{\boldsymbol z}[\widehat{f_{J\mid\boldsymbol z}}(S)]=\widehat f(S)`,
and
$$`\mathbb E_{\boldsymbol z}
  \left[\widehat{f_{J\mid\boldsymbol z}}(S)^2\right]
=\sum_{T\subseteq\bar J}\widehat f(S\cup T)^2.`
:::

:::definition "definition-3.23" (parent := "fabl-chapter-3") (lean := "FABL.subspaceRestriction") (uses := "support-affine-subspaces-and-subcubes") (tags := "section-3-3, fidelity-exact")
*Definition 3.23.* If $`f:\mathbb F_2^n\to\mathbb R` and
$`H\le\mathbb F_2^n` is a linear subspace, write $`f_H:H\to\mathbb R`
for the restriction of $`f` to $`H`; thus $`f_H(h)=f(h)` for every $`h\in H`.
:::

:::definition "definition-3.24" (parent := "fabl-chapter-3") (lean := "FABL.domainTranslate") (uses := "definition-1.2") (tags := "section-3-3, fidelity-exact")
*Definition 3.24.* Let $`f:\mathbb F_2^n\to\mathbb R` and
$`z\in\mathbb F_2^n`. Define $`f^{+z}:\mathbb F_2^n\to\mathbb R` by
$`f^{+z}(x)=f(x+z)`.
:::

:::lemma_ "fact-3.25" (parent := "fabl-chapter-3") (lean := "FABL.vectorFourierCoeff_domainTranslate, FABL.vectorFourierCoeff_domainTranslate_eq_binarySign, FABL.domainTranslate_fourier_expansion") (uses := "definition-3.24, equation-3.1, support-binary-fourier-expansion") (tags := "section-3-3, fidelity-exact")
*Fact 3.25.* For every $`\gamma\in\widehat{\mathbb F_2^n}`, the Fourier
coefficient of $`f^{+z}` is
$$`\widehat{f^{+z}}(\gamma)
=(-1)^{\gamma\cdot z}\widehat f(\gamma)
=\chi_\gamma(z)\widehat f(\gamma).`
Equivalently,
$$`f^{+z}(x)
=\sum_{\gamma\in\widehat{\mathbb F_2^n}}
  \chi_\gamma(z)\widehat f(\gamma)\chi_\gamma(x).`
Here the dual group $`\widehat{\mathbb F_2^n}` is identified with
$`\mathbb F_2^n` through the dot product.
:::

:::definition "definition-3.26" (parent := "fabl-chapter-3") (lean := "FABL.affineSubspaceRestriction") (uses := "definition-3.23, definition-3.24, support-affine-subspaces-and-subcubes") (tags := "section-3-3, fidelity-exact")
*Definition 3.26.* Let $`f:\mathbb F_2^n\to\mathbb R`,
$`z\in\mathbb F_2^n`, and $`H\le\mathbb F_2^n`. Write
$`f_H^{+z}:H\to\mathbb R` for the function $`(f^{+z})_H`; equivalently,
$`f_H^{+z}(h)=f(h+z)` for $`h\in H`.
This is the restriction of $`f` to the coset $`H+z`, with the representative
$`z` made explicit.
:::

:::lemma_ "support-coset-average-inner" (parent := "fabl-chapter-3") (lean := "FABL.finiteAddFourierCoeff, FABL.finiteAddFourierCoeff_zero_eq_expect, FABL.finiteAddFourierCoeff_affineSubspaceRestriction_zero_eq_expect, FABL.expect_vectorWalshCharacter_submodule, FABL.uniformInner_subsetDensity_domainTranslate_eq_sum, FABL.expect_affineSubspaceRestriction_eq_uniformInner") (uses := "definition-3.26, fact-1.21, definition-1.22") (tags := "section-3-3, support, fidelity-exact")
*Average on an affine subspace.* Let
$`f:\mathbb F_2^n\to\mathbb R`, $`H\le\mathbb F_2^n`, and
$`z\in\mathbb F_2^n`. The Fourier coefficient of $`f_H^{+z}` at the trivial
character is its uniform average on $`H`, and this average is the
density-weighted inner product on the ambient cube:
$$`\widehat{f_H^{+z}}(0)
=\mathbb E_{\boldsymbol h\sim H}[f(\boldsymbol h+z)]
=\langle\varphi_H,f^{+z}\rangle.`
:::

:::theorem "poisson-summation-formula" (parent := "fabl-chapter-3") (lean := "FABL.expect_affineSubspaceRestriction_eq_sum, FABL.poissonSummationFormula") (uses := "support-coset-average-inner, plancherel, proposition-3.11, fact-3.25, support-orthogonal-complement-f2") (tags := "section-3-3, fidelity-exact")
*Poisson Summation Formula.* Let $`f:\mathbb F_2^n\to\mathbb R`,
$`H\le\mathbb F_2^n`, and $`z\in\mathbb F_2^n`. Then
$$`\mathbb E_{\boldsymbol h\sim H}[f(\boldsymbol h+z)]
=\sum_{\gamma\in H^\perp}\chi_\gamma(z)\widehat f(\gamma),`
where
$$`H^\perp
=\left\{\gamma\in\widehat{\mathbb F_2^n}:
  \gamma\cdot h=0\ \text{for every }h\in H\right\}.`
:::
