/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.ProbabilityDensitiesAndConvolution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The “Fourier expansion”: functions as multilinear polynomials" =>

:::lemma_ "support-indicator-interpolation" (lean := "FABL.indicatorPolynomial, FABL.indicatorPolynomial_eq_ite, FABL.sum_indicatorPolynomial") (tags := "section-1-2, support")
*Section 1.2.* For $`a,x\in\{-1,1\}^n`, define
$`\mathbf 1_{\{a\}}(x)=\prod_{i=1}^n\frac{1+a_i x_i}{2}.`
This polynomial equals $`1` when $`x=a` and $`0` otherwise. Consequently,
every $`f:\{-1,1\}^n\to\mathbb R` satisfies
$$`f(x)=\sum_{a\in\{-1,1\}^n}f(a)\mathbf 1_{\{a\}}(x).`
:::

:::definition "support-sign-monomial" (lean := "FABL.monomial, FABL.multilinearPolynomial, FABL.fourierCoeff") (tags := "section-1-2, support")
*Section 1.2.* For $`S\subseteq[n]` and $`x\in\{-1,1\}^n`, write
$$`x^S=\chi_S(x)=\prod_{i\in S}x_i,
\qquad x^\varnothing=1.`
A squarefree coefficient family $`a(S)` determines the multilinear polynomial
$`x\mapsto\sum_{S\subseteq[n]}a(S)x^S`; for a function $`f`, the corresponding
coefficient is denoted $`\widehat f(S)`.
:::

:::theorem "theorem-1.1" (lean := "FABL.fourier_expansion_unique, FABL.fourier_expansion") (uses := "support-indicator-interpolation") (tags := "section-1-2, fidelity-exact-up-to-squarefree-coefficient-representation")
*Theorem 1.1.* Every function $`f : \{-1,1\}^n \to \mathbb R` can be uniquely
expressed as a multilinear polynomial
$$`f(x) = \sum_{S \subseteq [n]} \widehat f(S)x^S,
\qquad x^S = \prod_{i \in S}x_i,`
with $`x^\varnothing = 1`. This expression is the Fourier expansion of $`f`,
the real number $`\widehat f(S)` is the Fourier coefficient of $`f` on $`S`,
and the collection of coefficients is the Fourier spectrum of $`f`.
:::

:::definition "support-exercise-1.10-degree" (lean := "FABL.fourierSupport, FABL.fourierDegree, FABL.mem_fourierSupport, FABL.fourierDegree_le_iff, FABL.fourierDegree_le_dimension") (uses := "theorem-1.1") (tags := "section-1-2, support, fidelity-exact-with-explicit-zero-function-convention")
*Exercise 1.10: real degree.* If
$`f:\{-1,1\}^n\to\mathbb R` is not identically zero, its real degree is the
degree of its multilinear Fourier expansion:
$$`
\deg(f)=\max\{|S|:S\subseteq[n],\ \widehat f(S)\ne0\}.
`
Equivalently, $`\deg(f)\le k` if and only if
$`\widehat f(S)=0` whenever $`|S|>k`. For the zero function, set
$`\deg(0)=0`.
:::

:::lemma_ "support-exercise-1.11b-granularity" (lean := "FABL.IsFourierGranular, FABL.isFourierGranular_signValue_of_fourierDegree_le") (uses := "support-exercise-1.10-degree, theorem-1.1") (tags := "section-1-2, support, fidelity-generalized-degree-at-most")
*Exercise 1.11(b).* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` has $`\deg(f)=k\ge1`. Then the Fourier spectrum
of $`f` is $`2^{1-k}`-granular: for every $`S\subseteq[n]` there is an
integer $`z_S` such that $`\widehat f(S)=z_S\,2^{1-k}.`

The same conclusion holds under the weaker hypothesis
$`\deg(f)\le k` with $`k\ge1`.
:::

:::definition "definition-1.2" (lean := "FABL.binarySign, FABL.coordinateSum, FABL.χ, FABL.χ_add") (tags := "section-1-2, fidelity-exact")
*Definition 1.2.* Let $`\chi : \mathbb F_2 \to \mathbb R` be given by
$`\chi(0)=+1` and $`\chi(1)=-1`. For $`S \subseteq [n]`, define
$`\chi_S : \mathbb F_2^n \to \mathbb R` by
$$`\chi_S(x) = \prod_{i \in S}\chi(x_i)
= (-1)^{\sum_{i \in S}x_i}.`
This satisfies $`\chi_S(x+y)=\chi_S(x)\chi_S(y)`
for all $`x,y \in \mathbb F_2^n`.
:::

:::lemma_ "support-binary-fourier-expansion" (lean := "FABL.binaryFourierCoeff, FABL.binary_fourier_expansion") (uses := "definition-1.2, theorem-1.5") (tags := "section-1-2, support")
*Additive-cube bridge for Definition 1.2 and Theorem 1.1.* Every function
$`f:\mathbb F_2^n\to\mathbb R` has the subset-indexed Fourier expansion
$$`f(x)=\sum_{S\subseteq[n]}\widehat f(S)\chi_S(x),`
where $`\widehat f(S)=\mathbb E_{x\sim\mathbb F_2^n}[f(x)\chi_S(x)]`.
:::
