/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.BasicFourierFormulas

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Fourier formulas" =>

:::proposition "proposition-1.8" (parent := "fabl-chapter-1") (lean := "FABL.fourierCoeff_eq_uniformInner") (uses := "theorem-1.1, theorem-1.5") (tags := "section-1-4, fidelity-exact")
*Proposition 1.8.* For $`f:\{-1,1\}^n\to\mathbb R` and
$`S\subseteq[n]`, the Fourier coefficient of $`f` on $`S` is
$$`\widehat f(S)=\langle f,\chi_S\rangle
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}
[f(\boldsymbol{x})\chi_S(\boldsymbol{x})].`
:::

:::theorem "parseval" (parent := "fabl-chapter-1") (lean := "FABL.parseval, FABL.sum_sq_fourierCoeff_eq_one") (uses := "theorem-1.5, proposition-1.8") (tags := "section-1-4, fidelity-exact")
*Parseval's Theorem.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`\langle f,f\rangle
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}[f(\boldsymbol{x})^2]
=\sum_{S\subseteq[n]}\widehat f(S)^2.`
In particular, if $`f:\{-1,1\}^n\to\{-1,1\}` is Boolean-valued, then
$`\sum_{S\subseteq[n]}\widehat f(S)^2=1.`
:::

:::theorem "plancherel" (parent := "fabl-chapter-1") (lean := "FABL.plancherel") (uses := "theorem-1.5, proposition-1.8") (tags := "section-1-4, fidelity-exact")
*Plancherel's Theorem.* For every
$`f,g:\{-1,1\}^n\to\mathbb R`,
$$`\langle f,g\rangle
=\mathbb E_{\boldsymbol{x}\sim\{-1,1\}^n}[f(\boldsymbol{x})g(\boldsymbol{x})]
=\sum_{S\subseteq[n]}\widehat f(S)\widehat g(S).`
:::

:::proposition "proposition-1.9" (parent := "fabl-chapter-1") (lean := "FABL.uniformInner_eq_uniformProbability_eq_sub_ne, FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist") (uses := "definition-1.3, definition-1.10") (tags := "section-1-4, fidelity-exact")
*Proposition 1.9.* If $`f,g:\{-1,1\}^n\to\{-1,1\}`, then
$$`\langle f,g\rangle
=\Pr[f(\boldsymbol{x})=g(\boldsymbol{x})]
-\Pr[f(\boldsymbol{x})\ne g(\boldsymbol{x})]
=1-2\operatorname{dist}(f,g).`
:::

:::definition "definition-1.10" (parent := "fabl-chapter-1") (lean := "FABL.relativeHammingDist") (tags := "section-1-4, fidelity-conservative-generalization")
*Definition 1.10.* For $`f,g:\{-1,1\}^n\to\{-1,1\}`, their relative
Hamming distance is
$$`\operatorname{dist}(f,g)
=\Pr_{\boldsymbol{x}}[f(\boldsymbol{x})\ne g(\boldsymbol{x})],`
the fraction of inputs on which they disagree.
:::

:::definition "definition-1.11" (parent := "fabl-chapter-1") (lean := "FABL.mean, FABL.IsBalanced, FABL.mean_eq_probability_one_sub_probability_neg_one, FABL.isBalanced_iff_uniformProbability_one_eq_half") (uses := "notation-1.4") (tags := "section-1-4, fidelity-exact")
*Definition 1.11.* The mean of $`f:\{-1,1\}^n\to\mathbb R` is
$`\mathbb E[f]`. When $`f` has mean $`0`, it is called unbiased, or balanced.
If $`f:\{-1,1\}^n\to\{-1,1\}` is Boolean-valued, then
$`\mathbb E[f]=\Pr[f=1]-\Pr[f=-1];`
thus $`f` is unbiased if and only if it takes value $`1` on exactly half of the
points of the Hamming cube.
:::

:::lemma_ "fact-1.12" (parent := "fabl-chapter-1") (lean := "FABL.mean_eq_fourierCoeff_empty, FABL.isBalanced_iff_fourierCoeff_empty_eq_zero") (uses := "proposition-1.8") (tags := "section-1-4, fidelity-exact")
*Fact 1.12.* If $`f:\{-1,1\}^n\to\mathbb R`, then
$`\mathbb E[f]=\widehat f(\varnothing).`
In particular, a Boolean-valued $`f` is unbiased if and only if its empty-set
Fourier coefficient is $`0`.
:::

:::proposition "proposition-1.13" (parent := "fabl-chapter-1") (lean := "FABL.variance, FABL.variance_eq_uniformInner_centered, FABL.variance_eq_sum_sq_fourierCoeff") (uses := "parseval, fact-1.12") (tags := "section-1-4, fidelity-exact")
*Proposition 1.13.* The variance of $`f:\{-1,1\}^n\to\mathbb R` is
$$`\operatorname{Var}[f]
=\langle f-\mathbb E[f],f-\mathbb E[f]\rangle
=\mathbb E[f^2]-\mathbb E[f]^2
=\sum_{\substack{S\subseteq[n]\\S\ne\varnothing}}\widehat f(S)^2.`
:::

:::lemma_ "fact-1.14" (parent := "fabl-chapter-1") (lean := "FABL.variance_eq_four_mul_probabilities") (uses := "definition-1.11, proposition-1.13") (tags := "section-1-4, fidelity-exact")
*Fact 1.14.* If $`f:\{-1,1\}^n\to\{-1,1\}`, then
$$`\operatorname{Var}[f]
=1-\mathbb E[f]^2
=4\Pr[f(\boldsymbol{x})=1]\Pr[f(\boldsymbol{x})=-1]
\in[0,1].`
:::

:::lemma_ "support-exercise-1.16" (parent := "fabl-chapter-1") (lean := "FABL.relativeHammingDist_one_eq_uniformProbability_neg_one, FABL.relativeHammingDist_neg_one_eq_uniformProbability_one, FABL.variance_eq_four_mul_relativeHammingDist_one_mul_neg_one") (uses := "fact-1.14, definition-1.10") (tags := "section-1-4, support")
*Exercise 1.16.* For $`f:\{-1,1\}^n\to\{-1,1\}`,
$`\operatorname{dist}(f,1)=\Pr[f=-1], \qquad \operatorname{dist}(f,-1)=\Pr[f=1],`
and therefore $`\operatorname{Var}[f]=4\operatorname{dist}(f,1)\operatorname{dist}(f,-1).`
:::

:::proposition "proposition-1.15" (parent := "fabl-chapter-1") (lean := "FABL.distanceToNearestConstant, FABL.variance_bounds_distanceToNearestConstant") (uses := "fact-1.14, support-exercise-1.16") (tags := "section-1-4, fidelity-exact")
*Proposition 1.15.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and set
$`\epsilon=\min\{\operatorname{dist}(f,1),\operatorname{dist}(f,-1)\}.`
Then $`2\epsilon\le\operatorname{Var}[f]\le4\epsilon.`
:::

:::proposition "proposition-1.16" (parent := "fabl-chapter-1") (lean := "FABL.covariance, FABL.covariance_eq_uniformInner_centered, FABL.covariance_eq_sum_fourierCoeff_mul") (uses := "plancherel, fact-1.12") (tags := "section-1-4, fidelity-exact")
*Proposition 1.16.* The covariance of
$`f,g:\{-1,1\}^n\to\mathbb R` is
$$`\operatorname{Cov}[f,g]
=\langle f-\mathbb E[f],g-\mathbb E[g]\rangle
=\mathbb E[fg]-\mathbb E[f]\mathbb E[g]
=\sum_{\substack{S\subseteq[n]\\S\ne\varnothing}}
\widehat f(S)\widehat g(S).`
:::

:::definition "definition-1.17" (parent := "fabl-chapter-1") (lean := "FABL.fourierWeight") (uses := "proposition-1.8") (tags := "section-1-4, fidelity-exact")
*Definition 1.17.* For $`f:\{-1,1\}^n\to\mathbb R` and
$`S\subseteq[n]`, the Fourier weight of $`f` on $`S` is
$`\widehat f(S)^2.`
:::

:::definition "definition-1.18" (parent := "fabl-chapter-1") (lean := "FABL.spectralSample, FABL.spectralSample_apply_toReal") (uses := "definition-1.17, parseval") (tags := "section-1-4, fidelity-exact-with-PMF-codomain")
*Definition 1.18.* Given $`f:\{-1,1\}^n\to\{-1,1\}`, the spectral
sample $`\mathcal S_f` is the probability distribution on subsets of $`[n]`
in which the set $`S` has probability $`\widehat f(S)^2`. Write
$`\boldsymbol{S}\sim\mathcal S_f` for a draw from this distribution.
:::

:::definition "definition-1.19" (parent := "fabl-chapter-1") (lean := "FABL.fourierWeightAtLevel, FABL.fourierWeightAtMost, FABL.degreePart, FABL.fourierWeightAtLevel_eq_uniformLpNorm_degreePart_sq, FABL.fourierWeightAbove, FABL.lowDegreePart, FABL.spectralSample_card_eq") (uses := "definition-1.17, definition-1.18") (tags := "section-1-4, fidelity-definitions-generalized-to-all-natural-k")
*Definition 1.19.* For $`f:\{-1,1\}^n\to\mathbb R` and an integer $`k`
with $`0\le k\le n`, the Fourier weight of $`f` at degree $`k` is
$$`\mathbf W^k[f]
=\sum_{\substack{S\subseteq[n]\\|S|=k}}\widehat f(S)^2.`
If $`f` is Boolean-valued, equivalently
$`\mathbf W^k[f]=\Pr_{\boldsymbol{S}\sim\mathcal S_f}[|\boldsymbol{S}|=k].`
Define the degree-$`k` part of $`f` by
$`f^{=k}=\sum_{|S|=k}\widehat f(S)\chi_S.`
Then Parseval's Theorem gives $`\mathbf W^k[f]=\lVert f^{=k}\rVert_2^2`.
Also write
$$`\mathbf W^{>k}[f]=\sum_{|S|>k}\widehat f(S)^2,
\qquad
f^{\le k}=\sum_{|S|\le k}\widehat f(S)\chi_S.`
:::
