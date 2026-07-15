/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.KKL
import FABL.Chapter04.Tribes

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Tribes" =>

:::lemma_ "fact-4.10" (lean := "FABL.uniformProbability_andFunction_eq_neg_one, FABL.uniformProbability_andFunction_eq_one, FABL.tribes_zero, FABL.tribes_neg_one_probability_zero, FABL.tribes_neg_one_probability") (uses := "definition-2.7") (tags := "section-4-2, fidelity-exact")
*Fact 4.10.* For the tribes function
$`\operatorname{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}` of Definition 2.7,
$$`
\Pr_{\boldsymbol x}\bigl[\operatorname{Tribes}_{w,s}(\boldsymbol x)=-1\bigr]
=1-(1-2^{-w})^s.
`
:::

:::definition "definition-4.11" (lean := "FABL.IsTribesCriticalSizeCandidate, FABL.tribesCriticalSize, FABL.tribesCriticalDimension, FABL.tribesCritical, FABL.tribesCriticalSize_spec") (uses := "definition-2.7, fact-4.10") (tags := "section-4-2, fidelity-exact-with-verified-search-bound")
*Definition 4.11.* For $`w\in\mathbb N^+`, let $`s=s_w` be the largest integer
such that $`1-(1-2^{-w})^s\le 1/2`. Writing $`n=n_w=sw`, define
$`\operatorname{Tribes}_n:\{-1,1\}^n\to\{-1,1\}` to be
$`\operatorname{Tribes}_{w,s}`. This is defined only for certain
$`n`: $`1,4,15,40,\ldots`. Production code implements the largest-integer
choice by a search up to $`2^{w+2}`; Proposition 4.12 proves that for every
$`w>0` this equals the floor of the unrestricted real threshold.
:::

:::proposition "proposition-4.12" (lean := "FABL.tribesCriticalThreshold, FABL.tribesCriticalSize_eq_floor_threshold, FABL.tribesCriticalSizeError, FABL.tribesCriticalSize_eq_main_sub_error, FABL.tribesCriticalSizeError_mem_Icc, FABL.tribesCriticalSizeError_isTheta_one, FABL.tribesCriticalDimensionError, FABL.tribesCriticalDimension_eq_main_sub_error, FABL.tribesCriticalDimensionError_eq, FABL.tribesCriticalDimensionError_isTheta_natCast, FABL.tribesCriticalSizeError_isLittleO_two_pow, FABL.tribesCriticalDimension_isEquivalent_main, FABL.tendsto_tribesCriticalDimension_succ_div, FABL.tribesCriticalWidthError, FABL.tribesCriticalWidth_eq_log_sub_loglog_add_error, FABL.tendsto_log_tribesCriticalDimension_div_width, FABL.tribesCriticalWidthError_isLittleO_one, FABL.tendsto_tribesCriticalDimension_atTop, FABL.tendsto_two_pow_mul_log_tribesCriticalDimension_div, FABL.tribesCriticalPowerRelativeError, FABL.tribesCriticalPowerRelativeError_isLittleO_one, FABL.eventually_two_pow_eq_dimension_div_log_mul_one_add_error, FABL.tribesCriticalProbabilityDeficit, FABL.tribesCritical_neg_one_probability_eq_half_sub_deficit, FABL.tribesCriticalProbabilityDeficit_eq_pow, FABL.tribesCriticalProbabilityDeficit_mem_Icc, FABL.tribesCriticalProbabilityDeficit_isBigO_log_dimension_div_dimension") (uses := "definition-4.11, fact-4.10") (tags := "section-4-2, fidelity-exact")
*Proposition 4.12.* For the function $`\operatorname{Tribes}_n` of
Definition 4.11 one has:
- $`s=\ln(2)\,2^w-\Theta_w(1)`;
- $`n=\ln(2)\,w\,2^w-\Theta(w)`, and thus $`n_{w+1}=(2+o(1))n_w`;
- $`w=\log n-\log\ln n+o_n(1)` and $`2^w=\frac{n}{\ln n}(1+o_n(1))`;
- $`\Pr[\operatorname{Tribes}_n=-1]=\frac12-O\bigl(\frac{\log n}{n}\bigr)`.

Lean indexes these limits by $`w`. It also proves $`n_w\to\infty`, so the
$`o_n(1)` notation is interpreted along exactly the input-length sequence from
Definition 4.11. The probability $`O` term is represented by a nonnegative
deficit from $`1/2`; its Lean bound uses $`\ln n/n`, which differs from the
book's base-$`2` $`\log n/n` only by a fixed positive factor.
:::

:::proposition "proposition-4.13" (lean := "FABL.tribesCoord, FABL.TribesRestTrue, FABL.TribesOthersFalse, FABL.isPivotal_tribes_iff, FABL.card_andFunction_eq_one, FABL.booleanInfluence_tribes, FABL.totalInfluence_tribes, FABL.tribesCriticalSize_pos, FABL.tribesCriticalCoordinateInfluence, FABL.booleanInfluence_tribesCritical, FABL.totalInfluence_tribesCritical, FABL.tendsto_tribesCriticalCoordinateInfluence_mul_dimension_div_log, FABL.tribesCriticalCoordinateInfluenceRelativeError, FABL.tribesCriticalCoordinateInfluenceRelativeError_isLittleO_one, FABL.eventually_booleanInfluence_tribesCritical_eq_log_dimension_div_mul_one_add_error, FABL.eventually_totalInfluence_tribesCritical_eq_log_dimension_mul_one_add_error") (uses := "definition-4.11, fact-4.10, proposition-4.12, definition-2.13, definition-2.27") (tags := "section-4-2, fidelity-exact")
*Proposition 4.13.* For every coordinate $`i\in[n]`,
$$`
\operatorname{Inf}_i[\operatorname{Tribes}_n]
=\frac{\ln n}{n}\,(1\pm o(1)),
`
and therefore
$`\mathbf I[\operatorname{Tribes}_n]=(\ln n)(1\pm o(1))`.
Production first proves the exact formula for every $`w,s\ge 1` and every coordinate
$`i\in[sw]`:
$$`
\operatorname{Inf}_i[\operatorname{Tribes}_{w,s}]
=2^{-(w-1)}(1-2^{-w})^{s-1},
`
hence
$`\mathbf I[\operatorname{Tribes}_{w,s}]=sw\cdot 2^{-(w-1)}(1-2^{-w})^{s-1}`,
via the pivotality characterization (rest of the home tribe True and every other
tribe False). Specializing to $`s_w`, Lean proves that the common coordinate
influence times $`n_w/\ln n_w` tends to $`1`. It packages this as one relative
error $`\varepsilon_w=o(1)`, uniform in every dependent coordinate
$`i:\operatorname{Fin}(n_w)`, and reuses the same error in the total-influence
identity. Thus both displayed book conclusions are represented literally along
the sequence $`n=n_w\to\infty`.
:::

:::theorem "kkl-theorem" (lean := "FABL.maximumInfluence, FABL.exists_booleanInfluence_eq_maximumInfluence, FABL.edgeKKL, FABL.kkl") (uses := "definition-2.13, proposition-1.13") (tags := "section-4-2, fidelity-exact-with-explicit-constant, proof-from-chapter-9")
*Kahn–Kalai–Linial (KKL) Theorem.* For every
$`f:\{-1,1\}^n\to\{-1,1\}`,
$$`
\operatorname{MaxInf}[f]
=\max_{i\in[n]}\operatorname{Inf}_i[f]
\ge
\operatorname{Var}[f]\cdot\Omega\Bigl(\frac{\log n}{n}\Bigr).
`
The book states KKL in Section 4.2 and defers the proof to Section 9.6.
Production keeps the canonical public declaration here and proves the uniform,
full-dimensional estimate
$$`
\operatorname{MaxInf}[f]
\ge \operatorname{Var}[f]\frac{\ln n}{100n}.
`
For $`n>0`, a coordinate is proved to attain `MaxInf`; dimension zero is assigned
the empty maximum $`0`. The displayed bound is therefore literal for every
$`n`, including $`n=0,1` where its right-hand side is $`0`. The proof also exposes
the exact Edge-KKL estimate from Theorem 9.24,
$`\operatorname{MaxInf}[f]\ge 9\,9^{-K}/K^2` for
$`K=\mathbf I[f]/\operatorname{Var}[f]`, and derives the stated constant using
the hypercontractive argument of Section 9.6. Natural logarithm differs from
the book's base-$`2` logarithm by a fixed positive factor only.
:::

:::proposition "proposition-4.14" (lean := "FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one, FABL.fourierCoeff_tribes_empty, FABL.signValue_andFunction, FABL.signValue_orFunction, FABL.tribeFrequencyPart, FABL.mem_tribeFrequencyPart, FABL.tribeFrequencySupportSize, FABL.tribes_toReal_eq, FABL.fourierCoeff_andFunction_empty, FABL.fourierCoeff_andFunction_of_ne_empty, FABL.fourierCoeff_andFunction, FABL.expect_one_add_andFunction_mul_monomial, FABL.tribesBlockEquiv, FABL.tribesBlockEquiv_apply, FABL.tribeOffsetEmbed, FABL.tribeFrequencyPart_biUnion, FABL.disjoint_tribeOffsetEmbed, FABL.card_tribeFrequencyPart_sum, FABL.monomial_eq_prod_tribeFrequencyPart, FABL.finArrowConsEquiv, FABL.expect_prod_finArrow, FABL.fourierCoeff_tribes_eq_prod, FABL.prod_expect_one_add_and_tribeFrequencyPart, FABL.fourierCoeff_tribes_of_ne_empty, FABL.fourierCoeff_tribes") (uses := "definition-2.7, fact-4.10") (tags := "section-4-2, fidelity-exact")
*Proposition 4.14.* Index Fourier coefficients of
$`\operatorname{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}` by sets
$`T=(T_1,\ldots,T_s)\subseteq[sw]`, where $`T_i` is the intersection of $`T`
with the $`i`th tribe. Then
$$`
\widehat{\operatorname{Tribes}}_{w,s}(T)
=
\begin{cases}
2(1-2^{-w})^s-1
& \text{if }T=\emptyset,\\
2(-1)^{k+|T|}2^{-kw}(1-2^{-w})^{s-k}
& \text{if }k=\#\{i:T_i\neq\emptyset\}>0.
\end{cases}
`
Production proves both cases by reindexing the cube into independent tribes,
factoring the block expectations, and reducing each factor to the complete Fourier
expansion of $`\mathrm{AND}_w`.
:::
