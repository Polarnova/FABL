/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
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

:::definition "definition-4.11" (lean := "FABL.IsTribesCriticalSizeCandidate, FABL.tribesCriticalSize, FABL.tribesCriticalDimension, FABL.tribesCritical, FABL.tribesCriticalSize_spec") (uses := "definition-2.7, fact-4.10") (tags := "section-4-2, fidelity-exact-with-explicit-search-bound")
*Definition 4.11.* For $`w\in\mathbb N^+`, let $`s=s_w` be the largest integer
such that $`1-(1-2^{-w})^s\le 1/2`. Writing $`n=n_w=sw`, define
$`\operatorname{Tribes}_n:\{-1,1\}^n\to\{-1,1\}` to be
$`\operatorname{Tribes}_{w,s}`. This is defined only for certain
$`n`: $`1,4,15,40,\ldots`. Production code searches up to the explicit bound
$`2^{w+2}`, which is large enough for the book asymptotics.
:::

:::proposition "proposition-4.12" (uses := "definition-4.11, fact-4.10") (tags := "section-4-2")
*Proposition 4.12.* For the function $`\operatorname{Tribes}_n` of
Definition 4.11 one has:
- $`s=\ln(2)\,2^w-\Theta_w(1)`;
- $`n=\ln(2)\,w\,2^w-\Theta(w)`, and thus $`n_{w+1}=(2+o(1))n_w`;
- $`w=\log n-\log\ln n+o_n(1)` and $`2^w=\frac{n}{\ln n}(1+o_n(1))`;
- $`\Pr[\operatorname{Tribes}_n=-1]=\frac12-O\bigl(\frac{\log n}{n}\bigr)`.
:::

:::proposition "proposition-4.13" (lean := "FABL.tribesCoord, FABL.TribesRestTrue, FABL.TribesOthersFalse, FABL.isPivotal_tribes_iff, FABL.card_andFunction_eq_one, FABL.booleanInfluence_tribes, FABL.totalInfluence_tribes") (uses := "definition-4.11, fact-4.10, proposition-4.12, definition-2.13, definition-2.27") (tags := "section-4-2, fidelity-exact-general-w-s")
*Proposition 4.13.* For every coordinate $`i\in[n]`,
$$`
\operatorname{Inf}_i[\operatorname{Tribes}_n]
=\frac{\ln n}{n}\,(1\pm o(1)),
`
and therefore
$`\mathbf I[\operatorname{Tribes}_n]=(\ln n)(1\pm o(1))`.
Production proves the exact formula for every $`w,s\ge 1` and every coordinate
$`i\in[sw]`:
$$`
\operatorname{Inf}_i[\operatorname{Tribes}_{w,s}]
=2^{-(w-1)}(1-2^{-w})^{s-1},
`
hence
$`\mathbf I[\operatorname{Tribes}_{w,s}]=sw\cdot 2^{-(w-1)}(1-2^{-w})^{s-1}`,
via the pivotality characterization (rest of the home tribe True and every other
tribe False). The critical-size asymptotic form stated above is the composition of
this exact identity with Proposition 4.12 and remains open until that asymptotic
analysis is formalized.
:::

:::theorem "kkl-theorem" (uses := "definition-2.13, proposition-1.13") (tags := "section-4-2, fidelity-statement-only, deferred-proof-chapter-9")
*Kahn–Kalai–Linial (KKL) Theorem.* For every
$`f:\{-1,1\}^n\to\{-1,1\}`,
$$`
\operatorname{MaxInf}[f]
=\max_{i\in[n]}\operatorname{Inf}_i[f]
\ge
\operatorname{Var}[f]\cdot\Omega\Bigl(\frac{\log n}{n}\Bigr).
`
The book states KKL in Section 4.2 and defers the proof to Chapter 9. The
canonical public declaration belongs to this earliest statement; no second
API is to be created when the Chapter 9 proof is formalized.
:::

:::proposition "proposition-4.14" (lean := "FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one, FABL.fourierCoeff_tribes_empty, FABL.signValue_andFunction, FABL.signValue_orFunction, FABL.tribeFrequencyPart, FABL.mem_tribeFrequencyPart, FABL.tribeFrequencySupportSize, FABL.tribes_toReal_eq, FABL.fourierCoeff_andFunction_empty, FABL.fourierCoeff_andFunction_of_ne_empty, FABL.fourierCoeff_andFunction, FABL.expect_one_add_andFunction_mul_monomial") (uses := "definition-2.7, fact-4.10") (tags := "section-4-2, fidelity-partial-and-fourier-and-empty-tribes")
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
Production proves the empty-set tribes coefficient, the real product encodings of
$`\mathrm{AND}`/$`\mathrm{OR}`, the complete Fourier expansion of $`\mathrm{AND}_w`,
and the one-point moments $`\mathbb E[(1+\mathrm{AND})\chi_S]` used by the product
argument. The assembled nonzero-frequency tribes formula (product over independent
blocks) remains open production work.
:::
