/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.RandomRestrictions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Random restrictions" =>

:::definition "definition-4.15" (parent := "fabl-chapter-4") (lean := "FABL.deltaRandomSubsetWeight, FABL.deltaRandomSubsetWeight_nonneg, FABL.sum_deltaRandomSubsetWeight, FABL.expectDeltaRandomSubset, FABL.expectRandomRestriction, FABL.coordRestrictionWeight, FABL.sum_coordRestrictionWeight, FABL.restrictionAssignmentWeight, FABL.sum_restrictionAssignmentWeight") (tags := "section-4-3, fidelity-exact")
*Definition 4.15.* For $`\delta\in[0,1]`, a set $`J` is a *$`\delta`-random
subset* of a finite set $`N` if each element of $`N` is included independently
with probability $`\delta`. A *$`\delta`-random restriction* on
$`\{-1,1\}^n` is a pair $`(\boldsymbol J\mid\boldsymbol z)` obtained by first
drawing a $`\delta`-random subset $`\boldsymbol J\subseteq[n]` and then drawing
$`\boldsymbol z\sim\{-1,1\}^{\overline{\boldsymbol J}}` uniformly. Coordinate $`i` is
*free* if $`i\in\boldsymbol J` and *fixed* otherwise. Equivalently, each
coordinate is independently free with probability $`\delta` and fixed to
$`\pm1` with probability $`(1-\delta)/2` each.
:::

:::definition "definition-4.16" (parent := "fabl-chapter-4") (lean := "FABL.extendedSignRestriction, FABL.extendedSignRestriction_apply, FABL.extendedSignRestriction_setCoordinate_of_not_mem") (uses := "definition-3.18") (tags := "section-4-3, fidelity-exact")
*Definition 4.16.* Given $`f:\{-1,1\}^n\to\mathbb R`, free coordinates
$`I\subseteq[n]`, and a fixing $`z\in\{-1,1\}^{\overline I}` of the remaining
coordinates, one may identify the restricted function
$`f_{I\mid z}:\{-1,1\}^I\to\mathbb R` with its extension
$`f_{I\mid z}:\{-1,1\}^n\to\mathbb R` that holds the coordinates in
$`\overline I` fixed at $`z` and ignores the values of those fixed
coordinates as free inputs. When dealing with random restrictions this
extension convention is the default.
:::

:::proposition "proposition-4.17" (parent := "fabl-chapter-4") (lean := "FABL.expect_fourierCoeff_empty_randomRestriction, FABL.sum_deltaRandomSubsetWeight_supset, FABL.ambientRestrictionFourierCoeff, FABL.ambientRestrictionFourierCoeff_eq, FABL.expect_ambientRestrictionFourierCoeff, FABL.expect_fourierCoeff_randomRestriction, FABL.liftFreeFrequency_freeFrequencyPart_of_subset, FABL.expect_sq_ambientRestrictionFourierCoeff, FABL.subset_of_inter_eq, FABL.subset_of_inter_eq_left, FABL.sum_deltaRandomSubsetWeight_inter_eq, FABL.sum_sq_fourier_of_inter_eq, FABL.expect_sq_fourierCoeff_randomRestriction") (uses := "definition-4.15, definition-4.16, corollary-3.22") (tags := "section-4-3, fidelity-exact")
*Proposition 4.17.* Fix $`f:\{-1,1\}^n\to\mathbb R` and $`S\subseteq[n]`. If
$`(\boldsymbol J\mid\boldsymbol z)` is a $`\delta`-random restriction on
$`\{-1,1\}^n`, then (treating restricted functions as maps
$`\{-1,1\}^n\to\mathbb R`)
$$`
\mathbb E\bigl[\widehat{f_{\boldsymbol J\mid\boldsymbol z}}(S)\bigr]
=\Pr[S\subseteq\boldsymbol J]\,\widehat f(S)
=\delta^{|S|}\,\widehat f(S),
`
and
$$`
\mathbb E\bigl[\widehat{f_{\boldsymbol J\mid\boldsymbol z}}(S)^2\bigr]
=\sum_{U\subseteq[n]}\Pr[U\cap\boldsymbol J=S]\,\widehat f(U)^2
=\sum_{U\supseteq S}\delta^{|S|}(1-\delta)^{|U\setminus S|}\,\widehat f(U)^2.
`
For the first identity, use Corollary 3.22 and
$`\sum_{J\supseteq S}w_\delta(J)=\delta^{|S|}`. For the second, apply the
free/fixed Parseval identity on each free set, reindex by the ambient
frequencies satisfying $`U\cap J=S`, and use
$`\sum_{J:U\cap J=S}w_\delta(J)=\delta^{|S|}(1-\delta)^{|U\setminus S|}` when $`S\subseteq U`.
:::

:::corollary "corollary-4.18" (parent := "fabl-chapter-4") (lean := "FABL.sum_deltaRandomSubsetWeight_mem, FABL.freePart, FABL.discreteDerivative_extendedSignRestriction_of_mem, FABL.expect_sq_discreteDerivative_combine, FABL.expect_sq_discreteDerivative_product, FABL.expect_influence_extendedSignRestriction_of_mem, FABL.expect_influence_extended_randomRestriction, FABL.expect_totalInfluence_extended_randomRestriction") (uses := "proposition-4.17, theorem-2.20, definition-2.27") (tags := "section-4-3, fidelity-exact")
*Corollary 4.18.* Fix $`f:\{-1,1\}^n\to\mathbb R` and $`i\in[n]`. If
$`(\boldsymbol J\mid\boldsymbol z)` is a $`\delta`-random restriction, then
$`\mathbb E[\operatorname{Inf}_i[f_{\boldsymbol J\mid\boldsymbol z}]]
=\delta\operatorname{Inf}_i[f]`. Hence also
$`\mathbb E[\mathbf I[f_{\boldsymbol J\mid\boldsymbol z}]]=\delta\mathbf I[f]`.
A Fourier-free proof proceeds as in Exercise 4.9: condition on whether $`i`
is free. In the free case, the free/fixed product measure recovers the
ambient influence, while $`\Pr[i\in\boldsymbol J]=\delta`.
:::

:::lemma_ "lemma-4.19" (parent := "fabl-chapter-4") (lean := "FABL.literal_not_falsified_local_weight, FABL.DNFTerm.notFalsified, FABL.term_not_falsified_weight, FABL.restrictedWidth_ge_probability_le") (uses := "definition-4.1, definition-4.15, definition-4.16") (tags := "section-4-3, fidelity-exact-coordinate-restriction-model")
*Lemma 4.19.* Let $`T` be a DNF term over $`\{-1,1\}^n` and fix
$`w\in\mathbb N^+`. Let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`(1/2)`-random restriction on $`\{-1,1\}^n`. Then
$$`
\Pr\bigl[\operatorname{width}(T_{\boldsymbol J\mid\boldsymbol z})\ge w\bigr]
\le\Bigl(\frac34\Bigr)^w.
`
Under the half-random restriction, each coordinate is free with probability
$`1/2` and fixed to either sign with probability $`1/4`. Thus a term is not
falsified with probability $`(3/4)^{\operatorname{width}(T)}`, which gives
the tail bound.
:::

:::theorem "theorem-4.20" (parent := "fabl-chapter-4") (lean := "FABL.sum_inverse_two_pow_succ_Ico_le, FABL.DNFFormula.selectedTerm, FABL.DNFFormula.selectedWidth, FABL.DNFFormula.selectedTerm_mem, FABL.DNFFormula.selectedTerm_eval, FABL.DNFFormula.selectedWidth_eq_zero_of_eval_ne, FABL.DNFFormula.selectedWidth_le_dimension, FABL.card_negOnePivotal_le_selectedWidth, FABL.selectedWidth_tail_probability_le, FABL.uniformProbability_le_one, FABL.expect_selectedWidth_eq_sum_tail, FABL.expect_selectedWidth_le_clog_add_one, FABL.totalInfluence_le_two_mul_clog_add_one_of_hasDNFSizeLE") (uses := "proposition-4.7, definition-4.3") (tags := "section-4-3, fidelity-exact-explicit-logarithmic-bound")
*Theorem 4.20.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF of size
$`s`. Then $`\mathbf I[f]\le O(\log s)`.
More precisely,
$$`
\mathbf I[f]\le 2\bigl(\lceil\log_2 s\rceil+1\bigr),
`
which implies the stated $`O(\log s)` claim. Select one satisfied
term on every true input, bound the number of negative pivotal coordinates by that
term's width, prove the tail estimate
$`\Pr[\operatorname{width}\ge k]\le s2^{-k}`, and sum the tails.
:::
