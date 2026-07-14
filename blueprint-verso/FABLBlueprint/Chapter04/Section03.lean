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

:::definition "definition-4.15" (lean := "FABL.deltaRandomSubsetWeight, FABL.deltaRandomSubsetWeight_nonneg, FABL.sum_deltaRandomSubsetWeight, FABL.expectDeltaRandomSubset, FABL.expectRandomRestriction, FABL.coordRestrictionWeight, FABL.sum_coordRestrictionWeight, FABL.restrictionAssignmentWeight, FABL.sum_restrictionAssignmentWeight") (tags := "section-4-3, fidelity-exact")
*Definition 4.15.* For $`\delta\in[0,1]`, a set $`J` is a *$`\delta`-random
subset* of a finite set $`N` if each element of $`N` is included independently
with probability $`\delta`. A *$`\delta`-random restriction* on
$`\{-1,1\}^n` is a pair $`(\boldsymbol J\mid\boldsymbol z)` obtained by first
drawing a $`\delta`-random subset $`\boldsymbol J\subseteq[n]` and then drawing
$`\boldsymbol z\sim\{-1,1\}^{\boldsymbol J}` uniformly. Coordinate $`i` is
*free* if $`i\in\boldsymbol J` and *fixed* otherwise. Equivalently, each
coordinate is independently free with probability $`\delta` and fixed to
$`\pm1` with probability $`(1-\delta)/2` each.
:::

:::definition "definition-4.16" (lean := "FABL.extendedSignRestriction, FABL.extendedSignRestriction_apply, FABL.extendedSignRestriction_setCoordinate_of_not_mem") (uses := "definition-3.18") (tags := "section-4-3, fidelity-exact")
*Definition 4.16.* Given $`f:\{-1,1\}^n\to\mathbb R`, free coordinates
$`I\subseteq[n]`, and a fixing $`z\in\{-1,1\}^{\overline I}` of the remaining
coordinates, one may identify the restricted function
$`f_{I\mid z}:\{-1,1\}^I\to\mathbb R` with its extension
$`f_{I\mid z}:\{-1,1\}^n\to\mathbb R` that holds the coordinates in
$`\overline I` fixed at $`z` and ignores the values of those fixed
coordinates as free inputs. When dealing with random restrictions this
extension convention is the default.
:::

:::proposition "proposition-4.17" (lean := "FABL.expect_fourierCoeff_empty_randomRestriction, FABL.sum_deltaRandomSubsetWeight_supset, FABL.ambientRestrictionFourierCoeff, FABL.ambientRestrictionFourierCoeff_eq, FABL.expect_ambientRestrictionFourierCoeff, FABL.expect_fourierCoeff_randomRestriction, FABL.liftFreeFrequency_freeFrequencyPart_of_subset, FABL.expect_sq_ambientRestrictionFourierCoeff, FABL.subset_of_inter_eq, FABL.subset_of_inter_eq_left, FABL.sum_deltaRandomSubsetWeight_inter_eq, FABL.sum_sq_fourier_of_inter_eq, FABL.expect_sq_fourierCoeff_randomRestriction") (uses := "definition-4.15, definition-4.16, corollary-3.22") (tags := "section-4-3, fidelity-exact")
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
Production proves both displays: the first moment via free-set weights
$`\sum_{J\supseteq S}w_\delta(J)=\delta^{|S|}` and Corollary 3.22; the second moment via
the free/fixed Parseval identity on each free set, reindexing to ambient frequencies
with $`U\cap J=S`, and the intersection weight formula
$`\sum_{J:U\cap J=S}w_\delta(J)=\delta^{|S|}(1-\delta)^{|U\setminus S|}` when $`S\subseteq U`.
:::

:::corollary "corollary-4.18" (lean := "FABL.sum_deltaRandomSubsetWeight_mem, FABL.freePart, FABL.discreteDerivative_extendedSignRestriction_of_mem, FABL.expect_sq_discreteDerivative_combine, FABL.expect_sq_discreteDerivative_product, FABL.expect_influence_extendedSignRestriction_of_mem, FABL.expect_influence_extended_randomRestriction, FABL.expect_totalInfluence_extended_randomRestriction") (uses := "proposition-4.17, theorem-2.20, definition-2.27") (tags := "section-4-3, fidelity-exact")
*Corollary 4.18.* Fix $`f:\{-1,1\}^n\to\mathbb R` and $`i\in[n]`. If
$`(\boldsymbol J\mid\boldsymbol z)` is a $`\delta`-random restriction, then
$`\mathbb E[\operatorname{Inf}_i[f_{\boldsymbol J\mid\boldsymbol z}]]
=\delta\operatorname{Inf}_i[f]`. Hence also
$`\mathbb E[\mathbf I[f_{\boldsymbol J\mid\boldsymbol z}]]=\delta\mathbf I[f]`.
Proved Fourier-free (Exercise 4.9 style): condition on whether $`i` is free; when free,
the free/fixed product measure recovers ambient influence; free-set weight of
$`\{J:i\in J\}` is $`\delta`$.
:::

:::lemma_ "lemma-4.19" (lean := "FABL.literal_not_falsified_local_weight, FABL.DNFTerm.notFalsified, FABL.term_not_falsified_weight, FABL.restrictedWidth_ge_probability_le") (uses := "definition-4.1, definition-4.15, definition-4.16") (tags := "section-4-3, fidelity-exact-coordinate-restriction-model")
*Lemma 4.19.* Let $`T` be a DNF term over $`\{-1,1\}^n` and fix
$`w\in\mathbb N^+`. Let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`(1/2)`-random restriction on $`\{-1,1\}^n`. Then
$$`
\Pr\bigl[\operatorname{width}(T_{\boldsymbol J\mid\boldsymbol z})\ge w\bigr]
\le\Bigl(\frac34\Bigr)^w.
`
Production formalizes the half-random restriction as an independent product over
coordinates (free with weight $`1/2`, fixed to each sign with weight $`1/4`),
proves the non-falsification weight equals $`(3/4)^{\operatorname{width}(T)}`,
and obtains the stated tail bound.
:::

:::theorem "theorem-4.20" (lean := "FABL.totalInfluence_le_of_hasDNFSizeLE") (uses := "lemma-4.19, proposition-4.7, corollary-4.18, definition-4.3") (tags := "section-4-3, fidelity-weak-dimension-bound")
*Theorem 4.20.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF of size
$`s`. Then $`\mathbf I[f]\le O(\log s)`.
The production declaration currently records the honest dimension-scale bound
$`\mathbf I[f]\le 2n` obtained from Proposition 4.7 and the universal width-$`n`
DNF representation; the book’s $`O(\log s)` constant-factor refinement via
Lemma 4.19 and Corollary 4.18 is the intended strengthening.
:::
