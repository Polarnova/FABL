/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.DNFFourier

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Håstad's Switching Lemma and the spectrum of DNFs" =>

:::lemma_ "support-exercise-4.19" (lean := "FABL.DNFTerm.Compatible, FABL.DNFFormula.IsBadRestriction, FABL.DNFFormula.badRestrictions, FABL.DNFFormula.badExtension, FABL.DNFFormula.badExtensionMap, FABL.DNFFormula.badExtensionFiber, FABL.DNFFormula.badExtensionFiber_card_le_width, FABL.DNFFormula.restrictionAssignmentWeightAt_badExtension_eq, FABL.DNFFormula.restrictionAssignmentWeightAt_badExtension_le, FABL.DNFFormula.badRestrictionWeight, FABL.exercise4_19, FABL.DNFFormula.badRestrictionWeight_eq_coordSwitchingFailureProbability, FABL.exercise4_19_switchingFailureProbability") (uses := "definition-4.1, definition-4.15") (tags := "section-4-4, support, fidelity-exact-coordinate-restriction-extension-counting")
*Exercise 4.19 (Baby Switching Lemma with constant $`3`).* Let
$`\varphi=T_1\vee\cdots\vee T_s` be a DNF of width $`w\ge1` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction with
$`\delta\le1/3`. Call a restriction $`R=(J\mid z)` *bad* when
$`\varphi_{J\mid z}` is non-constant. For each bad $`R`, let $`T_i` be the
first restricted term that is neither constantly True nor constantly False,
and let $`j` be the first surviving variable in that term.

(a) There is a unique extension $`R'=(J\setminus\{j\}\mid z')` that does not
falsify $`T_i`. (b) No $`R'` is produced by more than $`w` bad restrictions.
(c) Their exact random-restriction weights satisfy
$$`
\Pr[(\boldsymbol J\mid\boldsymbol z)=R]
=\frac{2\delta}{1-\delta}\Pr[(\boldsymbol J\mid\boldsymbol z)=R'].
`
(d) Consequently
$`\Pr[(\boldsymbol J\mid\boldsymbol z)\text{ is bad}]\le3\delta w`.

Production implements this first-compatible-term extension map, proves its fiber bound, proves
the exact ratio in (c), and transports the final estimate between the independent-coordinate and
$`(\boldsymbol J\mid\boldsymbol z)` restriction models.
:::

:::theorem "baby-switching-lemma" (lean := "FABL.babySwitchingLemma_dnf, FABL.switchingFailureProbability_booleanDual, FABL.babySwitchingLemma") (uses := "definition-4.3, definition-4.4, definition-4.15, support-exercise-4.19") (tags := "section-4-4, fidelity-exact")
*Baby Switching Lemma.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF
or CNF of width at most $`w` and let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`\delta`-random restriction. Then
$$`
\Pr\bigl[f_{\boldsymbol J\mid\boldsymbol z}\text{ is not a constant function}\bigr]
\le 5\delta w.
`
This is the $`k=1` case of Håstad's Switching Lemma. Production proves the
size-independent constant $`5` for DNFs and transfers it to CNFs by Boolean
duality.
:::

:::theorem "hastads-switching-lemma" (lean := "FABL.hastadSwitchingLemma_dnf, FABL.hastadSwitchingLemma") (uses := "definition-4.3, definition-4.4, definition-4.15, definition-3.14") (tags := "section-4-4, fidelity-exact")
*Håstad's Switching Lemma.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a
DNF or CNF of width at most $`w` and let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`\delta`-random restriction. Then for every $`k\in\mathbb N`,
$$`
\Pr\bigl[\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})\ge k\bigr]
\le(5\delta w)^k,
`
where $`\operatorname{DT}(g)` denotes the decision-tree depth of $`g`. The
bound has no dependence on the DNF size or on $`n`.
:::

:::lemma_ "lemma-4.21" (lean := "FABL.lemma4_21") (uses := "definition-4.15, definition-4.16, definition-3.1, proposition-3.16, proposition-4.17") (tags := "section-4-4, fidelity-exact")
*Lemma 4.21.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction with
$`\delta>0`. Fix $`k\in\mathbb N^+` and write
$`\epsilon=\Pr[\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})\ge k]`.
Then the Fourier spectrum of $`f` is $`3\epsilon`-concentrated on degree up
to $`3k/\delta`.

Production uses the exact failure probability as $`\epsilon` and the exact real cutoff
$`3k/\delta`; the interval condition $`\delta\le 1` is part of the random-restriction
parameter domain.
:::

:::theorem "theorem-4.22" (lean := "FABL.dnfSwitchingDepth, FABL.theorem4_22") (uses := "hastads-switching-lemma, lemma-4.21, definition-4.3") (tags := "section-4-4, fidelity-finite-explicit-asymptotic-bridge")
*Theorem 4.22.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` is computable by a DNF of
width $`w`. Then the Fourier spectrum of $`f` is $`\epsilon`-concentrated on
degree up to $`O\bigl(w\log(1/\epsilon)\bigr)`.

Production proves the explicit cutoff
$`30w\lceil\log_2(3/\epsilon)\rceil` for $`0<\epsilon\le1`, including the
$`w=0` constant-function endpoint.
:::

:::lemma_ "support-exercise-4.11" (lean := "FABL.fourierCoeff_extendedSignRestriction_liftFree, FABL.fourierCoeff_extendedSignRestriction, FABL.sum_abs_ambientRestrictionFourierCoeff, FABL.exercise4_11_restriction") (uses := "proposition-3.16, proposition-4.17") (tags := "section-4-4, support, fidelity-exact")
*Exercise 4.11.* Prove Lemma 4.23.

Production supplies the proof route by combining the restriction/Fourier coefficient bridge with
$`\|\widehat g\|_1\le2^{\operatorname{DT}(g)}` for each restricted Boolean function.
:::

:::lemma_ "lemma-4.23" (lean := "FABL.abs_expectRandomRestriction_le_expect_abs, FABL.sum_expectRandomRestriction, FABL.expectRandomRestriction_mono, FABL.lemma4_23") (uses := "support-exercise-4.11, definition-4.15, proposition-4.17") (tags := "section-4-4, fidelity-exact")
*Lemma 4.23.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction. Then
$$`
\sum_{U\subseteq[n]}\delta^{|U|}\,\bigl|\widehat f(U)\bigr|
\le
\mathbb E_{(\boldsymbol J\mid\boldsymbol z)}
  \Bigl[2^{\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})}\Bigr].
`
:::

:::theorem "theorem-4.24" (lean := "FABL.lowDegreeFourierOneNorm_le_two_mul_inv_pow_of_expected_two_pow_le, FABL.theorem4_24_of_switchingFailureProbability_le_quarter, FABL.theorem4_24") (uses := "hastads-switching-lemma, lemma-4.23, definition-4.3") (tags := "section-4-4, fidelity-book-endpoint-corrected")
*Theorem 4.24.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` is computable by a DNF of
width $`w`. Then for every $`k`,
$$`
\sum_{|U|\le k}\bigl|\widehat f(U)\bigr|
\le 2\cdot(20w)^k.
`

The printed statement requires the endpoint condition $`w\ge1`: for $`w=0` and $`k>0`, a
constant function has $`|\widehat f(\varnothing)|=1` while the displayed right-hand side is zero.
Production proves the corrected positive-width form with the same constant.
:::

:::theorem "theorem-4.25" (lean := "FABL.dnfSpectralConcentrationDegree, FABL.dnfSpectralFamilySizeBound, FABL.theorem4_25") (uses := "theorem-4.22, theorem-4.24, support-exercise-3.16, support-exercise-3.17, definition-4.3") (tags := "section-4-4, fidelity-finite-explicit-asymptotic-bridge")
*Theorem 4.25.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF of width
$`w\ge2`. Then for every $`\epsilon\in(0,1/2]`, the Fourier spectrum of $`f` is
$`\epsilon`-concentrated on a collection $`\mathcal F` with
$$`
|\mathcal F|\le w^{O\bigl(w\log(1/\epsilon)\bigr)}.
`
In particular, width-$`O(\log n)` DNFs with constant $`\epsilon` are
concentrated on a collection of cardinality $`n^{O(\log\log n)}`. Combined
with Proposition 4.9 and Exercise 3.17, size-$`s` DNFs are
$`\epsilon`-concentrated on a collection of cardinality at most
$`(s/\epsilon)^{O(\log\log(s/\epsilon)\cdot\log(1/\epsilon))}`.
Production replaces the asymptotic notation by the finite degree
$`30w\lceil\log_2(12/\epsilon)\rceil` and the explicit concentrating-family
bound obtained from its low-degree Fourier one-norm estimate.
:::
