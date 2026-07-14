/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.Switching

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Håstad's Switching Lemma and the spectrum of DNFs" =>

:::lemma_ "support-exercise-4.19" (lean := "FABL.freeIndicator, FABL.expect_freeIndicator, FABL.expect_sum_freeIndicator, FABL.indicator_nonempty_inter_le_sum_free, FABL.expect_nonempty_inter_le, FABL.DNFTerm.supportIndices, FABL.DNFTerm.card_supportIndices_eq_width, FABL.dnfHasFreeSupportIndicator, FABL.dnfTermFreeSupportSum, FABL.dnfHasFreeSupportIndicator_le_sum, FABL.expect_dnfTermFreeSupportSum") (uses := "definition-4.1, definition-4.15") (tags := "section-4-4, support, fidelity-weak-size-dependent")
*Exercise 4.19 (Baby Switching Lemma with constant $`3`).* Let
$`\varphi=T_1\vee\cdots\vee T_s` be a DNF of width $`w\ge1` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction with
$`\delta\le1/3`. If a restriction is *bad* when
$`\varphi_{\boldsymbol J\mid\boldsymbol z}` is non-constant, then by a
uniqueness/extension counting argument on the first non-trivial restricted
term one obtains
$`\Pr[(\boldsymbol J\mid\boldsymbol z)\text{ is bad}]\le 3\delta w`.
Production currently associates a size-dependent free-support collision bound
$`\Pr[\text{some term support meets free set}]\le s\cdot w\cdot\delta`, which is
necessary for non-constancy of the restricted DNF. The size-independent
constant $`3` (Exercise 4.19) and $`5` (Baby Switching) remain open.
:::

:::theorem "baby-switching-lemma" (lean := "FABL.babySwitching_sizeDependent") (uses := "definition-4.3, definition-4.15, support-exercise-4.19") (tags := "section-4-4, fidelity-weak-size-dependent")
*Baby Switching Lemma.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF
or CNF of width at most $`w` and let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`\delta`-random restriction. Then
$$`
\Pr\bigl[f_{\boldsymbol J\mid\boldsymbol z}\text{ is not a constant function}\bigr]
\le 5\delta w.
`
This is the $`k=1` case of Håstad's Switching Lemma. Production associates the
proved size-dependent intermediate bound of Exercise 4.19 above; the
size-independent constant $`5` remains open.
:::

:::theorem "hastads-switching-lemma" (uses := "definition-4.3, definition-4.15, definition-3.14") (tags := "section-4-4")
*Håstad's Switching Lemma.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a
DNF or CNF of width at most $`w` and let $`(\boldsymbol J\mid\boldsymbol z)` be a
$`\delta`-random restriction. Then for every $`k\in\mathbb N^+`,
$$`
\Pr\bigl[\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})\ge k\bigr]
\le(5\delta w)^k,
`
where $`\operatorname{DT}(g)` denotes the decision-tree depth of $`g`. The
bound has no dependence on the DNF size or on $`n`.
:::

:::lemma_ "lemma-4.21" (uses := "definition-4.15, definition-4.16, definition-3.1, proposition-3.16, proposition-4.17") (tags := "section-4-4")
*Lemma 4.21.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction with
$`\delta>0`. Fix $`k\in\mathbb N^+` and write
$`\epsilon=\Pr[\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})\ge k]`.
Then the Fourier spectrum of $`f` is $`3\epsilon`-concentrated on degree up
to $`3k/\delta`.
:::

:::theorem "theorem-4.22" (uses := "hastads-switching-lemma, lemma-4.21, definition-4.3") (tags := "section-4-4")
*Theorem 4.22.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` is computable by a DNF of
width $`w`. Then the Fourier spectrum of $`f` is $`\epsilon`-concentrated on
degree up to $`O\bigl(w\log(1/\epsilon)\bigr)`.
:::

:::lemma_ "support-exercise-4.11" (uses := "proposition-3.16, proposition-4.17") (tags := "section-4-4, support")
*Exercise 4.11.* In the setting of Lemma 4.21, replace the degree bound for
depth-$`k` decision trees by the Fourier $`1`-norm bound
$`\|\widehat g\|_1\le 2^{\operatorname{DT}(g)}` to obtain the weighted
coefficient estimate used by Lemma 4.23.
:::

:::lemma_ "lemma-4.23" (uses := "support-exercise-4.11, definition-4.15") (tags := "section-4-4")
*Lemma 4.23.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and let
$`(\boldsymbol J\mid\boldsymbol z)` be a $`\delta`-random restriction. Then
$$`
\sum_{U\subseteq[n]}\delta^{|U|}\,\bigl|\widehat f(U)\bigr|
\le
\mathbb E_{(\boldsymbol J\mid\boldsymbol z)}
  \Bigl[2^{\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})}\Bigr].
`
:::

:::theorem "theorem-4.24" (uses := "hastads-switching-lemma, lemma-4.23, definition-4.3") (tags := "section-4-4")
*Theorem 4.24.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` is computable by a DNF of
width $`w`. Then for every $`k`,
$$`
\sum_{|U|\le k}\bigl|\widehat f(U)\bigr|
\le 2\cdot(20w)^k.
`
:::

:::theorem "theorem-4.25" (uses := "theorem-4.22, theorem-4.24, support-exercise-3.16, support-exercise-3.17, definition-4.3") (tags := "section-4-4")
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
:::
