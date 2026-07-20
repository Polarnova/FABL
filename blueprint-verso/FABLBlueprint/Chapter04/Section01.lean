/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.DNFFormulas

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "DNF formulas" =>

:::definition "definition-4.1" (parent := "fabl-chapter-4") (lean := "FABL.Literal, FABL.Literal.eval, FABL.Literal.eval_eq_neg_one_iff, FABL.Literal.negate, FABL.DNFTerm, FABL.DNFTerm.width, FABL.DNFTerm.eval, FABL.DNFTerm.eval_eq_neg_one_iff, FABL.DNFFormula, FABL.DNFFormula.size, FABL.DNFFormula.width, FABL.DNFFormula.eval, FABL.DNFFormula.eval_eq_neg_one_iff, FABL.DNFFormula.toBooleanFunction") (tags := "section-4-1, fidelity-exact-sign-cube-literals")
*Definition 4.1.* A *DNF* (disjunctive normal form) formula over Boolean
variables $`x_1,\ldots,x_n` is a logical OR of *terms*, each of which is a
logical AND of *literals*. A literal is either a variable $`x_i` or its
logical negation $`\overline{x_i}`. No term contains both a variable and its
negation. The number of literals in a term is its *width*. A DNF formula is
often identified with the Boolean function $`f:\{0,1\}^n\to\{0,1\}` (or, in
$`\pm1` notation, $`f:\{-1,1\}^n\to\{-1,1\}`) that it computes.
In $`\pm1` notation, a literal is a coordinate together with its required
sign, with $`-1` representing logical True.
:::

:::lemma_ "example-4.2" (parent := "fabl-chapter-4") (lean := "FABL.signToBit, FABL.sort3, FABL.sort3ReducedDNF, FABL.sort3DNF, FABL.sort3ReducedDNF_toBooleanFunction, FABL.sort3DNF_toBooleanFunction, FABL.size_sort3ReducedDNF, FABL.width_sort3ReducedDNF, FABL.size_sort3DNF, FABL.width_sort3DNF") (uses := "definition-4.1") (tags := "section-4-1, fidelity-exact-canonical-sign-bridge-with-redundancy-note")
*Example 4.2.* The function $`\operatorname{Sort}_3:\{-1,1\}^3\to\{-1,1\}` is
defined by $`\operatorname{Sort}_3(x_1,x_2,x_3)=-1` if and only if the bits are
sorted in either nondecreasing or nonincreasing order under the canonical
embedding $`0\mapsto+1`, $`1\mapsto-1`. It is computed by the width-$`2` DNF
$$`
(x_1\wedge x_2)
\vee
(\overline{x_2}\wedge\overline{x_3})
\vee
(\overline{x_1}\wedge x_3)
\vee
(x_1\wedge\overline{x_3}).
`
The displayed formula has four terms, with its last term redundant; deleting it
gives the size-$`3`, width-$`2` formula asserted in the following paragraph of
the book. Both formulas compute $`\operatorname{Sort}_3`.
:::

:::lemma_ "support-exercise-4.1" (parent := "fabl-chapter-4") (lean := "FABL.DNFTerm.minterm, FABL.DNFTerm.width_minterm, FABL.DNFTerm.eval_minterm_eq_neg_one_iff, FABL.mintermDNF, FABL.size_mintermDNF_le, FABL.width_mintermDNF_le, FABL.mintermDNF_toBooleanFunction, FABL.exists_DNFFormula_size_width_bound, FABL.hasDNFSizeLE_two_pow, FABL.hasDNFWidthLE_dimension") (uses := "definition-4.1") (tags := "section-4-1, support, fidelity-exact")
*Exercise 4.1.* Every function $`f:\{-1,1\}^n\to\{-1,1\}` is computable by a
DNF formula of size at most $`2^n` and width at most $`n`. (Take the OR of
all full minterms corresponding to inputs where $`f` is True.)
:::

:::definition "definition-4.3" (parent := "fabl-chapter-4") (lean := "FABL.HasDNFSizeLE, FABL.HasDNFWidthLE, FABL.DNFsize, FABL.DNFwidth, FABL.hasDNFSizeLE_DNFsize, FABL.hasDNFWidthLE_DNFwidth") (uses := "definition-4.1, support-exercise-4.1") (tags := "section-4-1, fidelity-exact")
*Definition 4.3.* The *size* of a DNF formula is its number of terms. The
*width* is the maximum width of its terms. For
$`f:\{-1,1\}^n\to\{-1,1\}` write $`\operatorname{DNFsize}(f)` (respectively,
$`\operatorname{DNFwidth}(f)`) for the least size (respectively, width) of a
DNF formula computing $`f`.
:::

:::definition "definition-4.4" (parent := "fabl-chapter-4") (lean := "FABL.CNFFormula, FABL.CNFFormula.size, FABL.CNFFormula.width, FABL.CNFFormula.clauseEval, FABL.CNFFormula.eval, FABL.CNFFormula.toBooleanFunction, FABL.HasCNFSizeLE, FABL.HasCNFWidthLE") (uses := "definition-4.1") (tags := "section-4-1, fidelity-exact")
*Definition 4.4.* A *CNF* (conjunctive normal form) formula is a logical AND
of *clauses*, each of which is a logical OR of literals. Size and width are
defined exactly as for DNFs.
:::

:::lemma_ "support-exercise-4.2" (parent := "fabl-chapter-4") (lean := "FABL.CNFFormula.booleanDual, FABL.CNFFormula.switchAndOr, FABL.CNFFormula.clauseEval_neg_iff_termEval, FABL.CNFFormula.switchAndOr_toBooleanFunction, FABL.hasDNFSizeWidth_of_hasCNFSizeWidth") (uses := "definition-4.4") (tags := "section-4-1, support, fidelity-exact")
*Exercise 4.2.* Suppose a CNF computes $`f:\{0,1\}^n\to\{0,1\}`. Switching
ANDs with ORs yields a DNF computing the Boolean dual
$`f^\dagger:\{0,1\}^n\to\{0,1\}` defined by
$`f^\dagger(x)=\neg f(\neg x)` (cf. Exercise 1.8). In $`\pm1` notation this is
$`f^\dagger(x)=-f(-x)`.
:::

:::proposition "proposition-4.5" (parent := "fabl-chapter-4") (lean := "FABL.booleanFunctionOfBinary, FABL.binaryOfBooleanFunction, FABL.F₂DecisionTree.Path.toDNFTerm, FABL.F₂DecisionTree.Path.width_toDNFTerm, FABL.F₂DecisionTree.Path.eval_toDNFTerm_eq_neg_one_iff, FABL.F₂DecisionTree.Path.toCNFClause, FABL.F₂DecisionTree.Path.width_toCNFClause, FABL.F₂DecisionTree.Path.clauseEval_toCNFClause_eq_one_iff, FABL.F₂DecisionTree.toDNFFormula, FABL.F₂DecisionTree.size_toDNFFormula_le, FABL.F₂DecisionTree.width_toDNFFormula_le, FABL.F₂DecisionTree.toDNFFormula_toBooleanFunction, FABL.F₂DecisionTree.hasDNFSizeWidth_of_decisionTree, FABL.F₂DecisionTree.hasDNFSizeWidth_of_computes, FABL.F₂DecisionTree.toCNFFormula, FABL.F₂DecisionTree.size_toCNFFormula_le, FABL.F₂DecisionTree.width_toCNFFormula_le, FABL.F₂DecisionTree.eval_toCNFFormula_eq_one, FABL.F₂DecisionTree.toCNFFormula_toBooleanFunction, FABL.F₂DecisionTree.hasCNFSizeWidth_of_decisionTree, FABL.F₂DecisionTree.hasCNFSizeWidth_of_computes, FABL.exists_DNF_of_decisionTree, FABL.exists_CNF_of_decisionTree") (uses := "definition-4.1, definition-4.3, definition-4.4, definition-3.13, definition-3.14") (tags := "section-4-1, fidelity-exact-binary-sign-bridge")
*Proposition 4.5.* Let $`f:\{0,1\}^n\to\{0,1\}` be computable by a decision
tree $`T` of size $`s` and depth $`k`. Then $`f` is computable by a DNF (and
also by a CNF) of size at most $`s` and width at most $`k`.
Take one DNF term for each True leaf path and one clause excluding each False
leaf path. Under the standard
$`\mathbb F_2\leftrightarrow\{\pm1\}` correspondence, these formulas compute
$`f` and have the asserted size and width.
:::

:::lemma_ "example-4.6" (parent := "fabl-chapter-4") (lean := "FABL.sort3DecisionTreeDNFPrefix, FABL.sort3DecisionTreeDNFPrinted, FABL.size_sort3DecisionTreeDNFPrinted, FABL.width_sort3DecisionTreeDNFPrinted, FABL.sort3DecisionTreeDNFPrinted_counterexample, FABL.sort3DecisionTreeDNF, FABL.size_sort3DecisionTreeDNF, FABL.width_sort3DecisionTreeDNF, FABL.sort3DecisionTreeDNF_toBooleanFunction") (uses := "example-4.2, proposition-4.5, definition-3.13") (tags := "section-4-1, fidelity-book-erratum")
*Example 4.6.* Converting the decision tree for $`\operatorname{Sort}_3` from
Figure 3.1 by the construction of Proposition 4.5 is printed as
$$`
(\overline{x_1}\wedge\overline{x_3}\wedge\overline{x_2})
\vee(\overline{x_1}\wedge x_3)
\vee(x_1\wedge\overline{x_2}\wedge\overline{x_3})
\vee(x_2\wedge x_3).
`
It has size $`4` (at most the tree size $`6`) and width $`3` (at most the tree
depth $`3`). In the May 2021 edition the printed formula is not equivalent to
$`\operatorname{Sort}_3`: on the sorted input $`110` it is False. Replacing
the last term by $`x_1\wedge x_2` gives a formula that computes
$`\operatorname{Sort}_3` with the same size and width.
:::

:::lemma_ "support-exercise-2.10" (parent := "fabl-chapter-4") (lean := "FABL.IsNegOnePivotal, FABL.booleanInfluence_eq_two_mul_negOnePivotal_probability, FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal") (uses := "definition-2.12, definition-2.13, definition-2.27, proposition-2.28") (tags := "section-4-1, support, fidelity-exact")
*Exercise 2.10 (negative-one-pivotal form used by Proposition 4.7).* For
$`f:\{-1,1\}^n\to\{-1,1\}`,
$$`
\mathbf I[f]
=2\,\mathbb E_{\boldsymbol x\sim\{-1,1\}^n}
  \bigl[\#\{i : i\text{ is }(-1)\text{-pivotal for }f\text{ on }\boldsymbol x\}\bigr],
`
where coordinate $`i` is *(-1)-pivotal* on $`x` if $`f(x)=-1` (True) and
$`f(x^{\oplus i})=1` (False). Equivalently,
$`\operatorname{Inf}_i[f]=2\Pr[i\text{ is }(-1)\text{-pivotal}]`.
:::

:::proposition "proposition-4.7" (parent := "fabl-chapter-4") (lean := "FABL.card_negOnePivotal_le_width, FABL.totalInfluence_le_two_mul_of_hasDNFWidthLE, FABL.sq_discreteDerivative_booleanDual, FABL.totalInfluence_booleanDual, FABL.totalInfluence_le_two_mul_of_hasCNFWidthLE") (uses := "definition-4.3, definition-4.4, support-exercise-2.10") (tags := "section-4-1, fidelity-exact")
*Proposition 4.7.* Suppose $`f:\{-1,1\}^n\to\{-1,1\}` has
$`\operatorname{DNFwidth}(f)\le w`. Then $`\mathbf I[f]\le 2w`.
(The same bound holds for CNFs of width at most $`w`, since
$`\mathbf I[f^\dagger]=\mathbf I[f]`.)
:::

:::corollary "corollary-4.8" (parent := "fabl-chapter-4") (lean := "FABL.isFourierSpectrumConcentratedUpTo_of_hasDNFWidthLE") (uses := "proposition-4.7, proposition-3.2, definition-3.1") (tags := "section-4-1, fidelity-exact")
*Corollary 4.8.* Let $`f:\{-1,1\}^n\to\{-1,1\}` have
$`\operatorname{DNFwidth}(f)\le w`. Then for every $`\epsilon>0`, the Fourier
spectrum of $`f` is $`\epsilon`-concentrated on degree up to $`2w/\epsilon`.
:::

:::proposition "proposition-4.9" (parent := "fabl-chapter-4") (lean := "FABL.DNFFormula.truncateWidth, FABL.DNFFormula.width_truncateWidth_le, FABL.dnfWidthTruncationCutoff, FABL.relativeHammingDist_truncateWidth_le, FABL.exists_DNF_width_truncation_close, FABL.CNFFormula.booleanDual_involutive, FABL.CNFFormula.relativeHammingDist_booleanDual, FABL.CNFFormula.truncateWidth, FABL.CNFFormula.width_truncateWidth_le, FABL.CNFFormula.relativeHammingDist_truncateWidth_le_of_size_le, FABL.exists_CNF_width_truncation_close") (uses := "definition-4.1, definition-4.3, definition-4.4, definition-1.10") (tags := "section-4-1, fidelity-book-wording-clarified")
*Proposition 4.9.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF (or
CNF) of size $`s` and let $`\epsilon\in(0,1]`. Then $`f` is $`\epsilon`-close
(in relative Hamming distance) to a function $`g` computable by a DNF of
width $`\log(s/\epsilon)`.

The May 2021 text prints “DNF” in the conclusion even for the parenthetical CNF input, then says
that the analogous proof works for CNFs. Thus a DNF input gives a DNF output
and a CNF input gives a CNF output, both with the natural cutoff
$`\lceil\log_2(s/\epsilon)\rceil`.
:::

:::lemma_ "support-exercise-3.17" (parent := "fabl-chapter-4") (lean := "FABL.fourierCoeff_sub, FABL.IsFourierSpectrumConcentratedOn.transfer_of_uniformLpNorm_sub_sq_le") (uses := "definition-3.28, parseval") (tags := "section-4-1, support, fidelity-exact")
*Exercise 3.17 (concentration transfer).* Suppose the Fourier spectrum of
$`f:\{-1,1\}^n\to\mathbb R` is $`\epsilon_1`-concentrated on a collection
$`\mathcal F`, and $`g:\{-1,1\}^n\to\mathbb R` satisfies
$`\lVert f-g\rVert_2^2\le\epsilon_2`. Then the Fourier spectrum of $`g` is
$`2(\epsilon_1+\epsilon_2)`-concentrated on $`\mathcal F`.
:::

:::theorem "mansours-conjecture" (parent := "fabl-chapter-4") (uses := "definition-4.3, definition-3.28") (tags := "section-4-1, open, conjecture")
*Mansour's Conjecture.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a DNF
of size $`s>1` and let $`\epsilon\in(0,1/2]`.

*Strong form.* The Fourier spectrum of $`f` is $`\epsilon`-concentrated on a
collection $`\mathcal F` with $`|\mathcal F|\le s^{O(\log(1/\epsilon))}`.

*Weaker form.* If $`s\le\operatorname{poly}(n)` and $`\epsilon>0` is any fixed
constant, then one may take $`|\mathcal F|\le\operatorname{poly}(n)`.

This conjecture remains open.
:::
