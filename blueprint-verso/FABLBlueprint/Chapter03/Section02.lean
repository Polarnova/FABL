/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter03.SubspacesAndDecisionTrees

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Subspaces and decision trees" =>

:::lemma_ "equation-3.1" (lean := "FABL.f₂Support, FABL.f₂CubeOfFinset, FABL.f₂CubeEquivFinset, FABL.f₂DotProduct_eq_coordinateSum_f₂Support, FABL.vectorWalshCharacter, FABL.vectorWalshCharacter_apply, FABL.vectorWalshCharacter_f₂CubeOfFinset_singleton, FABL.vectorWalshCharacter_zero, FABL.vectorWalshCharacter_mul, FABL.vectorWalshCharacter_injective, FABL.vectorFourierCoeff, FABL.vector_fourier_expansion") (uses := "fact-1.6, theorem-1.1, theorem-1.5") (tags := "section-3-2, support, fidelity-exact-vector-indexing")
*Vector-indexed Fourier characters and Equation (3.1).* Regard
$`\mathbb F_2^n` as an $`n`-dimensional vector space over $`\mathbb F_2`.
For $`\gamma,x\in\mathbb F_2^n`, set
$`\chi_\gamma(x)=(-1)^{\gamma\mathbin\cdot x}`,
where the dot product is computed in $`\mathbb F_2`. Then $`\chi_0` is the
constant-one function, $`\chi_{e_i}` is the $`i`th dictator, and
$$`
\chi_\beta\chi_\gamma=\chi_{\beta+\gamma}
\qquad\text{for all }\beta,\gamma\in\mathbb F_2^n. \tag{3.1}
`
The indexing is injective and respects addition and multiplication, so the
character family is identified with the additive group $`\mathbb F_2^n`.
Writing a second copy of the group as
$`\widehat{\mathbb F_2^n}`, every $`f:\mathbb F_2^n\to\mathbb R` has the
Fourier expansion
$$`
f(x)=\sum_{\gamma\in\widehat{\mathbb F_2^n}}
  \widehat f(\gamma)\chi_\gamma(x).
`
:::

:::definition "definition-3.8" (lean := "FABL.spectralPNorm, FABL.spectralInfinityNorm, FABL.vector_plancherel, FABL.uniformLpNorm_two_eq_spectralPNorm_two") (uses := "equation-3.1, plancherel") (tags := "section-3-2, fidelity-exact-with-infinity-convention")
*Definition 3.8.* For $`f:\{-1,1\}^n\to\mathbb R` and
$`1\le p<\infty`, the *Fourier* or *spectral $`p`-norm* is
$$`
\lVert\widehat f\rVert_p
=\left(
  \sum_{\gamma\in\widehat{\mathbb F_2^n}}
    |\widehat f(\gamma)|^p
 \right)^{1/p}.
`
The sum uses counting measure on $`\widehat{\mathbb F_2^n}`. For the
endpoint used below,
$$`
\lVert\widehat f\rVert_\infty
=\max_{\gamma\in\widehat{\mathbb F_2^n}}|\widehat f(\gamma)|.
`
Parseval's Theorem is equivalently
$`\lVert f\rVert_2=\lVert\widehat f\rVert_2`.
:::

:::definition "definition-3.9" (lean := "FABL.spectralSparsity") (uses := "equation-3.1") (tags := "section-3-2, fidelity-exact")
*Definition 3.9.* The *Fourier* or *spectral sparsity* of
$`f:\{-1,1\}^n\to\mathbb R` is
$$`
\operatorname{sparsity}(\widehat f)
=|\operatorname{supp}(\widehat f)|
=\#\{\gamma\in\widehat{\mathbb F_2^n}:\widehat f(\gamma)\ne0\}.
`
:::

:::definition "definition-3.10" (lean := "FABL.IsVectorFourierGranular, FABL.isVectorFourierGranular_iff") (uses := "equation-3.1, support-exercise-1.11b-granularity") (tags := "section-3-2, fidelity-exact")
*Definition 3.10.* The Fourier transform $`\widehat f` is
*$`\epsilon`-granular* if every Fourier coefficient is an integer multiple of
$`\epsilon`; that is,
$$`
\forall\gamma\in\widehat{\mathbb F_2^n}\;\exists z\in\mathbb Z,
\qquad \widehat f(\gamma)=z\epsilon.
`
:::

:::lemma_ "support-orthogonal-complement-f2" (lean := "FABL.f₂DotProductBilin, FABL.f₂DotProductBilin_nondegenerate, FABL.perpendicularSubspace, FABL.mem_perpendicularSubspace_iff, FABL.f₂Codimension, FABL.finrank_perpendicularSubspace, FABL.perpendicularSubspace_perpendicularSubspace, FABL.card_perpendicularSubspace") (uses := "equation-3.1") (tags := "section-3-2, support, fidelity-exact")
*Perpendicular subspaces over $`\mathbb F_2`.* For a linear subspace
$`A\le\mathbb F_2^n`, define
$$`
A^\perp
=\{\gamma\in\widehat{\mathbb F_2^n}:
  \gamma\mathbin\cdot x=0\text{ for every }x\in A\}.
`
Then
$$`
\dim A^\perp=n-\dim A,
\qquad
A=(A^\perp)^\perp.
`
The quantity $`\dim A^\perp` is the codimension of $`A`.
:::

:::proposition "proposition-3.11" (lean := "FABL.subspaceCharacterSum, FABL.inversePerpendicularCard, FABL.setIndicator_submodule_fourier_expansion, FABL.subsetDensity_submodule_fourier_expansion, FABL.subspaceUniformProbability_eq_inversePerpendicularCard") (uses := "definition-1.22, equation-3.1, support-orthogonal-complement-f2") (tags := "section-3-2, fidelity-exact")
*Proposition 3.11.* If $`A\le\mathbb F_2^n` has
$`\operatorname{codim}A=\dim A^\perp=k`,
then its indicator and its uniform probability density have the Fourier
expansions
$$`
\mathbf1_A
=\sum_{\gamma\in A^\perp}2^{-k}\chi_\gamma,
\qquad
\varphi_A
=\sum_{\gamma\in A^\perp}\chi_\gamma.
`
:::

:::lemma_ "support-affine-subspaces-and-subcubes" (lean := "FABL.binaryAffineSubspace, FABL.mem_binaryAffineSubspace_iff_add_mem, FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity, FABL.F₂DecisionTree.coordinateSubcube, FABL.F₂DecisionTree.coordinateSubcube_eq_binaryAffineSubspace") (uses := "equation-3.1, support-orthogonal-complement-f2") (tags := "section-3-2, support, fidelity-exact")
*Affine subspaces, parity conditions, and subcubes.* If
$`H\le\mathbb F_2^n` and $`a\in\mathbb F_2^n`, then the affine subspace
$`A=H+a` is equivalently
$$`
A=\{x\in\mathbb F_2^n:
  \gamma\mathbin\cdot x=\gamma\mathbin\cdot a
  \text{ for every }\gamma\in H^\perp\}.
`
When the displayed parity conditions specialize to coordinate equations
$`x_i=a_i`, their solution set is a *subcube*; the Lean declaration identifies
this coordinate subcube with the corresponding affine subspace.
:::

:::lemma_ "support-exercise-3.11" (lean := "FABL.setIndicator_binaryAffineSubspace_apply, FABL.affineSubspaceUniformProbability_eq_inversePerpendicularCard, FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff, FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem, FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem, FABL.sum_abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace") (uses := "definition-3.8, definition-3.9, definition-3.10, proposition-3.11, support-affine-subspaces-and-subcubes") (tags := "section-3-2, support, fidelity-exact")
*Exercise 3.11.* Derive the affine extension of Proposition 3.11. Namely, if
$`A=H+a` has codimension $`k`, prove
$$`
\widehat{\mathbf1_A}(\gamma)
=\begin{cases}
  \chi_\gamma(a)2^{-k},&\gamma\in H^\perp,\\
  0,&\gamma\notin H^\perp,
\end{cases}
`
and hence
$$`
\varphi_A=\sum_{\gamma\in H^\perp}
  \chi_\gamma(a)\chi_\gamma.
`
Also prove
$$`
\operatorname{sparsity}(\widehat{\mathbf1_A})=2^k,
\qquad
\lVert\widehat{\mathbf1_A}\rVert_\infty=2^{-k},
\qquad
\lVert\widehat{\mathbf1_A}\rVert_1=1,
`
and that $`\widehat{\mathbf1_A}` is $`2^{-k}`-granular.
:::

:::proposition "proposition-3.12" (lean := "FABL.setIndicator_binaryAffineSubspace_fourier_expansion, FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem, FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem, FABL.subsetDensity_binaryAffineSubspace_fourier_expansion, FABL.spectralSparsity_setIndicator_binaryAffineSubspace, FABL.isVectorFourierGranular_setIndicator_binaryAffineSubspace, FABL.spectralInfinityNorm_setIndicator_binaryAffineSubspace, FABL.spectralPNorm_one_setIndicator_binaryAffineSubspace") (uses := "definition-3.8, definition-3.9, definition-3.10, support-exercise-3.11") (tags := "section-3-2, fidelity-exact")
*Proposition 3.12.* If $`A=H+a` is an affine subspace of
$`\mathbb F_2^n` of codimension $`k`, then
$$`
\widehat{\mathbf1_A}(\gamma)
=\begin{cases}
  \chi_\gamma(a)2^{-k},&\gamma\in H^\perp,\\
  0,&\gamma\notin H^\perp.
\end{cases}
`
Consequently,
$$`
\varphi_A=\sum_{\gamma\in H^\perp}
  \chi_\gamma(a)\chi_\gamma.
`
Moreover,
$`\operatorname{sparsity}(\widehat{\mathbf1_A})=2^k`,
$`\widehat{\mathbf1_A}` is $`2^{-k}`-granular, and
$$`
\lVert\widehat{\mathbf1_A}\rVert_\infty=2^{-k},
\qquad
\lVert\widehat{\mathbf1_A}\rVert_1=1.
`
:::

:::definition "definition-3.13" (lean := "FABL.F₂DecisionTree, FABL.DecisionTree, FABL.F₂DecisionTree.eval, FABL.F₂DecisionTree.Computes, FABL.F₂DecisionTree.computes_iff, FABL.F₂DecisionTree.completeTree, FABL.F₂DecisionTree.completeTree_computes") (tags := "section-3-2, fidelity-exact")
*Definition 3.13.* A *decision tree* $`T` representing a function
$`f:\mathbb F_2^n\to\mathbb R` is a rooted binary tree whose internal nodes
are labelled by coordinates $`i\in[n]`, whose two outgoing edges at every
internal node are labelled $`0` and $`1`, and whose leaves are labelled by
real numbers. No coordinate may occur more than once on a root-to-leaf path.

On input $`x\in\mathbb F_2^n`, computation starts at the root. At an internal
node labelled $`i`, the tree queries $`x_i` and follows the outgoing edge
labelled $`x_i`. The output is the label of the leaf reached. The tree
computes $`f` when this output equals $`f(x)` for every input $`x`.
:::

:::definition "definition-3.14" (lean := "FABL.F₂DecisionTree.leafCount, FABL.F₂DecisionTree.depth, FABL.F₂DecisionTree.depth_le_dimension, FABL.F₂DecisionTree.leafCount_le_two_pow_depth, FABL.F₂DecisionTree.decisionTreeDepth, FABL.F₂DecisionTree.decisionTreeSize, FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth, FABL.F₂DecisionTree.exists_computingTree_leafCount_eq_decisionTreeSize, FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes, FABL.F₂DecisionTree.decisionTreeSize_le_of_computes") (uses := "definition-3.13") (tags := "section-3-2, fidelity-exact")
*Definition 3.14.* The *size* $`s` of a decision tree $`T` is its number of
leaves. Its *depth* $`k` is the maximum length of a root-to-leaf path. For
decision trees over $`\mathbb F_2^n`,
$$`
k\le n,
\qquad
s\le2^k.
`
For $`f:\mathbb F_2^n\to\mathbb R`, write $`\operatorname{DT}(f)` for the
least depth and $`\operatorname{DT}_{\mathrm{size}}(f)` for the least size of a
decision tree computing $`f`. The two quantities are optimized independently,
and each minimum has its own attaining tree.
:::

:::lemma_ "support-decision-tree-path-subcubes" (lean := "FABL.F₂DecisionTree.Path, FABL.F₂DecisionTree.Path.support, FABL.F₂DecisionTree.Path.length, FABL.F₂DecisionTree.Path.Matches, FABL.F₂DecisionTree.Path.cylinder, FABL.F₂DecisionTree.paths, FABL.F₂DecisionTree.path_length_le_depth, FABL.F₂DecisionTree.length_paths_eq_leafCount, FABL.F₂DecisionTree.existsUnique_path_mem_and_matches, FABL.F₂DecisionTree.Path.cylinder_eq_coordinateSubcube, FABL.F₂DecisionTree.Path.codimension_coordinateZeroSubspace_eq_length, FABL.F₂DecisionTree.computes_eq_path_output_of_matches") (uses := "definition-3.13, definition-3.14, support-affine-subspaces-and-subcubes") (tags := "section-3-2, support, fidelity-exact")
*Path subcubes of a decision tree.* Let $`T` compute
$`f:\mathbb F_2^n\to\mathbb R`, and let $`P` be a root-to-leaf path. The set
$`C_P` of inputs following $`P` is a subcube whose codimension is the length
of $`P`. The function $`f` is constant on $`C_P`; denote this value by
$`f(P)`. Every input follows exactly one path, so
$`\{C_P:P\text{ is a root-to-leaf path of }T\}` is a partition of
$`\mathbb F_2^n`.
:::

:::lemma_ "fact-3.15" (lean := "FABL.F₂DecisionTree.pathExpansion, FABL.F₂DecisionTree.eval_eq_pathExpansion, FABL.F₂DecisionTree.computes_eq_pathExpansion") (uses := "support-decision-tree-path-subcubes") (tags := "section-3-2, fidelity-exact")
*Fact 3.15.* If $`f:\mathbb F_2^n\to\mathbb R` is computed by a decision
tree $`T`, then
$$`
f=\sum_{\text{paths }P\text{ of }T}f(P)\mathbf1_{C_P}.
`
:::

:::lemma_ "support-exercise-3.21" (lean := "FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace, FABL.F₂DecisionTree.Path.spectralSparsity_indicator, FABL.F₂DecisionTree.Path.spectralPNorm_one_indicator, FABL.F₂DecisionTree.Path.isVectorFourierGranular_indicator, FABL.F₂DecisionTree.Path.vectorFourierDegree_indicator_le_length, FABL.F₂DecisionTree.vectorFourierCoeff_pathExpansion, FABL.F₂DecisionTree.vectorFourierDegree_pathExpansion_le, FABL.F₂DecisionTree.spectralSparsity_pathExpansion_le_sum, FABL.F₂DecisionTree.spectralPNorm_one_pathExpansion_le_sum_abs_output, FABL.F₂DecisionTree.isVectorFourierGranular_pathExpansion") (uses := "definition-3.8, definition-3.9, definition-3.10, fact-3.15, proposition-3.12") (tags := "section-3-2, support, fidelity-exact")
*Exercise 3.21.* Let $`f:\mathbb F_2^n\to\mathbb R` be computed by a
decision tree of size $`s` and depth $`k`. Using the path-subcube expansion,
prove
$$`
\deg(f)\le k,
\qquad
\operatorname{sparsity}(\widehat f)\le s2^k\le4^k,
`
and
$$`
\lVert\widehat f\rVert_1
\le\lVert f\rVert_\infty s
\le\lVert f\rVert_\infty2^k.
`
If $`f:\mathbb F_2^n\to\mathbb Z`, also prove that $`\widehat f` is
$`2^{-k}`-granular.
:::

:::proposition "proposition-3.16" (lean := "FABL.F₂DecisionTree.vectorFourierDegree_le_depth_of_computes, FABL.F₂DecisionTree.spectralSparsity_le_of_computes, FABL.F₂DecisionTree.spectralPNorm_one_le_infinityNorm_mul_leafCount_of_computes, FABL.F₂DecisionTree.spectralPNorm_one_le_infinityNorm_mul_two_pow_depth_of_computes, FABL.F₂DecisionTree.isVectorFourierGranular_inverseTwoPowDepth_of_computes_int") (uses := "definition-3.14, fact-3.15, proposition-3.12, support-exercise-3.21") (tags := "section-3-2, fidelity-exact")
*Proposition 3.16.* Let $`f:\mathbb F_2^n\to\mathbb R` be computed by a
decision tree $`T` of size $`s` and depth $`k`. Then

* $`\deg(f)\le k`;
* $`\operatorname{sparsity}(\widehat f)\le s2^k\le4^k`;
* $`\lVert\widehat f\rVert_1
   \le\lVert f\rVert_\infty s
   \le\lVert f\rVert_\infty2^k`;
* if $`f:\mathbb F_2^n\to\mathbb Z`, then $`\widehat f` is
  $`2^{-k}`-granular.
:::

:::lemma_ "support-exercise-3.22" (lean := "FABL.F₂DecisionTree.truncate, FABL.F₂DecisionTree.depth_truncate_le, FABL.F₂DecisionTree.exists_long_path_of_eval_truncate_ne, FABL.F₂DecisionTree.longPathIndicatorSum, FABL.F₂DecisionTree.relativeHammingDist_eval_truncate_le, FABL.F₂DecisionTree.decisionTreeTruncationDegree, FABL.F₂DecisionTree.mul_inverseTwoPow_decisionTreeTruncationDegree_le, FABL.F₂DecisionTree.relativeHammingDist_eval_truncate_decisionTreeTruncationDegree_le, FABL.F₂DecisionTree.exists_truncatedTree_close") (uses := "definition-3.1, definition-3.13, proposition-3.16") (tags := "section-3-2, support, fidelity-log-base-two-and-ceiling-explicit")
*Exercise 3.22.* Let $`f:\mathbb F_2^n\to\{-1,1\}` be computed by a
decision tree $`T` of size $`s`, and let $`\epsilon\in(0,1]`. Truncate every
path, if necessary, so that its length is at most
$`k=\left\lceil\log_2(s/\epsilon)\right\rceil`,
creating new leaves labelled $`-1` or $`1` as necessary. Show that the
resulting decision tree $`T'` computes a function $`\epsilon`-close to $`f`;
that is,
$$`
\Pr_{\boldsymbol x\sim\mathbb F_2^n}
[T'(\boldsymbol x)\ne f(\boldsymbol x)]\le\epsilon.
`
The Hamming-distance conclusion holds for any choice of the new sign labels.
For the Fourier-tail estimate used in Proposition 3.17, the production proof
separately truncates the real-valued tree with new leaves labelled $`0` and
applies Parseval to its squared approximation error. The book writes
$`\log(s/\epsilon)` and suppresses the integer rounding; the displayed
base-two ceiling is the exact convention used by the Lean declaration.
:::

:::proposition "proposition-3.17" (lean := "FABL.F₂DecisionTree.vectorFourierWeightAbove, FABL.F₂DecisionTree.vectorFourierWeightAbove_le_expect_sq_sub_of_degree_le, FABL.F₂DecisionTree.vectorFourierWeightAbove_eval_le_leafCount_mul_inverseTwoPow, FABL.F₂DecisionTree.vectorFourierWeightAbove_decisionTreeTruncationDegree_le, FABL.F₂DecisionTree.isFourierSpectrumConcentratedUpTo_of_decisionTree") (uses := "definition-3.1, parseval, proposition-3.16, support-exercise-3.22") (tags := "section-3-2, fidelity-log-base-two-and-ceiling-explicit")
*Proposition 3.17.* Let $`f:\mathbb F_2^n\to\{-1,1\}` be computable by a
decision tree of size $`s`, and let $`\epsilon\in(0,1]`. Then the Fourier
spectrum of $`f` is $`\epsilon`-concentrated on degree up to the explicit
integer cutoff $`k=\left\lceil\log_2(s/\epsilon)\right\rceil`.
Equivalently,
$$`
\sum_{\substack{\gamma\in\widehat{\mathbb F_2^n}\\
                 |\gamma|>k}}
  \widehat f(\gamma)^2
\le\epsilon,
`
where $`|\gamma|` is the Hamming weight of $`\gamma`. This makes explicit the
base-two logarithm and ceiling convention suppressed in the book's phrase
“degree up to $`\log(s/\epsilon)`”.
:::
