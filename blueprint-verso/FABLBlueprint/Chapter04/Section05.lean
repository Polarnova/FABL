/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.CircuitInfluence
import FABL.Chapter04.LMN
import FABL.Chapter04.Parity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: LMN's work on constant-depth circuits" =>

:::definition "definition-4.26" (parent := "fabl-chapter-4") (lean := "FABL.CircuitGate, FABL.CircuitGate.dual, FABL.CircuitGate.evalTerm, FABL.CircuitGate.evalFinset, FABL.CircuitTail, FABL.CircuitTail.layerCount, FABL.CircuitTail.eq_output_of_layerCount_eq_one, FABL.CircuitTail.eval, FABL.DepthCircuit, FABL.DepthCircuit.depth, FABL.DepthCircuit.depth_ge_two, FABL.DepthCircuit.evalLayer1, FABL.DepthCircuit.selectedLayer1Terms, FABL.DepthCircuit.selectedLayer1DNF, FABL.DepthCircuit.selectedLayer1CNF, FABL.DepthCircuit.layer2GateFunction, FABL.DepthCircuit.selectedLayer1DNF_toBooleanFunction, FABL.DepthCircuit.selectedLayer1CNF_toBooleanFunction, FABL.DepthCircuit.eval, FABL.DepthCircuit.toBooleanFunction, FABL.DepthCircuit.ofDNF, FABL.DepthCircuit.depth_ofDNF, FABL.DepthCircuit.eval_ofDNF, FABL.DepthCircuit.toBooleanFunction_ofDNF, FABL.DepthCircuit.ofCNF, FABL.DepthCircuit.depth_ofCNF, FABL.DepthCircuit.eval_ofCNF, FABL.DepthCircuit.toBooleanFunction_ofCNF") (tags := "section-4-5, fidelity-exact-intrinsic-layered-model")
*Definition 4.26.* For an integer $`d\ge2`, a *depth-$`d` circuit* over
Boolean variables $`x_1,\ldots,x_n` is a directed acyclic graph whose nodes
(“gates”) are arranged in $`d+1` layers, with every wire going from layer
$`j-1` to layer $`j` for some $`j\in[d]`. Layer $`0` has exactly $`2n` nodes
labelled by the $`2n` literals, and layer $`d` has exactly one output node.
Nodes in layers $`1,3,5,\ldots` share one of the labels $`\wedge` or $`\vee`,
and nodes in layers $`2,4,6,\ldots` share the other label. Each node computes
a function $`\{-1,1\}^n\to\{-1,1\}`: literals compute themselves, and
$`\wedge` (respectively $`\vee`) nodes compute the logical AND (respectively
OR) of their incoming functions. The circuit computes the function computed
by its output node. In particular, DNFs and CNFs are depth-$`2` circuits.
:::

:::definition "definition-4.27" (parent := "fabl-chapter-4") (lean := "FABL.CircuitTail.internalNodeCount, FABL.DepthCircuit.size, FABL.DepthCircuit.width, FABL.DepthCircuit.width_selectedLayer1DNF_le, FABL.DepthCircuit.width_selectedLayer1CNF_le, FABL.DepthCircuit.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE, FABL.DepthCircuit.toBooleanFunction_hasDNFWidthLE_or_hasCNFWidthLE_of_depth_eq_two, FABL.DepthCircuit.size_ofDNF, FABL.DepthCircuit.width_ofDNF, FABL.DepthCircuit.size_ofCNF, FABL.DepthCircuit.width_ofCNF, FABL.DepthCircuit.HasDepthCircuit, FABL.DepthCircuit.hasDepthCircuit_toBooleanFunction, FABL.DepthCircuit.hasDepthCircuit_ofDNF, FABL.DepthCircuit.hasDepthCircuit_ofCNF") (uses := "definition-4.26") (tags := "section-4-5, fidelity-exact")
*Definition 4.27.* The *size* of a depth-$`d` circuit is the number of nodes
in layers $`1` through $`d-1`. Its *width* is the maximum in-degree of any
node at layer $`1`. As with DNFs and CNFs, no layer-$`1` node is connected to
a variable or its negation more than once.
:::

:::lemma_ "lemma-4.28" (parent := "fabl-chapter-4") (lean := "FABL.switchingLayerRate, FABL.circuitCompressionRate, FABL.lmnLayerCutoff, FABL.lmnOutputCutoff, FABL.lemma4_28") (uses := "definition-4.26, definition-4.27, hastads-switching-lemma, proposition-4.5") (tags := "section-4-5, fidelity-natural-ceiling-specialization")
*Lemma 4.28.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d`
circuit of size $`s` and width $`w`, and let $`\epsilon\in(0,1]`. Set
$$`
\delta=\frac1{10w}\Bigl(\frac1{10\ell}\Bigr)^{d-2},
\qquad
\ell=\log(2s/\epsilon).
`
If $`(\boldsymbol J\mid\boldsymbol z)` is a $`\delta`-random restriction, then
$$`
\Pr\bigl[\operatorname{DT}(f_{\boldsymbol J\mid\boldsymbol z})\ge\log(2/\epsilon)\bigr]
\le\epsilon.
`

Round the logarithmic decision-tree and width thresholds up to natural
numbers, with $`s,w>0`. When $`\log_2(2s/\epsilon)` is nonintegral, the
resulting restriction rate is slightly smaller than the printed real-log
rate.
:::

:::theorem "lmn-theorem" (parent := "fabl-chapter-4") (lean := "FABL.lmnWidthCutoff, FABL.lmnDegreeCutoff, FABL.lmn_theorem") (uses := "lemma-4.28, lemma-4.21, proposition-4.9, support-exercise-3.17, definition-3.1") (tags := "section-4-5, fidelity-finite-explicit-asymptotic-bridge")
*LMN Theorem (Linial–Mansour–Nisan).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d` circuit of size
$`s>1` and let $`\epsilon\in(0,1/2]`. Then the Fourier spectrum of $`f` is
$`\epsilon`-concentrated up to degree
$$`
O\bigl(\log(s/\epsilon)\bigr)^{d-1}\cdot\log(1/\epsilon).
`

Rounding the logarithmic thresholds in Lemma 4.28 gives a natural-number
cutoff of the displayed asymptotic order.
:::

:::lemma_ "remark-4.29" (parent := "fabl-chapter-4") (tags := "section-4-5, external-result, unformalized")
*Remark 4.29.* Håstad has slightly sharpened the degree bound in the LMN
Theorem to
$`O\bigl(\log(s/\epsilon)\bigr)^{d-2}\cdot\log s\cdot\log(1/\epsilon)`.
This strengthening uses Håstad's sharper switching argument.
:::

:::lemma_ "support-exercise-4.20" (parent := "fabl-chapter-4") (lean := "FABL.DepthCircuit.HasDepthWidthTailSizeCircuit, FABL.DepthCircuit.exercise4_20, FABL.DepthCircuit.HasDepthSizeCircuit, FABL.DepthCircuit.exercise4_20b") (uses := "theorem-4.20, definition-4.26, definition-4.27, lemma-4.19") (tags := "section-4-5, support, fidelity-finite-explicit-asymptotic-bridge")
*Exercise 4.20.* A *$`(d,w,s')`*-circuit is a depth-$`d` circuit of width at
most $`w` with at most $`s'` nodes at layers $`2` through $`d`. By induction
on $`d\ge2`, every $`f:\{-1,1\}^n\to\{-1,1\}` computable by a
$`(d,w,s')`-circuit satisfies
$`\mathbf I[f]\le w\cdot O(\log s')^{d-2}`. Deduce Theorem 4.30.
In fact,
$$`
\mathbf I[f]
\le
2w\left[
20\left(\left\lceil\log_2(s'+1)\right\rceil+2\right)
\right]^{d-2}.
`
:::

:::theorem "theorem-4.30" (parent := "fabl-chapter-4") (lean := "FABL.DepthCircuit.theorem4_30") (uses := "support-exercise-4.20") (tags := "section-4-5, fidelity-finite-explicit-asymptotic-bridge")
*Theorem 4.30.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d`
circuit of size $`s`. Then $`\mathbf I[f]\le O(\log s)^{d-1}`.
More explicitly,
$$`
\mathbf I[f]
\le
4\left[
20\left(\left\lceil\log_2(s+2)\right\rceil+2\right)
\right]^{d-1}.
`
:::

:::theorem "theorem-4.31" (parent := "fabl-chapter-4") (lean := "FABL.depthSizeCircuitClass, FABL.lmnCircuitLearningDegree, FABL.lmnCircuitLearnerWorkCost, FABL.theorem4_31, FABL.card_lmnCircuitLearningFamily_le") (uses := "lmn-theorem, low-degree-algorithm, definition-3.27") (tags := "section-4-5, fidelity-finite-executable-asymptotic-bridge")
*Theorem 4.31.* Let $`\mathcal C` be the class of functions
$`f:\{-1,1\}^n\to\{-1,1\}` computable by depth-$`d` circuits of size
$`\operatorname{poly}(n)`. Then $`\mathcal C` can be learned from random
examples with error any $`\epsilon=1/\operatorname{poly}(n)` in time
$`n^{O(\log^d n)}`. Equivalently, the complexity class $`\mathrm{AC}^0` is
learnable in quasipolynomial time.
For fixed $`d`, the explicit LMN degree and the random-example learner of
Theorem 3.29 give the displayed quasipolynomial bound.
:::

:::lemma_ "support-exercise-4.12" (parent := "fabl-chapter-4") (lean := "FABL.DNFFormula.term_width_eq_dimension_of_computes_parity, FABL.DNFFormula.size_lower_bound_of_computes_parity, FABL.parityDNF, FABL.parityDNF_toBooleanFunction, FABL.size_parityDNF, FABL.DNFsize_parityFunction_univ, FABL.parityCNF, FABL.size_parityCNF, FABL.parityCNF_toBooleanFunction, FABL.CNFFormula.clause_width_eq_dimension_of_computes_parity, FABL.CNFFormula.size_lower_bound_of_computes_parity, FABL.parityDepthCircuitFromBlocks, FABL.depth_parityDepthCircuitFromBlocks, FABL.size_parityDepthCircuitFromBlocks, FABL.toBooleanFunction_parityDepthCircuitFromBlocks, FABL.parityRealRoot, FABL.parityRealRoot_pow_pred, FABL.parityBlockSide, FABL.parityBlockSide_pow_covers, FABL.canonicalParityCircuit_size_real_le, FABL.hasDepthCircuit_parity_depth_three, FABL.hasDepthCircuit_parity_general") (uses := "definition-4.1, definition-4.26, definition-4.27") (tags := "section-4-5, support, fidelity-exact-explicit-root-scale-bound")
*Exercise 4.12 (parity formula tightness and circuit upper bounds).*
(a) The parity $`\chi_{[n]}` is computed by a DNF (or CNF) of size $`2^{n-1}`.
(b) This size bound is tight: every term in such a DNF, and dually every
clause in such a CNF, must have width exactly $`n`.
(c) There is a depth-$`3` circuit of size $`O(n^{1/2})\cdot 2^{n^{1/2}}`
computing $`\chi_{[n]}`.
(d) More generally, for every $`d\ge2` there is a depth-$`d` circuit of size
$`O\bigl(n^{1-1/(d-1)}\bigr)\cdot 2^{n^{1/(d-1)}}` computing $`\chi_{[n]}`.
For $`n>0`, the exact DNF and CNF size is $`2^{n-1}`, and every term or
clause has full width. For the circuit construction, take block side
$`\max(1,\lceil n^{1/(d-1)}\rceil)`. The resulting finite size bound and the identity
$`(n^{1/(d-1)})^{d-2}=n^{1-1/(d-1)}` give an explicit finite root-scale envelope corresponding to
the displayed asymptotic, including the $`d=2` endpoint and non-perfect-power dimensions.
:::

:::corollary "corollary-4.32" (parent := "fabl-chapter-4") (lean := "FABL.fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one, FABL.parityAgreement_forces_concentration_cutoff, FABL.DepthCircuit.corollary4_32") (uses := "lmn-theorem") (tags := "section-4-5, fidelity-finite-inverse-cutoff-asymptotic-bridge")
*Corollary 4.32.* Fix any constant $`\epsilon_0>0`. Suppose $`C` is a
depth-$`d` circuit over $`\{-1,1\}^n` with
$`\Pr_{\boldsymbol x}[C(\boldsymbol x)=\chi_{[n]}(\boldsymbol x)]\ge\frac12+\epsilon_0`.
Then the size of $`C` is at least $`2^{\Omega\bigl(n^{1/(d-1)}\bigr)}`.
More precisely, every $`s>1` whose LMN cutoff is below $`n` is strictly
smaller than the circuit size. Inverting this cutoff gives the displayed
$`2^{\Omega(n^{1/(d-1)})}` lower bound.
:::
