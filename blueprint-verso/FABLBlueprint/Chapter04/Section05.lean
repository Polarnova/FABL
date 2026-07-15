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

:::definition "definition-4.26" (lean := "FABL.CircuitGate, FABL.CircuitGate.dual, FABL.CircuitGate.evalTerm, FABL.CircuitGate.evalFinset, FABL.CircuitTail, FABL.CircuitTail.layerCount, FABL.CircuitTail.eq_output_of_layerCount_eq_one, FABL.CircuitTail.eval, FABL.DepthCircuit, FABL.DepthCircuit.depth, FABL.DepthCircuit.depth_ge_two, FABL.DepthCircuit.evalLayer1, FABL.DepthCircuit.selectedLayer1Terms, FABL.DepthCircuit.selectedLayer1DNF, FABL.DepthCircuit.selectedLayer1CNF, FABL.DepthCircuit.layer2GateFunction, FABL.DepthCircuit.selectedLayer1DNF_toBooleanFunction, FABL.DepthCircuit.selectedLayer1CNF_toBooleanFunction, FABL.DepthCircuit.eval, FABL.DepthCircuit.toBooleanFunction, FABL.DepthCircuit.ofDNF, FABL.DepthCircuit.depth_ofDNF, FABL.DepthCircuit.eval_ofDNF, FABL.DepthCircuit.toBooleanFunction_ofDNF, FABL.DepthCircuit.ofCNF, FABL.DepthCircuit.depth_ofCNF, FABL.DepthCircuit.eval_ofCNF, FABL.DepthCircuit.toBooleanFunction_ofCNF") (tags := "section-4-5, fidelity-exact-intrinsic-layered-model")
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
Production represents layer $`0` implicitly by the canonical positive and
negative literals. Every higher wire has a typed source in the immediately
preceding layer, the tail has exactly one output gate, and the uniform
alternating layer labels are derived from the layer-$`1` label. Thus malformed
wires, mixed-label layers, and a missing output gate are unrepresentable.
DNFs and CNFs embed as depth-$`2` instances.
:::

:::definition "definition-4.27" (lean := "FABL.CircuitTail.internalNodeCount, FABL.DepthCircuit.size, FABL.DepthCircuit.width, FABL.DepthCircuit.width_selectedLayer1DNF_le, FABL.DepthCircuit.width_selectedLayer1CNF_le, FABL.DepthCircuit.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE, FABL.DepthCircuit.toBooleanFunction_hasDNFWidthLE_or_hasCNFWidthLE_of_depth_eq_two, FABL.DepthCircuit.size_ofDNF, FABL.DepthCircuit.width_ofDNF, FABL.DepthCircuit.size_ofCNF, FABL.DepthCircuit.width_ofCNF, FABL.DepthCircuit.HasDepthCircuit, FABL.DepthCircuit.hasDepthCircuit_toBooleanFunction, FABL.DepthCircuit.hasDepthCircuit_ofDNF, FABL.DepthCircuit.hasDepthCircuit_ofCNF") (uses := "definition-4.26") (tags := "section-4-5, fidelity-exact")
*Definition 4.27.* The *size* of a depth-$`d` circuit is the number of nodes
in layers $`1` through $`d-1`. Its *width* is the maximum in-degree of any
node at layer $`1`. As with DNFs and CNFs, no layer-$`1` node is connected to
a variable or its negation more than once.
:::

:::lemma_ "lemma-4.28" (lean := "FABL.switchingLayerRate, FABL.circuitCompressionRate, FABL.lmnLayerCutoff, FABL.lmnOutputCutoff, FABL.lemma4_28") (uses := "definition-4.26, definition-4.27, hastads-switching-lemma, proposition-4.5") (tags := "section-4-5, fidelity-natural-ceiling-specialization")
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

Production interprets the logarithmic decision-tree and width thresholds by natural ceilings and
proves the resulting discrete restriction-rate specialization, with explicit hypotheses $`s>0`
and $`w>0`. When $`\log_2(2s/\epsilon)` is nonintegral, this rate is slightly smaller than the
printed real-log rate.
:::

:::theorem "lmn-theorem" (lean := "FABL.lmnWidthCutoff, FABL.lmnDegreeCutoff, FABL.lmn_theorem") (uses := "lemma-4.28, lemma-4.21, proposition-4.9, support-exercise-3.17, definition-3.1") (tags := "section-4-5, fidelity-finite-explicit-asymptotic-bridge")
*LMN Theorem (Linial–Mansour–Nisan).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d` circuit of size
$`s>1` and let $`\epsilon\in(0,1/2]`. Then the Fourier spectrum of $`f` is
$`\epsilon`-concentrated up to degree
$$`
O\bigl(\log(s/\epsilon)\bigr)^{d-1}\cdot\log(1/\epsilon).
`

Production proves concentration up to the explicit natural cutoff `lmnDegreeCutoff d s ε`, the
finite representative of the displayed asymptotic degree. The $`O`-comparison itself is not exposed
as a separate Lean declaration.
:::

:::lemma_ "remark-4.29" (tags := "section-4-5, external-result, unformalized")
*Remark 4.29.* Håstad has slightly sharpened the degree bound in the LMN
Theorem to
$`O\bigl(\log(s/\epsilon)\bigr)^{d-2}\cdot\log s\cdot\log(1/\epsilon)`.
This historical strengthening needs Håstad's separate sharper argument; it does not follow from the
ordinary switching-lemma LMN proof formalized here. The node therefore deliberately has no Lean
association rather than weakening the stated bound.
:::

:::lemma_ "support-exercise-4.20" (lean := "FABL.DepthCircuit.HasDepthWidthTailSizeCircuit, FABL.DepthCircuit.exercise4_20, FABL.DepthCircuit.HasDepthSizeCircuit, FABL.DepthCircuit.exercise4_20b") (uses := "theorem-4.20, definition-4.26, definition-4.27, lemma-4.19") (tags := "section-4-5, support, fidelity-finite-explicit-asymptotic-bridge")
*Exercise 4.20.* A *$`(d,w,s')`*-circuit is a depth-$`d` circuit of width at
most $`w` with at most $`s'` nodes at layers $`2` through $`d`. By induction
on $`d\ge2`, every $`f:\{-1,1\}^n\to\{-1,1\}` computable by a
$`(d,w,s')`-circuit satisfies
$`\mathbf I[f]\le w\cdot O(\log s')^{d-2}`. Deduce Theorem 4.30.
Production proves the explicit stronger bound
$$`
\mathbf I[f]\le2w\cdot\operatorname{circuitInfluenceStep}(s')^{d-2}.
`
:::

:::theorem "theorem-4.30" (lean := "FABL.DepthCircuit.theorem4_30") (uses := "support-exercise-4.20") (tags := "section-4-5, fidelity-finite-explicit-asymptotic-bridge")
*Theorem 4.30.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d`
circuit of size $`s`. Then $`\mathbf I[f]\le O(\log s)^{d-1}`.
Production proves
$$`
\mathbf I[f]\le4\cdot\operatorname{circuitInfluenceStep}(s+1)^{d-1},
`
where `circuitInfluenceStep` is an explicit natural logarithmic envelope.
:::

:::theorem "theorem-4.31" (lean := "FABL.depthSizeCircuitClass, FABL.lmnCircuitLearningDegree, FABL.lmnCircuitLearnerWorkCost, FABL.theorem4_31, FABL.card_lmnCircuitLearningFamily_le") (uses := "lmn-theorem, low-degree-algorithm, definition-3.27") (tags := "section-4-5, fidelity-finite-executable-asymptotic-bridge")
*Theorem 4.31.* Let $`\mathcal C` be the class of functions
$`f:\{-1,1\}^n\to\{-1,1\}` computable by depth-$`d` circuits of size
$`\operatorname{poly}(n)`. Then $`\mathcal C` can be learned from random
examples with error any $`\epsilon=1/\operatorname{poly}(n)` in time
$`n^{O(\log^d n)}`. Equivalently, the complexity class $`\mathrm{AC}^0` is
learnable in quasipolynomial time.
Production gives the finite executable random-example learner, its explicit LMN degree, zero-query
property, success bound, and exact pathwise work schedule. These are the finite ingredients
underlying the displayed fixed-depth quasipolynomial estimate; the asymptotic family-level bound is
not separately packaged as a Lean theorem.
:::

:::lemma_ "support-exercise-4.12" (lean := "FABL.DNFFormula.term_width_eq_dimension_of_computes_parity, FABL.DNFFormula.size_lower_bound_of_computes_parity, FABL.parityDNF, FABL.parityDNF_toBooleanFunction, FABL.size_parityDNF, FABL.DNFsize_parityFunction_univ, FABL.parityCNF, FABL.size_parityCNF, FABL.parityCNF_toBooleanFunction, FABL.CNFFormula.clause_width_eq_dimension_of_computes_parity, FABL.CNFFormula.size_lower_bound_of_computes_parity, FABL.parityDepthCircuitFromBlocks, FABL.depth_parityDepthCircuitFromBlocks, FABL.size_parityDepthCircuitFromBlocks, FABL.toBooleanFunction_parityDepthCircuitFromBlocks, FABL.parityRealRoot, FABL.parityRealRoot_pow_pred, FABL.parityBlockSide, FABL.parityBlockSide_pow_covers, FABL.canonicalParityCircuit_size_real_le, FABL.hasDepthCircuit_parity_depth_three, FABL.hasDepthCircuit_parity_general") (uses := "definition-4.1, definition-4.26, definition-4.27") (tags := "section-4-5, support, fidelity-exact-explicit-root-scale-bound")
*Exercise 4.12 (parity formula tightness and circuit upper bounds).*
(a) The parity $`\chi_{[n]}` is computed by a DNF (or CNF) of size $`2^{n-1}`.
(b) This size bound is tight: every term in such a DNF, and dually every
clause in such a CNF, must have width exactly $`n`.
(c) There is a depth-$`3` circuit of size $`O(n^{1/2})\cdot 2^{n^{1/2}}`
computing $`\chi_{[n]}`.
(d) More generally, for every $`d\ge2` there is a depth-$`d` circuit of size
$`O\bigl(n^{1-1/(d-1)}\bigr)\cdot 2^{n^{1/(d-1)}}` computing $`\chi_{[n]}`.
Production proves the exact DNF and CNF size $`2^{n-1}` for $`n>0`, the full-width lower bound
and resulting size lower bound for both DNF terms and CNF clauses, and a genuine alternating
layered circuit for every $`d\ge2`. The canonical
block side is $`\max(1,\lceil n^{1/(d-1)}\rceil)`; the explicit finite size bound and the identity
$`(n^{1/(d-1)})^{d-2}=n^{1-1/(d-1)}` give an explicit finite root-scale envelope corresponding to
the displayed asymptotic, including the $`d=2` endpoint and non-perfect-power dimensions.
:::

:::corollary "corollary-4.32" (lean := "FABL.fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one, FABL.parityAgreement_forces_concentration_cutoff, FABL.DepthCircuit.corollary4_32") (uses := "lmn-theorem") (tags := "section-4-5, fidelity-finite-inverse-cutoff-asymptotic-bridge")
*Corollary 4.32.* Fix any constant $`\epsilon_0>0`. Suppose $`C` is a
depth-$`d` circuit over $`\{-1,1\}^n` with
$`\Pr_{\boldsymbol x}[C(\boldsymbol x)=\chi_{[n]}(\boldsymbol x)]\ge\frac12+\epsilon_0`.
Then the size of $`C` is at least $`2^{\Omega\bigl(n^{1/(d-1)}\bigr)}`.
Production proves the exact finite inverse-cutoff obstruction: every candidate size $`s>1` whose
LMN cutoff is below $`n` is strictly smaller than the actual circuit size. The formal API stops at
this obstruction; the asymptotic inversion to $`2^{\Omega(n^{1/(d-1)})}` is not a separate Lean
declaration.
:::
