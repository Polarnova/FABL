/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter04.Circuits

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: LMN's work on constant-depth circuits" =>

:::definition "definition-4.26" (lean := "FABL.CircuitGate, FABL.CircuitGate.eval, FABL.DepthCircuit, FABL.DepthCircuit.evalLayer1, FABL.DepthCircuit.evalHigherLayer, FABL.DepthCircuit.eval, FABL.DepthCircuit.toBooleanFunction, FABL.DepthCircuit.ofDNF, FABL.DepthCircuit.ofCNF") (tags := "section-4-5, fidelity-layered-wire-model")
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
Production uses an explicit layered wire-index model with layer-1 terms and
higher AND/OR layers; DNF/CNF embed as depth-$`2` instances.
:::

:::definition "definition-4.27" (lean := "FABL.DepthCircuit.size, FABL.DepthCircuit.width, FABL.DepthCircuit.size_ofDNF, FABL.DepthCircuit.width_ofDNF, FABL.DepthCircuit.size_ofCNF, FABL.DepthCircuit.width_ofCNF, FABL.DepthCircuit.HasDepthCircuit") (uses := "definition-4.26") (tags := "section-4-5, fidelity-exact")
*Definition 4.27.* The *size* of a depth-$`d` circuit is the number of nodes
in layers $`1` through $`d-1`. Its *width* is the maximum in-degree of any
node at layer $`1`. As with DNFs and CNFs, no layer-$`1` node is connected to
both a variable and its negation more than once (no repeated opposite
literals on the same gate).
:::

:::lemma_ "lemma-4.28" (uses := "definition-4.26, definition-4.27, hastads-switching-lemma, proposition-4.5") (tags := "section-4-5")
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
:::

:::theorem "lmn-theorem" (uses := "lemma-4.28, lemma-4.21, proposition-4.9, support-exercise-3.17, definition-3.1") (tags := "section-4-5")
*LMN Theorem (Linial–Mansour–Nisan).* Let
$`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d` circuit of size
$`s>1` and let $`\epsilon\in(0,1/2]`. Then the Fourier spectrum of $`f` is
$`\epsilon`-concentrated up to degree
$$`
O\bigl(\log(s/\epsilon)\bigr)^{d-1}\cdot\log(1/\epsilon).
`
:::

:::lemma_ "remark-4.29" (uses := "lmn-theorem") (tags := "section-4-5")
*Remark 4.29.* Håstad has slightly sharpened the degree bound in the LMN
Theorem to
$`O\bigl(\log(s/\epsilon)\bigr)^{d-2}\cdot\log s\cdot\log(1/\epsilon)`.
:::

:::lemma_ "support-exercise-4.20" (uses := "theorem-4.20, definition-4.26, definition-4.27, lemma-4.19") (tags := "section-4-5, support")
*Exercise 4.20.* A *$`(d,w,s')`*-circuit is a depth-$`d` circuit of width at
most $`w` with at most $`s'` nodes at layers $`2` through $`d`. By induction
on $`d\ge2`, every $`f:\{-1,1\}^n\to\{-1,1\}` computable by a
$`(d,w,s')`-circuit satisfies
$`\mathbf I[f]\le w\cdot O(\log s')^{d-2}`. Deduce Theorem 4.30.
:::

:::theorem "theorem-4.30" (uses := "support-exercise-4.20") (tags := "section-4-5")
*Theorem 4.30.* Let $`f:\{-1,1\}^n\to\{-1,1\}` be computable by a depth-$`d`
circuit of size $`s`. Then $`\mathbf I[f]\le O(\log s)^{d-1}`.
:::

:::theorem "theorem-4.31" (uses := "lmn-theorem, low-degree-algorithm, definition-3.27") (tags := "section-4-5")
*Theorem 4.31.* Let $`\mathcal C` be the class of functions
$`f:\{-1,1\}^n\to\{-1,1\}` computable by depth-$`d` circuits of size
$`\operatorname{poly}(n)`. Then $`\mathcal C` can be learned from random
examples with error any $`\epsilon=1/\operatorname{poly}(n)` in time
$`n^{O(\log^d n)}`. Equivalently, the complexity class $`\mathrm{AC}^0` is
learnable in quasipolynomial time.
:::

:::lemma_ "support-exercise-4.12" (uses := "definition-4.1, definition-4.26, definition-4.27") (tags := "section-4-5, support")
*Exercise 4.12 (parity upper bounds).*
(a) The parity $`\chi_{[n]}` is computed by a DNF (or CNF) of size $`2^{n-1}`.
(b) This size bound is tight: every term in such a DNF must have width
exactly $`n`.
(c) There is a depth-$`3` circuit of size $`O(n^{1/2})\cdot 2^{n^{1/2}}`
computing $`\chi_{[n]}`.
(d) More generally, for every $`d\ge2` there is a depth-$`d` circuit of size
$`O\bigl(n^{1-1/(d-1)}\bigr)\cdot 2^{n^{1/(d-1)}}` computing $`\chi_{[n]}`.
:::

:::corollary "corollary-4.32" (uses := "lmn-theorem, support-exercise-4.12") (tags := "section-4-5")
*Corollary 4.32.* Fix any constant $`\epsilon_0>0`. Suppose $`C` is a
depth-$`d` circuit over $`\{-1,1\}^n` with
$`\Pr_{\boldsymbol x}[C(\boldsymbol x)=\chi_{[n]}(\boldsymbol x)]\ge\frac12+\epsilon_0`.
Then the size of $`C` is at least $`2^{\Omega\bigl(n^{1/(d-1)}\bigr)}`.
:::
