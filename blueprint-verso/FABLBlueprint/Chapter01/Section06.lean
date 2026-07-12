/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter01.BLR

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: Almost linear functions and the BLR Test" =>

:::definition "definition-1.28" (lean := "FABL.IsF₂Linear, FABL.f₂DotProduct, FABL.isF₂Linear_iff_exists_dotProduct, FABL.isF₂Linear_iff_exists_coordinateSum") (tags := "section-1-6, fidelity-exact")
*Definition 1.28.* A function $`f:\mathbb F_2^n\to\mathbb F_2` is linear if
either of the following equivalent conditions holds:

1. $`f(x+y)=f(x)+f(y)` for all $`x,y\in\mathbb F_2^n`;
2. There is some $`a\in\mathbb F_2^n` such that
   $`f(x)=a\mathbin{\cdot}x` for every $`x\in\mathbb F_2^n`; equivalently,
   there is some $`S\subseteq[n]` such that
   $`f(x)=\sum_{i\in S}x_i` for every $`x\in\mathbb F_2^n`.
:::

:::definition "definition-1.29" (lean := "FABL.IsClose, FABL.IsFar, FABL.distanceToProperty, FABL.IsCloseToProperty, FABL.exists_relativeHammingDist_eq_distanceToProperty, FABL.isCloseToProperty_iff_distanceToProperty_le") (uses := "definition-1.10") (tags := "section-1-6, fidelity-conservative-generalization-of-common-codomain")
*Definition 1.29.* If $`f` and $`g` are Boolean-valued functions, they are
$`\epsilon`-close if $`\operatorname{dist}(f,g)\le\epsilon`; otherwise they are
$`\epsilon`-far. If $`\mathcal P` is a nonempty property of $`n`-bit Boolean
functions, define
$$`\operatorname{dist}(f,\mathcal P)
=\min_{g\in\mathcal P}\operatorname{dist}(f,g).`
The function $`f` is $`\epsilon`-close to $`\mathcal P` if
$`\operatorname{dist}(f,\mathcal P)\le\epsilon`; equivalently, if it is
$`\epsilon`-close to some $`g\in\mathcal P`.
:::

:::definition "blr-test" (lean := "FABL.blrAccepts, FABL.blrAcceptanceProbability") (uses := "notation-1.4") (tags := "section-1-6, fidelity-exact")
*BLR Test.* Given query access to $`f:\mathbb F_2^n\to\mathbb F_2`:

1. Choose independent uniform $`\boldsymbol{x},\boldsymbol{y}\in\mathbb F_2^n`.
2. Query $`f` at $`\boldsymbol{x}`, $`\boldsymbol{y}`, and
   $`\boldsymbol{x}+\boldsymbol{y}`.
3. Accept if
   $`f(\boldsymbol{x})+f(\boldsymbol{y})=f(\boldsymbol{x}+\boldsymbol{y})`.
:::

:::lemma_ "support-blr-cubic-identity" (lean := "FABL.signEncode, FABL.realSignEncodedFunction, FABL.binaryParitySign, FABL.two_mul_blrAcceptanceProbability_sub_one_eq_sum_cube_fourierCoeff") (uses := "blr-test, plancherel, theorem-1.27") (tags := "section-1-6, support")
*Equation (1.10).* If $`f:\mathbb F_2^n\to\mathbb F_2` and $`F` is its
$`\{-1,1\}`-valued encoding, then
$$`2\Pr[\text{BLR accepts }f]-1
=\sum_{S\subseteq[n]}\widehat F(S)^3.`
:::

:::theorem "theorem-1.30" (lean := "FABL.close_to_linear_of_blrAcceptanceProbability_eq") (uses := "blr-test, definition-1.29, theorem-1.27, parseval, plancherel, proposition-1.9, definition-1.28, support-blr-cubic-identity") (tags := "section-1-6, fidelity-exact")
*Theorem 1.30.* Suppose the BLR Test accepts
$`f:\mathbb F_2^n\to\mathbb F_2` with probability $`1-\epsilon`. Then $`f` is
$`\epsilon`-close to being linear.
:::

:::proposition "proposition-1.31" (lean := "FABL.localCorrection, FABL.localCorrection_successProbability") (uses := "definition-1.29, definition-1.2") (tags := "section-1-6, fidelity-exact-pointwise-quantifier-order")
*Proposition 1.31.* Suppose $`f:\mathbb F_2^n\to\{-1,1\}` is
$`\epsilon`-close to the linear function $`\chi_S`. Then, for every
$`x\in\mathbb F_2^n`, the following algorithm outputs $`\chi_S(x)` with
probability at least $`1-2\epsilon`:

1. Choose uniform $`\boldsymbol{y}\in\mathbb F_2^n`.
2. Query $`f` at $`\boldsymbol{y}` and $`x+\boldsymbol{y}`.
3. Output $`f(\boldsymbol{y})f(x+\boldsymbol{y})`.

The probability bound holds for every requested $`x`.
:::
