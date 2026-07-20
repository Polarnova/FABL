/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter02.SocialChoiceFunctions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Social choice functions" =>

:::definition "definition-2.1" (parent := "fabl-chapter-2") (lean := "FABL.thresholdSign, FABL.majority, FABL.IsMajorityFunction, FABL.majority_isMajorityFunction") (tags := "section-2-1, fidelity-exact")
*Definition 2.1.* For odd $`n`, the majority function
$`\operatorname{Maj}_n:\{-1,1\}^n\to\{-1,1\}` is
$`\operatorname{Maj}_n(x)=\operatorname{sgn}(x_1+x_2+\cdots+x_n)`.
Occasionally, when $`n` is even, a function is called a majority function if
its value is the sign of $`x_1+\cdots+x_n` whenever this sum is nonzero.
:::

:::definition "definition-2.2" (parent := "fabl-chapter-2") (lean := "FABL.andFunction, FABL.orFunction") (tags := "section-2-1, fidelity-exact")
*Definition 2.2.* The function
$`\operatorname{AND}_n:\{-1,1\}^n\to\{-1,1\}` is $`+1` unless
$`x=(-1,-1,\ldots,-1)`. The function
$`\operatorname{OR}_n:\{-1,1\}^n\to\{-1,1\}` is $`-1` unless
$`x=(+1,+1,\ldots,+1)`.
:::

:::definition "definition-2.3" (parent := "fabl-chapter-2") (lean := "FABL.dictator, FABL.dictator_toReal_eq_monomial_singleton") (uses := "support-sign-monomial") (tags := "section-2-1, fidelity-exact")
*Definition 2.3.* The $`i`th dictator function
$`\chi_i:\{-1,1\}^n\to\{-1,1\}` is $`\chi_i(x)=x_i`.
Here $`\chi_i` abbreviates the singleton parity function $`\chi_{\{i\}}`.
:::

:::definition "definition-2.4" (parent := "fabl-chapter-2") (lean := "FABL.IsKJunta, FABL.isKJunta_iff_exists_factorization") (tags := "section-2-1, fidelity-exact")
*Definition 2.4.* A function $`f:\{-1,1\}^n\to\{-1,1\}` is a
$`k`-junta, for $`k\in\mathbb N`, if it depends on at most $`k` input
coordinates; that is, there are $`i_1,\ldots,i_k\in[n]` and a function
$`g:\{-1,1\}^k\to\{-1,1\}` such that
$`f(x)=g(x_{i_1},\ldots,x_{i_k})` for every $`x\in\{-1,1\}^n`. Informally,
$`f` is called a junta when it
depends on only a constant number of coordinates.
:::

:::definition "definition-2.5" (parent := "fabl-chapter-2") (lean := "FABL.IsLinearThreshold") (tags := "section-2-1, fidelity-exact")
*Definition 2.5.* A function $`f:\{-1,1\}^n\to\{-1,1\}` is a
weighted majority, or a linear threshold function, if there are
$`a_0,a_1,\ldots,a_n\in\mathbb R` such that
$`f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)`.
:::

:::definition "definition-2.6" (parent := "fabl-chapter-2") (lean := "FABL.recursiveMajority, FABL.recursiveMajority_one, FABL.recursiveMajority_succ") (uses := "definition-2.1") (tags := "section-2-1, fidelity-exact")
*Definition 2.6.* The depth-$`d` recursive majority of $`n`, denoted
$`\operatorname{Maj}_n^{\otimes d}`, is the Boolean function on $`n^d` bits
defined inductively by $`\operatorname{Maj}_n^{\otimes 1}=\operatorname{Maj}_n`
and
$$`\operatorname{Maj}_n^{\otimes(d+1)}
  (x^{(1)},\ldots,x^{(n)})
=\operatorname{Maj}_n\bigl(
  \operatorname{Maj}_n^{\otimes d}(x^{(1)}),\ldots,
  \operatorname{Maj}_n^{\otimes d}(x^{(n)})\bigr),`
where each $`x^{(i)}\in\{-1,1\}^{n^d}`.
:::

:::definition "definition-2.7" (parent := "fabl-chapter-2") (lean := "FABL.inputBlock, FABL.tribes") (uses := "definition-2.2") (tags := "section-2-1, fidelity-exact")
*Definition 2.7.* The tribes function of width $`w` and size $`s` is
$`\operatorname{Tribes}_{w,s}:\{-1,1\}^{sw}\to\{-1,1\}` defined by
$$`\operatorname{Tribes}_{w,s}(x^{(1)},\ldots,x^{(s)})
=\operatorname{OR}_s\bigl(
  \operatorname{AND}_w(x^{(1)}),\ldots,
  \operatorname{AND}_w(x^{(s)})\bigr),`
where each $`x^{(i)}\in\{-1,1\}^w`.
:::

:::lemma_ "support-exercise-1.30a" (parent := "fabl-chapter-2") (lean := "FABL.permuteInput, FABL.permuteFinset, FABL.fourierCoeff_comp_permuteInput") (uses := "proposition-1.8") (tags := "section-2-1, support, fidelity-exact")
*Exercise 1.30(a).* A permutation $`\pi\in S_n` acts on strings by
$`(x^\pi)_i=x_{\pi(i)}` and on functions by
$`f^\pi(x)=f(x^\pi)`. For every $`f:\{-1,1\}^n\to\mathbb R` and
$`S\subseteq[n]`, its Fourier coefficients obey
$`\widehat{f^\pi}(S)=\widehat f\bigl(\pi^{-1}(S)\bigr)`.
:::

:::definition "definition-2.8" (parent := "fabl-chapter-2") (lean := "Monotone, Function.Odd, FABL.IsUnanimous, FABL.IsSymmetric, FABL.isSymmetric_iff_eq_of_positiveCoordinateCount_eq") (uses := "support-exercise-1.30a") (tags := "section-2-1, fidelity-exact")
*Definition 2.8.* A function $`f:\{-1,1\}^n\to\{-1,1\}` is:

* _monotone_ if $`f(x)\le f(y)` whenever $`x\le y` coordinatewise;
* _odd_ if $`f(-x)=-f(x)`;
* _unanimous_ if $`f(1,\ldots,1)=1` and
  $`f(-1,\ldots,-1)=-1`;
* _symmetric_ if $`f(x^\pi)=f(x)` for every $`\pi\in S_n`; equivalently,
  $`f(x)` depends only on the number of coordinates of $`x` equal to $`1`.

The definitions of monotone, odd, and symmetric also apply to
$`f:\{-1,1\}^n\to\mathbb R`.
:::

:::lemma_ "support-exercise-2.3" (parent := "fabl-chapter-2") (lean := "FABL.IsEqualWeightThreshold, FABL.symmetric_and_monotone_iff_isEqualWeightThreshold, FABL.may_theorem") (uses := "definition-2.1, definition-2.5, definition-2.8") (tags := "section-2-1, support, fidelity-exact")
*Exercise 2.3: May's Theorem.*

1. A function $`f:\{-1,1\}^n\to\{-1,1\}` is symmetric and monotone if
   and only if it has a weighted-majority representation
   $`f(x)=\operatorname{sgn}(a_0+x_1+\cdots+x_n)`
   with all nonconstant weights equal to $`1`.
2. If $`f:\{-1,1\}^n\to\{-1,1\}` is symmetric, monotone, and odd, then
   $`n` is odd and $`f=\operatorname{Maj}_n`.
:::

:::lemma_ "example-2.9" (parent := "fabl-chapter-2") (lean := "FABL.example2_9") (uses := "definition-2.1, definition-2.2, definition-2.3, definition-2.6, definition-2.7, definition-2.8, support-exercise-2.3") (tags := "section-2-1, fidelity-exact")
*Example 2.9.* For odd $`n`, $`\operatorname{Maj}_n` is monotone, odd,
unanimous, and symmetric; by May's Theorem it is the only function with all
four properties. Dictator functions and recursive majority functions are
monotone, odd, and unanimous. For $`n\ge2`, the functions
$`\operatorname{AND}_n` and $`\operatorname{OR}_n` are monotone, unanimous,
and symmetric, but are not odd. For $`w,s\ge2`, tribes functions are monotone
and unanimous; they are not symmetric, but they have the weaker property
defined next. (These lower bounds make explicit the degenerate arities
suppressed in the book's prose.)
:::

:::definition "definition-2.10" (parent := "fabl-chapter-2") (lean := "FABL.IsTransitiveSymmetric") (uses := "support-exercise-1.30a") (tags := "section-2-1, fidelity-exact")
*Definition 2.10.* A function $`f:\{-1,1\}^n\to\{-1,1\}` is
transitive-symmetric if, for every $`i,i'\in[n]`, there is a permutation
$`\pi\in S_n` such that $`\pi(i)=i'` and $`f(x^\pi)=f(x)` for every
$`x\in\{-1,1\}^n`.
:::

:::definition "definition-2.11" (parent := "fabl-chapter-2") (lean := "FABL.impartialCulture") (uses := "notation-1.4") (tags := "section-2-1, fidelity-exact")
*Definition 2.11.* The impartial culture assumption is that the $`n` voters'
preferences are independent and uniformly random.
:::
