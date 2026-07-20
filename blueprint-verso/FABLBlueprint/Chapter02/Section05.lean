/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter02.Arrow
import FABL.Chapter02.ArrowLevelOneBound

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Highlight: Arrow's Theorem" =>

:::lemma_ "support-exercise-1.1i" (parent := "fabl-chapter-2") (lean := "FABL.IsNAE3, FABL.Ranking3, FABL.rankingPreference, FABL.rankingPreference_isNAE3, FABL.exists_rankingPreference_eq_iff_isNAE3") (tags := "section-2-5, support, fidelity-exact")
*Exercise 1.1(i).* The not-all-equal function
$`\operatorname{NAE}_n:\{-1,1\}^n\to\{0,1\}` is defined by
$$`
\operatorname{NAE}_n(x)=1
\quad\Longleftrightarrow\quad
x_1,\ldots,x_n\text{ are not all equal}.
`
For $`n=3`, its satisfying inputs are exactly
$$`
\{(+1,+1,-1),(+1,-1,-1),(-1,+1,-1),
  (-1,+1,+1),(+1,-1,+1),(-1,-1,+1)\}.
`
:::

:::definition "support-three-candidate-condorcet-model" (parent := "fabl-chapter-2") (lean := "FABL.PairwiseContest, FABL.RankingProfile, FABL.pairwiseVotes, FABL.societalOutcome, FABL.SatisfiesIIA, FABL.societalOutcome_satisfiesIIA") (uses := "support-exercise-1.1i") (tags := "section-2-5, support, fidelity-exact")
*Three-candidate Condorcet model.* Let the candidates be $`a,b,c` and let
$`f:\{-1,1\}^n\to\{-1,1\}` be a two-candidate voting rule. Write
$`x,y,z\in\{-1,1\}^n` for the voters' pairwise preferences in the elections
$`a` versus $`b`, $`b` versus $`c`, and $`c` versus $`a`, respectively, with
the first-listed candidate encoded by $`+1`. Each voter's strict ranking is
therefore encoded by one of the six triples satisfying
$`\operatorname{NAE}_3`. The three societal pairwise outcomes are
$`(f(x),f(y),f(z))`.
:::

:::definition "definition-2.55" (parent := "fabl-chapter-2") (lean := "FABL.IsCondorcetWinner, FABL.HasCondorcetWinner, FABL.HasSocietalCondorcetWinner, FABL.hasCondorcetWinner_iff_isNAE3") (uses := "support-three-candidate-condorcet-model") (tags := "section-2-5, fidelity-exact")
*Definition 2.55.* In an election employing Condorcet's method with voting
rule $`f:\{-1,1\}^n\to\{-1,1\}`, a candidate is a *Condorcet winner* if it
wins every pairwise election in which it participates.

For three candidates, there is no Condorcet winner precisely when the
societal outcome $`(f(x),f(y),f(z))` is one of the two all-equal triples
$`(-1,-1,-1)` and $`(+1,+1,+1)`; this event is Condorcet's Paradox.
:::

:::theorem "arrows-theorem" (parent := "fabl-chapter-2") (lean := "FABL.arrowsTheorem") (uses := "definition-2.3, definition-2.8, definition-2.55, theorem-2.49, theorem-2.56, support-exercise-1.19ab") (tags := "section-2-5, fidelity-exact")
*Arrow's Theorem.* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` is a unanimous voting rule used in a
three-candidate Condorcet election. If every profile of voters' strict
rankings has a Condorcet winner, then $`f` is a dictatorship: there exists
$`i\in[n]` such that $`f(x)=\chi_i(x)=x_i` for every
$`x\in\{-1,1\}^n`.
:::

:::lemma_ "support-kalai-condorcet-calculation" (parent := "fabl-chapter-2") (lean := "FABL.expect_rankingPreference, FABL.expect_rankingPreference_mul, FABL.expect_rankingProfile_prod, FABL.nae3Indicator, FABL.nae3Indicator_eq_polynomial, FABL.expect_monomial_pairwiseVotes_mul, FABL.expect_pairwiseVotes_mul_eq_fourier_sum, FABL.expect_pairwiseVotes_mul_eq_noiseStability, FABL.condorcetWinnerIndicator_eq_nae3") (uses := "definition-2.11, definition-2.41, definition-2.55, support-exercise-1.1i, theorem-1.1") (tags := "section-2-5, support, fidelity-exact")
*Kalai's Condorcet calculation.* Under impartial culture for a
three-candidate election, the triples
$`(\boldsymbol x_i,\boldsymbol y_i,\boldsymbol z_i)` are independent across
$`i` and are each uniform on the six satisfying inputs of
$`\operatorname{NAE}_3`. Moreover,
$$`
\Pr[\text{there is a Condorcet winner}]
=\mathbb E[\operatorname{NAE}_3(
 f(\boldsymbol x),f(\boldsymbol y),f(\boldsymbol z))],
\tag{2.8}`
the multilinear expansion is
$$`
\operatorname{NAE}_3(w_1,w_2,w_3)
=\frac34-\frac14w_1w_2-\frac14w_1w_3-\frac14w_2w_3,
`
and each of
$`(\boldsymbol x,\boldsymbol y)`,
$`(\boldsymbol x,\boldsymbol z)`, and
$`(\boldsymbol y,\boldsymbol z)` is a $`(-1/3)`-correlated pair.
:::

:::theorem "theorem-2.56" (parent := "fabl-chapter-2") (lean := "FABL.condorcetWinnerProbability, FABL.condorcetWinnerProbability_eq_noiseStability") (uses := "definition-2.11, definition-2.42, definition-2.55, support-kalai-condorcet-calculation") (tags := "section-2-5, fidelity-exact")
*Theorem 2.56.* Consider a three-candidate Condorcet election using
$`f:\{-1,1\}^n\to\{-1,1\}`. Under the impartial culture assumption, the
probability of a Condorcet winner is exactly
$`\frac34-\frac34\operatorname{Stab}_{-1/3}[f]`.
:::

:::theorem "guilbauds-formula" (parent := "fabl-chapter-2") (lean := "FABL.tendsto_condorcetWinnerProbability_majority_odd") (uses := "definition-2.1, theorem-2.45, theorem-2.56") (tags := "section-2-5, fidelity-exact")
*Guilbaud's Formula.* In a three-candidate Condorcet election using
$`\operatorname{Maj}_n`, the probability of a Condorcet winner tends, as odd
$`n` tends to infinity, to $`\frac{3}{2\pi}\arccos(-1/3)\approx91.2\%`.
:::

:::theorem "theorem-2.57" (parent := "fabl-chapter-2") (lean := "FABL.condorcetWinnerProbability_le_of_equalSingletonFourierCoefficients, FABL.two_thirds_div_nat_isLittleO_one, FABL.exists_condorcetWinnerProbability_upperError_isLittleO, FABL.condorcetWinnerProbability_eventually_le_seven_ninths_add_four_div_nine_pi_add") (uses := "proposition-2.58, corollary-2.59") (tags := "section-2-5, fidelity-exact")
*Theorem 2.57.* In a three-candidate Condorcet election using a rule
$`f:\{-1,1\}^n\to\{-1,1\}` whose singleton Fourier coefficients
$`\widehat f(i)` are all equal, the probability of a Condorcet winner is at
most $`\frac79+\frac{4}{9\pi}+o_n(1)\approx91.9\%`.
:::

:::lemma_ "support-exercise-2.24" (parent := "fabl-chapter-2") (lean := "FABL.HasEqualSingletonFourierCoefficients, FABL.sum_fourierCoeff_singleton_neg, FABL.abs_sum_fourierCoeff_singleton_le_majority, FABL.fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div, FABL.totalInfluence_majority_odd_sq_div_card, FABL.totalInfluence_majority_sq_div_card_le, FABL.fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card, FABL.three_div_nat_isLittleO_one") (uses := "theorem-2.33") (tags := "section-2-5, support, fidelity-exact")
*Exercise 2.24.* Prove Proposition 2.58 with $`O(n^{-1})` in place of
$`o_n(1)`. The suggested estimate, obtained using Theorem 2.33, is
$$`
\widehat f(i)
\le \frac{\sqrt{2/\pi}}{\sqrt n}+O(n^{-3/2})
`
for every $`i\in[n]` when all singleton Fourier coefficients are equal.
:::

:::proposition "proposition-2.58" (parent := "fabl-chapter-2") (lean := "FABL.exists_levelOneWeight_upperError_isLittleO, FABL.fourierWeightAtLevel_one_eventually_le_two_div_pi_add") (uses := "definition-1.19, theorem-2.33, support-exercise-2.24") (tags := "section-2-5, fidelity-exact")
*Proposition 2.58.* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` has all singleton Fourier coefficients
$`\widehat f(i)` equal. Then $`\mathbf W^1[f]\le\frac2\pi+o_n(1)`.
Exercise 2.24 asks for the stronger error term $`O(n^{-1})`.
:::

:::corollary "corollary-2.59" (parent := "fabl-chapter-2") (lean := "FABL.condorcetWinnerProbability_le") (uses := "definition-1.19, theorem-2.49, theorem-2.56, parseval") (tags := "section-2-5, fidelity-exact")
*Corollary 2.59.* In a three-candidate Condorcet election using
$`f:\{-1,1\}^n\to\{-1,1\}`, the probability of a Condorcet winner is at
most $`\frac79+\frac29\mathbf W^1[f]`.
:::

:::corollary "corollary-2.60" (parent := "fabl-chapter-2") (lean := "FABL.exists_signedDictator_relativeHammingDist_le_of_condorcetWinnerProbability_eq_one_sub, FABL.relativeHammingDist_signedDictator_family_isBigO_of_condorcetWinnerProbability_eq_one_sub") (uses := "definition-1.10, corollary-2.59, fkn-theorem") (tags := "section-2-5, fidelity-exact")
*Corollary 2.60.* Suppose that, in a three-candidate Condorcet election using
$`f:\{-1,1\}^n\to\{-1,1\}`, the probability of a Condorcet winner is
$`1-\epsilon`. Then there is an $`i\in[n]` and a sign
$`\sigma\in\{-1,1\}` such that
$`\operatorname{dist}(f,\sigma\chi_i)=O(\epsilon)`.
:::

:::theorem "fkn-theorem" (parent := "fabl-chapter-2") (lean := "FABL.signedDictator, FABL.fkn, FABL.fkn_family_isBigO") (uses := "definition-1.10, definition-1.19, definition-2.3") (tags := "section-2-5, fidelity-exact")
*Friedgut-Kalai-Naor (FKN) Theorem.* Suppose
$`f:\{-1,1\}^n\to\{-1,1\}` satisfies $`\mathbf W^1[f]\ge1-\delta`.
Then there is an $`i\in[n]` and a sign $`\sigma\in\{-1,1\}` such that
$`\operatorname{dist}(f,\sigma\chi_i)=O(\delta)`.
The book proves this theorem in Chapter 9.1. It later improves the distance
bound in Chapter 5.4 to
$`\delta/4+O(\delta^2\log(2/\delta))`.
:::
