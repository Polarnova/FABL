/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter02.NoiseStability

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Noise stability" =>

:::definition "definition-2.40" (lean := "FABL.correlationKeepProbability, FABL.coordinateNoisePMF, FABL.nonnegativeCorrelationProbability, FABL.coordinateResamplingNoisePMF, FABL.coordinateResamplingNoisePMF_eq_coordinateNoisePMF, FABL.noiseKernel, FABL.resamplingNoiseKernel, FABL.resamplingNoiseKernel_eq_noiseKernel") (uses := "notation-1.4") (tags := "section-2-4, fidelity-exact")
*Definition 2.40.* Let $`\rho\in[0,1]` and fix
$`x\in\{-1,1\}^n`. The notation
$`\boldsymbol y\sim N_\rho(x)` means that the coordinates of
$`\boldsymbol y` are drawn independently, with
$$`
\boldsymbol y_i=
\begin{cases}
x_i & \text{with probability }\rho,\\
\text{a uniformly random bit} & \text{with probability }1-\rho.
\end{cases}`
Equivalently, and extending the notation to every $`\rho\in[-1,1]`,
$$`
\boldsymbol y_i=
\begin{cases}
x_i & \text{with probability }\frac12+\frac12\rho,\\
-x_i & \text{with probability }\frac12-\frac12\rho.
\end{cases}`
We say that $`\boldsymbol y` is $`\rho`-correlated to $`x`.
:::

:::definition "definition-2.41" (lean := "FABL.correlatedPairPMF, FABL.correlatedPairPMF_map_swap, FABL.correlatedPairPMF_expect_signValue_fst, FABL.correlatedPairPMF_expect_signValue_snd, FABL.correlatedPairPMF_expect_signValue_mul") (uses := "definition-2.40, notation-1.4") (tags := "section-2-4, fidelity-exact")
*Definition 2.41.* Draw $`\boldsymbol x` uniformly from
$`\{-1,1\}^n` and then draw
$`\boldsymbol y\sim N_\rho(\boldsymbol x)`. The resulting
$`(\boldsymbol x,\boldsymbol y)` is called a $`\rho`-correlated pair of random
strings. This definition is symmetric in $`\boldsymbol x` and
$`\boldsymbol y`. Equivalently, independently for every $`i\in[n]`,
the pair $`(\boldsymbol x_i,\boldsymbol y_i)` satisfies
$$`
\mathbb E[\boldsymbol x_i]=\mathbb E[\boldsymbol y_i]=0,
\qquad
\mathbb E[\boldsymbol x_i\boldsymbol y_i]=\rho.
`
:::

:::definition "definition-2.42" (lean := "FABL.noiseStability, FABL.correlatedAgreementProbability, FABL.correlatedDisagreementProbability, FABL.noiseStability_toReal_eq_agreement_sub_disagreement, FABL.noiseStability_toReal_eq_two_mul_agreement_sub_one") (uses := "definition-2.41") (tags := "section-2-4, fidelity-exact")
*Definition 2.42.* For $`f:\{-1,1\}^n\to\mathbb R` and
$`\rho\in[-1,1]`, the noise stability of $`f` at $`\rho` is
$$`
\operatorname{Stab}_\rho[f]
=\mathbb E_{(\boldsymbol x,\boldsymbol y)\ \rho\text{-correlated}}
 [f(\boldsymbol x)f(\boldsymbol y)].
`
If $`f:\{-1,1\}^n\to\{-1,1\}`, then
$$`
\operatorname{Stab}_\rho[f]
=\Pr[f(\boldsymbol x)=f(\boldsymbol y)]
 -\Pr[f(\boldsymbol x)\ne f(\boldsymbol y)]
=2\Pr[f(\boldsymbol x)=f(\boldsymbol y)]-1,
`
where all probabilities are over a $`\rho`-correlated pair.
:::

:::definition "definition-2.43" (lean := "FABL.noiseSensitivity, FABL.noiseSensitivity_eq_half_sub_half_noiseStability") (uses := "definition-2.41, definition-2.42") (tags := "section-2-4, fidelity-exact")
*Definition 2.43.* Let $`f:\{-1,1\}^n\to\{-1,1\}` and
$`\delta\in[0,1]`. The noise sensitivity $`\operatorname{NS}_\delta[f]` is
the probability that $`f(\boldsymbol x)\ne f(\boldsymbol y)`, where
$`\boldsymbol x` is uniform and $`\boldsymbol y` is obtained by reversing
each bit of $`\boldsymbol x` independently with probability $`\delta`.
Equivalently,
$`\operatorname{NS}_\delta[f]=\frac12-\frac12\operatorname{Stab}_{1-2\delta}[f]`.
:::

:::lemma_ "example-2.44" (lean := "FABL.noiseStability_const_one, FABL.noiseStability_const_neg_one, FABL.noiseStability_dictator, FABL.noiseSensitivity_dictator, FABL.noiseStability_parityFunction") (uses := "definition-1.2, definition-2.3, definition-2.42, definition-2.43") (tags := "section-2-4, fidelity-exact")
*Example 2.44.* The constant functions $`\pm1` have noise stability $`1`
for every $`\rho`. Dictators satisfy
$`\operatorname{Stab}_\rho[\chi_i]=\rho` and
$`\operatorname{NS}_\delta[\chi_i]=\delta`.
More generally, for every $`S\subseteq[n]`,
$$`
\operatorname{Stab}_\rho[\chi_S]
=\mathbb E[\boldsymbol x^S\boldsymbol y^S]
=\mathbb E\!\left[\prod_{i\in S}
  \boldsymbol x_i\boldsymbol y_i\right]
=\prod_{i\in S}\mathbb E[\boldsymbol x_i\boldsymbol y_i]
=\rho^{|S|}.
`
:::

:::theorem "theorem-2.45" (lean := "FABL.tendsto_noiseStability_majority_odd, FABL.two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos, FABL.tendsto_noiseStability_majority_odd_arccos, FABL.tendsto_noiseSensitivity_majority_odd, FABL.arccos_one_sub_two_mul_eq_two_mul_arcsin_sqrt, FABL.arccos_one_sub_two_mul_sub_two_mul_sqrt_isBigO, FABL.majorityNoiseSensitivityLimit_sub_two_div_pi_mul_sqrt_isBigO") (uses := "definition-2.1, definition-2.42, definition-2.43") (tags := "section-2-4, fidelity-exact")
*Theorem 2.45.* For every $`\rho\in[-1,1]`, as odd $`n` tends to infinity,
$$`
\lim_{\substack{n\to\infty\\n\text{ odd}}}
\operatorname{Stab}_\rho[\operatorname{Maj}_n]
=\frac2\pi\arcsin\rho
=1-\frac2\pi\arccos\rho.
`
Equivalently, for every $`\delta\in[0,1]`,
$$`
\lim_{\substack{n\to\infty\\n\text{ odd}}}
\operatorname{NS}_\delta[\operatorname{Maj}_n]
=\frac1\pi\arccos(1-2\delta).
`
Consequently, using
$`\arccos(1-2\delta)=2\sqrt\delta+O(\delta^{3/2})`,
$$`
\lim_{\substack{n\to\infty\\n\text{ odd}}}
\operatorname{NS}_\delta[\operatorname{Maj}_n]
=\frac2\pi\sqrt\delta+O(\delta^{3/2}).
`
The book proves this theorem in Chapter 5.2.
:::

:::definition "definition-2.46" (lean := "FABL.noiseOperator, FABL.noiseOperator_apply_eq_pmfExpectation") (uses := "definition-2.40") (tags := "section-2-4, fidelity-exact")
*Definition 2.46.* For $`\rho\in[-1,1]`, the noise operator with parameter
$`\rho` is the linear operator $`T_\rho` on functions
$`f:\{-1,1\}^n\to\mathbb R` defined by
$$`
T_\rho f(x)=\mathbb E_{\boldsymbol y\sim N_\rho(x)}[f(\boldsymbol y)].
`
:::

:::proposition "proposition-2.47" (lean := "FABL.noiseOperator_monomial_apply, FABL.noiseOperator_fourier_expansion, FABL.noiseOperator_eq_sum_degreePart") (uses := "definition-2.46, theorem-1.1, definition-1.19") (tags := "section-2-4, fidelity-exact")
*Proposition 2.47.* For $`f:\{-1,1\}^n\to\mathbb R`, the Fourier
expansion of $`T_\rho f` is
$$`
T_\rho f
=\sum_{S\subseteq[n]}\rho^{|S|}\widehat f(S)\chi_S
=\sum_{k=0}^n\rho^k f^{=k}.
`
Equivalently, every Walsh character is an eigenfunction:
$`T_\rho\chi_S=\rho^{|S|}\chi_S`.
:::

:::lemma_ "fact-2.48" (lean := "FABL.noiseStability_eq_uniformInner_noiseOperator") (uses := "definition-2.41, definition-2.42, definition-2.46") (tags := "section-2-4, fidelity-exact")
*Fact 2.48.* For every $`f:\{-1,1\}^n\to\mathbb R` and
$`\rho\in[-1,1]`, one has
$`\operatorname{Stab}_\rho[f]=\langle f,T_\rho f\rangle`.
:::

:::theorem "theorem-2.49" (lean := "FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff, FABL.noiseStability_eq_sum_level_rho_pow_mul_fourierWeight, FABL.noiseStability_toReal_eq_spectralSample_moment, FABL.noiseSensitivity_eq_sum_level") (uses := "definition-1.18, definition-1.19, definition-2.43, proposition-2.47, fact-2.48, plancherel") (tags := "section-2-4, fidelity-exact")
*Theorem 2.49.* For every $`f:\{-1,1\}^n\to\mathbb R` and
$`\rho\in[-1,1]`,
$$`
\operatorname{Stab}_\rho[f]
=\sum_{S\subseteq[n]}\rho^{|S|}\widehat f(S)^2
=\sum_{k=0}^n\rho^k\mathbf W^k[f].
`
Hence, if $`f:\{-1,1\}^n\to\{-1,1\}`, then
$$`
\operatorname{Stab}_\rho[f]
=\mathbb E_{\boldsymbol S\sim\mathcal S_f}[\rho^{|\boldsymbol S|}],
\tag{2.6}`
and, for $`\delta\in[0,1]`,
$$`
\operatorname{NS}_\delta[f]
=\frac12\sum_{k=0}^n
 \bigl(1-(1-2\delta)^k\bigr)\mathbf W^k[f].
\tag{2.7}`
:::

:::lemma_ "support-exercise-2.42" (lean := "FABL.noiseSensitivity_le_delta_mul_totalInfluence") (uses := "definition-2.27, theorem-2.49") (tags := "section-2-4, support, fidelity-exact")
*Exercise 2.42.* For every
$`f:\{-1,1\}^n\to\{-1,1\}` and every $`\delta\in[0,1]`,
$$`
\operatorname{NS}_\delta[f]\le\delta\mathbf I[f].
`
:::

:::proposition "proposition-2.50" (lean := "FABL.noiseStability_le_rho_of_balanced, FABL.noiseStability_eq_rho_iff_signed_dictator") (uses := "definition-1.11, theorem-2.49, support-exercise-1.19ab, parseval") (tags := "section-2-4, fidelity-exact")
*Proposition 2.50.* Let $`\rho\in(0,1)`. If
$`f:\{-1,1\}^n\to\{-1,1\}` is unbiased, then
$`\operatorname{Stab}_\rho[f]\le\rho`.
Equality holds if and only if $`f=\pm\chi_i` for some $`i\in[n]`.
:::

:::proposition "proposition-2.51" (lean := "FABL.deriv_stabilityCurve_zero, FABL.deriv_stabilityCurve_one, FABL.deriv_noiseSensitivityCurve_zero, FABL.monotoneOn_noiseSensitivityCurve") (uses := "definition-1.19, definition-2.43, theorem-2.38, theorem-2.49") (tags := "section-2-4, fidelity-exact")
*Proposition 2.51.* For every $`f:\{-1,1\}^n\to\mathbb R`,
$$`
\left.\frac{d}{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=0}
=\mathbf W^1[f],
\qquad
\left.\frac{d}{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=1}
=\mathbf I[f].
`
For $`f:\{-1,1\}^n\to\{-1,1\}`,
$`\operatorname{NS}_\delta[f]` is increasing on $`[0,1/2]`, and the second
identity is equivalently
$`\left.\frac{d}{d\delta}\operatorname{NS}_\delta[f]\right|_{\delta=0}=\mathbf I[f]`.
:::

:::definition "definition-2.52" (lean := "FABL.stableInfluence, FABL.stableInfluence_eq_noiseStability_discreteDerivative, FABL.totalStableInfluence") (uses := "definition-2.16, definition-2.42, theorem-2.20") (tags := "section-2-4, fidelity-exact")
*Definition 2.52.* Let $`f:\{-1,1\}^n\to\mathbb R`,
$`\rho\in[0,1]`, and $`i\in[n]`. The $`\rho`-stable influence of coordinate
$`i` on $`f` is
$$`
\operatorname{Inf}^{(\rho)}_i[f]
=\operatorname{Stab}_\rho[D_i f]
=\sum_{S\ni i}\rho^{|S|-1}\widehat f(S)^2,
`
where $`0^0` is interpreted as $`1`. The total $`\rho`-stable influence is
$`\mathbf I^{(\rho)}[f]=\sum_{i=1}^n\operatorname{Inf}^{(\rho)}_i[f]`.
:::

:::lemma_ "support-exercise-2.40" (lean := "FABL.deriv_stabilityCurve_eq_totalStableInfluence, FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff") (uses := "definition-2.52, theorem-2.38, theorem-2.49") (tags := "section-2-4, support, fidelity-exact")
*Exercise 2.40.* Verify that, for every
$`f:\{-1,1\}^n\to\mathbb R` and $`\rho\in[0,1]`,
$$`
\mathbf I^{(\rho)}[f]
=\frac{d}{d\rho}\operatorname{Stab}_\rho[f]
=\sum_{k=1}^n k\rho^{k-1}\mathbf W^k[f].
`
:::

:::lemma_ "fact-2.53" (lean := "FABL.totalStableInfluence_eq_sum_level") (uses := "definition-2.52, support-exercise-2.40") (tags := "section-2-4, fidelity-exact")
*Fact 2.53.* For every $`f:\{-1,1\}^n\to\mathbb R` and
$`\rho\in[0,1]`,
$$`
\mathbf I^{(\rho)}[f]
=\frac{d}{d\rho}\operatorname{Stab}_\rho[f]
=\sum_{k=1}^n k\rho^{k-1}\mathbf W^k[f].
`
:::

:::lemma_ "support-exercise-2.45" (lean := "FABL.card_mul_one_sub_pow_le_inv") (tags := "section-2-4, support, fidelity-exact")
*Exercise 2.45.* For every $`0<\delta\le1` and every positive integer
$`k`, one has $`(1-\delta)^{k-1}k\le\frac1\delta`.
One may compare both sides with
$`1+(1-\delta)+(1-\delta)^2+\cdots+(1-\delta)^{k-1}`.
:::

:::proposition "proposition-2.54" (lean := "FABL.card_stableInfluence_ge_le") (uses := "proposition-1.13, definition-2.52, fact-2.53, support-exercise-2.45") (tags := "section-2-4, fidelity-exact-denominator-delta-epsilon")
*Proposition 2.54.* Suppose $`f:\{-1,1\}^n\to\mathbb R` satisfies
$`\operatorname{Var}[f]\le1`. Given $`0<\delta\le1` and
$`0<\epsilon\le1`, let
$$`
J=\left\{i\in[n]:
\operatorname{Inf}^{(1-\delta)}_i[f]\ge\epsilon\right\}.
`
Then $`|J|\le\frac1{\delta\epsilon}`.
:::
