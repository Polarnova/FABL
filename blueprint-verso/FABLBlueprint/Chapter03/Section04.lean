/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import FABL.Chapter03.LearningTheory

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Learning theory" =>

:::definition "definition-3.27" (lean := "FABL.LearningAccuracy, FABL.learningAccuracy_toReal_mem_Icc, FABL.LearningAccess, FABL.LearningCost, FABL.LearningProgram, FABL.LearningProgram.runWithCost, FABL.LearningProgram.eventProbability, FABL.FiniteHypothesisRepresentation, FABL.LearningAlgorithm, FABL.LearnsConceptClassWithError") (uses := "definition-1.10, definition-1.29, notation-1.4") (tags := "section-3-4, fidelity-exact-finite-rational-accuracy-encoding")
*Definition 3.27.* In the model of PAC (*Probably Approximately Correct*)
learning under the uniform distribution on $`\{-1,1\}^n`, a learning problem
is specified by a concept class
$$`
\mathcal C\subseteq
\{f:\{-1,1\}^n\to\{-1,1\}\}.
`
A learning algorithm $`A` for $`\mathcal C` is randomized and has limited
access to an unknown target $`f\in\mathcal C`. The two access models, in
increasing order of strength, are:

* *random examples*: $`A` may draw independent pairs $`(x,f(x))`, where
  $`x` is uniform on $`\{-1,1\}^n`;
* *queries*: $`A` may request $`f(x)` for any $`x\in\{-1,1\}^n` of its
  choice.

The algorithm also receives an accuracy parameter $`\epsilon\in[0,1/2]` and
must output a finite circuit representation of a hypothesis
$`h:\{-1,1\}^n\to\{-1,1\}`. It *learns $`\mathcal C` with error
$`\epsilon`* if, for every target $`f\in\mathcal C`, with high probability
its output satisfies
$$`
\operatorname{dist}(f,h)
=\Pr_{x\sim\{-1,1\}^n}[f(x)\ne h(x)]
\le\epsilon.
`
Here and throughout this chapter, “with high probability” may be fixed to
mean success probability at least $`9/10`.
:::

:::definition "definition-3.28" (lean := "FABL.fourierWeightOutside, FABL.IsFourierSpectrumConcentratedOn, FABL.spectralSampleOutsideProbability, FABL.spectralSampleOutsideProbability_eq_fourierWeightOutside, FABL.isFourierSpectrumConcentratedOn_iff_spectralSampleOutsideProbability_le") (uses := "definition-1.17, definition-1.18, parseval, proposition-1.8") (tags := "section-3-4, fidelity-exact")
*Definition 3.28.* Let $`\mathcal F` be a collection of subsets of $`[n]`.
The Fourier spectrum of $`f:\{-1,1\}^n\to\mathbb R` is
*$`\epsilon`-concentrated on $`\mathcal F`* if
$$`
\sum_{\substack{S\subseteq[n]\\S\notin\mathcal F}}
  \widehat f(S)^2\le\epsilon.
`
For Boolean-valued $`f`, this is equivalently
$$`
\Pr_{\boldsymbol S\sim\mathcal S_f}
 [\boldsymbol S\notin\mathcal F]\le\epsilon,
`
where $`\mathcal S_f` is the spectral sample of $`f`.
:::

:::theorem "theorem-3.29" (lean := "FABL.not_isFourierSpectrumConcentratedOn_empty, FABL.finiteFamily_nonempty_of_spectrum_concentrated, FABL.SparseFourierHypothesis.finiteRepresentation, FABL.finiteFamilyFourierEstimatorOutput_decode_encode, FABL.finiteFamilyFourierEstimatorOutput_evaluationWork, FABL.uniformLpNorm_sub_sparseFourierApproximation_sq, FABL.finiteFamilyCoefficientAccuracy, FABL.finiteFamilyCoefficientConfidence, FABL.finiteFamilySamplesPerCoefficient, FABL.finiteFamilyFourierEstimatorProgram, FABL.runWithCost_finiteFamilyFourierEstimatorProgram, FABL.finiteFamilyFourierEstimatorProgram_cost_eq, FABL.finiteFamilyFourierEstimatorProgram_cost_polyBound, FABL.measure_finiteFamily_someCoefficient_bad_le_one_tenth, FABL.relativeHammingDist_sparseFourierHypothesis_of_coefficients_le, FABL.relativeHammingDist_finiteFamilyFourierEstimatorOutput_le_of_no_bad, FABL.measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth, FABL.finiteFamilyFourierEstimatorProgram_failureProbability_le_one_tenth") (uses := "definition-3.27, definition-3.28, parseval, proposition-3.30, proposition-3.31, theorem-1.1") (tags := "section-3-4, fidelity-exact-stronger-rational-scheduler")
*Theorem 3.29.* Assume that a learning algorithm $`A` has at least
random-example access to a target
$`f:\{-1,1\}^n\to\{-1,1\}`. Suppose that $`A` can identify a finite
collection $`\mathcal F\subseteq2^{[n]}` on which the Fourier spectrum of
$`f` is $`\epsilon/2`-concentrated. Then, using
$`\operatorname{poly}(|\mathcal F|,n,1/\epsilon)` additional time and random
examples, $`A` can output, with probability at least $`9/10`, a finite circuit
representation of a hypothesis $`h` satisfying
$`\operatorname{dist}(f,h)\le\epsilon`.

For nonempty $`\mathcal F`, the procedure estimates every
$`\widehat f(S)`, $`S\in\mathcal F`, to accuracy
$`|\widetilde f(S)-\widehat f(S)|\le \frac{\sqrt\epsilon}{2\sqrt{|\mathcal F|}}`
with per-coefficient failure probability at most
$`1/(10|\mathcal F|)`, and outputs the sparse Fourier hypothesis
$$`
h(x)=\operatorname{sgn}\!\left(
  \sum_{S\in\mathcal F}\widetilde f(S)\chi_S(x)
\right).
`
The empty-family case is handled directly. The simultaneous-estimation
guarantee and Parseval give
$$`
\left\|f-\sum_{S\in\mathcal F}\widetilde f(S)\chi_S\right\|_2^2
=\sum_{S\in\mathcal F}
  (\widehat f(S)-\widetilde f(S))^2
 +\sum_{S\notin\mathcal F}\widehat f(S)^2
\le\epsilon.
`

One may instead use the rational per-coefficient accuracy
$`\epsilon/(2|\mathcal F|)`. For
$`0<\epsilon\le1/2` and nonempty $`\mathcal F`, this is no larger than the
displayed $`\sqrt\epsilon/(2\sqrt{|\mathcal F|})` budget and therefore gives
the same conclusion with a conservative polynomial sample bound. The
empty-family premise is impossible for a Boolean target in this parameter
range because its total Fourier weight is $`1`.
:::

:::proposition "proposition-3.30" (lean := "FABL.PositiveLearningParameter, FABL.fourierEstimatorFailureBits, FABL.fourierEstimatorSampleCount, FABL.fourierEstimatorSampleCount_cast_le, FABL.rationalFourierObservation, FABL.empiricalFourierCoeff, FABL.finiteUniformEmpiricalMean, FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le, FABL.fourierCoeffEstimatorProgram, FABL.scheduledFourierCoeffEstimatorProgram, FABL.runWithCost_scheduledFourierCoeffEstimatorProgram, FABL.scheduledFourierCoeffEstimatorProgram_cost_eq, FABL.scheduledFourierCoeffEstimatorProgram_failureProbability_le") (uses := "notation-1.4, proposition-1.8") (tags := "section-3-4, fidelity-exact")
*Proposition 3.30.* Given random-example access to
$`f:\{-1,1\}^n\to\{-1,1\}`, there is a randomized algorithm which takes
as input $`S\subseteq[n]` and $`0<\delta,\epsilon\le1/2`, and outputs an
estimate $`\widetilde f(S)` satisfying
$$`
\Pr\!\left[
 |\widetilde f(S)-\widehat f(S)|>\epsilon
\right]\le\delta.
`
Its running time is $`\operatorname{poly}(n,1/\epsilon)\log(1/\delta)`.
Concretely, it takes
$`m=O\!\left(\frac{\log(1/\delta)}{\epsilon^2}\right)` independent random
examples, makes exactly $`m` random-example calls, and
returns the empirical average of the $`\{-1,1\}`-valued samples
$`f(x)\chi_S(x)`.
:::

:::proposition "proposition-3.31" (lean := "FABL.indicator_ne_thresholdSign_le_sq, FABL.relativeHammingDist_thresholdSign_le_uniformLpNorm_two_sq, FABL.relativeHammingDist_thresholdSign_le_of_uniformLpNorm_two_sq_le") (uses := "definition-1.10") (tags := "section-3-4, fidelity-exact")
*Proposition 3.31.* Suppose that
$`f:\{-1,1\}^n\to\{-1,1\}` and
$`g:\{-1,1\}^n\to\mathbb R` satisfy $`\|f-g\|_2^2\le\epsilon`.
Define $`h:\{-1,1\}^n\to\{-1,1\}` by
$`h(x)=\operatorname{sgn}(g(x))`, choosing either value in $`\{-1,1\}`
when $`g(x)=0`. Then $`\operatorname{dist}(f,h)\le\epsilon`.
:::

:::theorem "low-degree-algorithm" (lean := "FABL.lowDegreeFourierFamily, FABL.mem_lowDegreeFourierFamily, FABL.lowDegreeFourierFamily_nonempty, FABL.card_lowDegreeFourierFamily_eq_sum_choose, FABL.card_lowDegreeFourierFamily_le, FABL.fourierWeightOutside_lowDegreeFourierFamily, FABL.isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff, FABL.fourierWeightAboveReal_antitone, FABL.IsFourierSpectrumConcentratedUpTo.mono_cutoff, FABL.IsFourierSpectrumConcentratedUpTo.mono_error, FABL.lowDegreeFourierEstimatorProgram, FABL.lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth, FABL.lowDegreeFourierEstimatorProgram_cost_polyBound") (uses := "definition-3.1, theorem-3.29") (tags := "section-3-4, fidelity-exact-with-explicit-cardinality-bound")
*The Low-Degree Algorithm.* Let $`k\ge1`, and let $`\mathcal C` be a
concept class such that every
$`f:\{-1,1\}^n\to\{-1,1\}` in $`\mathcal C` has its Fourier spectrum
$`\epsilon/2`-concentrated up to degree $`k`. Then $`\mathcal C` can be
learned using only random examples, with error $`\epsilon` and success
probability at least $`9/10`, in time $`\operatorname{poly}(n^k,1/\epsilon)`.
The output is the sparse Fourier circuit from Theorem 3.29, indexed by
$$`
\mathcal F_k=\{S\subseteq[n]:|S|\le k\},
\qquad
|\mathcal F_k|=\sum_{j=0}^k\binom nj=O(n^k).
`
:::

:::corollary "corollary-3.32" (lean := "FABL.totalInfluenceLearningDegree, FABL.isFourierSpectrumConcentratedUpTo_totalInfluenceLearningDegree, FABL.lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth") (uses := "low-degree-algorithm, proposition-3.2") (tags := "section-3-4, fidelity-exact-with-ceiling-explicit")
*Corollary 3.32.* For $`t\ge1`, let
$$`
\mathcal C=
\{f:\{-1,1\}^n\to\{-1,1\}:\mathbf I[f]\le t\}.
`
Then $`\mathcal C` is learnable from random examples with error $`\epsilon`
and success probability at least $`9/10` in time $`n^{O(t/\epsilon)}`.
The Low-Degree Algorithm uses degree $`k=\lceil2t/\epsilon\rceil`.
:::

:::corollary "corollary-3.33" (lean := "FABL.monotoneLearningDegree, FABL.lowDegreeFourierEstimatorProgram_of_monotone_failure_le_one_tenth") (uses := "corollary-3.32, definition-2.8, theorem-2.33") (tags := "section-3-4, fidelity-exact")
*Corollary 3.33.* Let
$$`
\mathcal C=
\{f:\{-1,1\}^n\to\{-1,1\}:f\text{ is monotone}\}.
`
Then $`\mathcal C` is learnable from random examples with error $`\epsilon`
and success probability at least $`9/10` in time $`n^{O(\sqrt n/\epsilon)}`.
:::

:::corollary "corollary-3.34" (lean := "FABL.noiseSensitivityLearningDegree, FABL.isFourierSpectrumConcentratedUpTo_noiseSensitivityLearningDegree, FABL.lowDegreeFourierEstimatorProgram_of_noiseSensitivity_failure_le_one_tenth") (uses := "low-degree-algorithm, proposition-3.3") (tags := "section-3-4, fidelity-exact-with-ceiling-explicit")
*Corollary 3.34.* For $`\delta\in(0,1/2]`, let
$$`
\mathcal C=
\left\{f:\{-1,1\}^n\to\{-1,1\}:
  \operatorname{NS}_\delta[f]\le\epsilon/6\right\}.
`
Then $`\mathcal C` is learnable from random examples with error $`\epsilon`
and success probability at least $`9/10` in time
$`\operatorname{poly}(n^{1/\delta},1/\epsilon)`.
:::

:::corollary "corollary-3.35" (lean := "FABL.decisionTreeLearningDegree, FABL.lowDegreeFourierEstimatorProgram_of_decisionTree_failure_le_one_tenth") (uses := "definition-3.14, low-degree-algorithm, proposition-3.17") (tags := "section-3-4, fidelity-exact-with-cube-bridge-explicit")
*Corollary 3.35.* Let
$$`
\mathcal C=
\left\{f:\{-1,1\}^n\to\{-1,1\}:
  \operatorname{DTsize}(f)\le s\right\}.
`
Then $`\mathcal C` is learnable from random examples with error $`\epsilon`
and success probability at least $`9/10` in time $`n^{O(\log(s/\epsilon))}`.
:::

:::theorem "theorem-3.36" (lean := "FABL.finiteFamilyCoefficientFailureBits_eq, FABL.exactDegreeSamplesPerCoefficient, FABL.exactDegreeFourierEstimatorLabeledOutput, FABL.exactDegreeFourierEstimatorProgram, FABL.runWithCost_exactDegreeFourierEstimatorProgram, FABL.exactDegreeFourierEstimatorProgram_cost_eq, FABL.exactDegreeSamplesPerCoefficient_cast_le, FABL.measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth, FABL.exactDegreeFourierEstimatorProgram_failureProbability_le_one_tenth, FABL.fourierDegree_toReal_le_depth_of_decisionTree, FABL.exactDegreeFourierEstimatorProgram_of_decisionTree_failureProbability_le_one_tenth") (uses := "definition-3.13, definition-3.27, support-exercise-3.36") (tags := "section-3-4, fidelity-exact-with-explicit-scheduler-bound")
*Theorem 3.36.* Let $`k\ge1`, and let
$$`
\mathcal C=
\{f:\{-1,1\}^n\to\{-1,1\}:\deg(f)\le k\}.
`
Then $`\mathcal C` is learnable from random examples with error $`0` and
success probability at least $`9/10` in time
$`n^k\operatorname{poly}(n,2^k)`.
In particular, this class contains all functions computed by decision trees
of depth at most $`k`. The learner outputs a finite sparse Fourier circuit
which computes the target exactly on every input.

Using a positive rational accuracy schedule, let $`m_{n,k}` be the number of
samples per coefficient. The exact pathwise cost is
$$`
\left(
  |\mathcal F_k|m_{n,k},\ 0,\
  |\mathcal F_k|m_{n,k}+|\mathcal F_k|m_{n,k}(n+1)
\right)
`
and the explicit bound
$$`
m_{n,k}\le
\frac{4\,\operatorname{clog}_2(20|\mathcal F_k|)}
     {(2^{-(k+1)})^2}.
`
Together with $`|\mathcal F_k|=O(n^k)`, this is the displayed
$`n^k\operatorname{poly}(n,2^k)` running-time bound.
:::

:::lemma_ "support-exercise-3.36" (lean := "FABL.degreeFourierGranularity, FABL.degreeFourierGranularity_pos, FABL.degreeFourierGranularity_cast, FABL.roundToDegreeFourierGranularity, FABL.roundToDegreeFourierGranularity_eq_of_close, FABL.degreeFourierCoefficientAccuracy, FABL.degreeFourierCoefficientAccuracy_value, FABL.finiteFamilyCoefficientBadSetWithParameters, FABL.measure_finiteFamilyCoefficientBadSetWithParameters_le, FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth, FABL.exactDegreeFourierEstimatorOutput, FABL.exactDegreeFourierEstimatorOutput_coefficient_cast_eq, FABL.exactDegreeFourierEstimatorOutput_realValue_eq, FABL.exactDegreeFourierEstimatorOutput_evaluate_eq") (uses := "low-degree-algorithm, proposition-3.30, theorem-3.29, support-exercise-1.11b-granularity, theorem-1.1") (tags := "section-3-4, support, fidelity-exact")
*Exercise 3.36.* Prove the exact-learning assertion of Theorem 3.36: for
$`k\ge1`, the class of Boolean functions of degree at most $`k` is learnable
from random examples with error $`0`, success probability at least $`9/10`,
and running time $`n^k\operatorname{poly}(n,2^k)`.
The required exact-recovery guarantee uses the following assertion from
Exercise 1.11: if a Boolean function has degree at most $`k`, each of its
Fourier coefficients is an integer multiple of $`2^{1-k}`. Thus simultaneous
estimates of all degree-at-most-$`k` coefficients to strictly less than half
this spacing can be rounded to their unique exact values; their Fourier
expansion then gives a sparse circuit computing $`f` exactly. The learner
uses at most $`\sum_{j=0}^k\binom nj=O(n^k)` coefficient estimations, with
the individual confidence budgets chosen so that all roundings are correct
with probability at least $`9/10`.
:::
