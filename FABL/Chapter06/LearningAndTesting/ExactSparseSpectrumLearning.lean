/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.SparseSpectrum
public import FABL.Chapter05.SmallLowDegreeWeightPTF
public import FABL.Chapter06.LearningAndTesting.DeterministicGoldreichLevin

/-!
# Exact deterministic learning of sparse Fourier spectra

Book items: O'Donnell, Exercise 3.37(c) and Theorem 6.43.

The learner reuses the Chapter 3 Goldreich--Levin prefix controller and the deterministic
Chapter 6 restricted-weight and small-bias estimators.  Exercise 3.32 supplies the Fourier
lattice: every nonzero coefficient of a Boolean function with spectrum size at most
`2^(k+1)` has magnitude at least the lattice spacing.  The controller therefore lists the
whole support, and the final rational estimates can be rounded to the exact coefficients.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Concrete finite parameters -/

/-- The explicit representative of the book's `2^{O(k)}` spectral-sparsity bound. -/
def exactSparseSpectrumSparsityBound (k : ℕ) : ℕ :=
  2 ^ (k + 1)

/-- The advertised sparsity bound is always large enough for Exercise 3.32's strengthened
granularity theorem. -/
theorem exactSparseSpectrumSparsityBound_two_le (k : ℕ) :
    2 ≤ exactSparseSpectrumSparsityBound k := by
  have hpow : 0 < 2 ^ k := pow_pos (by omega) k
  simp only [exactSparseSpectrumSparsityBound, pow_succ]
  omega

/-- The finite accuracy input encodes one quarter of the Fourier lattice spacing. -/
abbrev exactSparseSpectrumAccuracyInput (n k : ℕ) (hn : 0 < n) : SmallBiasInput where
  n := n
  numerator := 1
  denominator := 4 * 2 ^ k
  n_pos := hn
  numerator_pos := by norm_num
  twice_numerator_le_denominator := by
    have hpow : 0 < 2 ^ k := pow_pos (by omega) k
    omega

/-- The deterministic Goldreich--Levin input used by the exact learner. -/
noncomputable abbrev exactSparseSpectrumGoldreichLevinInput
    (n k : ℕ) (hn : 0 < n) : DeterministicGoldreichLevinInput where
  accuracy := exactSparseSpectrumAccuracyInput n k hn
  fourierBound := exactSparseSpectrumSparsityBound k
  fourierBound_pos := (by
    exact (show 1 ≤ 2 by omega).trans
      (exactSparseSpectrumSparsityBound_two_le k))

/-- The concrete learning parameter is exactly the coefficient-rounding accuracy for the
`(k+1)`st Fourier lattice. -/
theorem exactSparseSpectrumGoldreichLevinInput_learningParameter
    (n k : ℕ) (hn : 0 < n) :
    (exactSparseSpectrumGoldreichLevinInput n k hn).learningParameter =
      degreeFourierCoefficientAccuracy (k + 1) := by
  apply Subtype.ext
  have hleft :
      (exactSparseSpectrumGoldreichLevinInput n k hn).learningParameter.1 =
        (1 : ℚ) / (4 * 2 ^ k) := by
    apply Rat.cast_injective (α := ℝ)
    rw [(exactSparseSpectrumGoldreichLevinInput n k hn).learningParameter_cast]
    norm_num [SmallBiasInput.epsilon]
  rw [hleft, degreeFourierCoefficientAccuracy_value]
  rw [show k + 1 + 1 = k + 2 by omega, pow_add, inv_pow]
  field_simp
  norm_num

/-- For the chosen power-of-two sparsity bound, Exercise 3.32's spacing is the
degree-`k+1` spacing. -/
theorem spectralSparsityGranularity_exactSparseSpectrumSparsityBound (k : ℕ) :
    spectralSparsityGranularity (exactSparseSpectrumSparsityBound k) =
      degreeFourierGranularity (k + 1) := by
  simp [spectralSparsityGranularity, exactSparseSpectrumSparsityBound,
    Nat.log_pow (by norm_num : 1 < 2)]

/-- The list threshold is no larger than the Fourier lattice spacing. -/
theorem exactSparseSpectrumGoldreichLevinInput_threshold_le_granularity
    (n k : ℕ) (hn : 0 < n) :
    (((exactSparseSpectrumGoldreichLevinInput n k hn).threshold.1 : ℚ) : ℝ) ≤
      (degreeFourierGranularity (k + 1) : ℝ) := by
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  have hparameter : input.learningParameter =
      degreeFourierCoefficientAccuracy (k + 1) := by
    simpa [input] using
      exactSparseSpectrumGoldreichLevinInput_learningParameter n k hn
  have hgranularity : (0 : ℝ) <
      (degreeFourierGranularity (k + 1) : ℝ) := by
    exact_mod_cast degreeFourierGranularity_pos (k + 1)
  have hfamily : (1 : ℝ) ≤ 4 * input.familySizeBound := by
    have hpositive : 1 ≤ input.familySizeBound := input.familySizeBound_pos
    exact_mod_cast (show 1 ≤ 4 * input.familySizeBound by omega)
  rw [show (exactSparseSpectrumGoldreichLevinInput n k hn).threshold =
      input.threshold by rfl, input.threshold_cast, hparameter]
  have haccuracy :
      (((degreeFourierCoefficientAccuracy (k + 1)).1 : ℚ) : ℝ) =
        (degreeFourierGranularity (k + 1) : ℝ) / 4 := by
    norm_num [degreeFourierCoefficientAccuracy]
  rw [haccuracy]
  calc
    (degreeFourierGranularity (k + 1) : ℝ) / 4 /
          (4 * input.familySizeBound) ≤
        (degreeFourierGranularity (k + 1) : ℝ) / 4 / 1 := by
      gcongr
    _ ≤ (degreeFourierGranularity (k + 1) : ℝ) := by
      nlinarith

/-- The final deterministic coefficient estimate is strictly inside half a lattice spacing. -/
theorem exactSparseSpectrumGoldreichLevinInput_coefficientEpsilon_lt_half_granularity
    (n k : ℕ) (hn : 0 < n) :
    (exactSparseSpectrumGoldreichLevinInput n k hn).coefficientInput.epsilon <
      (degreeFourierGranularity (k + 1) : ℝ) / 2 := by
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  have hparameter : input.learningParameter =
      degreeFourierCoefficientAccuracy (k + 1) := by
    simpa [input] using
      exactSparseSpectrumGoldreichLevinInput_learningParameter n k hn
  have hgranularity : (0 : ℝ) <
      (degreeFourierGranularity (k + 1) : ℝ) := by
    exact_mod_cast degreeFourierGranularity_pos (k + 1)
  have hcap : (2 : ℝ) ≤
      2 * goldreichLevinActiveCap input.threshold := by
    exact_mod_cast (Nat.mul_le_mul_left 2
      (goldreichLevinActiveCap_pos input.threshold))
  rw [show (exactSparseSpectrumGoldreichLevinInput n k hn).coefficientInput =
      input.coefficientInput by rfl, input.coefficientInput_epsilon, hparameter]
  have haccuracy :
      (((degreeFourierCoefficientAccuracy (k + 1)).1 : ℚ) : ℝ) =
        (degreeFourierGranularity (k + 1) : ℝ) / 4 := by
    norm_num [degreeFourierCoefficientAccuracy]
  rw [haccuracy]
  calc
    (degreeFourierGranularity (k + 1) : ℝ) / 4 /
          (2 * goldreichLevinActiveCap input.threshold) ≤
        (degreeFourierGranularity (k + 1) : ℝ) / 4 / 2 := by
      gcongr
    _ < (degreeFourierGranularity (k + 1) : ℝ) / 2 := by
      nlinarith

/-! ## Sparsity consequences -/

/-- The vector-indexed sparsity promise gives the integral Fourier `1`-norm promise required by
the reused deterministic Goldreich--Levin learner. -/
theorem fourierOneNorm_toReal_le_of_spectralSparsity_le
    (target : BooleanFunction n) (S : ℕ)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤ S) :
    fourierOneNorm target.toReal ≤ S := by
  classical
  let f : 𝔽₂^[n] → ℝ := fun x ↦
    signValue (target (binaryCubeSignEquiv n x))
  have hparseval :
      ∑ gamma, vectorFourierCoeff f gamma ^ 2 = 1 := by
    simpa [f] using sum_sq_vectorFourierCoeff_signValue_eq_one
      (fun x : 𝔽₂^[n] ↦ target (binaryCubeSignEquiv n x))
  have hcoefficient (gamma : 𝔽₂^[n]) :
      |vectorFourierCoeff f gamma| ≤ 1 := by
    have hterm : vectorFourierCoeff f gamma ^ 2 ≤
        ∑ eta, vectorFourierCoeff f eta ^ 2 := by
      exact Finset.single_le_sum
        (fun eta _ ↦ sq_nonneg (vectorFourierCoeff f eta))
        (Finset.mem_univ gamma)
    rw [hparseval] at hterm
    have habsSq : |vectorFourierCoeff f gamma| ^ 2 ≤ 1 := by
      simpa [sq_abs] using hterm
    nlinarith [abs_nonneg (vectorFourierCoeff f gamma)]
  have hsupportSum :
      (∑ gamma, |vectorFourierCoeff f gamma|) =
        ∑ gamma ∈ vectorFourierSupport f, |vectorFourierCoeff f gamma| := by
    rw [vectorFourierSupport]
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro gamma _
    by_cases hzero : vectorFourierCoeff f gamma = 0 <;> simp [hzero]
  have honeNorm : fourierOneNorm target.toReal =
      ∑ gamma, |vectorFourierCoeff f gamma| := by
    rw [fourierOneNorm_eq_spectralPNorm_one, spectralPNorm_one_eq_sum_abs]
    rfl
  have hsparsity' : spectralSparsity f ≤ S := by
    simpa [f] using hsparsity
  rw [honeNorm, hsupportSum]
  calc
    (∑ gamma ∈ vectorFourierSupport f, |vectorFourierCoeff f gamma|) ≤
        ∑ _gamma ∈ vectorFourierSupport f, (1 : ℝ) := by
      exact Finset.sum_le_sum fun gamma _ ↦ hcoefficient gamma
    _ = ((vectorFourierSupport f).card : ℝ) := by simp
    _ = (spectralSparsity f : ℝ) := by
      rw [spectralSparsity_eq_card_vectorFourierSupport]
    _ ≤ (S : ℝ) := by
      exact_mod_cast hsparsity'

/-- Exercise 3.32 specialized to the exact learner's power-of-two bound and transported back to
the sign cube. -/
theorem isFourierGranular_toReal_of_exactSparseSpectrumSparsity
    (target : BooleanFunction n) (k : ℕ)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k) :
    IsFourierGranular target.toReal
      (degreeFourierGranularity (k + 1) : ℝ) := by
  have hgranular := isVectorFourierGranular_signValue_of_spectralSparsity_le
    (fun x : 𝔽₂^[n] ↦ target (binaryCubeSignEquiv n x))
    (exactSparseSpectrumSparsityBound_two_le k) hsparsity
  unfold IsVectorFourierGranular at hgranular
  rw [spectralSparsityGranularity_exactSparseSpectrumSparsityBound] at hgranular
  have hbridge :
      binaryFunctionOnSignCube (fun x : 𝔽₂^[n] ↦
        signValue (target (binaryCubeSignEquiv n x))) = target.toReal := by
    funext x
    simp [binaryFunctionOnSignCube, BooleanFunction.toReal]
  rwa [hbridge] at hgranular

/-- Every nonzero coefficient under the sparsity promise has magnitude at least one lattice
spacing. -/
theorem degreeFourierGranularity_le_abs_fourierCoeff_of_exactSparseSpectrum
    (target : BooleanFunction n) (k : ℕ)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k)
    (U : Finset (Fin n)) (hU : fourierCoeff target.toReal U ≠ 0) :
    (degreeFourierGranularity (k + 1) : ℝ) ≤
      |fourierCoeff target.toReal U| := by
  obtain ⟨z, hz⟩ :=
    isFourierGranular_toReal_of_exactSparseSpectrumSparsity target k hsparsity U
  have hzNe : z ≠ 0 := by
    intro hzero
    apply hU
    rw [hz, hzero]
    norm_num
  have honeAbs : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hzNe
  have hgranularity : (0 : ℝ) ≤
      (degreeFourierGranularity (k + 1) : ℝ) := by
    exact_mod_cast (degreeFourierGranularity_pos (k + 1)).le
  rw [hz, abs_mul, abs_of_nonneg hgranularity]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right honeAbs hgranularity

/-! ## Exact lattice rounding -/

/-- Round every coefficient of a sparse rational hypothesis to the exact sparsity lattice. -/
def roundSparseSpectrumHypothesis (k : ℕ) (hypothesis : SparseFourierHypothesis n) :
    SparseFourierHypothesis n :=
  SparseFourierHypothesis.ofCoefficients hypothesis.support fun U ↦
    roundToDegreeFourierGranularity (k + 1) (hypothesis.coefficient U)

@[simp] theorem roundSparseSpectrumHypothesis_support
    (k : ℕ) (hypothesis : SparseFourierHypothesis n) :
    (roundSparseSpectrumHypothesis k hypothesis).support = hypothesis.support :=
  rfl

@[simp] theorem roundSparseSpectrumHypothesis_coefficient
    (k : ℕ) (hypothesis : SparseFourierHypothesis n)
    (U : hypothesis.support) :
    (roundSparseSpectrumHypothesis k hypothesis).coefficient U =
      roundToDegreeFourierGranularity (k + 1) (hypothesis.coefficient U) :=
  rfl

/-- Every coefficient returned by the deterministic final batch rounds to its exact Fourier
coefficient, including zero coefficients admitted as list false positives. -/
theorem roundedDeterministicGoldreichLevinHypothesis_coefficient_cast_eq
    (k : ℕ) (hn : 0 < n) (target : BooleanFunction n)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k)
    (family : Finset (Finset (Fin n))) (U : family) :
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    let answers := fun i ↦ target (binaryCubeSignEquiv n
      (input.coefficientInput.sample i))
    (((roundSparseSpectrumHypothesis k
        (deterministicGoldreichLevinHypothesisFromAnswers
          input family answers)).coefficient U : ℚ) : ℝ) =
      fourierCoeff target.toReal U.1 := by
  dsimp only
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  have hnorm : fourierOneNorm target.toReal ≤ input.fourierBound := by
    simpa [input, exactSparseSpectrumGoldreichLevinInput] using
      fourierOneNorm_toReal_le_of_spectralSparsity_le target
        (exactSparseSpectrumSparsityBound k) hsparsity
  obtain ⟨z, hz⟩ :=
    isFourierGranular_toReal_of_exactSparseSpectrumSparsity target k hsparsity U.1
  have hestimate :=
    abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le
      input.coefficientInput target.toReal U.1 hnorm
  have hcast := rationalSmallBiasFourierEstimate_cast
    input.coefficientInput target U.1
  have hcast' :
      (rationalSmallBiasFourierEstimate input.coefficientInput U.1
          (fun i ↦ target (binaryCubeSignEquiv n
            (input.coefficientInput.sample i))) : ℝ) =
        smallBiasFourierEstimate target.toReal
          input.coefficientInput.sample U.1 := by
    convert hcast using 1
  have hclose :
      |(rationalSmallBiasFourierEstimate input.coefficientInput U.1
          (fun i ↦ target (binaryCubeSignEquiv n
            (input.coefficientInput.sample i))) : ℝ) -
          (z : ℝ) * (degreeFourierGranularity (k + 1) : ℝ)| <
        (degreeFourierGranularity (k + 1) : ℝ) / 2 := by
    rw [hcast', ← hz]
    exact hestimate.trans_lt (by
      simpa [input] using
        exactSparseSpectrumGoldreichLevinInput_coefficientEpsilon_lt_half_granularity
          n k hn)
  have hround := roundToDegreeFourierGranularity_eq_of_close (k + 1)
    (rationalSmallBiasFourierEstimate input.coefficientInput U.1
      (fun i ↦ target (binaryCubeSignEquiv n
        (input.coefficientInput.sample i)))) z hclose
  change
    (roundToDegreeFourierGranularity (k + 1)
      (rationalSmallBiasFourierEstimate input.coefficientInput U.1
        (fun i ↦ target (binaryCubeSignEquiv n
          (input.coefficientInput.sample i)))) : ℝ) = _
  rw [hround]
  norm_num only [Rat.cast_mul, Rat.cast_intCast]
  exact hz.symm

/-- A complete Goldreich--Levin family and exact rounded coefficients reconstruct the target's
real Fourier expansion. -/
theorem roundedDeterministicGoldreichLevinHypothesis_realValue_eq
    (k : ℕ) (hn : 0 < n) (target : BooleanFunction n)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k)
    (family : Finset (Finset (Fin n)))
    (hcomplete : ∀ U : Finset (Fin n),
      (((exactSparseSpectrumGoldreichLevinInput n k hn).threshold.1 : ℚ) : ℝ) ≤
          |fourierCoeff target.toReal U| → U ∈ family) :
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    let answers := fun i ↦ target (binaryCubeSignEquiv n
      (input.coefficientInput.sample i))
    (roundSparseSpectrumHypothesis k
      (deterministicGoldreichLevinHypothesisFromAnswers
        input family answers)).realValue = target.toReal := by
  dsimp only
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  let answers := fun i ↦ target (binaryCubeSignEquiv n
    (input.coefficientInput.sample i))
  have hsupport : ∀ U : Finset (Fin n),
      fourierCoeff target.toReal U ≠ 0 → U ∈ family := by
    intro U hU
    apply hcomplete U
    have hthreshold :
        (((exactSparseSpectrumGoldreichLevinInput n k hn).threshold.1 : ℚ) : ℝ) ≤
          (degreeFourierGranularity (k + 1) : ℝ) := by
      simpa [input] using
        exactSparseSpectrumGoldreichLevinInput_threshold_le_granularity n k hn
    exact hthreshold.trans
      (degreeFourierGranularity_le_abs_fourierCoeff_of_exactSparseSpectrum
        target k hsparsity U hU)
  funext x
  change
    (∑ U : family,
      (((roundSparseSpectrumHypothesis k
        (deterministicGoldreichLevinHypothesisFromAnswers
          input family answers)).coefficient U : ℚ) : ℝ) * monomial U.1 x) =
      target.toReal x
  calc
    (∑ U : family,
      (((roundSparseSpectrumHypothesis k
        (deterministicGoldreichLevinHypothesisFromAnswers
          input family answers)).coefficient U : ℚ) : ℝ) * monomial U.1 x) =
        ∑ U : family, fourierCoeff target.toReal U.1 * monomial U.1 x := by
      apply Finset.sum_congr rfl
      intro U _
      rw [roundedDeterministicGoldreichLevinHypothesis_coefficient_cast_eq
        k hn target hsparsity family U]
    _ = ∑ U ∈ family, fourierCoeff target.toReal U * monomial U x := by
      symm
      exact Finset.sum_subtype family (fun U ↦ Iff.rfl)
        (fun U ↦ fourierCoeff target.toReal U * monomial U x)
    _ = ∑ U : Finset (Fin n),
        fourierCoeff target.toReal U * monomial U x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro U _ hU
      have hzero : fourierCoeff target.toReal U = 0 := by
        by_contra hne
        exact hU (hsupport U hne)
      rw [hzero, zero_mul]
    _ = target.toReal x := (fourier_expansion target.toReal x).symm

/-- Exact real reconstruction yields the original Boolean function pointwise. -/
theorem roundedDeterministicGoldreichLevinHypothesis_evaluate_eq
    (k : ℕ) (hn : 0 < n) (target : BooleanFunction n)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k)
    (family : Finset (Finset (Fin n)))
    (hcomplete : ∀ U : Finset (Fin n),
      (((exactSparseSpectrumGoldreichLevinInput n k hn).threshold.1 : ℚ) : ℝ) ≤
          |fourierCoeff target.toReal U| → U ∈ family) :
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    let answers := fun i ↦ target (binaryCubeSignEquiv n
      (input.coefficientInput.sample i))
    (roundSparseSpectrumHypothesis k
      (deterministicGoldreichLevinHypothesisFromAnswers
        input family answers)).evaluate = target := by
  dsimp only
  rw [SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue,
    roundedDeterministicGoldreichLevinHypothesis_realValue_eq
      k hn target hsparsity family hcomplete]
  funext x
  apply signValue_injective
  rcases signValue_eq_neg_one_or_one (target x) with h | h <;>
    simp [BooleanFunction.toReal, h]

/-! ## Deterministic query program -/

/-- Mapping a deterministic query output preserves its exact path cost. -/
theorem DeterministicQueryProgram.runWithCost_map
    {Query Answer Output Result : Type*}
    (oracle : Query → Answer) (f : Output → Result)
    (program : DeterministicQueryProgram Query Answer Output) :
    DeterministicQueryProgram.runWithCost oracle (program.map f) =
      (f (DeterministicQueryProgram.runWithCost oracle program).1,
        (DeterministicQueryProgram.runWithCost oracle program).2) := by
  unfold DeterministicQueryProgram.map
  rw [DeterministicQueryProgram.runWithCost_bind]
  simp [DeterministicQueryProgram.runWithCost]

/-- Conservative local work for rounding the final capped coefficient family. -/
noncomputable def exactSparseSpectrumRoundingWork
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  goldreichLevinActiveCap input.threshold

/-- Positive-dimensional exact sparse-spectrum learner.  The final tick charges one rounding
operation for every slot in the controller's target-independent active-family cap. -/
noncomputable def positiveExactSparseSpectrumLearner
    (n k : ℕ) (hn : 0 < n) :
    DeterministicQueryProgram {−1,1}^[n] Sign (SparseFourierHypothesis n) :=
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  .tick (exactSparseSpectrumRoundingWork input)
    ((deterministicGoldreichLevinLearner input).map
      (roundSparseSpectrumHypothesis k))

/-- The positive-dimensional deterministic query program reconstructs every target satisfying
the advertised sparsity promise exactly. -/
theorem positiveExactSparseSpectrumLearner_evaluate_eq
    (k : ℕ) (hn : 0 < n) (target : BooleanFunction n)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k) :
    (DeterministicQueryProgram.runWithCost target
      (positiveExactSparseSpectrumLearner n k hn)).1.evaluate = target := by
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  have hnorm : fourierOneNorm target.toReal ≤ input.fourierBound := by
    simpa [input, exactSparseSpectrumGoldreichLevinInput] using
      fourierOneNorm_toReal_le_of_spectralSparsity_le target
        (exactSparseSpectrumSparsityBound k) hsparsity
  have hcorrect := deterministicGoldreichLevinProgram_isCorrectOutput
    input target hnorm
  obtain ⟨family, hactive, hcomplete, _hsound, hcap, _hcard⟩ := hcorrect
  dsimp only [input] at hactive hcomplete hcap
  have hsource :
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).1 =
      deterministicGoldreichLevinHypothesisFromAnswers input family
        (fun i ↦ target (binaryCubeSignEquiv input.accuracy.n
          (input.coefficientInput.sample i))) := by
    dsimp only [input] at ⊢
    rw [deterministicGoldreichLevinLearner,
      DeterministicQueryProgram.runWithCost_bind]
    change
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinSecondStage
          (exactSparseSpectrumGoldreichLevinInput n k hn)
          (DeterministicQueryProgram.runWithCost target
            (deterministicGoldreichLevinProgram
              (exactSparseSpectrumGoldreichLevinInput n k hn))).1)).1 = _
    simp only [deterministicGoldreichLevinSecondStage, hactive]
    rw [if_pos hcap]
    simpa only using congrArg Prod.fst
      (DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram
        (exactSparseSpectrumGoldreichLevinInput n k hn) target family)
  have hmap :
      DeterministicQueryProgram.runWithCost target
          ((deterministicGoldreichLevinLearner input).map
            (roundSparseSpectrumHypothesis k)) =
        (roundSparseSpectrumHypothesis k
            (DeterministicQueryProgram.runWithCost target
              (deterministicGoldreichLevinLearner input)).1,
          (DeterministicQueryProgram.runWithCost target
            (deterministicGoldreichLevinLearner input)).2) := by
    simpa only [input] using
      DeterministicQueryProgram.runWithCost_map target
        (roundSparseSpectrumHypothesis k)
        (deterministicGoldreichLevinLearner
          (exactSparseSpectrumGoldreichLevinInput n k hn))
  rw [positiveExactSparseSpectrumLearner,
    DeterministicQueryProgram.runWithCost, hmap, hsource]
  exact roundedDeterministicGoldreichLevinHypothesis_evaluate_eq
    k hn target hsparsity family (by simpa only [input] using hcomplete)

/-- A one-term rational Fourier hypothesis for a constant sign. -/
def constantSparseFourierHypothesis (n : ℕ) (value : Sign) :
    SparseFourierHypothesis n :=
  SparseFourierHypothesis.ofCoefficients {∅} fun _ ↦
    (((value : Sign) : ℤ) : ℚ)

/-- The one-term hypothesis evaluates to its defining constant. -/
theorem constantSparseFourierHypothesis_evaluate
    (n : ℕ) (value : Sign) :
    (constantSparseFourierHypothesis n value).evaluate = fun _ ↦ value := by
  rw [SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue]
  funext x
  change thresholdSign
      (∑ _U : ({∅} : Finset (Finset (Fin n))),
        ((((value : Sign) : ℤ) : ℚ) : ℝ) * monomial _U.1 x) = value
  have hindex : ∀ U : ({∅} : Finset (Finset (Fin n))), U.1 = ∅ := by
    intro U
    have hmem : (U : Finset (Fin n)) ∈ ({∅} : Finset (Finset (Fin n))) := U.2
    simpa only [Finset.mem_singleton] using hmem
  simp_rw [hindex]
  have hmonomial : monomial (∅ : Finset (Fin n)) x = 1 := by
    simp [monomial]
  rw [hmonomial]
  rcases Int.units_eq_one_or value with rfl | rfl <;> simp [thresholdSign]

/-- The zero-dimensional cube is learned by its unique membership query. -/
def zeroDimensionExactSparseSpectrumLearner (n : ℕ) :
    DeterministicQueryProgram {−1,1}^[n] Sign (SparseFourierHypothesis n) :=
  .queryBatch 1 (fun _ ↦ allOneSignCube n) fun answers ↦
    .pure (constantSparseFourierHypothesis n (answers 0))

/-- Exact output and visible cost of the zero-dimensional edge program. -/
theorem runWithCost_zeroDimensionExactSparseSpectrumLearner
    (target : BooleanFunction n) :
    DeterministicQueryProgram.runWithCost target
        (zeroDimensionExactSparseSpectrumLearner n) =
      (constantSparseFourierHypothesis n (target (allOneSignCube n)),
        DeterministicQueryProgram.queryBatchCost 1) := by
  rfl

/-- The edge program is exact whenever the input dimension is zero. -/
theorem zeroDimensionExactSparseSpectrumLearner_evaluate_eq
    (target : BooleanFunction n) (hn : ¬ 0 < n) :
    (DeterministicQueryProgram.runWithCost target
      (zeroDimensionExactSparseSpectrumLearner n)).1.evaluate = target := by
  rw [runWithCost_zeroDimensionExactSparseSpectrumLearner,
    constantSparseFourierHypothesis_evaluate]
  have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  funext x
  congr 1
  exact Subsingleton.elim _ _

/-- O'Donnell's exact sparse-spectrum learner, including the zero-dimensional cube. -/
noncomputable def exactSparseSpectrumLearner (n k : ℕ) :
    DeterministicQueryProgram {−1,1}^[n] Sign (SparseFourierHypothesis n) :=
  if hn : 0 < n then positiveExactSparseSpectrumLearner n k hn
  else zeroDimensionExactSparseSpectrumLearner n

/-- Every promised target is reconstructed exactly, with no probabilistic failure event. -/
theorem exactSparseSpectrumLearner_evaluate_eq
    (target : BooleanFunction n) (k : ℕ)
    (hsparsity : spectralSparsity (fun x : 𝔽₂^[n] ↦
      signValue (target (binaryCubeSignEquiv n x))) ≤
        exactSparseSpectrumSparsityBound k) :
    (DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).1.evaluate = target := by
  by_cases hn : 0 < n
  · rw [exactSparseSpectrumLearner, dif_pos hn]
    exact positiveExactSparseSpectrumLearner_evaluate_eq k hn target hsparsity
  · rw [exactSparseSpectrumLearner, dif_neg hn]
    exact zeroDimensionExactSparseSpectrumLearner_evaluate_eq target hn

/-- Chapter 3 membership-query presentation of the exact deterministic program. -/
noncomputable def exactSparseSpectrumLearningProgram
    (n k : ℕ) : LearningProgram n .queries (SparseFourierHypothesis n) :=
  DeterministicQueryProgram.toLearningProgram
    (exactSparseSpectrumLearner n k)

/-- The query-model adapter preserves the unique deterministic output and its exact cost. -/
theorem runWithCost_exactSparseSpectrumLearningProgram
    (target : BooleanFunction n) (k : ℕ) :
    LearningProgram.runWithCost target (exactSparseSpectrumLearningProgram n k) =
      PMF.pure (DeterministicQueryProgram.runWithCost target
        (exactSparseSpectrumLearner n k)) := by
  exact DeterministicQueryProgram.runWithCost_toLearningProgram target _

/-! ## Resource ledger and polynomial bound -/

/-- Target-independent membership-query budget of the exact learner. -/
noncomputable def exactSparseSpectrumQueryBudget (n k : ℕ) : ℕ :=
  if hn : 0 < n then
    deterministicGoldreichLevinQueryBudget
      (exactSparseSpectrumGoldreichLevinInput n k hn)
  else 1

/-- Target-independent charged-work budget of the exact learner. -/
noncomputable def exactSparseSpectrumWorkBudget (n k : ℕ) : ℕ :=
  if hn : 0 < n then
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    exactSparseSpectrumRoundingWork input +
      deterministicGoldreichLevinWorkBudget input
  else 1

/-- Every target, promised or not, follows a path within the advertised exact-learner budgets. -/
theorem exactSparseSpectrumLearner_resource_bounds
    (target : BooleanFunction n) (k : ℕ) :
    (DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).2.randomExamples = 0 ∧
    (DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).2.queries ≤
        exactSparseSpectrumQueryBudget n k ∧
    (DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).2.work ≤
        exactSparseSpectrumWorkBudget n k := by
  by_cases hn : 0 < n
  · let input := exactSparseSpectrumGoldreichLevinInput n k hn
    have hsource :=
      deterministicGoldreichLevinLearner_resource_bounds
        (exactSparseSpectrumGoldreichLevinInput n k hn) target
    change
        (DeterministicQueryProgram.runWithCost target
          (deterministicGoldreichLevinLearner input)).2.randomExamples = 0 ∧
        (DeterministicQueryProgram.runWithCost target
          (deterministicGoldreichLevinLearner input)).2.queries ≤
            deterministicGoldreichLevinQueryBudget input ∧
        (DeterministicQueryProgram.runWithCost target
          (deterministicGoldreichLevinLearner input)).2.work ≤
            deterministicGoldreichLevinWorkBudget input at hsource
    have hqueryBudget : exactSparseSpectrumQueryBudget n k =
        deterministicGoldreichLevinQueryBudget input := by
      rw [exactSparseSpectrumQueryBudget, dif_pos hn]
    have hworkBudget : exactSparseSpectrumWorkBudget n k =
        exactSparseSpectrumRoundingWork input +
          deterministicGoldreichLevinWorkBudget input := by
      rw [exactSparseSpectrumWorkBudget, dif_pos hn]
    rw [exactSparseSpectrumLearner, dif_pos hn,
      positiveExactSparseSpectrumLearner,
      DeterministicQueryProgram.runWithCost,
      DeterministicQueryProgram.runWithCost_map]
    change
      (0 + (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.randomExamples = 0) ∧
      (0 + (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.queries ≤
          exactSparseSpectrumQueryBudget n k) ∧
      (exactSparseSpectrumRoundingWork input +
          (DeterministicQueryProgram.runWithCost target
            (deterministicGoldreichLevinLearner input)).2.work ≤
        exactSparseSpectrumWorkBudget n k)
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.zero_add]
      exact hsource.1
    · rw [Nat.zero_add, hqueryBudget]
      exact hsource.2.1
    · rw [hworkBudget]
      exact Nat.add_le_add_left hsource.2.2
        (exactSparseSpectrumRoundingWork input)
  · rw [exactSparseSpectrumLearner, dif_neg hn,
      runWithCost_zeroDimensionExactSparseSpectrumLearner]
    simp [exactSparseSpectrumQueryBudget, exactSparseSpectrumWorkBudget, hn,
      DeterministicQueryProgram.queryBatchCost]

/-- Joint polynomial scale in the dimension and `2^k`. -/
noncomputable def exactSparseSpectrumRuntimeScale (n k : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (((2 ^ k + 1 : ℕ) : ℝ) ^ 2)

/-- The reused Goldreich--Levin scale is polynomial in `n` and `2^k`. -/
theorem exactSparseSpectrumGoldreichLevinInput_runtimeScale_le
    (n k : ℕ) (hn : 0 < n) :
    (exactSparseSpectrumGoldreichLevinInput n k hn).runtimeScale ≤
      12 * exactSparseSpectrumRuntimeScale n k := by
  let input := exactSparseSpectrumGoldreichLevinInput n k hn
  let X : ℝ := (2 ^ k : ℕ)
  have hXpos : 0 < X := by
    dsimp [X]
    positivity
  have hbound : (((input.fourierBound + 1 : ℕ) : ℝ)) = 2 * X + 1 := by
    simp [input, exactSparseSpectrumSparsityBound, X, pow_succ] ; ring
  have hepsilon : ((input.learningParameter.1 : ℚ) : ℝ) = 1 / (4 * X) := by
    rw [input.learningParameter_cast]
    simp [input, SmallBiasInput.epsilon, X]
  have hinner : (2 * X + 1) * X ≤ 3 * (X + 1) ^ 2 := by
    nlinarith [sq_nonneg X]
  have hmul :
      4 * ((n : ℝ) + 1) * ((2 * X + 1) * X) ≤
        4 * ((n : ℝ) + 1) * (3 * (X + 1) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  rw [show (exactSparseSpectrumGoldreichLevinInput n k hn).runtimeScale =
      input.runtimeScale by rfl, DeterministicGoldreichLevinInput.runtimeScale]
  change
    (((n + 1 : ℕ) : ℝ) * (((input.fourierBound + 1 : ℕ) : ℝ)) /
        ((input.learningParameter.1 : ℚ) : ℝ)) ≤
      12 * exactSparseSpectrumRuntimeScale n k
  rw [hbound, hepsilon]
  have hrewrite :
      (((n + 1 : ℕ) : ℝ) * (2 * X + 1)) / (1 / (4 * X)) =
        4 * (n + 1) * ((2 * X + 1) * X) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp [hXpos.ne']
  rw [hrewrite]
  calc
    4 * ((n : ℝ) + 1) * ((2 * X + 1) * X) ≤
        4 * ((n : ℝ) + 1) * (3 * (X + 1) ^ 2) := hmul
    _ = 12 * exactSparseSpectrumRuntimeScale n k := by
      simp [exactSparseSpectrumRuntimeScale, X] ; ring

/-- The fixed rounding charge is covered by the reused degree-100 Goldreich--Levin polynomial. -/
theorem exactSparseSpectrumRoundingWork_cast_le_goldreichLevinPolynomialRuntimeBound
    (input : DeterministicGoldreichLevinInput) :
    (exactSparseSpectrumRoundingWork input : ℝ) ≤
      input.polynomialRuntimeBound := by
  let R := input.runtimeScale
  have hR : 1 ≤ R := by
    simpa [R] using input.runtimeScale_factor_bounds.1
  have hcapSucc := input.activeCap_add_one_cast_le_runtimeScale
  have hcap : (exactSparseSpectrumRoundingWork input : ℝ) ≤
      2 ^ 13 * R ^ 8 := by
    calc
      (exactSparseSpectrumRoundingWork input : ℝ) ≤
          ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) := by
        unfold exactSparseSpectrumRoundingWork
        exact_mod_cast Nat.le_succ (goldreichLevinActiveCap input.threshold)
      _ ≤ 2 ^ 13 * input.runtimeScale ^ 8 := hcapSucc
      _ = 2 ^ 13 * R ^ 8 := by rfl
  have hpow : R ^ 8 ≤ R ^ 100 := pow_le_pow_right₀ hR (by omega)
  calc
    (exactSparseSpectrumRoundingWork input : ℝ) ≤
        2 ^ 13 * R ^ 8 := hcap
    _ ≤ 2 ^ 13 * R ^ 100 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 2 ^ 170 * R ^ 100 := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (pow_nonneg (zero_le_one.trans hR) 100)
    _ = input.polynomialRuntimeBound := by
      rfl

/-- One explicit polynomial envelope for both exact-learner resource components. -/
noncomputable def exactSparseSpectrumPolynomialRuntimeBound (n k : ℕ) : ℝ :=
  1 + 2 ^ 171 * (12 * exactSparseSpectrumRuntimeScale n k) ^ 100

/-- The target-independent query budget is polynomial in `n` and `2^k`. -/
theorem exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound (n k : ℕ) :
    (exactSparseSpectrumQueryBudget n k : ℝ) ≤
      exactSparseSpectrumPolynomialRuntimeBound n k := by
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaledNonneg :
      (0 : ℝ) ≤ 12 * exactSparseSpectrumRuntimeScale n k := by
    unfold exactSparseSpectrumRuntimeScale
    positivity
  by_cases hn : 0 < n
  · rw [exactSparseSpectrumQueryBudget, dif_pos hn]
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    have hbase := input.queryBudget_cast_le_polynomialRuntimeBound
    have hscale := exactSparseSpectrumGoldreichLevinInput_runtimeScale_le n k hn
    have hinputNonneg : 0 ≤ input.runtimeScale :=
      zero_le_one.trans input.runtimeScale_factor_bounds.1
    have hpow := pow_le_pow_left₀ hinputNonneg hscale 100
    calc
      (deterministicGoldreichLevinQueryBudget input : ℝ) ≤
          input.polynomialRuntimeBound := hbase
      _ ≤ 2 ^ 171 *
          (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 := by
        unfold DeterministicGoldreichLevinInput.polynomialRuntimeBound
        calc
          2 ^ 170 * input.runtimeScale ^ 100 ≤
              2 ^ 170 * (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ 2 ^ 171 *
              (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 := by
            rw [show (171 : ℕ) = 170 + 1 by omega, pow_succ]
            have hcoefficient : (2 : ℝ) ^ 170 ≤ 2 ^ 170 * 2 := by
              nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 170]
            exact mul_le_mul_of_nonneg_right
              hcoefficient
              (pow_nonneg hscaledNonneg 100)
      _ ≤ exactSparseSpectrumPolynomialRuntimeBound n k := by
        unfold exactSparseSpectrumPolynomialRuntimeBound
        exact le_add_of_nonneg_left zero_le_one
  · rw [exactSparseSpectrumQueryBudget, dif_neg hn]
    unfold exactSparseSpectrumPolynomialRuntimeBound
    have hnonneg : (0 : ℝ) ≤
        2 ^ 171 * (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 :=
      mul_nonneg (pow_nonneg htwoNonneg 171)
        (pow_nonneg hscaledNonneg 100)
    rw [Nat.cast_one]
    exact le_add_of_nonneg_right hnonneg

/-- The target-independent charged-work budget is polynomial in `n` and `2^k`. -/
theorem exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound (n k : ℕ) :
    (exactSparseSpectrumWorkBudget n k : ℝ) ≤
      exactSparseSpectrumPolynomialRuntimeBound n k := by
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaledNonneg :
      (0 : ℝ) ≤ 12 * exactSparseSpectrumRuntimeScale n k := by
    unfold exactSparseSpectrumRuntimeScale
    positivity
  by_cases hn : 0 < n
  · rw [exactSparseSpectrumWorkBudget, dif_pos hn]
    let input := exactSparseSpectrumGoldreichLevinInput n k hn
    have hwork := input.workBudget_cast_le_polynomialRuntimeBound
    have hround :=
      exactSparseSpectrumRoundingWork_cast_le_goldreichLevinPolynomialRuntimeBound input
    have hscale := exactSparseSpectrumGoldreichLevinInput_runtimeScale_le n k hn
    have hinputNonneg : 0 ≤ input.runtimeScale :=
      zero_le_one.trans input.runtimeScale_factor_bounds.1
    have hpow := pow_le_pow_left₀ hinputNonneg hscale 100
    calc
      ((exactSparseSpectrumRoundingWork input +
          deterministicGoldreichLevinWorkBudget input : ℕ) : ℝ) ≤
          input.polynomialRuntimeBound + input.polynomialRuntimeBound := by
        norm_num only [Nat.cast_add]
        exact add_le_add hround hwork
      _ = 2 ^ 171 * input.runtimeScale ^ 100 := by
        unfold DeterministicGoldreichLevinInput.polynomialRuntimeBound
        rw [show (171 : ℕ) = 170 + 1 by omega, pow_succ]
        ring
      _ ≤ 2 ^ 171 *
          (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg htwoNonneg 171)
      _ ≤ exactSparseSpectrumPolynomialRuntimeBound n k := by
        unfold exactSparseSpectrumPolynomialRuntimeBound
        exact le_add_of_nonneg_left zero_le_one
  · rw [exactSparseSpectrumWorkBudget, dif_neg hn]
    unfold exactSparseSpectrumPolynomialRuntimeBound
    have hnonneg : (0 : ℝ) ≤
        2 ^ 171 * (12 * exactSparseSpectrumRuntimeScale n k) ^ 100 :=
      mul_nonneg (pow_nonneg htwoNonneg 171)
        (pow_nonneg hscaledNonneg 100)
    rw [Nat.cast_one]
    exact le_add_of_nonneg_right hnonneg

/-- Actual deterministic membership-query use obeys the explicit polynomial envelope. -/
theorem exactSparseSpectrumLearner_queries_polynomial_le
    (target : BooleanFunction n) (k : ℕ) :
    ((DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).2.queries : ℝ) ≤
        exactSparseSpectrumPolynomialRuntimeBound n k := by
  have hresource := exactSparseSpectrumLearner_resource_bounds target k
  have hcast :
      ((DeterministicQueryProgram.runWithCost target
        (exactSparseSpectrumLearner n k)).2.queries : ℝ) ≤
        (exactSparseSpectrumQueryBudget n k : ℝ) := by
    exact_mod_cast hresource.2.1
  exact hcast.trans
    (exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound n k)

/-- Actual deterministic charged work obeys the explicit polynomial envelope. -/
theorem exactSparseSpectrumLearner_work_polynomial_le
    (target : BooleanFunction n) (k : ℕ) :
    ((DeterministicQueryProgram.runWithCost target
      (exactSparseSpectrumLearner n k)).2.work : ℝ) ≤
        exactSparseSpectrumPolynomialRuntimeBound n k := by
  have hresource := exactSparseSpectrumLearner_resource_bounds target k
  have hcast :
      ((DeterministicQueryProgram.runWithCost target
        (exactSparseSpectrumLearner n k)).2.work : ℝ) ≤
        (exactSparseSpectrumWorkBudget n k : ℝ) := by
    exact_mod_cast hresource.2.2
  exact hcast.trans
    (exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound n k)

/-! ## Definition 3.27 learning algorithm -/

/-- The concept class represented by the explicit `2^(k+1)` member of `2^{O(k)}`. -/
def exactSparseSpectrumConceptClass (n k : ℕ) : Set (BooleanFunction n) :=
  {target | spectralSparsity (fun x : 𝔽₂^[n] ↦
    signValue (target (binaryCubeSignEquiv n x))) ≤
      exactSparseSpectrumSparsityBound k}

/-- Exercise 3.37(c) and Theorem 6.43 as an honest deterministic Definition 3.27 query learner. -/
noncomputable def exactSparseSpectrumLearningAlgorithm (n k : ℕ) :
    LearningAlgorithm n .queries SparseFourierHypothesis.finiteRepresentation where
  program := fun _accuracy ↦ exactSparseSpectrumLearningProgram n k
  successProbability := fun target accuracy ↦
    LearningProgram.eventProbability (exactSparseSpectrumLearningProgram n k) target
      fun outcome ↦ relativeHammingDist target outcome.1.evaluate ≤ (accuracy.1 : ℝ)
  randomExampleCost := fun _ ↦ 0
  queryCost := fun _ ↦ exactSparseSpectrumQueryBudget n k
  workCost := fun _ ↦ exactSparseSpectrumWorkBudget n k
  successProbability_eq := by
    intro target accuracy
    rfl
  cost_le := by
    intro target accuracy outcome houtcome
    change SparseFourierHypothesis n × LearningCost at outcome
    rw [runWithCost_exactSparseSpectrumLearningProgram,
      PMF.mem_support_pure_iff] at houtcome
    subst outcome
    simpa only [Nat.le_zero] using
      exactSparseSpectrumLearner_resource_bounds target k

/-- On every promised target the exact learner's success probability is one, at every requested
accuracy including zero. -/
theorem exactSparseSpectrumLearningAlgorithm_successProbability_eq_one
    (target : BooleanFunction n) (k : ℕ)
    (htarget : target ∈ exactSparseSpectrumConceptClass n k)
    (accuracy : LearningAccuracy) :
    (exactSparseSpectrumLearningAlgorithm n k).successProbability target accuracy = 1 := by
  have hexact := exactSparseSpectrumLearner_evaluate_eq target k (by
    simpa [exactSparseSpectrumConceptClass] using htarget)
  change LearningProgram.eventProbability
      (exactSparseSpectrumLearningProgram n k) target
      (fun outcome ↦ relativeHammingDist target outcome.1.evaluate ≤
        (accuracy.1 : ℝ)) = 1
  unfold LearningProgram.eventProbability
  rw [runWithCost_exactSparseSpectrumLearningProgram,
    PMF.toOuterMeasure_pure_apply]
  have haccuracy : (0 : ℝ) ≤ (accuracy.1 : ℝ) := by
    exact_mod_cast accuracy.2.1
  simp [hexact, relativeHammingDist, haccuracy]

/-- The concrete deterministic algorithm learns the sparse-spectrum class exactly. -/
theorem exactSparseSpectrumLearningAlgorithm_learns
    (n k : ℕ) (accuracy : LearningAccuracy) :
    LearnsConceptClassWithError (exactSparseSpectrumLearningAlgorithm n k)
      (exactSparseSpectrumConceptClass n k) accuracy := by
  intro target htarget
  rw [exactSparseSpectrumLearningAlgorithm_successProbability_eq_one
    target k htarget accuracy]
  norm_num

/-- Book-facing zero-error statement: the unique output hypothesis equals the target, not merely
an approximation to it. -/
theorem exactSparseSpectrumLearningProgram_zero_error
    (target : BooleanFunction n) (k : ℕ)
    (htarget : target ∈ exactSparseSpectrumConceptClass n k)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (exactSparseSpectrumLearningProgram n k)).support) :
    outcome.1.evaluate = target ∧
      relativeHammingDist target outcome.1.evaluate = 0 := by
  rw [runWithCost_exactSparseSpectrumLearningProgram,
    PMF.mem_support_pure_iff] at houtcome
  subst outcome
  have hexact := exactSparseSpectrumLearner_evaluate_eq target k (by
    simpa [exactSparseSpectrumConceptClass] using htarget)
  exact ⟨hexact, by simp [hexact, relativeHammingDist]⟩

/-- O'Donnell, Exercise 3.37(c) and Theorem 6.43: every execution has zero error, consumes no
random examples, and has query and charged-work costs polynomial in `n` and `2^k`. -/
theorem exactSparseSpectrumLearningProgram_spec
    (target : BooleanFunction n) (k : ℕ)
    (htarget : target ∈ exactSparseSpectrumConceptClass n k)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (exactSparseSpectrumLearningProgram n k)).support) :
    outcome.1.evaluate = target ∧
      relativeHammingDist target outcome.1.evaluate = 0 ∧
      outcome.2.randomExamples = 0 ∧
      (outcome.2.queries : ℝ) ≤
        exactSparseSpectrumPolynomialRuntimeBound n k ∧
      (outcome.2.work : ℝ) ≤
        exactSparseSpectrumPolynomialRuntimeBound n k := by
  have hexact := exactSparseSpectrumLearningProgram_zero_error
    target k htarget outcome houtcome
  rw [runWithCost_exactSparseSpectrumLearningProgram,
    PMF.mem_support_pure_iff] at houtcome
  subst outcome
  have hresource := exactSparseSpectrumLearner_resource_bounds target k
  have hqueryCast :
      ((DeterministicQueryProgram.runWithCost target
        (exactSparseSpectrumLearner n k)).2.queries : ℝ) ≤
        (exactSparseSpectrumQueryBudget n k : ℝ) := by
    exact_mod_cast hresource.2.1
  have hworkCast :
      ((DeterministicQueryProgram.runWithCost target
        (exactSparseSpectrumLearner n k)).2.work : ℝ) ≤
        (exactSparseSpectrumWorkBudget n k : ℝ) := by
    exact_mod_cast hresource.2.2
  exact ⟨hexact.1, hexact.2, hresource.1,
    hqueryCast.trans
      (exactSparseSpectrumQueryBudget_cast_le_polynomialRuntimeBound n k),
    hworkCast.trans
      (exactSparseSpectrumWorkBudget_cast_le_polynomialRuntimeBound n k)⟩

end FABL
