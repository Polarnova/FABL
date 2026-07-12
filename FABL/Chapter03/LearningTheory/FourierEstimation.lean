/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.LearningTheory.Program

/-!
# Empirical Fourier estimation

Book items: Proposition 3.30.

The random-example Fourier estimator and its concentration bound.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

universe u v

variable {n : ℕ}

local instance fourierEstimationSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance fourierEstimationSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The rational observation whose expectation is the Fourier coefficient indexed by `S`. -/
def rationalFourierObservation (S : Finset (Fin n))
    (labeledSample : {−1,1}^[n] × Sign) : ℚ :=
  (((labeledSample.2 : Sign) : ℤ) : ℚ) *
    ∏ i ∈ S, (((labeledSample.1 i : Sign) : ℤ) : ℚ)

/-- The real observation used in the Fourier-coefficient concentration argument. -/
noncomputable def fourierObservation (target : BooleanFunction n)
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℝ :=
  target.toReal x * monomial S x

/-- The executable rational observation agrees with the real Fourier observation. -/
theorem rationalFourierObservation_cast (target : BooleanFunction n)
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    (rationalFourierObservation S (x, target x) : ℝ) =
      fourierObservation target S x := by
  simp [rationalFourierObservation, fourierObservation, monomial, signValue,
    BooleanFunction.toReal]

/-- Empirical average of `m` rational Fourier observations. Division by zero has its field
convention; the concentration theorem below assumes `m > 0`. -/
def empiricalFourierCoeff (S : Finset (Fin n)) {m : ℕ}
    (samples : Fin m → ({−1,1}^[n] × Sign)) : ℚ :=
  (∑ i, rationalFourierObservation S (samples i)) / m

/-- The real empirical Fourier average on a vector of sample inputs. -/
noncomputable def realEmpiricalFourierCoeff (target : BooleanFunction n)
    (S : Finset (Fin n)) {m : ℕ} (sampleInputs : Fin m → {−1,1}^[n]) : ℝ :=
  (∑ i, fourierObservation target S (sampleInputs i)) / m

/-- Casting the executable empirical estimate gives the corresponding real empirical average. -/
theorem empiricalFourierCoeff_cast (target : BooleanFunction n)
    (S : Finset (Fin n)) {m : ℕ} (sampleInputs : Fin m → {−1,1}^[n]) :
    (empiricalFourierCoeff S (fun i ↦ (sampleInputs i, target (sampleInputs i))) : ℝ) =
      realEmpiricalFourierCoeff target S sampleInputs := by
  simp [empiricalFourierCoeff, realEmpiricalFourierCoeff,
    rationalFourierObservation_cast]

/-- The finite random-example program in O'Donnell, Proposition 3.30. It draws exactly `m`
examples and computes their empirical Fourier observation average. -/
def fourierCoeffEstimatorProgram (S : Finset (Fin n)) (m : ℕ) :
    LearningProgram n .randomExamples ℚ :=
  .randomExampleBatch m fun samples ↦
    .tick (m * (S.card + 1)) (.pure (empiricalFourierCoeff S samples))

/-- The fully scheduled finite estimator from O'Donnell, Proposition 3.30. -/
def scheduledFourierCoeffEstimatorProgram (S : Finset (Fin n))
    (ε δ : PositiveLearningParameter) : LearningProgram n .randomExamples ℚ :=
  fourierCoeffEstimatorProgram S (fourierEstimatorSampleCount ε δ)

/-- The estimator program's output law, including its exact pathwise resource cost. -/
theorem runWithCost_fourierCoeffEstimatorProgram (target : BooleanFunction n)
    (S : Finset (Fin n)) (m : ℕ) :
    LearningProgram.runWithCost target (fourierCoeffEstimatorProgram S m) =
      (uniformPMF (Fin m → {−1,1}^[n])).map fun sampleInputs ↦
        (empiricalFourierCoeff S (fun i ↦ (sampleInputs i, target (sampleInputs i))),
          ⟨m, 0, m + m * (S.card + 1)⟩) := by
  unfold fourierCoeffEstimatorProgram LearningProgram.runWithCost
  simp only [LearningProgram.runWithCost, PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  congr 1

/-- Exact output law and pathwise cost of the scheduled Proposition 3.30 estimator. -/
theorem runWithCost_scheduledFourierCoeffEstimatorProgram
    (target : BooleanFunction n) (S : Finset (Fin n))
    (ε δ : PositiveLearningParameter) :
    LearningProgram.runWithCost target
        (scheduledFourierCoeffEstimatorProgram S ε δ) =
      (uniformPMF
        (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n])).map fun sampleInputs ↦
        (empiricalFourierCoeff S
          (fun i ↦ (sampleInputs i, target (sampleInputs i))),
          ⟨fourierEstimatorSampleCount ε δ, 0,
            fourierEstimatorSampleCount ε δ +
              fourierEstimatorSampleCount ε δ * (S.card + 1)⟩) := by
  exact runWithCost_fourierCoeffEstimatorProgram target S
    (fourierEstimatorSampleCount ε δ)

/-- Every scheduled estimator execution uses exactly the constructor-derived sample and work
counts, independently of the target and sampled inputs. -/
theorem scheduledFourierCoeffEstimatorProgram_cost_eq
    (target : BooleanFunction n) (S : Finset (Fin n))
    (ε δ : PositiveLearningParameter) (outcome : ℚ × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (scheduledFourierCoeffEstimatorProgram S ε δ)).support) :
    outcome.2 =
      ⟨fourierEstimatorSampleCount ε δ, 0,
        fourierEstimatorSampleCount ε δ +
          fourierEstimatorSampleCount ε δ * (S.card + 1)⟩ := by
  rw [runWithCost_scheduledFourierCoeffEstimatorProgram] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  rcases houtcome with ⟨sampleInputs, _, rfl⟩
  rfl

/-- Uniform finite sample vectors are products of their uniform coordinate measures. -/
theorem uniformSample_toMeasure_eq_pi
    (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (m : ℕ) :
    (uniformPMF (Fin m → Ω)).toMeasure =
      Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro samples
  rw [(uniformPMF (Fin m → Ω)).toMeasure_apply_singleton samples
    (measurableSet_singleton samples), Measure.pi_singleton]
  simp [uniformPMF, PMF.uniformOfFintype_apply, Fintype.card_pi, ENNReal.inv_pow]

/-- Uniform Boolean-cube input vectors are the corresponding finite product measure. -/
private theorem uniformSampleInputs_toMeasure_eq_pi (n m : ℕ) :
    (uniformPMF (Fin m → {−1,1}^[n])).toMeasure =
      Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure := by
  exact uniformSample_toMeasure_eq_pi {−1,1}^[n] m

/-- Empirical mean of a real observation on a finite uniform sample. -/
noncomputable def finiteUniformEmpiricalMean {Ω : Type*} [Fintype Ω]
    (observation : Ω → ℝ) {m : ℕ} (samples : Fin m → Ω) : ℝ :=
  (∑ i, observation (samples i)) / m

/-- Two-sided Hoeffding concentration for the empirical mean of any `[-1,1]`-valued observation
on a nonempty finite uniform space. -/
theorem measure_finiteUniformEmpiricalMean_sub_expect_ge_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (observation : Ω → ℝ)
    (hobservation : ∀ x, observation x ∈ Set.Icc (-1 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (uniformPMF (Fin m → Ω)).toMeasure.real
        {samples |
          ε ≤ |finiteUniformEmpiricalMean observation samples - (𝔼 x, observation x)|} ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  rw [uniformSample_toMeasure_eq_pi Ω m]
  let mean : ℝ := 𝔼 x : Ω, observation x
  let centeredSum : (Fin m → Ω) → ℝ := fun samples ↦
    ∑ i, (observation (samples i) - mean)
  let empiricalError : (Fin m → Ω) → ℝ := fun samples ↦
    finiteUniformEmpiricalMean observation samples - mean
  let upper : Set (Fin m → Ω) :=
    {samples | (m : ℝ) * ε ≤ centeredSum samples}
  let lower : Set (Fin m → Ω) :=
    {samples | (m : ℝ) * ε ≤ -centeredSum samples}
  have hcoordinate (i : Fin m) :
      HasSubgaussianMGF
        (fun samples : Fin m → Ω ↦ observation (samples i) - mean) 1
        (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure) := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure)
      (X := fun samples : Fin m → Ω ↦ observation (samples i))
      (measurable_of_finite fun samples : Fin m → Ω ↦
        observation (samples i)).aemeasurable
      (ae_of_all _ fun samples ↦ hobservation (samples i))
    have hmean :
        ∫ samples : Fin m → Ω, observation (samples i)
          ∂(Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure) = mean := by
      rw [integral_comp_eval
        (μ := fun _ : Fin m ↦ (uniformPMF Ω).toMeasure) (i := i)
        (measurable_of_finite observation).aestronglyMeasurable]
      exact integral_uniformPMF_eq_expect observation
    rw [hmean] at h
    norm_num at h ⊢
    exact h
  have hindep :
      iIndepFun
        (fun i (samples : Fin m → Ω) ↦ observation (samples i) - mean)
        (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure) := by
    exact iIndepFun_pi fun _ ↦
      (measurable_of_finite fun x : Ω ↦ observation x - mean).aemeasurable
  have hupper :
      (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure).real upper ≤
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
      (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
      (fun i _ ↦ hcoordinate i)
      (mul_nonneg (Nat.cast_nonneg m) hε)
    simpa [upper, centeredSum] using h
  have hlower :
      (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure).real lower ≤
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
    have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
      (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
      (fun i _ ↦ hcoordinate i)
    have h := hsum.neg.measure_ge_le (mul_nonneg (Nat.cast_nonneg m) hε)
    simpa [lower, centeredSum] using h
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum (samples : Fin m → Ω) :
      centeredSum samples = (m : ℝ) * empiricalError samples := by
    unfold centeredSum empiricalError
    rw [Finset.sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold finiteUniformEmpiricalMean
    have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
    field_simp
  have hset : {samples | ε ≤ |empiricalError samples|} = upper ∪ lower := by
    ext samples
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro habs
      by_cases hnonneg : 0 ≤ empiricalError samples
      · left
        change (m : ℝ) * ε ≤ centeredSum samples
        rw [hsum]
        rw [abs_of_nonneg hnonneg] at habs
        exact mul_le_mul_of_nonneg_left habs hmReal.le
      · right
        change (m : ℝ) * ε ≤ -centeredSum samples
        rw [hsum]
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at habs
        nlinarith [mul_le_mul_of_nonneg_left habs hmReal.le]
    · rintro (hupper' | hlower')
      · change (m : ℝ) * ε ≤ centeredSum samples at hupper'
        rw [hsum] at hupper'
        have h : ε ≤ empiricalError samples := by nlinarith
        exact h.trans (le_abs_self _)
      · change (m : ℝ) * ε ≤ -centeredSum samples at hlower'
        rw [hsum] at hlower'
        have hneg : ε ≤ -empiricalError samples := by nlinarith
        exact hneg.trans (neg_le_abs _)
  rw [show {samples |
      ε ≤ |finiteUniformEmpiricalMean observation samples - (𝔼 x, observation x)|} =
      {samples | ε ≤ |empiricalError samples|} by rfl, hset]
  calc
    (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure).real (upper ∪ lower) ≤
        (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure).real upper +
          (Measure.pi fun _ : Fin m ↦ (uniformPMF Ω).toMeasure).real lower :=
      measureReal_union_le upper lower
    _ ≤ Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) +
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
      have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
      field_simp
      ring

/-- A Fourier observation is always a sign. -/
theorem fourierObservation_mem_Icc (target : BooleanFunction n)
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    fourierObservation target S x ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases signValue_eq_neg_one_or_one (target x) with htarget | htarget <;>
    rcases sq_eq_one_iff.mp (monomial_sq S x) with hmonomial | hmonomial <;>
    simp [fourierObservation, BooleanFunction.toReal, htarget, hmonomial]

/-- The mean Fourier observation is the corresponding Fourier coefficient. -/
theorem integral_fourierObservation_uniformPMF (target : BooleanFunction n)
    (S : Finset (Fin n)) :
    ∫ x, fourierObservation target S x ∂(uniformPMF {−1,1}^[n]).toMeasure =
      fourierCoeff target.toReal S := by
  rw [integral_uniformPMF_eq_expect]
  rfl

/-- Hoeffding's lemma applied to one centered Fourier observation. -/
theorem fourierObservation_hasSubgaussianMGF (target : BooleanFunction n)
    (S : Finset (Fin n)) :
    HasSubgaussianMGF
      (fun x ↦ fourierObservation target S x - fourierCoeff target.toReal S) 1
      (uniformPMF {−1,1}^[n]).toMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (μ := (uniformPMF {−1,1}^[n]).toMeasure)
    (X := fourierObservation target S)
    (measurable_of_finite (fourierObservation target S)).aemeasurable
    (ae_of_all _ (fourierObservation_mem_Icc target S))
  rw [integral_fourierObservation_uniformPMF] at h
  norm_num at h ⊢
  exact h

/-- A centered observation at one coordinate of a uniform sample vector is sub-Gaussian. -/
private theorem sampleCoordinate_fourierObservation_hasSubgaussianMGF
    (target : BooleanFunction n) (S : Finset (Fin n)) (m : ℕ) (i : Fin m) :
    HasSubgaussianMGF
      (fun sampleInputs : Fin m → {−1,1}^[n] ↦
        fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S) 1
      (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure) := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (μ := Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure)
    (X := fun sampleInputs : Fin m → {−1,1}^[n] ↦
      fourierObservation target S (sampleInputs i))
    (measurable_of_finite fun sampleInputs : Fin m → {−1,1}^[n] ↦
      fourierObservation target S (sampleInputs i)).aemeasurable
    (ae_of_all _ fun sampleInputs ↦ fourierObservation_mem_Icc target S (sampleInputs i))
  have hmean :
      ∫ sampleInputs : Fin m → {−1,1}^[n],
          fourierObservation target S (sampleInputs i)
        ∂(Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure) =
        fourierCoeff target.toReal S := by
    rw [integral_comp_eval
      (μ := fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure) (i := i)
      (measurable_of_finite (fourierObservation target S)).aestronglyMeasurable]
    exact integral_fourierObservation_uniformPMF target S
  rw [hmean] at h
  norm_num at h ⊢
  exact h

/-- Upper-tail Hoeffding bound for the sum of centered Fourier observations. -/
private theorem measure_centeredFourierObservation_sum_ge_le
    (target : BooleanFunction n) (S : Finset (Fin n)) (m : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure).real
        {sampleInputs |
          (m : ℝ) * ε ≤ ∑ i,
            (fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)} ≤
      Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
  have hindep :
      iIndepFun
        (fun i (sampleInputs : Fin m → {−1,1}^[n]) ↦
          fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)
        (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure) := by
    exact iIndepFun_pi fun _ ↦
      (measurable_of_finite fun x : {−1,1}^[n] ↦
        fourierObservation target S x - fourierCoeff target.toReal S).aemeasurable
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
    (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
    (fun i _ ↦ sampleCoordinate_fourierObservation_hasSubgaussianMGF target S m i)
    (mul_nonneg (Nat.cast_nonneg m) hε)
  simpa using h

/-- Lower-tail Hoeffding bound for the sum of centered Fourier observations. -/
private theorem measure_neg_centeredFourierObservation_sum_ge_le
    (target : BooleanFunction n) (S : Finset (Fin n)) (m : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure).real
        {sampleInputs |
          (m : ℝ) * ε ≤ -∑ i,
            (fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)} ≤
      Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
  have hindep :
      iIndepFun
        (fun i (sampleInputs : Fin m → {−1,1}^[n]) ↦
          fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)
        (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure) := by
    exact iIndepFun_pi fun _ ↦
      (measurable_of_finite fun x : {−1,1}^[n] ↦
        fourierObservation target S x - fourierCoeff target.toReal S).aemeasurable
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
    (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
    (fun i _ ↦ sampleCoordinate_fourierObservation_hasSubgaussianMGF target S m i)
  have h := hsum.neg.measure_ge_le (mul_nonneg (Nat.cast_nonneg m) hε)
  simpa using h

/-- The centered observation sum is `m` times the empirical-average error. -/
private theorem sum_centeredFourierObservation_eq_mul_sub_realEmpirical
    (target : BooleanFunction n) (S : Finset (Fin n)) {m : ℕ} (hm : 0 < m)
    (sampleInputs : Fin m → {−1,1}^[n]) :
    (∑ i, (fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)) =
      (m : ℝ) *
        (realEmpiricalFourierCoeff target S sampleInputs - fourierCoeff target.toReal S) := by
  rw [Finset.sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold realEmpiricalFourierCoeff
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- Two-sided Hoeffding concentration for the empirical Fourier average. -/
theorem measure_realEmpiricalFourierCoeff_sub_ge_le
    (target : BooleanFunction n) (S : Finset (Fin n)) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real
        {sampleInputs |
          ε ≤ |realEmpiricalFourierCoeff target S sampleInputs -
            fourierCoeff target.toReal S|} ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  rw [uniformSampleInputs_toMeasure_eq_pi]
  let centeredSum : (Fin m → {−1,1}^[n]) → ℝ := fun sampleInputs ↦
    ∑ i, (fourierObservation target S (sampleInputs i) - fourierCoeff target.toReal S)
  let empiricalError : (Fin m → {−1,1}^[n]) → ℝ := fun sampleInputs ↦
    realEmpiricalFourierCoeff target S sampleInputs - fourierCoeff target.toReal S
  let upper : Set (Fin m → {−1,1}^[n]) :=
    {sampleInputs | (m : ℝ) * ε ≤ centeredSum sampleInputs}
  let lower : Set (Fin m → {−1,1}^[n]) :=
    {sampleInputs | (m : ℝ) * ε ≤ -centeredSum sampleInputs}
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hset : {sampleInputs | ε ≤ |empiricalError sampleInputs|} = upper ∪ lower := by
    ext sampleInputs
    simp only [Set.mem_setOf_eq, Set.mem_union]
    have hsum : centeredSum sampleInputs = (m : ℝ) * empiricalError sampleInputs := by
      exact sum_centeredFourierObservation_eq_mul_sub_realEmpirical
        target S hm sampleInputs
    constructor
    · intro habs
      by_cases hnonneg : 0 ≤ empiricalError sampleInputs
      · left
        change (m : ℝ) * ε ≤ centeredSum sampleInputs
        rw [hsum]
        rw [abs_of_nonneg hnonneg] at habs
        exact mul_le_mul_of_nonneg_left habs hmReal.le
      · right
        change (m : ℝ) * ε ≤ -centeredSum sampleInputs
        rw [hsum]
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at habs
        nlinarith [mul_le_mul_of_nonneg_left habs hmReal.le]
    · rintro (hupper | hlower)
      · change (m : ℝ) * ε ≤ centeredSum sampleInputs at hupper
        rw [hsum] at hupper
        have h : ε ≤ empiricalError sampleInputs := by nlinarith
        exact h.trans (le_abs_self _)
      · change (m : ℝ) * ε ≤ -centeredSum sampleInputs at hlower
        rw [hsum] at hlower
        have hneg : ε ≤ -empiricalError sampleInputs := by nlinarith
        exact hneg.trans (neg_le_abs _)
  rw [show {sampleInputs | ε ≤
      |realEmpiricalFourierCoeff target S sampleInputs - fourierCoeff target.toReal S|} =
      {sampleInputs | ε ≤ |empiricalError sampleInputs|} by rfl, hset]
  calc
    (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure).real (upper ∪ lower) ≤
        (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure).real upper +
          (Measure.pi fun _ : Fin m ↦ (uniformPMF {−1,1}^[n]).toMeasure).real lower :=
      measureReal_union_le upper lower
    _ ≤ Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) +
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
      apply add_le_add
      · exact measure_centeredFourierObservation_sum_ge_le target S m ε hε
      · exact measure_neg_centeredFourierObservation_sum_ge_le target S m ε hε
    _ = 2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
      have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
      field_simp
      ring

/-- The actual estimator program inherits the two-sided Hoeffding failure bound. -/
theorem fourierCoeffEstimatorProgram_failureProbability_le
    (target : BooleanFunction n) (S : Finset (Fin n)) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) :
    LearningProgram.eventProbability (fourierCoeffEstimatorProgram S m) target
        (fun outcome ↦ ε ≤ |(outcome.1 : ℝ) - fourierCoeff target.toReal S|) ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  unfold LearningProgram.eventProbability
  rw [runWithCost_fourierCoeffEstimatorProgram, PMF.toOuterMeasure_map_apply]
  rw [← (uniformPMF (Fin m → {−1,1}^[n])).toMeasure_apply_eq_toOuterMeasure]
  change (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real
      {sampleInputs |
        ε ≤ |(empiricalFourierCoeff S
          (fun i ↦ (sampleInputs i, target (sampleInputs i))) : ℝ) -
            fourierCoeff target.toReal S|} ≤ _
  simp_rw [empiricalFourierCoeff_cast]
  have hmean : (𝔼 x, fourierObservation target S x) =
      fourierCoeff target.toReal S := by
    rw [← integral_uniformPMF_eq_expect]
    exact integral_fourierObservation_uniformPMF target S
  simpa [finiteUniformEmpiricalMean, realEmpiricalFourierCoeff, hmean] using
    (measure_finiteUniformEmpiricalMean_sub_expect_ge_le
      (observation := fourierObservation target S)
      (fourierObservation_mem_Icc target S) hm ε hε)

/-- O'Donnell, Proposition 3.30: from random examples, the scheduled finite program estimates the
specified Fourier coefficient to additive error `ε`, except with probability at most `δ`. -/
theorem scheduledFourierCoeffEstimatorProgram_failureProbability_le
    (target : BooleanFunction n) (S : Finset (Fin n))
    (ε δ : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (scheduledFourierCoeffEstimatorProgram S ε δ) target
        (fun outcome ↦
          (ε.1 : ℝ) ≤ |(outcome.1 : ℝ) - fourierCoeff target.toReal S|) ≤
      (δ.1 : ℝ) := by
  exact (fourierCoeffEstimatorProgram_failureProbability_le target S
    (fourierEstimatorSampleCount_pos ε δ) (ε.1 : ℝ)
    (positiveLearningParameter_toReal_mem_Ioc ε).1.le).trans
      (two_mul_exp_neg_fourierEstimatorSampleCount_le ε δ)

end FABL
