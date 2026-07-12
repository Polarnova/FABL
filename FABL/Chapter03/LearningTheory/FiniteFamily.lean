/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.LearningTheory.LearningModel

/-!
# Finite-family Fourier learning

Book items: Theorem 3.29, Theorem 3.36, Exercise 3.36.

The finite-family learner, its resource bounds, and its success probability.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

universe u v

variable {n : ℕ}

local instance finiteFamilySignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance finiteFamilySignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- Sparse output computed from a matrix of labeled random examples. -/
def finiteFamilyFourierEstimatorLabeledOutput
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (samples : 𝓕 → Fin m → ({−1,1}^[n] × Sign)) :
    SparseFourierHypothesis n :=
  SparseFourierHypothesis.ofCoefficients 𝓕 fun S ↦
    empiricalFourierCoeff S.1 (samples S)

/-- Sparse output computed from a matrix of random-example inputs. -/
def finiteFamilyFourierEstimatorOutput (target : BooleanFunction n)
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (sampleInputs : 𝓕 → Fin m → {−1,1}^[n]) :
    SparseFourierHypothesis n :=
  finiteFamilyFourierEstimatorLabeledOutput 𝓕 m fun S i ↦
    (sampleInputs S i, target (sampleInputs S i))

/-- The finite-family estimator's output has exactly the prescribed finite Fourier support. -/
@[simp] theorem finiteFamilyFourierEstimatorOutput_support
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (sampleInputs : 𝓕 → Fin m → {−1,1}^[n]) :
    (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs).support = 𝓕 :=
  rfl

/-- Every concrete finite-family output round-trips through the sparse hypothesis's finite binary
encoding. -/
@[simp] theorem finiteFamilyFourierEstimatorOutput_decode_encode
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (sampleInputs : 𝓕 → Fin m → {−1,1}^[n]) :
    SparseFourierHypothesis.decode
        (SparseFourierHypothesis.encode
          (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs)) =
      some (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs) :=
  SparseFourierHypothesis.decode_encode _

/-- Evaluating the finite circuit output has the advertised support-linear structural work. -/
@[simp] theorem finiteFamilyFourierEstimatorOutput_evaluationWork
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (sampleInputs : 𝓕 → Fin m → {−1,1}^[n]) (x : {−1,1}^[n]) :
    SparseFourierHypothesis.evaluationWork
        (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs) x =
      𝓕.card * (n + 1) := by
  rfl

/-- The finite-family estimator with an explicit samples-per-coefficient input. -/
def finiteFamilyFourierEstimatorProgramWithSamples
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    LearningProgram n .randomExamples (SparseFourierHypothesis n) :=
  .randomExampleMatrixOutput 𝓕 m (𝓕.card * m * (n + 1))
    (finiteFamilyFourierEstimatorLabeledOutput 𝓕 m)

/-- The scheduled finite-family estimator used by Theorem 3.29. -/
def finiteFamilyFourierEstimatorProgram (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) :
    LearningProgram n .randomExamples (SparseFourierHypothesis n) :=
  finiteFamilyFourierEstimatorProgramWithSamples 𝓕
    (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε)

/-- The scheduled family learner is interpreted by the direct finite matrix-output law. -/
theorem runWithCost_finiteFamilyFourierEstimatorProgram
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) :
    LearningProgram.runWithCost target
        (finiteFamilyFourierEstimatorProgram 𝓕 h𝓕 ε) =
      LearningProgram.randomExampleMatrixOutputLaw target 𝓕
        (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε)
        (𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε * (n + 1))
        (finiteFamilyFourierEstimatorLabeledOutput 𝓕
          (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε)) := by
  rfl

/-- Every finite-family estimator path has exact target-independent resource usage. -/
theorem finiteFamilyFourierEstimatorProgram_cost_eq
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (finiteFamilyFourierEstimatorProgram 𝓕 h𝓕 ε)).support) :
    outcome.2 =
      ⟨𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε, 0,
        𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε +
          𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε * (n + 1)⟩ := by
  rw [runWithCost_finiteFamilyFourierEstimatorProgram] at houtcome
  unfold LearningProgram.randomExampleMatrixOutputLaw at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  rcases houtcome with ⟨sampleInputs, _, rfl⟩
  rfl

/-- The exact cost law in component form: the learner uses no membership queries, draws one row
of random examples per requested coefficient, and performs the stated finite amount of work. -/
theorem finiteFamilyFourierEstimatorProgram_cost_components
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (finiteFamilyFourierEstimatorProgram 𝓕 h𝓕 ε)).support) :
    outcome.2.randomExamples =
        𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε ∧
      outcome.2.queries = 0 ∧
      outcome.2.work =
        𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε +
          𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε * (n + 1) := by
  rw [finiteFamilyFourierEstimatorProgram_cost_eq target 𝓕 h𝓕 ε outcome houtcome]
  constructor
  · rfl
  · constructor <;> rfl

/-- The family confidence budget has the explicit binary logarithmic scheduler
`clog₂ (20|𝓕|)`. -/
theorem finiteFamilyCoefficientFailureBits_eq
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty) :
    fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) =
      Nat.clog 2 (20 * 𝓕.card) := by
  unfold fourierEstimatorFailureBits
  rw [show (finiteFamilyCoefficientConfidence 𝓕 h𝓕).1 =
    1 / (10 * 𝓕.card) by norm_num [finiteFamilyCoefficientConfidence]]
  have hcard : (𝓕.card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr h𝓕).ne'
  rw [show (2 : ℚ) / (1 / (10 * 𝓕.card)) =
    ((20 * 𝓕.card : ℕ) : ℚ) by
      push_cast
      field_simp
      ring]
  rw [Nat.ceil_natCast]

/-- Explicit scheduler bound for one coefficient row of the finite-family learner. -/
theorem finiteFamilySamplesPerCoefficient_cast_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε : PositiveLearningParameter) :
    (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε : ℚ) ≤
      16 * (𝓕.card : ℚ) ^ 2 *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by
  have hscheduler := fourierEstimatorSampleCount_cast_le
    (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
    (finiteFamilyCoefficientConfidence 𝓕 h𝓕)
  calc
    (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε : ℚ) ≤
        4 * fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
          (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1 ^ 2 := by
      simpa [finiteFamilySamplesPerCoefficient] using hscheduler
    _ = 16 * (𝓕.card : ℚ) ^ 2 *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by
      have hcard : (𝓕.card : ℚ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr h𝓕).ne'
      have hε : ε.1 ≠ 0 := ne_of_gt ε.2.1
      rw [show (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1 =
        ε.1 / (2 * 𝓕.card) by norm_num [finiteFamilyCoefficientAccuracy]]
      field_simp
      ring

/-- Explicit polynomial/logarithmic bound on all random examples used by the finite-family
learner. -/
theorem finiteFamilyTotalRandomExamples_cast_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε : PositiveLearningParameter) :
    ((𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε : ℕ) : ℚ) ≤
      16 * (𝓕.card : ℚ) ^ 3 *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by
  have hrow := finiteFamilySamplesPerCoefficient_cast_le 𝓕 h𝓕 ε
  norm_num only [Nat.cast_mul]
  calc
    (𝓕.card : ℚ) * (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε : ℚ) ≤
        (𝓕.card : ℚ) *
          (16 * (𝓕.card : ℚ) ^ 2 *
              fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
            ε.1 ^ 2) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = 16 * (𝓕.card : ℚ) ^ 3 *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by ring

/-- Explicit polynomial/logarithmic bound on the finite-family learner's total local work. -/
theorem finiteFamilyTotalWork_cast_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε : PositiveLearningParameter) :
    ((𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε +
        𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε * (n + 1) : ℕ) : ℚ) ≤
      16 * (𝓕.card : ℚ) ^ 3 * (n + 2) *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by
  have hsamples := finiteFamilyTotalRandomExamples_cast_le 𝓕 h𝓕 ε
  calc
    ((𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε +
        𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε * (n + 1) : ℕ) : ℚ) =
        ((𝓕.card * finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε : ℕ) : ℚ) *
          (n + 2) := by
      push_cast
      ring
    _ ≤ (16 * (𝓕.card : ℚ) ^ 3 *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2) * (n + 2) :=
      mul_le_mul_of_nonneg_right hsamples (by positivity)
    _ = 16 * (𝓕.card : ℚ) ^ 3 * (n + 2) *
          fourierEstimatorFailureBits (finiteFamilyCoefficientConfidence 𝓕 h𝓕) /
        ε.1 ^ 2 := by ring

/-- Every actual estimator path has zero query cost and the explicit
`poly(|𝓕|, n, 1/ε) · clog₂(20|𝓕|)` random-example and work bounds. -/
theorem finiteFamilyFourierEstimatorProgram_cost_polyBound
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (finiteFamilyFourierEstimatorProgram 𝓕 h𝓕 ε)).support) :
    (outcome.2.randomExamples : ℚ) ≤
        16 * (𝓕.card : ℚ) ^ 3 * Nat.clog 2 (20 * 𝓕.card) / ε.1 ^ 2 ∧
      outcome.2.queries = 0 ∧
      (outcome.2.work : ℚ) ≤
        16 * (𝓕.card : ℚ) ^ 3 * (n + 2) * Nat.clog 2 (20 * 𝓕.card) /
          ε.1 ^ 2 := by
  rcases finiteFamilyFourierEstimatorProgram_cost_components
      target 𝓕 h𝓕 ε outcome houtcome with ⟨hrandom, hqueries, hwork⟩
  constructor
  · rw [hrandom]
    have hbound := finiteFamilyTotalRandomExamples_cast_le 𝓕 h𝓕 ε
    rw [finiteFamilyCoefficientFailureBits_eq 𝓕 h𝓕] at hbound
    exact hbound
  · constructor
    · exact hqueries
    · rw [hwork]
      have hbound := finiteFamilyTotalWork_cast_le 𝓕 h𝓕 ε
      rw [finiteFamilyCoefficientFailureBits_eq 𝓕 h𝓕] at hbound
      exact hbound

/-- Uniform matrices of sample inputs are products of uniform row measures. -/
private theorem uniformSampleMatrix_toMeasure_eq_pi
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕 m).toMeasure =
      Measure.pi fun _ : 𝓕 ↦
        (uniformPMF (Fin m → {−1,1}^[n])).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro sampleInputs
  rw [(LearningProgram.randomExampleMatrixInputLaw 𝓕 m).toMeasure_apply_singleton
    sampleInputs (measurableSet_singleton sampleInputs), Measure.pi_singleton]
  simp [LearningProgram.randomExampleMatrixInputLaw, uniformPMF,
    PMF.uniformOfFintype_apply, Fintype.card_pi, ENNReal.inv_pow]

/-- Failure event for one row of a finite coefficient-estimation matrix, with independently
specified accuracy and confidence parameters. -/
def finiteFamilyCoefficientBadSetWithParameters
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (accuracy confidence : PositiveLearningParameter) (S : 𝓕) :
    Set (𝓕 → Fin (fourierEstimatorSampleCount accuracy confidence) → {−1,1}^[n]) :=
  {sampleInputs |
    (accuracy.1 : ℝ) ≤
      |realEmpiricalFourierCoeff target S.1 (sampleInputs S) -
        fourierCoeff target.toReal S.1|}

/-- A fixed row violates its requested accuracy with probability at most its confidence
budget. -/
theorem measure_finiteFamilyCoefficientBadSetWithParameters_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (accuracy confidence : PositiveLearningParameter) (S : 𝓕) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (fourierEstimatorSampleCount accuracy confidence)).toMeasure.real
        (finiteFamilyCoefficientBadSetWithParameters target 𝓕 accuracy confidence S) ≤
      (confidence.1 : ℝ) := by
  let m := fourierEstimatorSampleCount accuracy confidence
  let badRow : Set (Fin m → {−1,1}^[n]) :=
    {sampleInputs |
      (accuracy.1 : ℝ) ≤
        |realEmpiricalFourierCoeff target S.1 sampleInputs -
          fourierCoeff target.toReal S.1|}
  have hrow :
      (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real badRow ≤
        (confidence.1 : ℝ) := by
    exact (measure_realEmpiricalFourierCoeff_sub_ge_le target S.1
      (fourierEstimatorSampleCount_pos accuracy confidence) (accuracy.1 : ℝ)
      (positiveLearningParameter_toReal_mem_Ioc accuracy).1.le).trans
        (two_mul_exp_neg_fourierEstimatorSampleCount_le accuracy confidence)
  rw [uniformSampleMatrix_toMeasure_eq_pi]
  change (Measure.pi fun _ : 𝓕 ↦
      (uniformPMF (Fin m → {−1,1}^[n])).toMeasure).real
        ((fun sampleInputs ↦ sampleInputs S) ⁻¹' badRow) ≤ _
  have hbadMeasurable : MeasurableSet badRow := Set.toFinite badRow |>.measurableSet
  calc
    (Measure.pi fun _ : 𝓕 ↦
        (uniformPMF (Fin m → {−1,1}^[n])).toMeasure).real
          ((fun sampleInputs ↦ sampleInputs S) ⁻¹' badRow) =
        ((Measure.pi fun _ : 𝓕 ↦
          (uniformPMF (Fin m → {−1,1}^[n])).toMeasure).map
            (Function.eval S)).real badRow := by
      exact congrArg ENNReal.toReal (Measure.map_apply
        (μ := Measure.pi fun _ : 𝓕 ↦
          (uniformPMF (Fin m → {−1,1}^[n])).toMeasure)
        (f := Function.eval S) (measurable_pi_apply S) hbadMeasurable).symm
    _ = (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real badRow := by
      rw [(measurePreserving_eval
        (fun _ : 𝓕 ↦ (uniformPMF (Fin m → {−1,1}^[n])).toMeasure) S).map_eq]
    _ ≤ (confidence.1 : ℝ) := hrow

/-- A union bound over an arbitrary finite coefficient family accumulates the common per-row
confidence budget linearly. -/
theorem measure_finiteFamily_someCoefficientBadSetWithParameters_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (accuracy confidence : PositiveLearningParameter) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (fourierEstimatorSampleCount accuracy confidence)).toMeasure.real
        (⋃ S : 𝓕,
          finiteFamilyCoefficientBadSetWithParameters target 𝓕
            accuracy confidence S) ≤
      (𝓕.card : ℝ) * (confidence.1 : ℝ) := by
  calc
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (fourierEstimatorSampleCount accuracy confidence)).toMeasure.real
        (⋃ S : 𝓕,
          finiteFamilyCoefficientBadSetWithParameters target 𝓕
            accuracy confidence S) ≤
        ∑ S : 𝓕,
          (LearningProgram.randomExampleMatrixInputLaw 𝓕
            (fourierEstimatorSampleCount accuracy confidence)).toMeasure.real
            (finiteFamilyCoefficientBadSetWithParameters target 𝓕
              accuracy confidence S) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : 𝓕, (confidence.1 : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_finiteFamilyCoefficientBadSetWithParameters_le
        target 𝓕 accuracy confidence S
    _ = (𝓕.card : ℝ) * (confidence.1 : ℝ) := by
      simp [nsmul_eq_mul]

/-- With confidence `1/(10|𝓕|)`, the probability that any row violates an arbitrary requested
accuracy is at most `1/10`. -/
theorem measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (accuracy : PositiveLearningParameter) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (fourierEstimatorSampleCount accuracy
        (finiteFamilyCoefficientConfidence 𝓕 h𝓕))).toMeasure.real
        (⋃ S : 𝓕, finiteFamilyCoefficientBadSetWithParameters target 𝓕 accuracy
          (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S) ≤
      (1 / 10 : ℝ) := by
  calc
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (fourierEstimatorSampleCount accuracy
        (finiteFamilyCoefficientConfidence 𝓕 h𝓕))).toMeasure.real
        (⋃ S : 𝓕, finiteFamilyCoefficientBadSetWithParameters target 𝓕 accuracy
          (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S) ≤
        ∑ S : 𝓕,
          (LearningProgram.randomExampleMatrixInputLaw 𝓕
            (fourierEstimatorSampleCount accuracy
              (finiteFamilyCoefficientConfidence 𝓕 h𝓕))).toMeasure.real
            (finiteFamilyCoefficientBadSetWithParameters target 𝓕 accuracy
              (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : 𝓕, ((finiteFamilyCoefficientConfidence 𝓕 h𝓕).1 : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_finiteFamilyCoefficientBadSetWithParameters_le
        target 𝓕 accuracy (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S
    _ = (1 / 10 : ℝ) := by
      have hcard : (0 : ℝ) < 𝓕.card := by
        exact_mod_cast Finset.card_pos.mpr h𝓕
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [show ((finiteFamilyCoefficientConfidence 𝓕 h𝓕).1 : ℝ) =
        1 / (10 * 𝓕.card) by norm_num [finiteFamilyCoefficientConfidence]]
      field_simp

/-- The Theorem 3.29 failure event specializes the parameterized row event. -/
def finiteFamilyCoefficientBadSet
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) (S : 𝓕) :
    Set (𝓕 → Fin (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε) → {−1,1}^[n]) :=
  finiteFamilyCoefficientBadSetWithParameters target 𝓕
    (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε) (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S

/-- A Theorem 3.29 row is inaccurate with probability at most `1/(10|𝓕|)`. -/
theorem measure_finiteFamilyCoefficient_bad_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) (S : 𝓕) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε)).toMeasure.real
        (finiteFamilyCoefficientBadSet target 𝓕 h𝓕 ε S) ≤
      ((finiteFamilyCoefficientConfidence 𝓕 h𝓕).1 : ℝ) := by
  exact measure_finiteFamilyCoefficientBadSetWithParameters_le target 𝓕
    (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε) (finiteFamilyCoefficientConfidence 𝓕 h𝓕) S

/-- With the `1/(10|𝓕|)` confidence budget, the probability that any Theorem 3.29 row is
inaccurate is at most `1/10`. -/
theorem measure_finiteFamily_someCoefficient_bad_le_one_tenth
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (finiteFamilySamplesPerCoefficient 𝓕 h𝓕 ε)).toMeasure.real
        (⋃ S : 𝓕, finiteFamilyCoefficientBadSet target 𝓕 h𝓕 ε S) ≤
      (1 / 10 : ℝ) := by
  exact measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth
    target 𝓕 h𝓕 (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)

/-- Deterministic analytic core of Theorem 3.29: simultaneous coefficient accuracy and spectral
concentration imply that sign rounding of the sparse output has error at most `ε`. -/
theorem relativeHammingDist_sparseFourierHypothesis_of_coefficients_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) (coefficient : 𝓕 → ℚ)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝓕 : Set (Finset (Fin n))))
    (hcoefficient : ∀ S : 𝓕,
      |(coefficient S : ℝ) - fourierCoeff target.toReal S.1| ≤
        (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1) :
    relativeHammingDist target
      (SparseFourierHypothesis.ofCoefficients 𝓕 coefficient).evaluate ≤ (ε.1 : ℝ) := by
  let η : ℝ := (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1
  let realCoefficient :=
    SparseFourierHypothesis.realCoefficientOfCoefficients 𝓕 coefficient
  have hη : 0 ≤ η :=
    (positiveLearningParameter_toReal_mem_Ioc
      (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)).1.le
  have hcoefficientSum :
      (∑ S ∈ 𝓕, (fourierCoeff target.toReal S - realCoefficient S) ^ 2) ≤
        (𝓕.card : ℝ) * η ^ 2 := by
    calc
      (∑ S ∈ 𝓕, (fourierCoeff target.toReal S - realCoefficient S) ^ 2) ≤
          ∑ S ∈ 𝓕, η ^ 2 := by
        apply Finset.sum_le_sum
        intro S hS
        have habs :
            |fourierCoeff target.toReal S - (coefficient ⟨S, hS⟩ : ℝ)| ≤ η := by
          simpa [η, abs_sub_comm] using hcoefficient ⟨S, hS⟩
        have hrealCoefficient :
            realCoefficient S = (coefficient ⟨S, hS⟩ : ℝ) := by
          simp [realCoefficient,
            SparseFourierHypothesis.realCoefficientOfCoefficients, hS]
        rw [hrealCoefficient]
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hη] using habs)
      _ = (𝓕.card : ℝ) * η ^ 2 := by simp
  have houtside :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
        fourierCoeff target.toReal S ^ 2) ≤ (ε.1 : ℝ) / 2 := by
    simpa [IsFourierSpectrumConcentratedOn, fourierWeightOutside, fourierWeight] using
      hconcentration
  have hcard : (1 : ℝ) ≤ 𝓕.card := by
    exact_mod_cast (Finset.card_pos.mpr h𝓕)
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  have hηValue : η = (ε.1 : ℝ) / (2 * 𝓕.card) := by
    norm_num [η, finiteFamilyCoefficientAccuracy]
  have hcardPos : (0 : ℝ) < 𝓕.card := zero_lt_one.trans_le hcard
  have hsmall :
      (𝓕.card : ℝ) * η ^ 2 ≤ (ε.1 : ℝ) / 2 := by
    rw [hηValue]
    have hidentity :
        (𝓕.card : ℝ) * ((ε.1 : ℝ) / (2 * 𝓕.card)) ^ 2 =
          (ε.1 : ℝ) ^ 2 / (4 * 𝓕.card) := by
      field_simp
      ring
    rw [hidentity]
    rw [div_le_iff₀ (mul_pos (by norm_num) hcardPos)]
    have hlinear : (ε.1 : ℝ) ≤ 2 * 𝓕.card := by nlinarith [hε.2]
    have hmul := mul_le_mul_of_nonneg_left hlinear hε.1.le
    nlinarith
  have hL2 :
      uniformLpNorm 2 (fun x ↦ target.toReal x -
        (SparseFourierHypothesis.ofCoefficients 𝓕 coefficient).realValue x) ^ 2 ≤
        (ε.1 : ℝ) := by
    rw [SparseFourierHypothesis.realValue_ofCoefficients,
      uniformLpNorm_sub_sparseFourierApproximation_sq]
    exact (add_le_add hcoefficientSum houtside).trans (by nlinarith)
  rw [SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue]
  exact relativeHammingDist_thresholdSign_le_of_uniformLpNorm_two_sq_le
    target _ _ hL2

/-- Outside every scheduled coefficient failure event, the finite-family estimator outputs a
hypothesis of relative Hamming error at most `ε`. -/
theorem relativeHammingDist_finiteFamilyFourierEstimatorOutput_le_of_no_bad
    (target : BooleanFunction n) (𝒽 : Finset (Finset (Fin n)))
    (h𝒽 : 𝒽.Nonempty) (ε : PositiveLearningParameter)
    (sampleInputs :
      𝒽 → Fin (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) → {−1,1}^[n])
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝒽 : Set (Finset (Fin n))))
    (hgood : ∀ S : 𝒽,
      sampleInputs ∉ finiteFamilyCoefficientBadSet target 𝒽 h𝒽 ε S) :
    relativeHammingDist target
      (finiteFamilyFourierEstimatorOutput target 𝒽
        (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) sampleInputs).evaluate ≤
      (ε.1 : ℝ) := by
  change relativeHammingDist target
    (SparseFourierHypothesis.ofCoefficients 𝒽 fun S ↦
      empiricalFourierCoeff S.1 fun i ↦
        (sampleInputs S i, target (sampleInputs S i))).evaluate ≤ (ε.1 : ℝ)
  apply relativeHammingDist_sparseFourierHypothesis_of_coefficients_le
    target 𝒽 h𝒽 ε _ hconcentration
  intro S
  have hgoodS := hgood S
  change ¬((finiteFamilyCoefficientAccuracy 𝒽 h𝒽 ε).1 : ℝ) ≤
    |realEmpiricalFourierCoeff target S.1 (sampleInputs S) -
      fourierCoeff target.toReal S.1| at hgoodS
  rw [empiricalFourierCoeff_cast]
  exact (lt_of_not_ge hgoodS).le

/-- A uniform matrix of random examples makes the finite-family estimator inaccurate with
probability at most `1/10`. -/
theorem measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth
    (target : BooleanFunction n) (𝒽 : Finset (Finset (Fin n)))
    (h𝒽 : 𝒽.Nonempty) (ε : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝒽 : Set (Finset (Fin n)))) :
    (LearningProgram.randomExampleMatrixInputLaw 𝒽
      (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toMeasure.real
        {sampleInputs |
          (ε.1 : ℝ) < relativeHammingDist target
            (finiteFamilyFourierEstimatorOutput target 𝒽
              (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) sampleInputs).evaluate} ≤
      (1 / 10 : ℝ) := by
  let failure : Set
      (𝒽 → Fin (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) → {−1,1}^[n]) :=
    {sampleInputs |
      (ε.1 : ℝ) < relativeHammingDist target
        (finiteFamilyFourierEstimatorOutput target 𝒽
          (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) sampleInputs).evaluate}
  have hsubset : failure ⊆
      ⋃ S : 𝒽, finiteFamilyCoefficientBadSet target 𝒽 h𝒽 ε S := by
    intro sampleInputs hfailure
    by_contra hnotBad
    have hgood : ∀ S : 𝒽,
        sampleInputs ∉ finiteFamilyCoefficientBadSet target 𝒽 h𝒽 ε S := by
      intro S hbad
      exact hnotBad (Set.mem_iUnion.mpr ⟨S, hbad⟩)
    have hle := relativeHammingDist_finiteFamilyFourierEstimatorOutput_le_of_no_bad
      target 𝒽 h𝒽 ε sampleInputs hconcentration hgood
    exact (not_le_of_gt hfailure) hle
  change (LearningProgram.randomExampleMatrixInputLaw 𝒽
    (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toMeasure.real
      failure ≤ (1 / 10 : ℝ)
  exact (MeasureTheory.measureReal_mono hsubset).trans
    (measure_finiteFamily_someCoefficient_bad_le_one_tenth target 𝒽 h𝒽 ε)

/-- O'Donnell, Theorem 3.29, probabilistic conclusion for a nonempty concentrating family: the
scheduled random-example learner returns an `ε`-accurate sparse Fourier hypothesis with probability
at least `9/10`.  Equivalently, its failure probability is at most `1/10`. -/
theorem finiteFamilyFourierEstimatorProgram_failureProbability_le_one_tenth
    (target : BooleanFunction n) (𝒽 : Finset (Finset (Fin n)))
    (h𝒽 : 𝒽.Nonempty) (ε : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝒽 : Set (Finset (Fin n)))) :
    LearningProgram.eventProbability
        (finiteFamilyFourierEstimatorProgram 𝒽 h𝒽 ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  unfold LearningProgram.eventProbability
  rw [runWithCost_finiteFamilyFourierEstimatorProgram]
  rw [LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply]
  let failure : Set
      (𝒽 → Fin (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) → {−1,1}^[n]) :=
    {sampleInputs |
      (ε.1 : ℝ) < relativeHammingDist target
        (finiteFamilyFourierEstimatorOutput target 𝒽
          (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε) sampleInputs).evaluate}
  have hpreimage :
      LearningProgram.randomExampleMatrixOutcome target 𝒽
        (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)
        (𝒽.card * finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε * (n + 1))
        (finiteFamilyFourierEstimatorLabeledOutput 𝒽
          (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)) ⁻¹'
          {outcome |
            (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate} =
        failure := by
    rfl
  rw [hpreimage]
  have hmeasure :
      ((LearningProgram.randomExampleMatrixInputLaw 𝒽
        (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toOuterMeasure
          failure).toReal =
        (LearningProgram.randomExampleMatrixInputLaw 𝒽
          (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toMeasure.real
          failure := by
    exact congrArg ENNReal.toReal
      ((LearningProgram.randomExampleMatrixInputLaw 𝒽
        (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toMeasure_apply_eq_toOuterMeasure
          failure).symm
  rw [hmeasure]
  change (LearningProgram.randomExampleMatrixInputLaw 𝒽
    (finiteFamilySamplesPerCoefficient 𝒽 h𝒽 ε)).toMeasure.real
      failure ≤ (1 / 10 : ℝ)
  exact measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth
    target 𝒽 h𝒽 ε hconcentration

end FABL
