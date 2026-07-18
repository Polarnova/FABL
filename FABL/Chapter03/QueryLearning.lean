/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory

/-!
# Learning from membership queries

Book items: Exercise 3.39.

Uniform-input query simulations and the finite-family Fourier learner used in Section 3.5 of
O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance queryLearningSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance queryLearningSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- Query the target at every input in a fixed finite batch. -/
def queryInputBatchProgram :
    (m : ℕ) → (Fin m → {−1,1}^[n]) →
      LearningProgram n .queries (Fin m → ({−1,1}^[n] × Sign))
  | 0, _ => .pure fun i ↦ Fin.elim0 i
  | m + 1, inputs =>
      .query (inputs 0) fun answer ↦
        LearningProgram.map
          (Fin.cons (inputs 0, answer))
          (queryInputBatchProgram m (Fin.tail inputs))

/-- Querying a fixed batch returns exactly the target-labeled batch, at one query per input. -/
theorem runWithCost_queryInputBatchProgram
    (target : BooleanFunction n) (m : ℕ) (inputs : Fin m → {−1,1}^[n]) :
    LearningProgram.runWithCost target (queryInputBatchProgram m inputs) =
      PMF.pure
        ((fun i ↦ (inputs i, target (inputs i))),
          (⟨0, m, m⟩ : LearningCost)) := by
  induction m with
  | zero =>
      rw [queryInputBatchProgram, LearningProgram.runWithCost]
      congr 1
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · rfl
  | succ m ih =>
      rw [queryInputBatchProgram, LearningProgram.runWithCost,
        LearningProgram.runWithCost_map, ih, PMF.pure_map, PMF.pure_map]
      simp only [LearningProgram.addOutcomeCost]
      congr 1
      apply Prod.ext
      · funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rfl
        · rfl
      · apply LearningCost.toTriple_injective
        change (0 + 0, 1 + m, 1 + m) = (0, m + 1, m + 1)
        simp [Nat.add_comm]

/-- Generate a uniform input batch and label it using membership queries. -/
def queriedRandomExampleBatchProgram (m : ℕ) :
    LearningProgram n .queries (Fin m → ({−1,1}^[n] × Sign)) :=
  .uniformInputBatch m fun inputs ↦ queryInputBatchProgram m inputs

/-- The query simulation has the same uniform labeled output law as a random-example batch,
with one query per example and explicit input-generation work. -/
theorem runWithCost_queriedRandomExampleBatchProgram
    (target : BooleanFunction n) (m : ℕ) :
    LearningProgram.runWithCost target (queriedRandomExampleBatchProgram (n := n) m) =
      (uniformPMF (Fin m → {−1,1}^[n])).map fun inputs ↦
        ((fun i ↦ (inputs i, target (inputs i))),
          (⟨0, m, m * n + m⟩ : LearningCost)) := by
  unfold queriedRandomExampleBatchProgram
  simp only [LearningProgram.runWithCost, runWithCost_queryInputBatchProgram,
    PMF.pure_map, LearningProgram.addOutcomeCost]
  congr 1
  funext inputs
  simp only [Function.comp_apply]
  congr 1
  apply Prod.ext
  · rfl
  · apply LearningCost.toTriple_injective
    change (0 + 0, 0 + m, m * n + m) = (0, m, m * n + m)
    simp

/-- Enumerate a finite family-by-sample matrix with a single finite index. -/
noncomputable def finiteFamilyMatrixIndexEquiv
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    (𝓕 × Fin m) ≃ Fin (𝓕.card * m) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Reshape a linear batch into the matrix indexed by frequencies and sample positions. -/
noncomputable def finiteFamilyLinearToMatrixEquiv
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) (α : Type) :
    (Fin (𝓕.card * m) → α) ≃ (𝓕 → Fin m → α) :=
  (Equiv.arrowCongr (finiteFamilyMatrixIndexEquiv 𝓕 m).symm (Equiv.refl α)).trans
    (Equiv.curry 𝓕 (Fin m) α)

/-- Label a linearized finite-family sample matrix with membership queries and apply the existing
deterministic Fourier-estimator output function. -/
noncomputable def queriedFiniteFamilyFourierEstimatorFromInputs
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (inputs : Fin (𝓕.card * m) → {−1,1}^[n]) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  LearningProgram.bind
    (fun labeledInputs ↦
      .tick (𝓕.card * m * (n + 1))
        (.pure (finiteFamilyFourierEstimatorLabeledOutput 𝓕 m
          (finiteFamilyLinearToMatrixEquiv 𝓕 m ({−1,1}^[n] × Sign) labeledInputs))))
    (queryInputBatchProgram (𝓕.card * m) inputs)

/-- Deterministic output of the query simulation on a fixed linear input batch. -/
noncomputable def queriedFiniteFamilyFourierEstimatorOutput
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (inputs : Fin (𝓕.card * m) → {−1,1}^[n]) : SparseFourierHypothesis n :=
  finiteFamilyFourierEstimatorOutput target 𝓕 m
    (finiteFamilyLinearToMatrixEquiv 𝓕 m {−1,1}^[n] inputs)

/-- Exact cost after the uniform linear input batch has been generated. -/
def queriedFiniteFamilyFourierEstimatorInnerCost
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) : LearningCost :=
  ⟨0, 𝓕.card * m,
    𝓕.card * m + 𝓕.card * m * (n + 1)⟩

/-- On fixed inputs, the query program returns the existing deterministic finite-family output. -/
theorem runWithCost_queriedFiniteFamilyFourierEstimatorFromInputs
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ)
    (inputs : Fin (𝓕.card * m) → {−1,1}^[n]) :
    LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorFromInputs 𝓕 m inputs) =
      PMF.pure
        (queriedFiniteFamilyFourierEstimatorOutput target 𝓕 m inputs,
          queriedFiniteFamilyFourierEstimatorInnerCost (n := n) 𝓕 m) := by
  unfold queriedFiniteFamilyFourierEstimatorFromInputs
  rw [LearningProgram.runWithCost_bind, runWithCost_queryInputBatchProgram,
    PMF.pure_bind, LearningProgram.runWithCost, LearningProgram.runWithCost,
    PMF.pure_map, PMF.pure_map]
  simp only [LearningProgram.addOutcomeCost]
  congr 1

/-- The finite-family Fourier estimator implemented with uniform inputs and membership queries. -/
noncomputable def queriedFiniteFamilyFourierEstimatorProgramWithSamples
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  .uniformInputBatch (𝓕.card * m) fun inputs ↦
    queriedFiniteFamilyFourierEstimatorFromInputs 𝓕 m inputs

/-- Full exact cost of the query implementation, including uniform input generation. -/
def queriedFiniteFamilyFourierEstimatorCost
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) : LearningCost :=
  ⟨0, 𝓕.card * m,
    𝓕.card * m * n + 𝓕.card * m + 𝓕.card * m * (n + 1)⟩

/-- Exact output distribution and pathwise cost of the query implementation. -/
theorem runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithSamples 𝓕 m) =
      (uniformPMF (Fin (𝓕.card * m) → {−1,1}^[n])).map fun inputs ↦
        (queriedFiniteFamilyFourierEstimatorOutput target 𝓕 m inputs,
          queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕 m) := by
  unfold queriedFiniteFamilyFourierEstimatorProgramWithSamples
  simp only [LearningProgram.runWithCost,
    runWithCost_queriedFiniteFamilyFourierEstimatorFromInputs,
    PMF.pure_map, LearningProgram.addOutcomeCost]
  congr 1
  funext inputs
  simp only [Function.comp_apply]
  congr 1
  apply Prod.ext
  · rfl
  · apply LearningCost.toTriple_injective
    change
      (0 + 0, 0 + 𝓕.card * m,
        𝓕.card * m * n +
          (𝓕.card * m + 𝓕.card * m * (n + 1))) =
      (0, 𝓕.card * m,
        𝓕.card * m * n + 𝓕.card * m + 𝓕.card * m * (n + 1))
    simp [Nat.add_assoc]

/-- The linear uniform input law reshapes to the matrix law used by the random-example learner. -/
theorem map_uniformPMF_finiteFamilyLinearToMatrixEquiv
    (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    (uniformPMF (Fin (𝓕.card * m) → {−1,1}^[n])).map
        (finiteFamilyLinearToMatrixEquiv 𝓕 m {−1,1}^[n]) =
      uniformPMF (𝓕 → Fin m → {−1,1}^[n])
    := map_uniformPMF_equiv (finiteFamilyLinearToMatrixEquiv 𝓕 m {−1,1}^[n])

/-- Reshaping exposes exactly the uniform matrix law and the existing deterministic estimator
output, so all downstream concentration lemmas can be reused without a new analytic proof. -/
theorem runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples_uniformMatrix
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n))) (m : ℕ) :
    LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithSamples 𝓕 m) =
      (uniformPMF (𝓕 → Fin m → {−1,1}^[n])).map fun sampleInputs ↦
        (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs,
          queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕 m) := by
  rw [runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples]
  have h := congrArg
    (PMF.map fun sampleInputs : 𝓕 → Fin m → {−1,1}^[n] ↦
      (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs,
        queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕 m))
    (map_uniformPMF_finiteFamilyLinearToMatrixEquiv (n := n) 𝓕 m)
  rw [PMF.map_comp] at h
  simpa only [queriedFiniteFamilyFourierEstimatorOutput, Function.comp_def] using h

/-! ## Configurable-confidence finite-family query learner -/

/-- Divide a total failure budget equally among a nonempty finite coefficient family. -/
def finiteFamilyCoefficientConfidenceForTotal
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (δ : PositiveLearningParameter) : PositiveLearningParameter := by
  have hcard : 0 < 𝓕.card := Finset.card_pos.mpr h𝓕
  have hcardRat : (0 : ℚ) < 𝓕.card := by exact_mod_cast hcard
  refine ⟨δ.1 / 𝓕.card, div_pos δ.2.1 hcardRat, ?_⟩
  rw [div_le_iff₀ hcardRat]
  have hcardOne : (1 : ℚ) ≤ 𝓕.card := by exact_mod_cast hcard
  nlinarith [δ.2.2]

/-- Samples per coefficient for a prescribed total finite-family failure budget. -/
def queriedFiniteFamilySamplesPerCoefficient
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε δ : PositiveLearningParameter) : ℕ :=
  fourierEstimatorSampleCount (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
    (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ)

/-- The query-access finite-family learner with an explicit total failure budget. -/
noncomputable def queriedFiniteFamilyFourierEstimatorProgramWithConfidence
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε δ : PositiveLearningParameter) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  queriedFiniteFamilyFourierEstimatorProgramWithSamples 𝓕
    (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)

/-- A union bound over the finite family respects the caller's total failure budget. -/
theorem measure_finiteFamily_someCoefficientBadSetWithTotalConfidence_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)).toMeasure.real
        (⋃ S : 𝓕,
          finiteFamilyCoefficientBadSetWithParameters target 𝓕
            (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) S) ≤
      (δ.1 : ℝ) := by
  let accuracy := finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε
  let confidence := finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ
  let m := queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ
  calc
    (LearningProgram.randomExampleMatrixInputLaw 𝓕 m).toMeasure.real
        (⋃ S : 𝓕,
          finiteFamilyCoefficientBadSetWithParameters target 𝓕
            accuracy confidence S) ≤
        (𝓕.card : ℝ) * (confidence.1 : ℝ) :=
      measure_finiteFamily_someCoefficientBadSetWithParameters_le
        target 𝓕 accuracy confidence
    _ = (δ.1 : ℝ) := by
      have hcard : (0 : ℝ) < 𝓕.card := by
        exact_mod_cast Finset.card_pos.mpr h𝓕
      rw [show (confidence.1 : ℝ) = (δ.1 : ℝ) / 𝓕.card by
        norm_num [confidence, finiteFamilyCoefficientConfidenceForTotal]]
      field_simp

/-- If every queried empirical coefficient meets its allocated accuracy, the sparse hypothesis
has relative Hamming error at most `ε`. -/
theorem relativeHammingDist_queriedFiniteFamilyFourierEstimatorOutput_le_of_no_bad
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (sampleInputs :
      𝓕 → Fin (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ) → {−1,1}^[n])
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝓕 : Set (Finset (Fin n))))
    (hgood : ∀ S : 𝓕,
      sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target 𝓕
        (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
        (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) S) :
    relativeHammingDist target
      (finiteFamilyFourierEstimatorOutput target 𝓕
        (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)
        sampleInputs).evaluate ≤ (ε.1 : ℝ) := by
  change relativeHammingDist target
    (SparseFourierHypothesis.ofCoefficients 𝓕 fun S ↦
      empiricalFourierCoeff S.1 fun i ↦
        (sampleInputs S i, target (sampleInputs S i))).evaluate ≤ (ε.1 : ℝ)
  apply relativeHammingDist_sparseFourierHypothesis_of_coefficients_le
    target 𝓕 h𝓕 ε _ hconcentration
  intro S
  have hgoodS := hgood S
  change ¬((finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1 : ℝ) ≤
    |realEmpiricalFourierCoeff target S.1 (sampleInputs S) -
      fourierCoeff target.toReal S.1| at hgoodS
  rw [empiricalFourierCoeff_cast]
  exact (lt_of_not_ge hgoodS).le

/-- The deterministic query learner output fails with probability at most its total confidence
budget under the uniform matrix law. -/
theorem measure_queriedFiniteFamilyFourierEstimatorOutput_failure_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝓕 : Set (Finset (Fin n)))) :
    (LearningProgram.randomExampleMatrixInputLaw 𝓕
      (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)).toMeasure.real
        {sampleInputs |
          (ε.1 : ℝ) < relativeHammingDist target
            (finiteFamilyFourierEstimatorOutput target 𝓕
              (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)
              sampleInputs).evaluate} ≤
      (δ.1 : ℝ) := by
  let failure : Set
      (𝓕 → Fin (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ) →
        {−1,1}^[n]) :=
    {sampleInputs |
      (ε.1 : ℝ) < relativeHammingDist target
        (finiteFamilyFourierEstimatorOutput target 𝓕
          (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)
          sampleInputs).evaluate}
  have hsubset : failure ⊆
      ⋃ S : 𝓕, finiteFamilyCoefficientBadSetWithParameters target 𝓕
        (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
        (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) S := by
    intro sampleInputs hfailure
    by_contra hnotBad
    have hgood : ∀ S : 𝓕,
        sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target 𝓕
          (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
          (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) S := by
      intro S hbad
      exact hnotBad (Set.mem_iUnion.mpr ⟨S, hbad⟩)
    have hle :=
      relativeHammingDist_queriedFiniteFamilyFourierEstimatorOutput_le_of_no_bad
        target 𝓕 h𝓕 ε δ sampleInputs hconcentration hgood
    exact (not_le_of_gt hfailure) hle
  change (LearningProgram.randomExampleMatrixInputLaw 𝓕
    (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ)).toMeasure.real
      failure ≤ (δ.1 : ℝ)
  exact (MeasureTheory.measureReal_mono hsubset).trans
    (measure_finiteFamily_someCoefficientBadSetWithTotalConfidence_le
      target 𝓕 h𝓕 ε δ)

/-- The configurable query learner exceeds relative Hamming error `ε` with probability at most
its requested total failure budget. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_failureProbability_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝓕 : Set (Finset (Fin n)))) :
    LearningProgram.eventProbability
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)
        target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (δ.1 : ℝ) := by
  let m := queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ
  have hrun :
      LearningProgram.runWithCost target
          (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ) =
        (uniformPMF (𝓕 → Fin m → {−1,1}^[n])).map fun sampleInputs ↦
          (finiteFamilyFourierEstimatorOutput target 𝓕 m sampleInputs,
            queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕 m) := by
    simpa [queriedFiniteFamilyFourierEstimatorProgramWithConfidence, m] using
      runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples_uniformMatrix
        target 𝓕 m
  rw [LearningProgram.eventProbability_eq_toMeasure_real_of_runWithCost_eq_map
    (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)
    target (uniformPMF (𝓕 → Fin m → {−1,1}^[n]))
    (finiteFamilyFourierEstimatorOutput target 𝓕 m)
    (queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕 m) hrun
    (fun hypothesis ↦
      (ε.1 : ℝ) < relativeHammingDist target hypothesis.evaluate)]
  have hlaw :
      uniformPMF (𝓕 → Fin m → {−1,1}^[n]) =
        LearningProgram.randomExampleMatrixInputLaw 𝓕 m :=
    (LearningProgram.randomExampleMatrixInputLaw_eq_uniformPMF
      (n := n) 𝓕 m).symm
  rw [hlaw]
  simpa [m] using
    measure_queriedFiniteFamilyFourierEstimatorOutput_failure_le
      target 𝓕 h𝓕 ε δ hconcentration

/-- Every execution of the query learner has the explicit target-independent cost. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)).support) :
    outcome.2 = queriedFiniteFamilyFourierEstimatorCost (n := n) 𝓕
      (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ) := by
  rw [queriedFiniteFamilyFourierEstimatorProgramWithConfidence,
    runWithCost_queriedFiniteFamilyFourierEstimatorProgramWithSamples] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨sampleInputs, _, rfl⟩ := houtcome
  rfl

/-- Exact membership-query count of the configurable finite-family learner. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_eq
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)).support) :
    outcome.2.queries =
      𝓕.card * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ := by
  rw [queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq
    target 𝓕 h𝓕 ε δ outcome houtcome]
  rfl

/-- Exact local-work charge of the configurable finite-family learner. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_eq
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)).support) :
    outcome.2.work =
      𝓕.card * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ * n +
      𝓕.card * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ +
      𝓕.card * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ * (n + 1) := by
  rw [queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq
    target 𝓕 h𝓕 ε δ outcome houtcome]
  rfl

/-- Explicit polynomial/logarithmic scheduler bound for each queried coefficient row. -/
theorem queriedFiniteFamilySamplesPerCoefficient_cast_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (ε δ : PositiveLearningParameter) :
    (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ : ℚ) ≤
      16 * (𝓕.card : ℚ) ^ 2 *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by
  have hscheduler := fourierEstimatorSampleCount_cast_le
    (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
    (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ)
  calc
    (queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ : ℚ) ≤
        4 * fourierEstimatorFailureBits
          (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
          (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1 ^ 2 := by
      simpa [queriedFiniteFamilySamplesPerCoefficient] using hscheduler
    _ = 16 * (𝓕.card : ℚ) ^ 2 *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by
      have hcard : (𝓕.card : ℚ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr h𝓕).ne'
      have hε : ε.1 ≠ 0 := ne_of_gt ε.2.1
      rw [show (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε).1 =
        ε.1 / (2 * 𝓕.card) by norm_num [finiteFamilyCoefficientAccuracy]]
      field_simp
      ring

/-- Explicit polynomial/logarithmic query bound for the configurable learner. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_cast_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)).support) :
    (outcome.2.queries : ℚ) ≤
      16 * (𝓕.card : ℚ) ^ 3 *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by
  rw [queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_eq
    target 𝓕 h𝓕 ε δ outcome houtcome]
  push_cast
  have hsamples := queriedFiniteFamilySamplesPerCoefficient_cast_le 𝓕 h𝓕 ε δ
  have hcard : (0 : ℚ) ≤ 𝓕.card := by positivity
  calc
    (𝓕.card : ℚ) * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ ≤
        (𝓕.card : ℚ) *
          (16 * (𝓕.card : ℚ) ^ 2 *
            fourierEstimatorFailureBits
              (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
              ε.1 ^ 2) :=
      mul_le_mul_of_nonneg_left hsamples hcard
    _ = 16 * (𝓕.card : ℚ) ^ 3 *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by ring

/-- Explicit polynomial/logarithmic work bound for the configurable learner. -/
theorem queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_cast_le
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε δ : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence 𝓕 h𝓕 ε δ)).support) :
    (outcome.2.work : ℚ) ≤
      32 * (𝓕.card : ℚ) ^ 3 * (n + 1) *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by
  rw [queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_eq
    target 𝓕 h𝓕 ε δ outcome houtcome]
  push_cast
  have hsamples := queriedFiniteFamilySamplesPerCoefficient_cast_le 𝓕 h𝓕 ε δ
  have hcard : (0 : ℚ) ≤ 𝓕.card := by positivity
  have hn : (0 : ℚ) ≤ n + 1 := by positivity
  have hfactor : (0 : ℚ) ≤ 2 * (𝓕.card : ℚ) * (n + 1) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsamples hfactor
  calc
    (𝓕.card : ℚ) * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ * n +
        (𝓕.card : ℚ) * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ +
        (𝓕.card : ℚ) * queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ *
          (n + 1) =
        2 * (𝓕.card : ℚ) * (n + 1) *
          queriedFiniteFamilySamplesPerCoefficient 𝓕 h𝓕 ε δ := by ring
    _ ≤ 2 * (𝓕.card : ℚ) * (n + 1) *
        (16 * (𝓕.card : ℚ) ^ 2 *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
            ε.1 ^ 2) := hscaled
    _ = 32 * (𝓕.card : ℚ) ^ 3 * (n + 1) *
          fourierEstimatorFailureBits
            (finiteFamilyCoefficientConfidenceForTotal 𝓕 h𝓕 δ) /
        ε.1 ^ 2 := by ring

end FABL
