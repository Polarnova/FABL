/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevin.RestrictedWeights

/-!
# Restricted-weight estimation

Book items: Proposition 3.40.

The finite membership-query estimator and Proposition 3.40.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance glEstimatorSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance glEstimatorSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Finite query estimator -/

/-- Explicit local work charged for constructing two restricted inputs and evaluating the two
indexed monomials in one observation. -/
def restrictedFourierWeightObservationWork
    (J : Finset (Fin n)) (S : Finset J) : ℕ :=
  2 * n + 2 * S.card + 1

/-- One executable observation, using exactly two membership queries. -/
def restrictedFourierWeightObservationProgram
    (J : Finset (Fin n)) (S : Finset J) (z : FixedSignCube J)
    (y y' : FreeSignCube J) : LearningProgram n .queries ℚ :=
  .query (combineSignCube J y z) fun answer ↦
    .query (combineSignCube J y' z) fun answer' ↦
      .tick (restrictedFourierWeightObservationWork J S)
        (.pure (rationalRestrictedFourierWeightObservation J S z y y' answer answer'))

/-- Continuation-passing observation batch. Accumulating observations explicitly keeps every
query constructor visible while allowing both list output and empirical averaging to share the
same control flow. -/
def restrictedFourierWeightObservationBatchProgramWith {β : Type}
    (J : Finset (Fin n)) (S : Finset J) :
    (m : ℕ) → (Fin m → {−1,1}^[n]) → (Fin m → {−1,1}^[n]) →
      (Fin m → {−1,1}^[n]) → List ℚ →
        (List ℚ → LearningProgram n .queries β) → LearningProgram n .queries β
  | 0, _, _, _, observations, finish => finish observations.reverse
  | m + 1, zInputs, yInputs, y'Inputs, observations, finish =>
      let z := (signCubeSplitEquiv J (zInputs 0)).2
      let y := (signCubeSplitEquiv J (yInputs 0)).1
      let y' := (signCubeSplitEquiv J (y'Inputs 0)).1
      .query (combineSignCube J y z) fun answer ↦
        .query (combineSignCube J y' z) fun answer' ↦
          .tick (restrictedFourierWeightObservationWork J S)
            (restrictedFourierWeightObservationBatchProgramWith J S m
              (Fin.tail zInputs) (Fin.tail yInputs) (Fin.tail y'Inputs)
              (rationalRestrictedFourierWeightObservation J S z y y' answer answer' ::
                observations) finish)

/-- Sequentially execute the two-query observation for every coordinate of a finite sample
batch. -/
def restrictedFourierWeightObservationBatchProgram
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ)
    (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) :
    LearningProgram n .queries (List ℚ) :=
  restrictedFourierWeightObservationBatchProgramWith J S m
    zInputs yInputs y'Inputs [] .pure

/-- Accumulator form of the deterministic observation list. -/
def restrictedFourierWeightObservationBatchOutputAux
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) :
    (m : ℕ) → (Fin m → {−1,1}^[n]) → (Fin m → {−1,1}^[n]) →
      (Fin m → {−1,1}^[n]) → List ℚ → List ℚ
  | 0, _, _, _, observations => observations.reverse
  | m + 1, zInputs, yInputs, y'Inputs, observations =>
      let z := (signCubeSplitEquiv J (zInputs 0)).2
      let y := (signCubeSplitEquiv J (yInputs 0)).1
      let y' := (signCubeSplitEquiv J (y'Inputs 0)).1
      restrictedFourierWeightObservationBatchOutputAux target J S m
        (Fin.tail zInputs) (Fin.tail yInputs) (Fin.tail y'Inputs)
        (rationalRestrictedFourierWeightObservation J S z y y'
          (target (combineSignCube J y z)) (target (combineSignCube J y' z)) :: observations)

/-- Deterministic observation list produced from three input batches and a target oracle. -/
def restrictedFourierWeightObservationBatchOutput
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) : List ℚ :=
  restrictedFourierWeightObservationBatchOutputAux target J S m
    zInputs yInputs y'Inputs []

/-- The accumulator-form batch output is the existing prefix followed by the observations in
sample order. -/
theorem restrictedFourierWeightObservationBatchOutputAux_eq_append_ofFn
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n])
    (observations : List ℚ) :
    restrictedFourierWeightObservationBatchOutputAux target J S m
        zInputs yInputs y'Inputs observations =
      observations.reverse ++ List.ofFn fun i ↦
        rationalRestrictedFourierWeightObservationFromInputs target J S
          (zInputs i) (yInputs i) (y'Inputs i) := by
  induction m generalizing observations with
  | zero =>
      simp [restrictedFourierWeightObservationBatchOutputAux]
  | succ m ih =>
      rw [restrictedFourierWeightObservationBatchOutputAux]
      rw [ih]
      rw [List.ofFn_succ]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
        List.append_cancel_left_eq, List.cons.injEq, List.ofFn_inj]
      constructor
      · rfl
      · exact funext fun i ↦ rfl

/-- The deterministic batch output is exactly the list of pointwise executable observations. -/
theorem restrictedFourierWeightObservationBatchOutput_eq_ofFn
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) :
    restrictedFourierWeightObservationBatchOutput target J S m
        zInputs yInputs y'Inputs =
      List.ofFn fun i ↦
        rationalRestrictedFourierWeightObservationFromInputs target J S
          (zInputs i) (yInputs i) (y'Inputs i) := by
  simpa [restrictedFourierWeightObservationBatchOutput] using
    restrictedFourierWeightObservationBatchOutputAux_eq_append_ofFn
      target J S m zInputs yInputs y'Inputs []

/-- Rational empirical average of a finite observation list. -/
def empiricalRestrictedFourierWeight (m : ℕ) (observations : List ℚ) : ℚ :=
  observations.sum / m

/-- Proposition 3.40's finite query program. Three independent uniform full-cube batches are
projected to `z`, `y`, and `y'`; only the two combined inputs per observation are queried. -/
def restrictedFourierWeightEstimatorProgram
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ) :
    LearningProgram n .queries ℚ :=
  .uniformInputBatch m fun zInputs ↦
    .uniformInputBatch m fun yInputs ↦
      .uniformInputBatch m fun y'Inputs ↦
        restrictedFourierWeightObservationBatchProgramWith J S m
          zInputs yInputs y'Inputs [] fun observations ↦
            .tick (m + 1) (.pure (empiricalRestrictedFourierWeight m observations))

/-- Scheduled Proposition 3.40 estimator, reusing the computable positive rational scheduler
from Proposition 3.30. -/
def scheduledRestrictedFourierWeightEstimatorProgram
    (J : Finset (Fin n)) (S : Finset J)
    (ε δ : PositiveLearningParameter) : LearningProgram n .queries ℚ :=
  restrictedFourierWeightEstimatorProgram J S (fourierEstimatorSampleCount ε δ)

/-- Constructor-derived exact resource cost of the finite estimator. -/
def restrictedFourierWeightEstimatorCost
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ) : LearningCost :=
  ⟨0, 2 * m,
    3 * m * n + m * (2 + restrictedFourierWeightObservationWork J S) + (m + 1)⟩

/-- Deterministic estimator output associated with three sampled full-cube batches. -/
def restrictedFourierWeightEstimatorOutput
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) : ℚ :=
  empiricalRestrictedFourierWeight m
    (restrictedFourierWeightObservationBatchOutput target J S m
      zInputs yInputs y'Inputs)

/-- Real empirical mean corresponding to the executable rational estimator output. -/
noncomputable def realRestrictedFourierWeightEstimatorOutput
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) : ℝ :=
  (∑ i, restrictedFourierWeightObservationFromInputs target J S
    (zInputs i) (yInputs i) (y'Inputs i)) / m

/-- The executable output is the rational empirical mean of its pointwise observations. -/
theorem restrictedFourierWeightEstimatorOutput_eq_sum
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) :
    restrictedFourierWeightEstimatorOutput target J S m zInputs yInputs y'Inputs =
      (∑ i, rationalRestrictedFourierWeightObservationFromInputs target J S
        (zInputs i) (yInputs i) (y'Inputs i)) / m := by
  simp [restrictedFourierWeightEstimatorOutput, empiricalRestrictedFourierWeight,
    restrictedFourierWeightObservationBatchOutput_eq_ofFn, List.sum_ofFn]

/-- Casting the executable estimator output gives the corresponding real empirical mean. -/
theorem restrictedFourierWeightEstimatorOutput_cast
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) :
    (restrictedFourierWeightEstimatorOutput target J S m
      zInputs yInputs y'Inputs : ℝ) =
      realRestrictedFourierWeightEstimatorOutput target J S m
        zInputs yInputs y'Inputs := by
  simp [restrictedFourierWeightEstimatorOutput_eq_sum,
    realRestrictedFourierWeightEstimatorOutput,
    rationalRestrictedFourierWeightObservationFromInputs_cast]

/-- The three separately generated input batches inherit the same concentration bound. -/
theorem measure_restrictedFourierWeightEstimatorOutput_failure_le
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    {m : ℕ} (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (uniformPMF
      ((Fin m → {−1,1}^[n]) ×
        (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n]))).toMeasure.real
        {inputs |
          ε ≤ |realRestrictedFourierWeightEstimatorOutput target J S m
            inputs.1 inputs.2.1 inputs.2.2 -
              restrictedFourierWeight target.toReal J S|} ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  let e := restrictedFourierWeightBatchEquiv n m
  let failure : Set
      (Fin m → {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n]) :=
    {samples |
      ε ≤ |finiteUniformEmpiricalMean
        (restrictedFourierWeightTripleObservation target J S) samples -
          restrictedFourierWeight target.toReal J S|}
  have h := measure_restrictedFourierWeightTripleEmpiricalMean_failure_le
    target J S hm ε hε
  have hmap :
      (uniformPMF
        ((Fin m → {−1,1}^[n]) ×
          (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n]))).map e =
        uniformPMF
          (Fin m → {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n]) :=
    map_uniformPMF_equiv e
  change (uniformPMF
      (Fin m → {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n])).toMeasure.real
      failure ≤ _ at h
  rw [← hmap] at h
  have hmeasure :
      ((uniformPMF
        ((Fin m → {−1,1}^[n]) ×
          (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n]))).map e).toMeasure.real
          failure =
        (uniformPMF
          ((Fin m → {−1,1}^[n]) ×
            (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n]))).toMeasure.real
          (e ⁻¹' failure) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply e _ failure (measurable_of_finite e)
        (Set.toFinite failure).measurableSet)
  rw [hmeasure] at h
  simpa [e, failure, restrictedFourierWeightBatchEquiv,
    restrictedFourierWeightTripleObservation, finiteUniformEmpiricalMean,
    realRestrictedFourierWeightEstimatorOutput] using h

/-- Exact cost of the query-only observation batch, before uniform-input generation and final
averaging. -/
def restrictedFourierWeightObservationBatchCost
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ) : LearningCost :=
  ⟨0, 2 * m, m * (2 + restrictedFourierWeightObservationWork J S)⟩

/-- Exact law and cost of one two-query observation program. -/
theorem runWithCost_restrictedFourierWeightObservationProgram
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) (y y' : FreeSignCube J) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightObservationProgram J S z y y') =
      PMF.pure
        (rationalRestrictedFourierWeightObservation J S z y y'
          (target (combineSignCube J y z)) (target (combineSignCube J y' z)),
        ⟨0, 2, 2 + restrictedFourierWeightObservationWork J S⟩) := by
  unfold restrictedFourierWeightObservationProgram
  rw [LearningProgram.runWithCost, LearningProgram.runWithCost,
    LearningProgram.runWithCost, LearningProgram.runWithCost]
  rw [PMF.pure_map, PMF.pure_map, PMF.pure_map]
  simp only [LearningProgram.addOutcomeCost]
  congr 1
  congr 1
  change (⟨0, 2,
    1 + (1 + (restrictedFourierWeightObservationWork J S + 0))⟩ : LearningCost) = _
  simp
  omega

/-- Exact deterministic law of the accumulator-form query batch with a pure continuation. -/
theorem runWithCost_restrictedFourierWeightObservationBatchProgramWith_pure
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n])
    (observations : List ℚ) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightObservationBatchProgramWith J S m
          zInputs yInputs y'Inputs observations .pure) =
      PMF.pure
        (restrictedFourierWeightObservationBatchOutputAux target J S m
          zInputs yInputs y'Inputs observations,
        restrictedFourierWeightObservationBatchCost J S m) := by
  induction m generalizing observations with
  | zero =>
      rw [restrictedFourierWeightObservationBatchProgramWith,
        restrictedFourierWeightObservationBatchOutputAux,
        LearningProgram.runWithCost]
      congr 1
      congr 1
      change LearningCost.mk 0 0 0 =
        LearningCost.mk 0 (2 * 0) (0 * (2 + restrictedFourierWeightObservationWork J S))
      congr <;> simp
  | succ m ih =>
      rw [restrictedFourierWeightObservationBatchProgramWith,
        restrictedFourierWeightObservationBatchOutputAux]
      rw [LearningProgram.runWithCost, LearningProgram.runWithCost,
        LearningProgram.runWithCost,
        ih (Fin.tail zInputs) (Fin.tail yInputs) (Fin.tail y'Inputs)]
      rw [PMF.pure_map, PMF.pure_map, PMF.pure_map]
      simp only [LearningProgram.addOutcomeCost]
      congr 1
      congr 1
      change (
        ⟨0, 1 + (1 + (0 + (restrictedFourierWeightObservationBatchCost J S m).queries)),
          1 + (1 + (restrictedFourierWeightObservationWork J S +
            (restrictedFourierWeightObservationBatchCost J S m).work))⟩ : LearningCost) =
        restrictedFourierWeightObservationBatchCost J S (m + 1)
      simp [restrictedFourierWeightObservationBatchCost, Nat.add_mul]
      omega

/-- Exact deterministic law of the query-only observation batch. -/
theorem runWithCost_restrictedFourierWeightObservationBatchProgram
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n]) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightObservationBatchProgram J S m
          zInputs yInputs y'Inputs) =
      PMF.pure
        (restrictedFourierWeightObservationBatchOutput target J S m
          zInputs yInputs y'Inputs,
        restrictedFourierWeightObservationBatchCost J S m) := by
  exact runWithCost_restrictedFourierWeightObservationBatchProgramWith_pure
    target J S m zInputs yInputs y'Inputs []

/-- Exact deterministic law of an accumulator-form query batch followed by empirical averaging.
The averaging denominator is explicit so the induction can also describe a nonempty prefix. -/
theorem runWithCost_restrictedFourierWeightObservationBatchProgramWith_empirical
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (sampleCount m : ℕ) (zInputs yInputs y'Inputs : Fin m → {−1,1}^[n])
    (observations : List ℚ) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightObservationBatchProgramWith J S m
          zInputs yInputs y'Inputs observations fun outputs ↦
            .tick (sampleCount + 1)
              (.pure (empiricalRestrictedFourierWeight sampleCount outputs))) =
      PMF.pure
        (empiricalRestrictedFourierWeight sampleCount
          (restrictedFourierWeightObservationBatchOutputAux target J S m
            zInputs yInputs y'Inputs observations),
        ⟨0, 2 * m,
          m * (2 + restrictedFourierWeightObservationWork J S) + (sampleCount + 1)⟩) := by
  induction m generalizing observations with
  | zero =>
      rw [restrictedFourierWeightObservationBatchProgramWith,
        restrictedFourierWeightObservationBatchOutputAux,
        LearningProgram.runWithCost, LearningProgram.runWithCost]
      rw [PMF.pure_map]
      simp only [LearningProgram.addOutcomeCost]
      congr 1
      congr 1
      change LearningCost.mk 0 0 (sampleCount + 1) =
        LearningCost.mk 0 (2 * 0)
          (0 * (2 + restrictedFourierWeightObservationWork J S) + (sampleCount + 1))
      rw [LearningCost.mk.injEq]
      simp
  | succ m ih =>
      rw [restrictedFourierWeightObservationBatchProgramWith,
        restrictedFourierWeightObservationBatchOutputAux]
      rw [LearningProgram.runWithCost, LearningProgram.runWithCost,
        LearningProgram.runWithCost,
        ih (Fin.tail zInputs) (Fin.tail yInputs) (Fin.tail y'Inputs)]
      rw [PMF.pure_map, PMF.pure_map, PMF.pure_map]
      simp only [LearningProgram.addOutcomeCost]
      congr 1
      congr 1
      change LearningCost.mk 0
          (1 + (1 + (0 + 2 * m)))
          (1 + (1 + (restrictedFourierWeightObservationWork J S +
            (m * (2 + restrictedFourierWeightObservationWork J S) +
              (sampleCount + 1))))) =
        LearningCost.mk 0 (2 * (m + 1))
          ((m + 1) * (2 + restrictedFourierWeightObservationWork J S) +
            (sampleCount + 1))
      rw [LearningCost.mk.injEq]
      simp only [true_and]
      constructor
      · omega
      · rw [Nat.add_mul]
        omega

/-- Proposition 3.40 estimator's exact output law. The three nested binds are three independent
uniform full-cube batches; every leaf records the same constructor-derived cost. -/
theorem runWithCost_restrictedFourierWeightEstimatorProgram
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) (m : ℕ) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightEstimatorProgram J S m) =
      (uniformPMF (Fin m → {−1,1}^[n])).bind fun zInputs ↦
        (uniformPMF (Fin m → {−1,1}^[n])).bind fun yInputs ↦
          (uniformPMF (Fin m → {−1,1}^[n])).bind fun y'Inputs ↦
            PMF.pure
              (restrictedFourierWeightEstimatorOutput target J S m
                zInputs yInputs y'Inputs,
              restrictedFourierWeightEstimatorCost J S m) := by
  unfold restrictedFourierWeightEstimatorProgram
  simp only [LearningProgram.runWithCost,
    runWithCost_restrictedFourierWeightObservationBatchProgramWith_empirical,
    PMF.map_bind, PMF.pure_map, LearningProgram.addOutcomeCost]
  congr 1
  funext zInputs
  congr 1
  funext yInputs
  congr 1
  funext y'Inputs
  congr 1
  congr 1
  change LearningCost.mk 0 (0 + (0 + (0 + 2 * m)))
      (m * n + (m * n + (m * n +
        (m * (2 + restrictedFourierWeightObservationWork J S) + (m + 1))))) =
    LearningCost.mk 0 (2 * m)
      (3 * m * n + m * (2 + restrictedFourierWeightObservationWork J S) + (m + 1))
  rw [LearningCost.mk.injEq]
  simp only [zero_add, true_and]
  ring

/-- The estimator law is a pushforward of the uniform law on three input batches. -/
theorem runWithCost_restrictedFourierWeightEstimatorProgram_uniformProduct
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) (m : ℕ) :
    LearningProgram.runWithCost target
        (restrictedFourierWeightEstimatorProgram J S m) =
      (uniformPMF
        ((Fin m → {−1,1}^[n]) ×
          (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n]))).map fun inputs ↦
            (restrictedFourierWeightEstimatorOutput target J S m
              inputs.1 inputs.2.1 inputs.2.2,
            restrictedFourierWeightEstimatorCost J S m) := by
  rw [runWithCost_restrictedFourierWeightEstimatorProgram]
  have h := uniformPMF_bind_bind_map_triple
    (α := Fin m → {−1,1}^[n])
  have hmap := congrArg
    (PMF.map fun inputs ↦
      (restrictedFourierWeightEstimatorOutput target J S m
        inputs.1 inputs.2.1 inputs.2.2,
      restrictedFourierWeightEstimatorCost J S m)) h
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hmap
  convert hmap using 1
  rfl

/-- Every execution path of the finite restricted-weight estimator has the same exact cost. -/
theorem restrictedFourierWeightEstimatorProgram_cost_eq
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) (m : ℕ)
    (outcome : ℚ × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (restrictedFourierWeightEstimatorProgram J S m)).support) :
    outcome.2 = restrictedFourierWeightEstimatorCost J S m := by
  rw [runWithCost_restrictedFourierWeightEstimatorProgram] at houtcome
  rw [PMF.mem_support_bind_iff] at houtcome
  rcases houtcome with ⟨zInputs, _, houtcome⟩
  rw [PMF.mem_support_bind_iff] at houtcome
  rcases houtcome with ⟨yInputs, _, houtcome⟩
  rw [PMF.mem_support_bind_iff] at houtcome
  rcases houtcome with ⟨y'Inputs, _, houtcome⟩
  rw [PMF.mem_support_pure_iff] at houtcome
  subst outcome
  rfl

/-- Exact output law of the scheduled Proposition 3.40 estimator. -/
theorem runWithCost_scheduledRestrictedFourierWeightEstimatorProgram
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (ε δ : PositiveLearningParameter) :
    LearningProgram.runWithCost target
        (scheduledRestrictedFourierWeightEstimatorProgram J S ε δ) =
      (uniformPMF
        (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n])).bind fun zInputs ↦
        (uniformPMF
          (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n])).bind fun yInputs ↦
          (uniformPMF
            (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n])).bind fun y'Inputs ↦
            PMF.pure
              (restrictedFourierWeightEstimatorOutput target J S
                (fourierEstimatorSampleCount ε δ) zInputs yInputs y'Inputs,
              restrictedFourierWeightEstimatorCost J S
                (fourierEstimatorSampleCount ε δ)) := by
  exact runWithCost_restrictedFourierWeightEstimatorProgram target J S
    (fourierEstimatorSampleCount ε δ)

/-- The scheduled Proposition 3.40 program uses exactly twice the scheduler's sample count in
membership queries, independently of all random choices. -/
theorem scheduledRestrictedFourierWeightEstimatorProgram_queries_eq
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (ε δ : PositiveLearningParameter) (outcome : ℚ × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (scheduledRestrictedFourierWeightEstimatorProgram J S ε δ)).support) :
    outcome.2.queries = 2 * fourierEstimatorSampleCount ε δ := by
  have hcost := restrictedFourierWeightEstimatorProgram_cost_eq target J S
    (fourierEstimatorSampleCount ε δ) outcome houtcome
  rw [hcost]
  rfl

/-- The estimator's charged work is an explicit polynomial in the dimension, sample count, and
frequency size. -/
theorem restrictedFourierWeightEstimatorCost_work
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ) :
    (restrictedFourierWeightEstimatorCost J S m).work =
      3 * m * n + m * (2 + (2 * n + 2 * S.card + 1)) + (m + 1) := by
  rfl

/-- A dimension-only polynomial upper bound for the constructor-derived work charge. -/
theorem restrictedFourierWeightEstimatorCost_work_le
    (J : Finset (Fin n)) (S : Finset J) (m : ℕ) :
    (restrictedFourierWeightEstimatorCost J S m).work ≤
      8 * (m + 1) * (n + 1) := by
  have hS_le_J : S.card ≤ J.card := by
    simpa using Finset.card_le_univ S
  have hJ_le_n : J.card ≤ n := by
    simpa using Finset.card_le_univ J
  have hS_le_n : S.card ≤ n := hS_le_J.trans hJ_le_n
  rw [restrictedFourierWeightEstimatorCost_work]
  nlinarith

/-- O'Donnell, Proposition 3.40: the scheduled two-query-pair estimator approximates the
restricted Fourier weight within `ε`, except with probability at most `δ`. -/
theorem scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (ε δ : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (scheduledRestrictedFourierWeightEstimatorProgram J S ε δ) target
        (fun outcome ↦
          (ε.1 : ℝ) ≤
            |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|) ≤
      (δ.1 : ℝ) := by
  unfold LearningProgram.eventProbability
  change ((LearningProgram.runWithCost target
    (restrictedFourierWeightEstimatorProgram J S
      (fourierEstimatorSampleCount ε δ))).toOuterMeasure
        {outcome |
          (ε.1 : ℝ) ≤
            |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|}).toReal ≤ _
  rw [runWithCost_restrictedFourierWeightEstimatorProgram_uniformProduct]
  rw [PMF.toOuterMeasure_map_apply]
  let failure : Set
      ((Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
        (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
          (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n])) :=
    {inputs |
      (ε.1 : ℝ) ≤
        |realRestrictedFourierWeightEstimatorOutput target J S
          (fourierEstimatorSampleCount ε δ)
          inputs.1 inputs.2.1 inputs.2.2 -
            restrictedFourierWeight target.toReal J S|}
  have hpreimage :
      (fun inputs ↦
        (restrictedFourierWeightEstimatorOutput target J S
          (fourierEstimatorSampleCount ε δ)
          inputs.1 inputs.2.1 inputs.2.2,
        restrictedFourierWeightEstimatorCost J S
          (fourierEstimatorSampleCount ε δ))) ⁻¹'
        {outcome |
          (ε.1 : ℝ) ≤
            |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|} =
      failure := by
    ext inputs
    simp only [Set.mem_preimage, Set.mem_setOf_eq, failure]
    rw [restrictedFourierWeightEstimatorOutput_cast]
  rw [hpreimage]
  have hmeasure :
      ((uniformPMF
        ((Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
          (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
            (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]))).toOuterMeasure
          failure).toReal =
        (uniformPMF
          ((Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
            (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
              (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]))).toMeasure.real
            failure := by
    exact congrArg ENNReal.toReal
      ((uniformPMF
        ((Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
          (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]) ×
            (Fin (fourierEstimatorSampleCount ε δ) → {−1,1}^[n]))).toMeasure_apply_eq_toOuterMeasure
        failure).symm
  rw [hmeasure]
  exact (measure_restrictedFourierWeightEstimatorOutput_failure_le target J S
    (fourierEstimatorSampleCount_pos ε δ) (ε.1 : ℝ)
    (positiveLearningParameter_toReal_mem_Ioc ε).1.le).trans
      (two_mul_exp_neg_fourierEstimatorSampleCount_le ε δ)

/-- A binary-confidence envelope expressed only in Proposition 3.40's arbitrary positive real
failure parameter. The clipping at `1 / 2` matches the finite rational scheduler's domain. -/
noncomputable def realRestrictedFourierWeightFailureBits (δ : ℝ) : ℕ :=
  Nat.clog 2 (Nat.ceil (4 / min δ (1 / 2 : ℝ)))

/-- A rational confidence parameter above half of the clipped real parameter uses no more than the
real-parameter binary-confidence envelope. -/
theorem fourierEstimatorFailureBits_le_realRestrictedFourierWeightFailureBits
    (δ' : PositiveLearningParameter) (δ : ℝ) (hδ : 0 < δ)
    (hδ'Lower : min δ (1 / 2) / 2 < ((δ'.1 : ℚ) : ℝ)) :
    fourierEstimatorFailureBits δ' ≤ realRestrictedFourierWeightFailureBits δ := by
  unfold fourierEstimatorFailureBits realRestrictedFourierWeightFailureBits
  apply Nat.clog_mono_right
  rw [Nat.ceil_le]
  have hδclip : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  have hδ'pos : 0 < ((δ'.1 : ℚ) : ℝ) :=
    (div_pos hδclip (by norm_num)).trans hδ'Lower
  have hquotient :
      (2 : ℝ) / ((δ'.1 : ℚ) : ℝ) ≤ 4 / min δ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ hδ'pos hδclip]
    nlinarith
  have hreal :
      ((((2 : ℚ) / δ'.1 : ℚ) : ℝ)) ≤
        ((Nat.ceil (4 / min δ (1 / 2 : ℝ)) : ℕ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_ofNat]
    exact hquotient.trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- O'Donnell, Proposition 3.40 for arbitrary positive real accuracy and failure parameters.
The witnesses are finitely encoded positive rational scheduler parameters within a factor of two
of the clipped real inputs. -/
theorem exists_scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ ε' δ' : PositiveLearningParameter,
      min ε (1 / 2) / 2 < ((ε'.1 : ℚ) : ℝ) ∧
      ((ε'.1 : ℚ) : ℝ) < min ε (1 / 2) ∧
      min δ (1 / 2) / 2 < ((δ'.1 : ℚ) : ℝ) ∧
      ((δ'.1 : ℚ) : ℝ) < min δ (1 / 2) ∧
      LearningProgram.eventProbability
          (scheduledRestrictedFourierWeightEstimatorProgram J S ε' δ') target
          (fun outcome ↦
            ε ≤ |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|) ≤
        δ := by
  obtain ⟨ε', hε'Lower, hε'Upper⟩ :=
    exists_positiveLearningParameter_between_half ε hε
  obtain ⟨δ', hδ'Lower, hδ'Upper⟩ :=
    exists_positiveLearningParameter_between_half δ hδ
  refine ⟨ε', δ', hε'Lower, hε'Upper, hδ'Lower, hδ'Upper, ?_⟩
  calc
    LearningProgram.eventProbability
        (scheduledRestrictedFourierWeightEstimatorProgram J S ε' δ') target
        (fun outcome ↦
          ε ≤ |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|) ≤
      LearningProgram.eventProbability
        (scheduledRestrictedFourierWeightEstimatorProgram J S ε' δ') target
        (fun outcome ↦
          (ε'.1 : ℝ) ≤
            |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|) := by
        apply LearningProgram.eventProbability_mono
        intro outcome houtcome
        exact (hε'Upper.le.trans (min_le_left ε (1 / 2 : ℝ))).trans houtcome
    _ ≤ (δ'.1 : ℝ) :=
      scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le
        target J S ε' δ'
    _ ≤ δ :=
      (hδ'Upper.trans_le (min_le_left δ (1 / 2 : ℝ))).le

/-- Proposition 3.40's arbitrary-real scheduler with probability and pathwise resource bounds in
the original real parameters. With `E = min ε (1 / 2)` and
`B = realRestrictedFourierWeightFailureBits δ`, the selected rational scheduler uses at most
`16 * B / E²` samples; every path makes at most `32 * B / E²` membership queries and incurs at most
`256 * B * (n + 1) / E²` charged local work. -/
theorem exists_scheduledRestrictedFourierWeightEstimatorProgram_with_resource_bounds
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ ε' δ' : PositiveLearningParameter,
      min ε (1 / 2) / 2 < ((ε'.1 : ℚ) : ℝ) ∧
      ((ε'.1 : ℚ) : ℝ) < min ε (1 / 2) ∧
      min δ (1 / 2) / 2 < ((δ'.1 : ℚ) : ℝ) ∧
      ((δ'.1 : ℚ) : ℝ) < min δ (1 / 2) ∧
      LearningProgram.eventProbability
          (scheduledRestrictedFourierWeightEstimatorProgram J S ε' δ') target
          (fun outcome ↦
            ε ≤ |(outcome.1 : ℝ) - restrictedFourierWeight target.toReal J S|) ≤
        δ ∧
      fourierEstimatorFailureBits δ' ≤ realRestrictedFourierWeightFailureBits δ ∧
      (fourierEstimatorSampleCount ε' δ' : ℝ) ≤
        16 * realRestrictedFourierWeightFailureBits δ / min ε (1 / 2) ^ 2 ∧
      ∀ outcome,
        outcome ∈ (LearningProgram.runWithCost target
          (scheduledRestrictedFourierWeightEstimatorProgram J S ε' δ')).support →
        (outcome.2.queries : ℝ) ≤
            32 * realRestrictedFourierWeightFailureBits δ / min ε (1 / 2) ^ 2 ∧
          (outcome.2.work : ℝ) ≤
            256 * realRestrictedFourierWeightFailureBits δ * (n + 1) /
              min ε (1 / 2) ^ 2 := by
  obtain ⟨ε', δ', hε'Lower, hε'Upper, hδ'Lower, hδ'Upper, hfailure⟩ :=
    exists_scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le
      target J S ε δ hε hδ
  have hbits : fourierEstimatorFailureBits δ' ≤
      realRestrictedFourierWeightFailureBits δ :=
    fourierEstimatorFailureBits_le_realRestrictedFourierWeightFailureBits
      δ' δ hδ hδ'Lower
  have hsampleRat := fourierEstimatorSampleCount_cast_le ε' δ'
  have hsampleReal : (fourierEstimatorSampleCount ε' δ' : ℝ) ≤
      4 * (fourierEstimatorFailureBits δ' : ℝ) /
        (((ε'.1 : ℚ) : ℝ) ^ 2) := by
    exact_mod_cast hsampleRat
  have hsq : (min ε (1 / 2 : ℝ) / 2) ^ 2 ≤
      (((ε'.1 : ℚ) : ℝ) ^ 2) := by
    nlinarith [sq_nonneg
      (((ε'.1 : ℚ) : ℝ) - min ε (1 / 2 : ℝ) / 2)]
  have hsample : (fourierEstimatorSampleCount ε' δ' : ℝ) ≤
      16 * realRestrictedFourierWeightFailureBits δ / min ε (1 / 2) ^ 2 := by
    calc
      (fourierEstimatorSampleCount ε' δ' : ℝ) ≤
          4 * (fourierEstimatorFailureBits δ' : ℝ) /
            (((ε'.1 : ℚ) : ℝ) ^ 2) := hsampleReal
      _ ≤ 4 * (realRestrictedFourierWeightFailureBits δ : ℝ) /
            (((ε'.1 : ℚ) : ℝ) ^ 2) := by gcongr
      _ ≤ 4 * (realRestrictedFourierWeightFailureBits δ : ℝ) /
            (min ε (1 / 2 : ℝ) / 2) ^ 2 := by gcongr
      _ = 16 * realRestrictedFourierWeightFailureBits δ /
            min ε (1 / 2) ^ 2 := by ring
  refine ⟨ε', δ', hε'Lower, hε'Upper, hδ'Lower, hδ'Upper,
    hfailure, hbits, hsample, ?_⟩
  intro outcome houtcome
  let m := fourierEstimatorSampleCount ε' δ'
  have hsample : (m : ℝ) ≤
      16 * realRestrictedFourierWeightFailureBits δ / min ε (1 / 2) ^ 2 := by
    simpa [m] using hsample
  have hqueries :=
    scheduledRestrictedFourierWeightEstimatorProgram_queries_eq
      target J S ε' δ' outcome houtcome
  have hqueriesReal : (outcome.2.queries : ℝ) = 2 * (m : ℝ) := by
    exact_mod_cast hqueries
  have hcost := restrictedFourierWeightEstimatorProgram_cost_eq
    target J S m outcome (by
      simpa [scheduledRestrictedFourierWeightEstimatorProgram, m] using houtcome)
  have hworkNat := restrictedFourierWeightEstimatorCost_work_le J S m
  have hworkReal : (outcome.2.work : ℝ) ≤
      8 * ((m + 1 : ℕ) : ℝ) * (n + 1 : ℕ) := by
    rw [hcost]
    exact_mod_cast hworkNat
  have hmpos : 0 < m := fourierEstimatorSampleCount_pos ε' δ'
  have hmOne : m + 1 ≤ 2 * m := by omega
  constructor
  · calc
      (outcome.2.queries : ℝ) = 2 * (m : ℝ) := hqueriesReal
      _ ≤ 2 * (16 * realRestrictedFourierWeightFailureBits δ /
            min ε (1 / 2) ^ 2) := by gcongr
      _ = 32 * realRestrictedFourierWeightFailureBits δ /
            min ε (1 / 2) ^ 2 := by ring
  · calc
      (outcome.2.work : ℝ) ≤
          8 * ((m + 1 : ℕ) : ℝ) * (n + 1 : ℕ) := hworkReal
      _ ≤ 8 * (2 * (m : ℝ)) * (n + 1 : ℕ) := by
        gcongr
        exact_mod_cast hmOne
      _ ≤ 8 * (2 * (16 * realRestrictedFourierWeightFailureBits δ /
            min ε (1 / 2) ^ 2)) * (n + 1 : ℕ) := by gcongr
      _ = 256 * realRestrictedFourierWeightFailureBits δ * (n + 1) /
            min ε (1 / 2) ^ 2 := by
        push_cast
        ring

end FABL
