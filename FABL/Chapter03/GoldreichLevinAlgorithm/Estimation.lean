/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevin

/-!
# Goldreich-Levin stage estimation

Book item supported: Goldreich--Levin Theorem.

Finite prefix-estimation programs and their probability and resource bounds.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

def goldreichLevinWeightAccuracy
    (τ : GoldreichLevinThreshold) : PositiveLearningParameter := by
  refine ⟨τ.1 ^ 2 / 4, div_pos (sq_pos_of_pos τ.2.1) (by norm_num), ?_⟩
  have hτsq : τ.1 ^ 2 ≤ (1 : ℚ) := by
    have hproduct : (0 : ℚ) ≤ τ.1 * (1 - τ.1) :=
      mul_nonneg τ.2.1.le (sub_nonneg.mpr τ.2.2)
    nlinarith
  nlinarith

def goldreichLevinCallConfidence
    (n : ℕ) (τ : GoldreichLevinThreshold) : PositiveLearningParameter := by
  let denominator : ℚ :=
    40 * (n + 1) * (goldreichLevinActiveCap τ + 1)
  have hdenominator : (0 : ℚ) < denominator := by
    dsimp [denominator]
    positivity
  refine ⟨1 / denominator, div_pos zero_lt_one hdenominator, ?_⟩
  rw [div_le_iff₀ hdenominator]
  dsimp [denominator]
  have hn : (1 : ℚ) ≤ (n : ℚ) + 1 := by
    exact_mod_cast Nat.succ_pos n
  have hcap : (1 : ℚ) ≤ (goldreichLevinActiveCap τ : ℚ) + 1 := by
    exact_mod_cast Nat.succ_pos (goldreichLevinActiveCap τ)
  have hproduct :
      (1 : ℚ) ≤ ((n : ℚ) + 1) * ((goldreichLevinActiveCap τ : ℚ) + 1) :=
    by
      simpa using mul_le_mul hn hcap (by norm_num) (by positivity)
  nlinarith

structure GoldreichLevinEstimateRecord (n : ℕ) where
  coordinates : Finset (Fin n)
  frequencyPrefix : Finset (Fin n)
  estimate : ℚ
deriving DecidableEq

def GoldreichLevinEstimateRecord.key
    (record : GoldreichLevinEstimateRecord n) :
    Finset (Fin n) × Finset (Fin n) :=
  (record.coordinates, record.frequencyPrefix)

def GoldreichLevinEstimateRecord.Matches
    (record : GoldreichLevinEstimateRecord n)
    (J frequencyPrefix : Finset (Fin n)) : Prop :=
  record.coordinates = J ∧ record.frequencyPrefix = frequencyPrefix

instance (record : GoldreichLevinEstimateRecord n) (J frequencyPrefix : Finset (Fin n)) :
    Decidable (record.Matches J frequencyPrefix) := by
  unfold GoldreichLevinEstimateRecord.Matches
  infer_instance

def GoldreichLevinEstimateRecord.IsAccurate
    (record : GoldreichLevinEstimateRecord n)
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) : Prop :=
  |(record.estimate : ℝ) -
      restrictedFourierWeight target.toReal record.coordinates
        (freeFrequencyPart record.coordinates record.frequencyPrefix)| <
    (τ.1 : ℝ) ^ 2 / 4

def goldreichLevinTraceEstimate
    (trace : List (GoldreichLevinEstimateRecord n)) :
    RestrictedFourierWeightEstimate n :=
  fun J S ↦
    match trace.find? fun record ↦ decide (record.Matches J (liftFreeFrequency S)) with
    | some record => record.estimate
    | none => 0

def GoldreichLevinEstimateTrace.IsAccurate
    (trace : List (GoldreichLevinEstimateRecord n))
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) : Prop :=
  ∀ record ∈ trace, record.IsAccurate target τ

def GoldreichLevinEstimateTrace.Covers
    (trace : List (GoldreichLevinEstimateRecord n))
    (J : Finset (Fin n)) (frequencies : Finset (Finset (Fin n))) : Prop :=
  ∀ frequencyPrefix ∈ frequencies,
    ∃ record ∈ trace, record.Matches J frequencyPrefix

theorem goldreichLevinTraceEstimate_accurate_of_mem
    (trace : List (GoldreichLevinEstimateRecord n))
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (haccurate : GoldreichLevinEstimateTrace.IsAccurate trace target τ)
    (J : Finset (Fin n)) (frequencies : Finset (Finset (Fin n)))
    (hcover : GoldreichLevinEstimateTrace.Covers trace J frequencies)
    (frequencyPrefix : Finset (Fin n)) (hfrequency : frequencyPrefix ∈ frequencies)
    (hsubset : frequencyPrefix ⊆ J) :
    |((goldreichLevinTraceEstimate trace J (freeFrequencyPart J frequencyPrefix) : ℚ) : ℝ) -
        restrictedFourierWeight target.toReal J (freeFrequencyPart J frequencyPrefix)| <
      (τ.1 : ℝ) ^ 2 / 4 := by
  obtain ⟨record, hrecordTrace, hrecordMatch⟩ := hcover frequencyPrefix hfrequency
  unfold goldreichLevinTraceEstimate
  rw [liftFreeFrequency_freeFrequencyPart_eq_of_subset J frequencyPrefix hsubset]
  cases hfind : trace.find? fun candidate ↦
      decide (candidate.Matches J frequencyPrefix) with
  | none =>
      have hnone := (List.find?_eq_none.mp hfind) record hrecordTrace
      exact False.elim (hnone (by simpa using hrecordMatch))
  | some found =>
      have hfoundTrace : found ∈ trace := List.mem_of_find?_eq_some hfind
      have hfoundMatch : found.Matches J frequencyPrefix := by
        have := List.find?_some hfind
        simpa using this
      have hfoundAccurate := haccurate found hfoundTrace
      rcases hfoundMatch with ⟨rfl, hprefix⟩
      simpa [GoldreichLevinEstimateRecord.IsAccurate, hprefix] using hfoundAccurate

noncomputable def goldreichLevinCandidateEstimateProgram
    (τ : GoldreichLevinThreshold) (J : Finset (Fin n))
    (frequencyPrefix : Finset (Fin n)) :
    LearningProgram n .queries (GoldreichLevinEstimateRecord n) :=
  LearningProgram.map
    (fun estimate ↦ ⟨J, frequencyPrefix, estimate⟩)
    (scheduledRestrictedFourierWeightEstimatorProgram J
      (freeFrequencyPart J frequencyPrefix)
      (goldreichLevinWeightAccuracy τ)
      (goldreichLevinCallConfidence n τ))

theorem goldreichLevinCandidateEstimateProgram_key
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (key : Finset (Fin n) × Finset (Fin n))
    (outcome : GoldreichLevinEstimateRecord n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinCandidateEstimateProgram τ key.1 key.2)).support) :
    outcome.1.key = key := by
  rw [goldreichLevinCandidateEstimateProgram,
    LearningProgram.runWithCost_map] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨estimateOutcome, _, rfl⟩ := houtcome
  rfl

theorem goldreichLevinCandidateEstimateProgram_failureProbability_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (J frequencyPrefix : Finset (Fin n)) :
    LearningProgram.eventProbability
        (goldreichLevinCandidateEstimateProgram τ J frequencyPrefix) target
        (fun outcome ↦ ¬ outcome.1.IsAccurate target τ) ≤
      ((goldreichLevinCallConfidence n τ).1 : ℝ) := by
  unfold LearningProgram.eventProbability
  rw [goldreichLevinCandidateEstimateProgram,
    LearningProgram.runWithCost_map, PMF.toOuterMeasure_map_apply]
  have hpreimage :
      (fun outcome : ℚ × LearningCost ↦
        (GoldreichLevinEstimateRecord.mk J frequencyPrefix outcome.1, outcome.2)) ⁻¹'
          {outcome | ¬ outcome.1.IsAccurate target τ} =
        {outcome |
          (((goldreichLevinWeightAccuracy τ).1 : ℚ) : ℝ) ≤
            |(outcome.1 : ℝ) -
              restrictedFourierWeight target.toReal J
                (freeFrequencyPart J frequencyPrefix)|} := by
    ext outcome
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    unfold GoldreichLevinEstimateRecord.IsAccurate
    rw [not_lt]
    norm_num [goldreichLevinWeightAccuracy]
  rw [hpreimage]
  exact scheduledRestrictedFourierWeightEstimatorProgram_failureProbability_le
    target J (freeFrequencyPart J frequencyPrefix)
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)

theorem goldreichLevinCandidateEstimateProgram_queries_eq
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (J frequencyPrefix : Finset (Fin n))
    (outcome : GoldreichLevinEstimateRecord n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinCandidateEstimateProgram τ J frequencyPrefix)).support) :
    outcome.2.queries =
      2 * fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) := by
  rw [goldreichLevinCandidateEstimateProgram,
    LearningProgram.runWithCost_map] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨estimateOutcome, hestimate, rfl⟩ := houtcome
  exact scheduledRestrictedFourierWeightEstimatorProgram_queries_eq
    target J (freeFrequencyPart J frequencyPrefix)
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
      estimateOutcome hestimate

theorem goldreichLevinCandidateEstimateProgram_work_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (J frequencyPrefix : Finset (Fin n))
    (outcome : GoldreichLevinEstimateRecord n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinCandidateEstimateProgram τ J frequencyPrefix)).support) :
    outcome.2.work ≤
      8 * (fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
          (n + 1) := by
  rw [goldreichLevinCandidateEstimateProgram,
    LearningProgram.runWithCost_map] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨estimateOutcome, hestimate, rfl⟩ := houtcome
  let m := fourierEstimatorSampleCount
    (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
  have hcost := restrictedFourierWeightEstimatorProgram_cost_eq
    target J (freeFrequencyPart J frequencyPrefix) m estimateOutcome (by
      simpa [scheduledRestrictedFourierWeightEstimatorProgram, m] using hestimate)
  rw [hcost]
  exact restrictedFourierWeightEstimatorCost_work_le
    J (freeFrequencyPart J frequencyPrefix) m

noncomputable def goldreichLevinStageEstimateProgram
    (τ : GoldreichLevinThreshold) (k : ℕ) (hk : k < n)
    (active : Finset (Finset (Fin n))) :
    LearningProgram n .queries (List (GoldreichLevinEstimateRecord n)) :=
  let J := prefixCoordinates n (k + 1)
  let candidates := goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active
  let keys := candidates.toList.map fun frequencyPrefix ↦ (J, frequencyPrefix)
  LearningProgram.sequence
    (keys.map fun key ↦
      goldreichLevinCandidateEstimateProgram τ key.1 key.2)

theorem goldreichLevinStageEstimateProgram_output_keys
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (outcome : List (GoldreichLevinEstimateRecord n) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).support) :
    outcome.1.map GoldreichLevinEstimateRecord.key =
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).toList.map
        (fun frequencyPrefix ↦
          (prefixCoordinates n (k + 1), frequencyPrefix)) := by
  unfold goldreichLevinStageEstimateProgram at houtcome
  exact LearningProgram.map_output_eq_of_mem_support_sequence
    target
    (fun key ↦ goldreichLevinCandidateEstimateProgram τ key.1 key.2)
    GoldreichLevinEstimateRecord.key
    (fun key outcome h ↦
      goldreichLevinCandidateEstimateProgram_key target τ key outcome h)
    ((goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).toList.map
      fun frequencyPrefix ↦
        (prefixCoordinates n (k + 1), frequencyPrefix))
    outcome houtcome

theorem goldreichLevinStageEstimateProgram_covers
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (outcome : List (GoldreichLevinEstimateRecord n) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).support) :
    GoldreichLevinEstimateTrace.Covers outcome.1
      (prefixCoordinates n (k + 1))
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active) := by
  intro frequencyPrefix hfrequency
  have hkeyMem :
      (prefixCoordinates n (k + 1), frequencyPrefix) ∈
        outcome.1.map GoldreichLevinEstimateRecord.key := by
    rw [goldreichLevinStageEstimateProgram_output_keys
      target τ k hk active outcome houtcome]
    simp [hfrequency]
  rw [List.mem_map] at hkeyMem
  obtain ⟨record, hrecord, hkey⟩ := hkeyMem
  refine ⟨record, hrecord, ?_⟩
  simpa [GoldreichLevinEstimateRecord.key,
    GoldreichLevinEstimateRecord.Matches] using hkey

theorem goldreichLevinStageEstimateProgram_queries_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (outcome : List (GoldreichLevinEstimateRecord n) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).support) :
    outcome.2.queries ≤
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).card *
        (2 * fourierEstimatorSampleCount
          (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)) := by
  unfold goldreichLevinStageEstimateProgram at houtcome
  let keys :=
    (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).toList.map
      (fun frequencyPrefix ↦
        (prefixCoordinates n (k + 1), frequencyPrefix))
  have hbound := LearningProgram.costProjection_le_of_mem_support_sequence
    target LearningCost.queries rfl (fun _ _ ↦ rfl)
      (2 * fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ))
      (keys.map fun key ↦ goldreichLevinCandidateEstimateProgram τ key.1 key.2)
      outcome
      (by
        intro program hprogram
        rw [List.mem_map] at hprogram
        obtain ⟨key, hkey, rfl⟩ := hprogram
        intro componentOutcome hcomponent
        exact (goldreichLevinCandidateEstimateProgram_queries_eq
          target τ key.1 key.2 componentOutcome hcomponent).le)
      (by simpa [keys] using houtcome)
  simpa [keys] using hbound

theorem goldreichLevinStageEstimateProgram_work_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (outcome : List (GoldreichLevinEstimateRecord n) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).support) :
    outcome.2.work ≤
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).card *
        (8 * (fourierEstimatorSampleCount
          (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
            (n + 1)) := by
  unfold goldreichLevinStageEstimateProgram at houtcome
  let keys :=
    (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).toList.map
      (fun frequencyPrefix ↦
        (prefixCoordinates n (k + 1), frequencyPrefix))
  have hbound := LearningProgram.costProjection_le_of_mem_support_sequence
    target LearningCost.work rfl (fun _ _ ↦ rfl)
      (8 * (fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
          (n + 1))
      (keys.map fun key ↦ goldreichLevinCandidateEstimateProgram τ key.1 key.2)
      outcome
      (by
        intro program hprogram
        rw [List.mem_map] at hprogram
        obtain ⟨key, hkey, rfl⟩ := hprogram
        intro componentOutcome hcomponent
        exact goldreichLevinCandidateEstimateProgram_work_le
          target τ key.1 key.2 componentOutcome hcomponent)
      (by simpa [keys] using houtcome)
  simpa [keys] using hbound

theorem goldreichLevinCandidateEstimateProgram_outerFailureProbability_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (J frequencyPrefix : Finset (Fin n)) :
    LearningProgram.outerEventProbability
        (goldreichLevinCandidateEstimateProgram τ J frequencyPrefix) target
        (fun outcome ↦ ¬ outcome.1.IsAccurate target τ) ≤
      ENNReal.ofReal ((goldreichLevinCallConfidence n τ).1 : ℝ) := by
  apply (ENNReal.le_ofReal_iff_toReal_le
    (LearningProgram.outerEventProbability_ne_top
      (goldreichLevinCandidateEstimateProgram τ J frequencyPrefix) target
      (fun outcome ↦ ¬ outcome.1.IsAccurate target τ))
    (Rat.cast_nonneg.mpr (goldreichLevinCallConfidence n τ).2.1.le)).2
  simpa only [LearningProgram.outerEventProbability_toReal] using
    goldreichLevinCandidateEstimateProgram_failureProbability_le
      target τ J frequencyPrefix

theorem goldreichLevinStageEstimateProgram_outerFailureProbability_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n))) :
    LearningProgram.outerEventProbability
        (goldreichLevinStageEstimateProgram τ k hk active) target
        (fun outcome ↦ ∃ record ∈ outcome.1, ¬ record.IsAccurate target τ) ≤
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).card •
        ENNReal.ofReal ((goldreichLevinCallConfidence n τ).1 : ℝ) := by
  unfold goldreichLevinStageEstimateProgram
  simpa only [List.length_map, Finset.length_toList] using
    LearningProgram.outerEventProbability_sequence_exists_le_nsmul
      target (fun record : GoldreichLevinEstimateRecord n ↦
        ¬ record.IsAccurate target τ)
      (ENNReal.ofReal ((goldreichLevinCallConfidence n τ).1 : ℝ))
      (((goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).toList.map
          (fun frequencyPrefix ↦
            (prefixCoordinates n (k + 1), frequencyPrefix))).map
        (fun key ↦ goldreichLevinCandidateEstimateProgram τ key.1 key.2))
      (by
        intro program hprogram
        rw [List.mem_map] at hprogram
        obtain ⟨key, hkey, rfl⟩ := hprogram
        exact goldreichLevinCandidateEstimateProgram_outerFailureProbability_le
          target τ key.1 key.2)

end FABL
