/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevinAlgorithm.Estimation

/-!
# The adaptive Goldreich-Levin run

Book items: Goldreich--Levin Theorem.

The charged adaptive controller, failure budget, and correctness invariant.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

structure GoldreichLevinQueryState (n : ℕ) where
  active : Option (Finset (Finset (Fin n)))
  trace : List (GoldreichLevinEstimateRecord n)
deriving DecidableEq

def GoldreichLevinEstimateTrace.HasFailure
    (trace : List (GoldreichLevinEstimateRecord n))
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) : Prop :=
  ∃ record ∈ trace, ¬ record.IsAccurate target τ

def GoldreichLevinQueryState.HasFailure
    (state : GoldreichLevinQueryState n)
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) : Prop :=
  GoldreichLevinEstimateTrace.HasFailure state.trace target τ

def GoldreichLevinQueryState.SatisfiesInvariant
    (state : GoldreichLevinQueryState n)
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) (k : ℕ) : Prop :=
  ∃ active,
    state.active = some active ∧
    GoldreichLevinActiveInvariant target τ k active ∧
    active.card ≤ goldreichLevinActiveCap τ

theorem goldreichLevinActiveCap_pos (τ : GoldreichLevinThreshold) :
    0 < goldreichLevinActiveCap τ := by
  rw [goldreichLevinActiveCap, Nat.ceil_pos]
  exact div_pos (by norm_num) (sq_pos_of_pos τ.2.1)

theorem goldreichLevinInitialQueryState_satisfiesInvariant
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    (GoldreichLevinQueryState.mk (some {∅}) []).SatisfiesInvariant target τ 0 := by
  refine ⟨{∅}, rfl, goldreichLevinActiveInvariant_zero target τ, ?_⟩
  simpa using goldreichLevinActiveCap_pos τ

theorem not_goldreichLevinEstimateTrace_hasFailure_iff
    (trace : List (GoldreichLevinEstimateRecord n))
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    ¬GoldreichLevinEstimateTrace.HasFailure trace target τ ↔
      GoldreichLevinEstimateTrace.IsAccurate trace target τ := by
  simp [GoldreichLevinEstimateTrace.HasFailure,
    GoldreichLevinEstimateTrace.IsAccurate]

def goldreichLevinQueryStep
    (τ : GoldreichLevinThreshold) (k : ℕ) (hk : k < n)
    (state : GoldreichLevinQueryState n)
    (records : List (GoldreichLevinEstimateRecord n)) :
    GoldreichLevinQueryState n :=
  let trace := state.trace ++ records
  let active := state.active.bind fun current ↦
    goldreichLevinRefine τ (goldreichLevinTraceEstimate trace) k hk current
  ⟨active, trace⟩

theorem goldreichLevinQueryStep_satisfiesInvariant
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (state : GoldreichLevinQueryState n)
    (records : List (GoldreichLevinEstimateRecord n))
    (hinvariant : state.SatisfiesInvariant target τ k)
    (haccurate : GoldreichLevinEstimateTrace.IsAccurate
      (state.trace ++ records) target τ)
    (hcover : GoldreichLevinEstimateTrace.Covers records
      (prefixCoordinates n (k + 1))
      (goldreichLevinCandidates (⟨k, hk⟩ : Fin n)
        hinvariant.choose)) :
    (goldreichLevinQueryStep τ k hk state records).SatisfiesInvariant
      target τ (k + 1) := by
  let active := hinvariant.choose
  have hstateActive : state.active = some active := hinvariant.choose_spec.1
  have hactiveInvariant : GoldreichLevinActiveInvariant target τ k active :=
    hinvariant.choose_spec.2.1
  let trace := state.trace ++ records
  let estimate := goldreichLevinTraceEstimate trace
  let candidates := goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active
  have hcoverTrace : GoldreichLevinEstimateTrace.Covers trace
      (prefixCoordinates n (k + 1)) candidates := by
    intro frequencyPrefix hfrequency
    obtain ⟨record, hrecord, hmatch⟩ := hcover frequencyPrefix hfrequency
    exact ⟨record, List.mem_append.mpr (Or.inr hrecord), hmatch⟩
  have hcandidatesSubset : ∀ S ∈ candidates,
      S ⊆ prefixCoordinates n (k + 1) :=
    goldreichLevinCandidates_subset_prefixCoordinates_succ
      hk active hactiveInvariant.1
  have hstageAccurate :
      IsAccurateGoldreichLevinStage target τ estimate k hk active := by
    intro frequencyPrefix hfrequency
    exact goldreichLevinTraceEstimate_accurate_of_mem trace target τ haccurate
      (prefixCoordinates n (k + 1)) candidates hcoverTrace
      frequencyPrefix hfrequency (hcandidatesSubset frequencyPrefix hfrequency)
  let retained := goldreichLevinRetained τ estimate k hk active
  have hrefine : goldreichLevinRefine τ estimate k hk active = some retained :=
    goldreichLevinRefine_eq_some_retained_of_stageAccurate
      target τ estimate k hk active hactiveInvariant hstageAccurate
  have hnextInvariant :
      GoldreichLevinActiveInvariant target τ (k + 1) retained :=
    goldreichLevinActiveInvariant_retained
      target τ estimate k hk active hactiveInvariant hstageAccurate
  have hnextCap : retained.card ≤ goldreichLevinActiveCap τ :=
    card_goldreichLevinRetained_le_activeCap_of_stageAccurate
      target τ estimate k hk active hactiveInvariant hstageAccurate
  refine ⟨retained, ?_, hnextInvariant, hnextCap⟩
  simp [goldreichLevinQueryStep, hstateActive, trace, estimate, retained, hrefine]

theorem goldreichLevinQueryStep_hasFailure_iff_of_not_hasFailure
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (state : GoldreichLevinQueryState n)
    (records : List (GoldreichLevinEstimateRecord n))
    (hstate : ¬ state.HasFailure target τ) :
    (goldreichLevinQueryStep τ k hk state records).HasFailure target τ ↔
      ∃ record ∈ records, ¬ record.IsAccurate target τ := by
  simp only [GoldreichLevinQueryState.HasFailure,
    GoldreichLevinEstimateTrace.HasFailure, goldreichLevinQueryStep,
    List.mem_append]
  constructor
  · rintro ⟨record, hrecord | hrecord, hbad⟩
    · exact False.elim (hstate ⟨record, hrecord, hbad⟩)
    · exact ⟨record, hrecord, hbad⟩
  · rintro ⟨record, hrecord, hbad⟩
    exact ⟨record, Or.inr hrecord, hbad⟩

/-- Conservative local-work charge for forming the next candidate family, searching the accumulated
trace, filtering candidates, and checking the active-family cap at one Goldreich--Levin stage. -/
def goldreichLevinControllerStepWork
    (n : ℕ) (τ : GoldreichLevinThreshold) : ℕ :=
  16 * (n + 1) ^ 2 * (goldreichLevinActiveCap τ + 1) ^ 2

/-- One charged Goldreich--Levin controller transition after the stage estimators have run. -/
noncomputable def goldreichLevinStageStepProgram
    (τ : GoldreichLevinThreshold) (k : ℕ) (hk : k < n)
    (state : GoldreichLevinQueryState n)
    (active : Finset (Finset (Fin n))) :
    LearningProgram n .queries (GoldreichLevinQueryState n) :=
  .tick (goldreichLevinControllerStepWork n τ)
    (LearningProgram.map
      (goldreichLevinQueryStep τ k hk state)
      (goldreichLevinStageEstimateProgram τ k hk active))

/-- Exact output law and cost increment of one charged Goldreich--Levin controller transition. -/
theorem runWithCost_goldreichLevinStageStepProgram
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (state : GoldreichLevinQueryState n)
    (active : Finset (Finset (Fin n))) :
    LearningProgram.runWithCost target
        (goldreichLevinStageStepProgram τ k hk state active) =
      (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).map fun outcome ↦
          (goldreichLevinQueryStep τ k hk state outcome.1,
            ⟨0, 0, goldreichLevinControllerStepWork n τ⟩ + outcome.2) := by
  unfold goldreichLevinStageStepProgram
  rw [LearningProgram.runWithCost, LearningProgram.runWithCost_map, PMF.map_comp]
  congr 1

/-- Charging the controller does not change the failure event produced by a stage transition. -/
theorem outerEventProbability_goldreichLevinStageStepProgram_failure
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k < n) (state : GoldreichLevinQueryState n)
    (active : Finset (Finset (Fin n)))
    (hstate : ¬ state.HasFailure target τ) :
    LearningProgram.outerEventProbability
        (goldreichLevinStageStepProgram τ k hk state active) target
        (fun outcome ↦ outcome.1.HasFailure target τ) =
      LearningProgram.outerEventProbability
        (goldreichLevinStageEstimateProgram τ k hk active) target
        (fun outcome ↦ ∃ record ∈ outcome.1, ¬ record.IsAccurate target τ) := by
  unfold LearningProgram.outerEventProbability
  rw [runWithCost_goldreichLevinStageStepProgram, PMF.toOuterMeasure_map_apply]
  congr 1
  ext outcome
  exact goldreichLevinQueryStep_hasFailure_iff_of_not_hasFailure
    target τ k hk state outcome.1 hstate

def goldreichLevinStageFailureBudget
    (n : ℕ) (τ : GoldreichLevinThreshold) : ℝ≥0∞ :=
  (2 * goldreichLevinActiveCap τ) •
    ENNReal.ofReal ((goldreichLevinCallConfidence n τ).1 : ℝ)

theorem goldreichLevinFailureBudget_rat_le_one_twentieth
    (n : ℕ) (τ : GoldreichLevinThreshold) :
    (n : ℚ) * (2 * goldreichLevinActiveCap τ : ℕ) *
        (goldreichLevinCallConfidence n τ).1 ≤ 1 / 20 := by
  let K := goldreichLevinActiveCap τ
  let denominator : ℚ := 40 * (n + 1) * (K + 1)
  have hdenominator : (0 : ℚ) < denominator := by
    dsimp [denominator]
    positivity
  have hn : (0 : ℚ) ≤ n := by positivity
  have hK : (0 : ℚ) ≤ K := by positivity
  have hproduct :
      (n : ℚ) * K ≤ ((n : ℚ) + 1) * ((K : ℚ) + 1) := by
    nlinarith [mul_nonneg hn hK]
  have hconfidence : (goldreichLevinCallConfidence n τ).1 = 1 / denominator := rfl
  rw [hconfidence]
  have hrearrange :
      (n : ℚ) * (2 * K : ℕ) * (1 / denominator) =
        (2 * (n : ℚ) * K) / denominator := by
    push_cast
    field_simp
  rw [hrearrange, div_le_iff₀ hdenominator]
  dsimp [denominator]
  nlinarith

noncomputable def goldreichLevinQueryRunUpTo
    (τ : GoldreichLevinThreshold) :
    (k : ℕ) → k ≤ n → LearningProgram n .queries (GoldreichLevinQueryState n)
  | 0, _ => .pure ⟨some {∅}, []⟩
  | k + 1, hk =>
      LearningProgram.bind
        (fun state ↦
          match state.active with
          | none => .pure state
          | some active =>
              if active.card ≤ goldreichLevinActiveCap τ then
                goldreichLevinStageStepProgram τ k
                  (Nat.lt_of_succ_le hk) state active
              else
                .pure ⟨none, state.trace⟩)
        (goldreichLevinQueryRunUpTo τ k
          (Nat.le_trans (Nat.le_succ k) hk))

theorem goldreichLevinQueryRunUpTo_outerFailureProbability_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    ∀ (k : ℕ) (hk : k ≤ n),
      LearningProgram.outerEventProbability
          (goldreichLevinQueryRunUpTo τ k hk) target
          (fun outcome ↦ outcome.1.HasFailure target τ) ≤
        k • goldreichLevinStageFailureBudget n τ := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [goldreichLevinQueryRunUpTo,
        LearningProgram.outerEventProbability, LearningProgram.runWithCost,
        GoldreichLevinQueryState.HasFailure,
        GoldreichLevinEstimateTrace.HasFailure]
  | succ k ih =>
      intro hk
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hklt : k < n := Nat.lt_of_succ_le hk
      rw [goldreichLevinQueryRunUpTo]
      rw [succ_nsmul]
      apply LearningProgram.outerEventProbability_bind_le_add target
        (goldreichLevinQueryRunUpTo τ k hk')
        (fun state ↦
          match state.active with
          | none => .pure state
          | some active =>
              if active.card ≤ goldreichLevinActiveCap τ then
                goldreichLevinStageStepProgram τ k hklt state active
              else
                .pure ⟨none, state.trace⟩)
        (fun state ↦ state.HasFailure target τ)
        (fun state ↦ state.HasFailure target τ)
        (k • goldreichLevinStageFailureBudget n τ)
        (goldreichLevinStageFailureBudget n τ)
      · exact ih hk'
      · intro state hstate
        cases hactive : state.active with
        | none =>
            simp [LearningProgram.outerEventProbability,
              LearningProgram.runWithCost, hstate]
        | some active =>
            simp only
            by_cases hcap : active.card ≤ goldreichLevinActiveCap τ
            · rw [if_pos hcap]
              rw [outerEventProbability_goldreichLevinStageStepProgram_failure
                target τ k hklt state active hstate]
              refine (goldreichLevinStageEstimateProgram_outerFailureProbability_le
                target τ k hklt active).trans ?_
              apply nsmul_le_nsmul_left (by simp)
              exact (card_goldreichLevinCandidates_le_two_mul
                (⟨k, hklt⟩ : Fin n) active).trans
                (Nat.mul_le_mul_left 2 hcap)
            · rw [if_neg hcap]
              have hnoFailure :
                  ¬∃ record ∈ state.trace, ¬ record.IsAccurate target τ := by
                rintro ⟨record, hrecord, hbad⟩
                exact hstate ⟨record, hrecord, hbad⟩
              simp [LearningProgram.outerEventProbability,
                LearningProgram.runWithCost,
                GoldreichLevinQueryState.HasFailure,
                GoldreichLevinEstimateTrace.HasFailure, hnoFailure]

theorem goldreichLevinQueryRunUpTo_costProjection_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (projection : LearningCost → ℕ) (hzero : projection 0 = 0)
    (hadd : ∀ first second,
      projection (first + second) = projection first + projection second)
    (candidateBound : ℕ)
    (hstage : ∀ (k : ℕ) (hk : k < n)
      (active : Finset (Finset (Fin n)))
      (outcome : List (GoldreichLevinEstimateRecord n) × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (goldreichLevinStageEstimateProgram τ k hk active)).support →
      projection outcome.2 ≤
        (goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active).card *
          candidateBound) :
    ∀ (k : ℕ) (hk : k ≤ n)
      (outcome : GoldreichLevinQueryState n × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (goldreichLevinQueryRunUpTo τ k hk)).support →
      projection outcome.2 ≤
        k * (projection ⟨0, 0, goldreichLevinControllerStepWork n τ⟩ +
          2 * goldreichLevinActiveCap τ * candidateBound) := by
  intro k
  induction k with
  | zero =>
      intro hk outcome houtcome
      simp only [goldreichLevinQueryRunUpTo, LearningProgram.runWithCost,
        PMF.mem_support_pure_iff] at houtcome
      subst outcome
      simp [hzero]
  | succ k ih =>
      intro hk outcome houtcome
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hklt : k < n := Nat.lt_of_succ_le hk
      rw [goldreichLevinQueryRunUpTo,
        LearningProgram.runWithCost_bind] at houtcome
      rw [PMF.mem_support_bind_iff] at houtcome
      obtain ⟨previousOutcome, hprevious, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨continuationOutcome, hcontinuation, rfl⟩ := houtcome
      have hpreviousBound := ih hk' previousOutcome hprevious
      have hcontinuationBound :
          projection continuationOutcome.2 ≤
            projection ⟨0, 0, goldreichLevinControllerStepWork n τ⟩ +
              2 * goldreichLevinActiveCap τ * candidateBound := by
        cases hactive : previousOutcome.1.active with
        | none =>
            rw [hactive] at hcontinuation
            rw [LearningProgram.runWithCost,
              PMF.mem_support_pure_iff] at hcontinuation
            subst continuationOutcome
            simp [hzero]
        | some active =>
            rw [hactive] at hcontinuation
            simp only at hcontinuation
            by_cases hcap : active.card ≤ goldreichLevinActiveCap τ
            · rw [if_pos hcap,
                runWithCost_goldreichLevinStageStepProgram] at hcontinuation
              rw [PMF.mem_support_map_iff] at hcontinuation
              obtain ⟨recordsOutcome, hrecords, rfl⟩ := hcontinuation
              have hstageBound := hstage k hklt active recordsOutcome hrecords
              have hcandidates :=
                (card_goldreichLevinCandidates_le_two_mul
                  (⟨k, hklt⟩ : Fin n) active).trans
                  (Nat.mul_le_mul_left 2 hcap)
              rw [hadd]
              nlinarith
            · rw [if_neg hcap, LearningProgram.runWithCost,
                PMF.mem_support_pure_iff] at hcontinuation
              subst continuationOutcome
              simp [hzero]
      simp only [LearningProgram.addOutcomeCost, hadd]
      nlinarith

theorem goldreichLevinQueryRunUpTo_queries_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k ≤ n)
    (outcome : GoldreichLevinQueryState n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (goldreichLevinQueryRunUpTo τ k hk)).support) :
    outcome.2.queries ≤
      k * (2 * goldreichLevinActiveCap τ *
        (2 * fourierEstimatorSampleCount
          (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ))) := by
  simpa using
    goldreichLevinQueryRunUpTo_costProjection_le target τ
      LearningCost.queries rfl (fun _ _ ↦ rfl)
      (2 * fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ))
      (goldreichLevinStageEstimateProgram_queries_le target τ)
      k hk outcome houtcome

theorem goldreichLevinQueryRunUpTo_work_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (hk : k ≤ n)
    (outcome : GoldreichLevinQueryState n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (goldreichLevinQueryRunUpTo τ k hk)).support) :
    outcome.2.work ≤
      k * (goldreichLevinControllerStepWork n τ +
        2 * goldreichLevinActiveCap τ *
          (8 * (fourierEstimatorSampleCount
            (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
              (n + 1))) := by
  exact goldreichLevinQueryRunUpTo_costProjection_le target τ
    LearningCost.work rfl (fun _ _ ↦ rfl)
    (8 * (fourierEstimatorSampleCount
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
        (n + 1))
    (goldreichLevinStageEstimateProgram_work_le target τ)
    k hk outcome houtcome

theorem goldreichLevinQueryRunUpTo_satisfiesInvariant_of_mem_support
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    ∀ (k : ℕ) (hk : k ≤ n)
      (outcome : GoldreichLevinQueryState n × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (goldreichLevinQueryRunUpTo τ k hk)).support →
      ¬outcome.1.HasFailure target τ →
      outcome.1.SatisfiesInvariant target τ k := by
  intro k
  induction k with
  | zero =>
      intro hk outcome houtcome hgood
      simp only [goldreichLevinQueryRunUpTo, LearningProgram.runWithCost,
        PMF.mem_support_pure_iff] at houtcome
      subst outcome
      exact goldreichLevinInitialQueryState_satisfiesInvariant target τ
  | succ k ih =>
      intro hk outcome houtcome hgood
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hklt : k < n := Nat.lt_of_succ_le hk
      rw [goldreichLevinQueryRunUpTo,
        LearningProgram.runWithCost_bind] at houtcome
      rw [PMF.mem_support_bind_iff] at houtcome
      obtain ⟨previousOutcome, hprevious, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨continuationOutcome, hcontinuation, rfl⟩ := houtcome
      let state := previousOutcome.1
      cases hactive : state.active with
      | none =>
          have hactive' : previousOutcome.1.active = none := by
            simpa [state] using hactive
          rw [hactive'] at hcontinuation
          rw [LearningProgram.runWithCost, PMF.mem_support_pure_iff] at hcontinuation
          subst continuationOutcome
          have hpreviousGood : ¬state.HasFailure target τ := by
            simpa [LearningProgram.addOutcomeCost, state] using hgood
          have hpreviousInvariant := ih hk' previousOutcome hprevious hpreviousGood
          obtain ⟨active, hstateActive, _⟩ := hpreviousInvariant
          rw [hactive] at hstateActive
          contradiction
      | some active =>
          have hactive' : previousOutcome.1.active = some active := by
            simpa [state] using hactive
          rw [hactive'] at hcontinuation
          simp only at hcontinuation
          by_cases hcap : active.card ≤ goldreichLevinActiveCap τ
          · rw [if_pos hcap,
              runWithCost_goldreichLevinStageStepProgram] at hcontinuation
            rw [PMF.mem_support_map_iff] at hcontinuation
            obtain ⟨recordsOutcome, hrecords, rfl⟩ := hcontinuation
            have htraceGood :
                ¬GoldreichLevinEstimateTrace.HasFailure
                  (state.trace ++ recordsOutcome.1) target τ := by
              simpa [LearningProgram.addOutcomeCost,
                GoldreichLevinQueryState.HasFailure, goldreichLevinQueryStep]
                using hgood
            have htraceAccurate : GoldreichLevinEstimateTrace.IsAccurate
                (state.trace ++ recordsOutcome.1) target τ :=
              (not_goldreichLevinEstimateTrace_hasFailure_iff
                (state.trace ++ recordsOutcome.1) target τ).mp htraceGood
            have hpreviousAccurate :
                GoldreichLevinEstimateTrace.IsAccurate state.trace target τ := by
              intro record hrecord
              exact htraceAccurate record (List.mem_append.mpr (Or.inl hrecord))
            have hpreviousGood : ¬state.HasFailure target τ := by
              exact (not_goldreichLevinEstimateTrace_hasFailure_iff
                state.trace target τ).mpr hpreviousAccurate
            have hpreviousInvariant := ih hk' previousOutcome hprevious hpreviousGood
            have hchosen : hpreviousInvariant.choose = active := by
              apply Option.some.inj
              exact hpreviousInvariant.choose_spec.1.symm.trans hactive
            have hcover : GoldreichLevinEstimateTrace.Covers recordsOutcome.1
                (prefixCoordinates n (k + 1))
                (goldreichLevinCandidates (⟨k, hklt⟩ : Fin n)
                  hpreviousInvariant.choose) := by
              simpa [hchosen] using
                goldreichLevinStageEstimateProgram_covers
                  target τ k hklt active recordsOutcome hrecords
            exact goldreichLevinQueryStep_satisfiesInvariant
              target τ k hklt state recordsOutcome.1 hpreviousInvariant
              htraceAccurate hcover
          · rw [if_neg hcap, LearningProgram.runWithCost,
              PMF.mem_support_pure_iff] at hcontinuation
            subst continuationOutcome
            have hpreviousGood : ¬state.HasFailure target τ := by
              simpa [LearningProgram.addOutcomeCost, state,
                GoldreichLevinQueryState.HasFailure] using hgood
            have hpreviousInvariant := ih hk' previousOutcome hprevious hpreviousGood
            have hchosen : hpreviousInvariant.choose = active := by
              apply Option.some.inj
              exact hpreviousInvariant.choose_spec.1.symm.trans hactive
            exact False.elim (hcap (hchosen ▸ hpreviousInvariant.choose_spec.2.2))

theorem goldreichLevinActiveInvariant_complete
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ n active)
    (U : Finset (Fin n))
    (hheavy : (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U|) :
    U ∈ active := by
  simpa [prefixFrequency_eq_self (n := n) le_rfl U] using
    hinvariant.2.1 U hheavy

theorem goldreichLevinActiveInvariant_sound
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ n active)
    (U : Finset (Fin n)) (hU : U ∈ active) :
    (τ.1 : ℝ) / 2 < |fourierCoeff target.toReal U| := by
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  cases n with
  | zero =>
      have hUempty : U = ∅ := by
        ext i
        exact Fin.elim0 i
      subst U
      have hparseval := sum_sq_fourierCoeff_eq_one target
      have hsq : fourierCoeff target.toReal ∅ ^ 2 = 1 := by
        simpa using hparseval
      have habs : |fourierCoeff target.toReal ∅| = 1 := by
        nlinarith [sq_abs (fourierCoeff target.toReal ∅),
          abs_nonneg (fourierCoeff target.toReal ∅)]
      have hτle : (τ.1 : ℝ) ≤ 1 := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr τ.2.2
        norm_num at hcast
        exact hcast
      rw [habs]
      nlinarith
  | succ k =>
      have hweight := hinvariant.2.2 (by omega) U hU
      rw [prefixCoordinates_eq_univ (n := k + 1) le_rfl,
        restrictedFourierWeight_univ_freeFrequencyPart] at hweight
      have hsquare : ((τ.1 : ℝ) / 2) ^ 2 <
          |fourierCoeff target.toReal U| ^ 2 := by
        rw [sq_abs]
        nlinarith
      exact (sq_lt_sq₀ (div_nonneg hτpos.le (by norm_num)) (abs_nonneg _)).mp hsquare

theorem goldreichLevinActiveInvariant_card_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ n active) :
    (active.card : ℝ) ≤ 4 / (τ.1 : ℝ) ^ 2 := by
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  have hterm : ∀ U ∈ active,
      (τ.1 : ℝ) ^ 2 / 4 ≤ fourierCoeff target.toReal U ^ 2 := by
    intro U hU
    have hsound := goldreichLevinActiveInvariant_sound
      target τ active hinvariant U hU
    have hsquare := (sq_le_sq₀
      (div_nonneg hτpos.le (by norm_num)) (abs_nonneg _)).2 hsound.le
    rw [sq_abs] at hsquare
    nlinarith
  have hsum :
      (∑ U ∈ active, fourierCoeff target.toReal U ^ 2) ≤ 1 := by
    calc
      (∑ U ∈ active, fourierCoeff target.toReal U ^ 2) ≤
          ∑ U : Finset (Fin n), fourierCoeff target.toReal U ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
          (fun U _ _ ↦ sq_nonneg (fourierCoeff target.toReal U))
      _ = 1 := sum_sq_fourierCoeff_eq_one target
  have hcardMul : (active.card : ℝ) * ((τ.1 : ℝ) ^ 2 / 4) ≤ 1 := by
    calc
      (active.card : ℝ) * ((τ.1 : ℝ) ^ 2 / 4) =
          ∑ _U ∈ active, ((τ.1 : ℝ) ^ 2 / 4) := by simp
      _ ≤ ∑ U ∈ active, fourierCoeff target.toReal U ^ 2 :=
        Finset.sum_le_sum hterm
      _ ≤ 1 := hsum
  rw [le_div_iff₀ (sq_pos_of_pos hτpos)]
  nlinarith

end FABL
