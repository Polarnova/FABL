/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevinAlgorithm.Adaptive

/-!
# Goldreich-Levin resource closure

Book items: Goldreich--Levin Theorem.

Target-independent query and charged-work bounds and the final correctness theorem.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

def GoldreichLevinQueryState.IsCorrectOutput
    (state : GoldreichLevinQueryState n)
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) : Prop :=
  ∃ active,
    state.active = some active ∧
    (∀ U : Finset (Fin n),
      (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U| → U ∈ active) ∧
    (∀ U ∈ active, (τ.1 : ℝ) / 2 < |fourierCoeff target.toReal U|) ∧
    active.card ≤ goldreichLevinActiveCap τ ∧
    (active.card : ℝ) ≤ 4 / (τ.1 : ℝ) ^ 2

/-- Target-independent membership-query budget of the finite Goldreich--Levin oracle program. -/
def goldreichLevinQueryBudget
    (n : ℕ) (τ : GoldreichLevinThreshold) : ℕ :=
  n * (2 * goldreichLevinActiveCap τ *
    (2 * fourierEstimatorSampleCount
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)))

/-- Target-independent charged-work budget of the finite Goldreich--Levin oracle program. -/
def goldreichLevinWorkBudget
    (n : ℕ) (τ : GoldreichLevinThreshold) : ℕ :=
  n * (goldreichLevinControllerStepWork n τ +
    2 * goldreichLevinActiveCap τ *
      (8 * (fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) + 1) *
          (n + 1)))

/-- The active-family ceiling is at most `8 / τ²`. -/
theorem goldreichLevinActiveCap_cast_le (τ : GoldreichLevinThreshold) :
    (goldreichLevinActiveCap τ : ℚ) ≤ 8 / τ.1 ^ 2 := by
  have hτsq : τ.1 ^ 2 ≤ (1 : ℚ) := by
    nlinarith [mul_nonneg τ.2.1.le (sub_nonneg.mpr τ.2.2)]
  have hhalf : (1 / 2 : ℚ) ≤ 4 / τ.1 ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos τ.2.1)]
    nlinarith
  unfold goldreichLevinActiveCap
  calc
    (Nat.ceil ((4 : ℚ) / τ.1 ^ 2) : ℚ) ≤
        2 * ((4 : ℚ) / τ.1 ^ 2) := by
      apply Nat.ceil_le_two_mul
      norm_num at hhalf ⊢
      exact hhalf
    _ = 8 / τ.1 ^ 2 := by ring

/-- The active-family ceiling plus one is at most `9 / τ²`. -/
theorem goldreichLevinActiveCap_add_one_cast_le (τ : GoldreichLevinThreshold) :
    ((goldreichLevinActiveCap τ + 1 : ℕ) : ℚ) ≤ 9 / τ.1 ^ 2 := by
  have hcap := goldreichLevinActiveCap_cast_le τ
  have hτsqPos : (0 : ℚ) < τ.1 ^ 2 := sq_pos_of_pos τ.2.1
  have hτsq : τ.1 ^ 2 ≤ (1 : ℚ) := by
    nlinarith [mul_nonneg τ.2.1.le (sub_nonneg.mpr τ.2.2)]
  have hone : (1 : ℚ) ≤ 1 / τ.1 ^ 2 := by
    rw [le_div_iff₀ hτsqPos]
    simpa using hτsq
  calc
    ((goldreichLevinActiveCap τ + 1 : ℕ) : ℚ) =
        (goldreichLevinActiveCap τ : ℚ) + 1 := by push_cast; rfl
    _ ≤ 8 / τ.1 ^ 2 + 1 / τ.1 ^ 2 := add_le_add hcap hone
    _ = 9 / τ.1 ^ 2 := by ring

/-- The per-call confidence schedule uses at most a linear number of binary confidence bits. -/
theorem goldreichLevinCallConfidence_failureBits_le
    (n : ℕ) (τ : GoldreichLevinThreshold) :
    fourierEstimatorFailureBits (goldreichLevinCallConfidence n τ) ≤
      80 * (n + 1) * (goldreichLevinActiveCap τ + 1) := by
  unfold fourierEstimatorFailureBits
  let N := 80 * (n + 1) * (goldreichLevinActiveCap τ + 1)
  have hvalue : (2 : ℚ) / (goldreichLevinCallConfidence n τ).1 = (N : ℕ) := by
    change (2 : ℚ) /
      (1 / (40 * (n + 1) * (goldreichLevinActiveCap τ + 1))) = (N : ℕ)
    field_simp
    dsimp [N]
    norm_num
  have hceil : Nat.ceil ((2 : ℚ) / (goldreichLevinCallConfidence n τ).1) = N := by
    rw [hvalue]
    exact Nat.ceil_natCast N
  rw [hceil]
  exact Nat.clog_le_of_le_pow
    (show N ≤ 2 ^ N from Nat.lt_two_pow_self.le)

/-- The scheduled samples in one Goldreich--Levin bucket estimate have an explicit rational
polynomial upper bound. -/
theorem goldreichLevinSampleCount_cast_le
    (n : ℕ) (τ : GoldreichLevinThreshold) :
    (fourierEstimatorSampleCount
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) : ℚ) ≤
      5120 * (n + 1) * (goldreichLevinActiveCap τ + 1) / τ.1 ^ 4 := by
  have hscheduler := fourierEstimatorSampleCount_cast_le
    (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
  have hbits : (fourierEstimatorFailureBits
      (goldreichLevinCallConfidence n τ) : ℚ) ≤
      80 * (n + 1) * (goldreichLevinActiveCap τ + 1) := by
    exact_mod_cast goldreichLevinCallConfidence_failureBits_le n τ
  have hτ : τ.1 ≠ 0 := ne_of_gt τ.2.1
  calc
    (fourierEstimatorSampleCount
        (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ) : ℚ) ≤
      4 * fourierEstimatorFailureBits (goldreichLevinCallConfidence n τ) /
        (goldreichLevinWeightAccuracy τ).1 ^ 2 := hscheduler
    _ ≤ 4 * (80 * (n + 1) * (goldreichLevinActiveCap τ + 1)) /
        (goldreichLevinWeightAccuracy τ).1 ^ 2 := by
      gcongr
    _ = 5120 * (n + 1) * (goldreichLevinActiveCap τ + 1) / τ.1 ^ 4 := by
      change 4 * (80 * (n + 1) * (goldreichLevinActiveCap τ + 1)) /
        (τ.1 ^ 2 / 4) ^ 2 = _
      field_simp
      ring

/-- The complete Goldreich--Levin query budget is polynomial in `n` and `1 / τ`. -/
theorem goldreichLevinQueryBudget_cast_le
    (n : ℕ) (τ : GoldreichLevinThreshold) :
    (goldreichLevinQueryBudget n τ : ℚ) ≤
      2 ^ 21 * n * (n + 1) / τ.1 ^ 8 := by
  let m := fourierEstimatorSampleCount
    (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
  have hm := goldreichLevinSampleCount_cast_le n τ
  have hcap := goldreichLevinActiveCap_cast_le τ
  have hcapOne := goldreichLevinActiveCap_add_one_cast_le τ
  have hcapOne' : (goldreichLevinActiveCap τ : ℚ) + 1 ≤
      9 / τ.1 ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcapOne
  have hτpos : (0 : ℚ) < τ.1 := τ.2.1
  have hτne : τ.1 ≠ 0 := ne_of_gt hτpos
  have hm' : (m : ℚ) ≤
      5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4 := by
    calc
      (m : ℚ) ≤
          5120 * (n + 1) *
            ((goldreichLevinActiveCap τ : ℚ) + 1) / τ.1 ^ 4 := by
        simpa [m] using hm
      _ ≤ 5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4 := by
        gcongr
  calc
    (goldreichLevinQueryBudget n τ : ℚ) =
        4 * n * goldreichLevinActiveCap τ * m := by
      simp only [goldreichLevinQueryBudget, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ 4 * n * (8 / τ.1 ^ 2) *
        (5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4) := by
      gcongr
    _ = 1474560 * n * (n + 1) / τ.1 ^ 8 := by
      field_simp
      ring
    _ ≤ 2 ^ 21 * n * (n + 1) / τ.1 ^ 8 := by
      gcongr
      norm_num

/-- The complete charged-work budget is polynomial in `n` and `1 / τ`. -/
theorem goldreichLevinWorkBudget_cast_le
    (n : ℕ) (τ : GoldreichLevinThreshold) :
    (goldreichLevinWorkBudget n τ : ℚ) ≤
      2 ^ 25 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
  let m := fourierEstimatorSampleCount
    (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
  have hm := goldreichLevinSampleCount_cast_le n τ
  have hmpos : 0 < m := by
    exact fourierEstimatorSampleCount_pos
      (goldreichLevinWeightAccuracy τ) (goldreichLevinCallConfidence n τ)
  have hmOne : (m : ℚ) + 1 ≤ 2 * m := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hcap := goldreichLevinActiveCap_cast_le τ
  have hcapOne := goldreichLevinActiveCap_add_one_cast_le τ
  have hcapOne' : (goldreichLevinActiveCap τ : ℚ) + 1 ≤
      9 / τ.1 ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcapOne
  have hτpos : (0 : ℚ) < τ.1 := τ.2.1
  have hτne : τ.1 ≠ 0 := ne_of_gt hτpos
  have hm' : (m : ℚ) ≤
      5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4 := by
    calc
      (m : ℚ) ≤
          5120 * (n + 1) *
            ((goldreichLevinActiveCap τ : ℚ) + 1) / τ.1 ^ 4 := by
        simpa [m] using hm
      _ ≤ 5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4 := by
        gcongr
  have hτsq : τ.1 ^ 2 ≤ (1 : ℚ) := by
    nlinarith [mul_nonneg τ.2.1.le (sub_nonneg.mpr τ.2.2)]
  have hτfour : τ.1 ^ 4 ≤ (1 : ℚ) := by
    have hsquare := (sq_le_sq₀ (sq_nonneg τ.1) (by norm_num : (0 : ℚ) ≤ 1)).2 hτsq
    nlinarith
  have hτeight_le_four : τ.1 ^ 8 ≤ τ.1 ^ 4 := by
    have hproduct : (0 : ℚ) ≤ τ.1 ^ 4 * (1 - τ.1 ^ 4) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hτfour)
    nlinarith
  have hinvPow : (1 : ℚ) / τ.1 ^ 4 ≤ 1 / τ.1 ^ 8 := by
    rw [div_le_div_iff₀ (pow_pos hτpos 4) (pow_pos hτpos 8)]
    simpa using hτeight_le_four
  have hcontroller :
      (goldreichLevinControllerStepWork n τ : ℚ) ≤
        1296 * (n + 1) ^ 2 / τ.1 ^ 8 := by
    calc
      (goldreichLevinControllerStepWork n τ : ℚ) =
          16 * (n + 1) ^ 2 *
            ((goldreichLevinActiveCap τ : ℚ) + 1) ^ 2 := by
        simp only [goldreichLevinControllerStepWork, Nat.cast_mul,
          Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      _ ≤ 16 * (n + 1) ^ 2 * (9 / τ.1 ^ 2) ^ 2 := by
        gcongr
      _ = 1296 * (n + 1) ^ 2 / τ.1 ^ 4 := by
        field_simp
        ring
      _ ≤ 1296 * (n + 1) ^ 2 / τ.1 ^ 8 := by
        calc
          1296 * (n + 1) ^ 2 / τ.1 ^ 4 =
              (1296 * (n + 1) ^ 2) * (1 / τ.1 ^ 4) := by ring
          _ ≤ (1296 * (n + 1) ^ 2) * (1 / τ.1 ^ 8) := by gcongr
          _ = 1296 * (n + 1) ^ 2 / τ.1 ^ 8 := by ring
  have hestimator :
      (n : ℚ) *
          (16 * goldreichLevinActiveCap τ * (m + 1) * (n + 1)) ≤
        2 ^ 24 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
    have hmOneBound : (m : ℚ) + 1 ≤
        2 * (5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4) :=
      hmOne.trans (mul_le_mul_of_nonneg_left hm' (by norm_num))
    calc
      (n : ℚ) *
          (16 * goldreichLevinActiveCap τ * (m + 1) * (n + 1)) ≤
        n * (16 * (8 / τ.1 ^ 2) *
          (2 * (5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4)) *
            (n + 1)) := by
        gcongr
      _ = n * (32 * (8 / τ.1 ^ 2) *
          (5120 * (n + 1) * (9 / τ.1 ^ 2) / τ.1 ^ 4) * (n + 1)) := by ring
      _ = 11796480 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
        field_simp
        ring
      _ ≤ 2 ^ 24 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
        gcongr
        norm_num
  calc
    (goldreichLevinWorkBudget n τ : ℚ) =
        n * (goldreichLevinControllerStepWork n τ +
          16 * goldreichLevinActiveCap τ * (m + 1) * (n + 1)) := by
      simp only [goldreichLevinWorkBudget, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat]
      ring
    _ ≤ n * (1296 * (n + 1) ^ 2 / τ.1 ^ 8) +
        2 ^ 24 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
      have hcontrollerScaled := mul_le_mul_of_nonneg_left hcontroller
        (by positivity : (0 : ℚ) ≤ n)
      nlinarith
    _ = (1296 + 2 ^ 24) * n * (n + 1) ^ 2 / τ.1 ^ 8 := by ring
    _ ≤ 2 ^ 25 * n * (n + 1) ^ 2 / τ.1 ^ 8 := by
      gcongr
      norm_num

noncomputable def goldreichLevinQueryProgram
    (τ : GoldreichLevinThreshold) :
    LearningProgram n .queries (GoldreichLevinQueryState n) :=
  goldreichLevinQueryRunUpTo τ n le_rfl

theorem goldreichLevinQueryProgram_queries_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (outcome : GoldreichLevinQueryState n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (goldreichLevinQueryProgram τ)).support) :
    outcome.2.queries ≤ goldreichLevinQueryBudget n τ := by
  simpa [goldreichLevinQueryBudget] using
    goldreichLevinQueryRunUpTo_queries_le target τ n le_rfl outcome
      (by simpa [goldreichLevinQueryProgram] using houtcome)

theorem goldreichLevinQueryProgram_work_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (outcome : GoldreichLevinQueryState n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (goldreichLevinQueryProgram τ)).support) :
    outcome.2.work ≤ goldreichLevinWorkBudget n τ := by
  simpa [goldreichLevinWorkBudget] using
    goldreichLevinQueryRunUpTo_work_le target τ n le_rfl outcome
      (by simpa [goldreichLevinQueryProgram] using houtcome)

theorem goldreichLevinQueryProgram_correct_of_mem_support_of_not_hasFailure
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (outcome : GoldreichLevinQueryState n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (goldreichLevinQueryProgram τ)).support)
    (hgood : ¬outcome.1.HasFailure target τ) :
    outcome.1.IsCorrectOutput target τ := by
  have hinvariant := goldreichLevinQueryRunUpTo_satisfiesInvariant_of_mem_support
    target τ n le_rfl outcome (by
      simpa [goldreichLevinQueryProgram] using houtcome) hgood
  obtain ⟨active, hactive, hactiveInvariant, hactiveCap⟩ := hinvariant
  exact ⟨active, hactive,
    goldreichLevinActiveInvariant_complete target τ active hactiveInvariant,
    goldreichLevinActiveInvariant_sound target τ active hactiveInvariant,
    hactiveCap,
    goldreichLevinActiveInvariant_card_le target τ active hactiveInvariant⟩

theorem goldreichLevinQueryProgram_incorrectProbability_le_failureProbability
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ ¬outcome.1.IsCorrectOutput target τ) ≤
      LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ outcome.1.HasFailure target τ) := by
  let law := LearningProgram.runWithCost target (goldreichLevinQueryProgram τ)
  have houter :
      law.toOuterMeasure
          {outcome | ¬outcome.1.IsCorrectOutput target τ} ≤
        law.toOuterMeasure {outcome | outcome.1.HasFailure target τ} := by
    apply PMF.toOuterMeasure_mono
    rintro outcome ⟨hincorrect, hsupport⟩
    change outcome.1.HasFailure target τ
    by_contra hgood
    exact hincorrect
      (goldreichLevinQueryProgram_correct_of_mem_support_of_not_hasFailure
        target τ outcome hsupport hgood)
  unfold LearningProgram.eventProbability
  exact ENNReal.toReal_mono
    (LearningProgram.outerEventProbability_ne_top
      (goldreichLevinQueryProgram τ) target
      (fun outcome ↦ outcome.1.HasFailure target τ)) houter

theorem goldreichLevinQueryProgram_failureProbability_le_one_twentieth
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ outcome.1.HasFailure target τ) ≤ 1 / 20 := by
  have houter := goldreichLevinQueryRunUpTo_outerFailureProbability_le
    target τ n le_rfl
  have hfinite : n • goldreichLevinStageFailureBudget n τ ≠ ∞ := by
    simp only [goldreichLevinStageFailureBudget, nsmul_eq_mul]
    apply ENNReal.mul_ne_top
    · simp
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top (2 * goldreichLevinActiveCap τ)
      · exact ENNReal.ofReal_ne_top
  have hprob :
      LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
          (fun outcome ↦ outcome.1.HasFailure target τ) ≤
        (n • goldreichLevinStageFailureBudget n τ).toReal := by
    change
      (LearningProgram.outerEventProbability
        (goldreichLevinQueryRunUpTo τ n le_rfl) target
        (fun outcome ↦ outcome.1.HasFailure target τ)).toReal ≤ _
    exact ENNReal.toReal_mono hfinite houter
  have hbudgetReal :
      (n • goldreichLevinStageFailureBudget n τ).toReal =
        (n : ℝ) * (2 * goldreichLevinActiveCap τ : ℕ) *
          ((goldreichLevinCallConfidence n τ).1 : ℝ) := by
    simp [goldreichLevinStageFailureBudget, nsmul_eq_mul,
      ENNReal.toReal_ofReal,
      Rat.cast_nonneg.mpr (goldreichLevinCallConfidence n τ).2.1.le]
    ring
  have hrat := goldreichLevinFailureBudget_rat_le_one_twentieth n τ
  have hreal :
      (n : ℝ) * (2 * goldreichLevinActiveCap τ : ℕ) *
          ((goldreichLevinCallConfidence n τ).1 : ℝ) ≤ 1 / 20 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hrat
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] at hcast
    simpa using hcast
  calc
    LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ outcome.1.HasFailure target τ) ≤
        (n • goldreichLevinStageFailureBudget n τ).toReal := hprob
    _ = (n : ℝ) * (2 * goldreichLevinActiveCap τ : ℕ) *
        ((goldreichLevinCallConfidence n τ).1 : ℝ) := hbudgetReal
    _ ≤ 1 / 20 := hreal

theorem goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ ¬outcome.1.IsCorrectOutput target τ) ≤ 1 / 20 :=
  (goldreichLevinQueryProgram_incorrectProbability_le_failureProbability target τ).trans
    (goldreichLevinQueryProgram_failureProbability_le_one_twentieth target τ)

/-- The probability of violating any output guarantee is at most `1/10`. -/
theorem goldreichLevinQueryProgram_incorrectProbability_le_one_tenth
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    LearningProgram.eventProbability (goldreichLevinQueryProgram τ) target
        (fun outcome ↦ ¬outcome.1.IsCorrectOutput target τ) ≤ 1 / 10 :=
  (goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth target τ).trans (by norm_num)

end FABL
