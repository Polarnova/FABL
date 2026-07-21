/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter03.LearningTheory.FourierEstimation
import FABL.Chapter03.GoldreichLevin.RestrictedWeights
import FABL.Chapter03.Restrictions
import FABL.Chapter06.F₂Polynomials.Encoding
import FABL.Chapter06.Pseudorandomness.JuntaStableInfluence
import Mathlib.Data.Finset.Sort

/-!
# Learning juntas from a relevant-coordinate finder

Book items: Exercise 6.31 and Lemma 6.37.

The constant test is an actual random-example `LearningProgram`.  Restriction samples are
obtained from actual examples of the ambient target by finite rejection sampling; no conditional
sampling oracle is introduced.  The final section isolates the narrow interface assumed of the
relevant-coordinate finder in Lemma 6.37.
-/

open Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal

set_option autoImplicit false

@[expose] public section

namespace FABL

universe v

variable {n : ℕ}

local instance juntaLearningSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance juntaLearningSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Exercise 6.31(a): testing whether a junta is constant -/

/-- The three possible outcomes of the constant test. -/
inductive JuntaConstantDecision where
  /-- The target is the indicated constant sign. -/
  | constant (value : Sign)
  /-- The target is nonconstant. -/
  | nonconstant
deriving DecidableEq

namespace JuntaConstantDecision

/-- Semantic correctness of a constant-test decision. -/
def IsCorrect (target : BooleanFunction n) : JuntaConstantDecision → Prop
  | .constant value => target = fun _ ↦ value
  | .nonconstant => ¬ ∃ value : Sign, target = fun _ ↦ value

/-- The output constant transported to the book's `𝔽₂` convention. -/
def constantValueF₂? : JuntaConstantDecision → Option 𝔽₂
  | .constant value => some (binarySignEquiv.symm value)
  | .nonconstant => none

end JuntaConstantDecision

/-- Accuracy `2⁻⁽ᵏ⁺²⁾` used to distinguish a constant `k`-junta from a nonconstant one. -/
def juntaConstantAccuracy (k : ℕ) : PositiveLearningParameter := by
  refine ⟨1 / (2 : ℚ) ^ (k + 2), by positivity, ?_⟩
  have hden : (2 : ℚ) ≤ (2 : ℚ) ^ (k + 2) := by
    calc
      (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ (k + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  nlinarith

@[simp] theorem juntaConstantAccuracy_cast (k : ℕ) :
    (((juntaConstantAccuracy k).1 : ℚ) : ℝ) =
      1 / (2 : ℝ) ^ (k + 2) := by
  norm_num [juntaConstantAccuracy]

/-- Rational decision threshold halfway inside the junta mean gap. -/
def juntaConstantThreshold (k : ℕ) : ℚ :=
  1 - 2 * (juntaConstantAccuracy k).1

@[simp] theorem juntaConstantThreshold_cast (k : ℕ) :
    (juntaConstantThreshold k : ℝ) =
      1 - 2 * (1 / (2 : ℝ) ^ (k + 2)) := by
  simp [juntaConstantThreshold]

/-- Pure controller for the empirical constant Fourier coefficient. -/
def decideJuntaConstant (k : ℕ) (estimate : ℚ) : JuntaConstantDecision :=
  if juntaConstantThreshold k < estimate then
    .constant 1
  else if estimate < -juntaConstantThreshold k then
    .constant (-1)
  else
    .nonconstant

/-- A `0`-junta is constant. -/
theorem exists_eq_const_of_isKJunta_zero
    (target : BooleanFunction n) (hjunta : IsKJunta target 0) :
    ∃ value : Sign, target = fun _ ↦ value := by
  classical
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hJ : J = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hJcard)
  let x₀ : {−1,1}^[n] := fun _ ↦ 1
  refine ⟨target x₀, ?_⟩
  funext x
  exact hdepends (by
    intro i hi
    simp [hJ] at hi)

/-- Public-API form of the constant-distance gap needed by Exercise 6.31(a).  The proof reuses
the variance gap from `JuntaStableInfluence`; it does not repeat the low-degree support argument
hidden inside that module. -/
theorem abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (hnonconstant : ¬ ∃ value : Sign, target = fun _ ↦ value) :
    |mean target.toReal| ≤ 1 - ((2 : ℝ)⁻¹) ^ k := by
  by_cases hk : k = 0
  · subst k
    exact False.elim (hnonconstant (exists_eq_const_of_isKJunta_zero target hjunta))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let gap : ℝ := ((2 : ℝ)⁻¹) ^ k
    have hgapNonneg : 0 ≤ gap := pow_nonneg (by norm_num) _
    have hgapLeOne : gap ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hdegree : fourierDegree target.toReal ≤ k :=
      fourierDegree_toReal_le_of_isKJunta target hjunta
    have hvariance := inv_two_pow_pred_le_variance_of_fourierDegree_le
      target k hkpos hdegree hnonconstant
    have hpred : ((2 : ℝ)⁻¹) ^ (k - 1) = 2 * gap := by
      simp only [gap]
      have hhalf : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      calc
        ((2 : ℝ)⁻¹) ^ (k - 1) =
            2 * (((2 : ℝ)⁻¹) ^ (k - 1) * (2 : ℝ)⁻¹) := by
          rw [hhalf]
          ring
        _ = 2 * ((2 : ℝ)⁻¹) ^ ((k - 1) + 1) := by rw [pow_succ]
        _ = 2 * ((2 : ℝ)⁻¹) ^ k := by rw [Nat.sub_add_cancel hkpos]
    rw [hpred, (variance_eq_four_mul_probabilities target).1] at hvariance
    by_contra hbound
    have habs : 1 - gap < |mean target.toReal| := lt_of_not_ge hbound
    have hsquares : (1 - gap) ^ 2 < |mean target.toReal| ^ 2 :=
      (sq_lt_sq₀ (sub_nonneg.mpr hgapLeOne) (abs_nonneg _)).2 habs
    rw [sq_abs] at hsquares
    nlinarith [sq_nonneg gap]

/-- The mean gap is four times the estimator accuracy. -/
theorem inv_two_pow_eq_four_mul_juntaConstantAccuracy (k : ℕ) :
    ((2 : ℝ)⁻¹) ^ k =
      4 * (((juntaConstantAccuracy k).1 : ℚ) : ℝ) := by
  rw [juntaConstantAccuracy_cast]
  rw [pow_add]
  have hhalf : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf, one_div_pow]
  norm_num
  field_simp

/-- Any estimate inside the scheduled accuracy radius yields the correct constant decision. -/
theorem decideJuntaConstant_isCorrect_of_close
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (estimate : ℚ)
    (hclose :
      |(estimate : ℝ) - fourierCoeff target.toReal ∅| <
        (((juntaConstantAccuracy k).1 : ℚ) : ℝ)) :
    (decideJuntaConstant k estimate).IsCorrect target := by
  classical
  rw [← mean_eq_fourierCoeff_empty] at hclose
  by_cases hconstant : ∃ value : Sign, target = fun _ ↦ value
  · obtain ⟨value, rfl⟩ := hconstant
    rcases Int.units_eq_one_or value with rfl | rfl
    · have hlower :
          (juntaConstantThreshold k : ℝ) < (estimate : ℝ) := by
        rw [juntaConstantThreshold_cast]
        rw [juntaConstantAccuracy_cast] at hclose
        have h := (abs_lt.mp hclose).1
        have hmean :
            mean (BooleanFunction.toReal
              (fun _ : SignCube n ↦ (1 : Sign))) = 1 := by
          simp only [mean, BooleanFunction.toReal, signValue_one,
            Fintype.expect_const]
        rw [hmean] at h
        have ha : 0 < 1 / (2 : ℝ) ^ (k + 2) := by positivity
        nlinarith
      have hlowerQ : juntaConstantThreshold k < estimate := by
        exact_mod_cast hlower
      simp [decideJuntaConstant, hlowerQ, JuntaConstantDecision.IsCorrect]
    · have hupper :
          (estimate : ℝ) < -(juntaConstantThreshold k : ℝ) := by
        rw [juntaConstantThreshold_cast]
        rw [juntaConstantAccuracy_cast] at hclose
        have h := (abs_lt.mp hclose).2
        have hmean :
            mean (BooleanFunction.toReal
              (fun _ : SignCube n ↦ (-1 : Sign))) = -1 := by
          simp only [mean, BooleanFunction.toReal, signValue_neg_one,
            Fintype.expect_const]
        rw [hmean] at h
        have ha : 0 < 1 / (2 : ℝ) ^ (k + 2) := by positivity
        nlinarith
      have hupperQ : estimate < -juntaConstantThreshold k := by
        exact_mod_cast hupper
      have hnotLowerQ : ¬ juntaConstantThreshold k < estimate := by
        intro hlowerQ
        have hlower : (juntaConstantThreshold k : ℝ) < estimate := by
          exact_mod_cast hlowerQ
        have hthreshold : (0 : ℝ) < juntaConstantThreshold k := by
          rw [juntaConstantThreshold_cast]
          have hpow : (4 : ℝ) ≤ 2 ^ (k + 2) := by
            rw [pow_add]
            norm_num
            exact one_le_pow₀ (by norm_num)
          have hpowPos : (0 : ℝ) < 2 ^ (k + 2) := by positivity
          rw [sub_pos]
          rw [show 2 * (1 / (2 : ℝ) ^ (k + 2)) =
            2 / (2 : ℝ) ^ (k + 2) by ring]
          rw [div_lt_iff₀ hpowPos]
          nlinarith
        nlinarith
      simp [decideJuntaConstant, hnotLowerQ, hupperQ,
        JuntaConstantDecision.IsCorrect]
  · have hmean :=
      abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant
        target k hjunta hconstant
    rw [inv_two_pow_eq_four_mul_juntaConstantAccuracy] at hmean
    rw [juntaConstantAccuracy_cast] at hmean hclose
    have herror := abs_lt.mp hclose
    have hnotUpperReal :
        ¬ (juntaConstantThreshold k : ℝ) < (estimate : ℝ) := by
      rw [juntaConstantThreshold_cast]
      intro h
      have hmeanUpper : mean target.toReal ≤ |mean target.toReal| := le_abs_self _
      nlinarith
    have hnotLowerReal :
        ¬ (estimate : ℝ) < -(juntaConstantThreshold k : ℝ) := by
      rw [juntaConstantThreshold_cast]
      intro h
      have hmeanLower : -|mean target.toReal| ≤ mean target.toReal := neg_abs_le _
      nlinarith
    have hnotUpper : ¬ juntaConstantThreshold k < estimate := by
      exact fun h ↦ hnotUpperReal (by exact_mod_cast h)
    have hnotLower : ¬ estimate < -juntaConstantThreshold k := by
      exact fun h ↦ hnotLowerReal (by exact_mod_cast h)
    simp [decideJuntaConstant, hnotUpper, hnotLower,
      JuntaConstantDecision.IsCorrect, hconstant]

/-- Exercise 6.31(a)'s actual random-example program. -/
def juntaConstantTestProgram (k : ℕ) (failure : PositiveLearningParameter) :
    LearningProgram n .randomExamples JuntaConstantDecision :=
  LearningProgram.map (decideJuntaConstant k)
    (scheduledFourierCoeffEstimatorProgram ∅ (juntaConstantAccuracy k) failure)

/-- The constant tester has exactly the constructor-derived sample and work counts. -/
theorem juntaConstantTestProgram_cost_eq
    (target : BooleanFunction n) (k : ℕ) (failure : PositiveLearningParameter)
    (outcome : JuntaConstantDecision × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (juntaConstantTestProgram k failure)).support) :
    outcome.2 =
      ⟨fourierEstimatorSampleCount (juntaConstantAccuracy k) failure, 0,
        2 * fourierEstimatorSampleCount (juntaConstantAccuracy k) failure⟩ := by
  rw [juntaConstantTestProgram, LearningProgram.runWithCost_map,
    PMF.mem_support_map_iff] at houtcome
  obtain ⟨estimate, hestimate, rfl⟩ := houtcome
  rw [scheduledFourierCoeffEstimatorProgram_cost_eq target ∅
    (juntaConstantAccuracy k) failure estimate hestimate]
  apply LearningCost.toTriple_injective
  simp [LearningCost.toTriple, two_mul]

/-- Exercise 6.31(a): the actual program misclassifies a `k`-junta with probability at most
`failure`. -/
theorem juntaConstantTestProgram_failureProbability_le
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability (juntaConstantTestProgram k failure) target
        (fun outcome ↦ ¬ outcome.1.IsCorrect target) ≤
      (failure.1 : ℝ) := by
  have hmap :
      LearningProgram.eventProbability (juntaConstantTestProgram k failure) target
          (fun outcome ↦ ¬ outcome.1.IsCorrect target) =
        LearningProgram.eventProbability
          (scheduledFourierCoeffEstimatorProgram ∅
            (juntaConstantAccuracy k) failure) target
          (fun outcome ↦ ¬ (decideJuntaConstant k outcome.1).IsCorrect target) := by
    unfold juntaConstantTestProgram LearningProgram.eventProbability
    rw [LearningProgram.runWithCost_map, PMF.toOuterMeasure_map_apply]
    rfl
  rw [hmap]
  refine (LearningProgram.eventProbability_mono
    (scheduledFourierCoeffEstimatorProgram ∅
      (juntaConstantAccuracy k) failure) target ?_).trans
      (scheduledFourierCoeffEstimatorProgram_failureProbability_le
        target ∅ (juntaConstantAccuracy k) failure)
  intro outcome hwrong
  by_contra hnotBad
  apply hwrong
  apply decideJuntaConstant_isCorrect_of_close target k hjunta outcome.1
  exact lt_of_not_ge hnotBad

/-- Explicit `poly(n,2^k) log(1/failure)` sample bound for Exercise 6.31(a). -/
theorem juntaConstantTestSampleCount_cast_le
    (k : ℕ) (failure : PositiveLearningParameter) :
    (fourierEstimatorSampleCount (juntaConstantAccuracy k) failure : ℚ) ≤
      64 * 4 ^ k * fourierEstimatorFailureBits failure := by
  calc
    (fourierEstimatorSampleCount (juntaConstantAccuracy k) failure : ℚ) ≤
        4 * fourierEstimatorFailureBits failure /
          (juntaConstantAccuracy k).1 ^ 2 :=
      fourierEstimatorSampleCount_cast_le (juntaConstantAccuracy k) failure
    _ = 64 * 4 ^ k * fourierEstimatorFailureBits failure := by
      simp only [juntaConstantAccuracy]
      rw [div_pow]
      have hkpow : ((2 : ℚ) ^ k) ^ 2 = 4 ^ k := by
        rw [pow_two, show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
      norm_num [pow_add]
      rw [mul_pow, hkpow]
      norm_num
      ring

/-! ## Exercise 6.31(b): rejection sampling a restriction -/

/-- Coordinates not yet fixed by the partial assignment `P`. -/
abbrev JuntaFreeIndex (P : Finset (Fin n)) := {i : Fin n // i ∉ P}

/-- A sign assignment on the coordinates fixed by `P`. -/
abbrev JuntaFixedAssignment (P : Finset (Fin n)) := P → Sign

/-- A sign assignment on the coordinates outside `P`. -/
abbrev JuntaFreeAssignment (P : Finset (Fin n)) := JuntaFreeIndex P → Sign

/-- Combine a fixed assignment on `P` with an assignment on its complement. -/
def combineJuntaAssignment (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (y : JuntaFreeAssignment P) : {−1,1}^[n] :=
  fun i ↦ if hi : i ∈ P then z ⟨i, hi⟩ else y ⟨i, hi⟩

/-- The canonical split into the fixed coordinates `P` and their complement. -/
def juntaAssignmentSplitEquiv (P : Finset (Fin n)) :
    {−1,1}^[n] ≃ JuntaFixedAssignment P × JuntaFreeAssignment P :=
  Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ P) (fun _ ↦ Sign)

@[simp] theorem juntaAssignmentSplitEquiv_symm_apply
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (y : JuntaFreeAssignment P) :
    (juntaAssignmentSplitEquiv P).symm (z, y) =
      combineJuntaAssignment P z y := by
  funext i
  by_cases hi : i ∈ P <;>
    simp [juntaAssignmentSplitEquiv, combineJuntaAssignment,
      Equiv.piEquivPiSubtypeProd_symm_apply, hi]

@[simp] theorem combineJuntaAssignment_apply_fixed
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (y : JuntaFreeAssignment P) (i : P) :
    combineJuntaAssignment P z y i = z i := by
  simp [combineJuntaAssignment, i.property]

@[simp] theorem combineJuntaAssignment_apply_free
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (y : JuntaFreeAssignment P) (i : JuntaFreeIndex P) :
    combineJuntaAssignment P z y i = y i := by
  simp [combineJuntaAssignment, i.property]

/-- Restrict a sign-valued target by fixing the coordinates in `P` to `z`. -/
def juntaRestriction (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) : JuntaFreeAssignment P → Sign :=
  fun y ↦ target (combineJuntaAssignment P z y)

/-- The same fixed assignment in the book's additive `𝔽₂` representation. -/
def juntaFixedAssignmentSignOfF₂ (P : Finset (Fin n)) (z : P → 𝔽₂) :
    JuntaFixedAssignment P :=
  fun i ↦ binarySignEquiv (z i)

/-- The same free assignment in the book's additive `𝔽₂` representation. -/
def juntaFreeAssignmentF₂OfSign (P : Finset (Fin n))
    (y : JuntaFreeAssignment P) : JuntaFreeIndex P → 𝔽₂ :=
  fun i ↦ binarySignEquiv.symm (y i)

/-- Additive-cube combination corresponding to `combineJuntaAssignment`. -/
def combineJuntaF₂Assignment (P : Finset (Fin n))
    (z : P → 𝔽₂) (y : JuntaFreeIndex P → 𝔽₂) : F₂Cube n :=
  fun i ↦ if hi : i ∈ P then z ⟨i, hi⟩ else y ⟨i, hi⟩

/-- The explicit `SignCube`/`F₂Cube` bridge commutes with a partial assignment. -/
theorem binaryCubeSignEquiv_combineJuntaF₂Assignment
    (P : Finset (Fin n)) (z : P → 𝔽₂)
    (y : JuntaFreeIndex P → 𝔽₂) :
    binaryCubeSignEquiv n (combineJuntaF₂Assignment P z y) =
      combineJuntaAssignment P (juntaFixedAssignmentSignOfF₂ P z)
        (fun i ↦ binarySignEquiv (y i)) := by
  funext i
  by_cases hi : i ∈ P <;>
    simp [combineJuntaF₂Assignment, combineJuntaAssignment,
      juntaFixedAssignmentSignOfF₂, binaryCubeSignEquiv_apply,
      binarySignEquiv, hi]

/-- The input of a random example agrees with the requested fixed assignment. -/
def MatchesJuntaAssignment (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (x : {−1,1}^[n]) : Prop :=
  ∀ i : P, x i = z i

instance (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (x : {−1,1}^[n]) : Decidable (MatchesJuntaAssignment P z x) :=
  Fintype.decidableForallFintype

/-- The free coordinates of an ambient input. -/
def juntaFreePart (P : Finset (Fin n)) (x : {−1,1}^[n]) :
    JuntaFreeAssignment P :=
  fun i ↦ x i

/-- The coordinates in `P` of an ambient input. -/
def juntaFixedPart (P : Finset (Fin n)) (x : {−1,1}^[n]) :
    JuntaFixedAssignment P :=
  fun i ↦ x i

@[simp] theorem juntaFixedPart_combineJuntaAssignment
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (y : JuntaFreeAssignment P) :
    juntaFixedPart P (combineJuntaAssignment P z y) = z := by
  funext i
  simp [juntaFixedPart]

@[simp] theorem juntaFreePart_combineJuntaAssignment
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (y : JuntaFreeAssignment P) :
    juntaFreePart P (combineJuntaAssignment P z y) = y := by
  funext i
  simp [juntaFreePart]

/-- Combining the free part of a matching input with the prescribed fixed assignment returns the
original ambient input. -/
theorem combineJuntaAssignment_freePart_of_matches
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (x : {−1,1}^[n]) (hx : MatchesJuntaAssignment P z x) :
    combineJuntaAssignment P z (juntaFreePart P x) = x := by
  funext i
  by_cases hi : i ∈ P
  · simpa [combineJuntaAssignment, hi] using hx ⟨i, hi⟩ |>.symm
  · simp [combineJuntaAssignment, juntaFreePart, hi]

/-- A labeled ambient example certified to lie in the requested restriction. -/
abbrev MatchedJuntaExample (P : Finset (Fin n)) (z : JuntaFixedAssignment P) :=
  {sample : {−1,1}^[n] × Sign // MatchesJuntaAssignment P z sample.1}

/-- Convert a certified accepted example to a labeled example on the free cube. -/
def matchedJuntaRestrictionExample (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (sample : MatchedJuntaExample P z) :
    JuntaFreeAssignment P × Sign :=
  (juntaFreePart P sample.1.1, sample.1.2)

/-- An accepted target-generated example has exactly the label of the restricted target. -/
theorem matchedJuntaRestrictionExample_label
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (sample : MatchedJuntaExample P z)
    (hlabel : sample.1.2 = target sample.1.1) :
    (matchedJuntaRestrictionExample P z sample).2 =
      juntaRestriction target P z (matchedJuntaRestrictionExample P z sample).1 := by
  rw [matchedJuntaRestrictionExample, juntaRestriction, hlabel,
    combineJuntaAssignment_freePart_of_matches P z sample.1.1 sample.2]

/-- Indices of a fixed-coordinate sequence that equal the requested assignment. -/
def fixedMatchingIndices (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    {R : ℕ} (fixed : Fin R → JuntaFixedAssignment P) : Finset (Fin R) :=
  Finset.univ.filter fun i ↦ fixed i = z

/-- Indices in a finite labeled batch whose inputs match the requested fixed assignment. -/
def juntaMatchingIndices (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    {R : ℕ} (samples : Fin R → ({−1,1}^[n] × Sign)) : Finset (Fin R) :=
  fixedMatchingIndices P z (fun i ↦ juntaFixedPart P (samples i).1)

/-- The number of examples in a batch that match a partial assignment. -/
def juntaMatchCount (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    {R : ℕ} (samples : Fin R → ({−1,1}^[n] × Sign)) : ℕ :=
  (juntaMatchingIndices P z samples).card

/-- Indicator-sum form of the accepted-example count. -/
theorem juntaMatchCount_eq_sum
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    {R : ℕ} (samples : Fin R → ({−1,1}^[n] × Sign)) :
    juntaMatchCount P z samples =
      ∑ i, if MatchesJuntaAssignment P z (samples i).1 then 1 else 0 := by
  classical
  simp only [juntaMatchCount, juntaMatchingIndices, fixedMatchingIndices,
    Finset.sum_boole]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

/-- Real indicator of a uniform ambient input matching the requested fixed assignment. -/
def juntaMatchObservation (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (x : {−1,1}^[n]) : ℝ :=
  if MatchesJuntaAssignment P z x then 1 else 0

theorem juntaMatchObservation_mem_Icc
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (x : {−1,1}^[n]) :
    juntaMatchObservation P z x ∈ Set.Icc (-(1 : ℝ)) 1 := by
  by_cases h : MatchesJuntaAssignment P z x <;>
    simp [juntaMatchObservation, h]

/-- A uniform ambient input matches a fixed assignment on `P` with probability `2⁻|P|`. -/
theorem expect_juntaMatchObservation
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P) :
    (𝔼 x : {−1,1}^[n], juntaMatchObservation P z x) =
      1 / (2 : ℝ) ^ P.card := by
  classical
  calc
    (𝔼 x : {−1,1}^[n], juntaMatchObservation P z x) =
        𝔼 p : JuntaFixedAssignment P × JuntaFreeAssignment P,
          juntaMatchObservation P z
            ((juntaAssignmentSplitEquiv P).symm p) := by
      symm
      apply Fintype.expect_equiv (juntaAssignmentSplitEquiv P).symm
      intro p
      rfl
    _ = 𝔼 fixed : JuntaFixedAssignment P,
          𝔼 _free : JuntaFreeAssignment P,
            if fixed = z then (1 : ℝ) else 0 := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro fixed _
      apply Finset.expect_congr rfl
      intro free _
      by_cases hfixed : fixed = z
      · subst fixed
        simp [juntaMatchObservation, MatchesJuntaAssignment]
      · have hnot : ¬ MatchesJuntaAssignment P z
            (combineJuntaAssignment P fixed free) := by
          intro hmatches
          apply hfixed
          funext i
          simpa using hmatches i
        simp [juntaMatchObservation, juntaAssignmentSplitEquiv_symm_apply,
          hfixed, hnot]
    _ = 𝔼 fixed : JuntaFixedAssignment P,
          if fixed = z then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro fixed _
      exact Finset.expect_const Finset.univ_nonempty _
    _ = 1 / Fintype.card (JuntaFixedAssignment P) :=
      uniformProbability_eq_singleton z
    _ = 1 / (2 : ℝ) ^ P.card := by
      norm_num [JuntaFixedAssignment, Fintype.card_fun, Sign]

/-- The executable count divided by the batch size is the empirical mean of the match
indicator. -/
theorem finiteUniformEmpiricalMean_juntaMatchObservation
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) {R : ℕ} (sampleInputs : Fin R → {−1,1}^[n]) :
    finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs =
      (juntaMatchCount P z
        (fun i ↦ (sampleInputs i, target (sampleInputs i))) : ℝ) / R := by
  rw [finiteUniformEmpiricalMean, juntaMatchCount_eq_sum]
  congr 1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : MatchesJuntaAssignment P z (sampleInputs i) <;>
    simp [juntaMatchObservation, h]

/-- The canonical inclusion of an initial segment into a larger finite ordinal. -/
def initialFinEmbedding {M L : ℕ} (h : M ≤ L) : Fin M ↪ Fin L where
  toFun i := ⟨i.1, i.2.trans_le h⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin L ↦ x.1) hij

/-- The first `M` occurrences of `z` in a fixed-coordinate sequence. -/
def fixedMatchingIndexEmbedding (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (fixed : Fin R → JuntaFixedAssignment P)
    (h : M ≤ (fixedMatchingIndices P z fixed).card) : Fin M ↪ Fin R :=
  (initialFinEmbedding h).trans
    ((fixedMatchingIndices P z fixed).orderEmbOfFin rfl).toEmbedding

/-- The first `M` matching batch indices, in increasing order. -/
def juntaMatchingIndexEmbedding (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (samples : Fin R → ({−1,1}^[n] × Sign))
    (h : M ≤ juntaMatchCount P z samples) : Fin M ↪ Fin R :=
  fixedMatchingIndexEmbedding P z M
    (fun i ↦ juntaFixedPart P (samples i).1) h

theorem juntaMatchingIndexEmbedding_matches
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (samples : Fin R → ({−1,1}^[n] × Sign))
    (h : M ≤ juntaMatchCount P z samples) (i : Fin M) :
    MatchesJuntaAssignment P z
      (samples (juntaMatchingIndexEmbedding P z M samples h i)).1 := by
  have hmem : juntaMatchingIndexEmbedding P z M samples h i ∈
      juntaMatchingIndices P z samples := by
    exact (juntaMatchingIndices P z samples).orderEmbOfFin_mem rfl _
  have hfixed := (Finset.mem_filter.mp hmem).2
  intro j
  exact congrFun hfixed j

/-- Take the first `M` accepted examples, returning `none` exactly when fewer than `M` inputs
match. -/
def takeMatchingJuntaExamples (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (M : ℕ) {R : ℕ} (samples : Fin R → ({−1,1}^[n] × Sign)) :
    Option (Fin M → MatchedJuntaExample P z) :=
  if h : M ≤ juntaMatchCount P z samples then
    some fun i ↦
      ⟨samples (juntaMatchingIndexEmbedding P z M samples h i),
        juntaMatchingIndexEmbedding_matches P z M samples h i⟩
  else
    none

theorem takeMatchingJuntaExamples_eq_none_iff
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (M : ℕ) {R : ℕ} (samples : Fin R → ({−1,1}^[n] × Sign)) :
    takeMatchingJuntaExamples P z M samples = none ↔
      juntaMatchCount P z samples < M := by
  classical
  rw [takeMatchingJuntaExamples]
  split_ifs with h
  · simp [h]
  · simp only [true_iff]
    omega

/-- Accuracy `2⁻⁽ᵏ⁺¹⁾`, at most half of the probability of matching at most `k`
fixed coordinates. -/
def juntaRestrictionMatchAccuracy (k : ℕ) : PositiveLearningParameter := by
  refine ⟨1 / (2 : ℚ) ^ (k + 1), by positivity, ?_⟩
  have hden : (2 : ℚ) ≤ (2 : ℚ) ^ (k + 1) := by
    calc
      (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  nlinarith

@[simp] theorem juntaRestrictionMatchAccuracy_cast (k : ℕ) :
    (((juntaRestrictionMatchAccuracy k).1 : ℚ) : ℝ) =
      1 / (2 : ℝ) ^ (k + 1) := by
  norm_num [juntaRestrictionMatchAccuracy]

/-- Batch size for finite rejection sampling.  The first summand supplies the expected `M`
acceptances, and the second is the Chapter 3 concentration schedule. -/
def juntaRestrictionSampleCount (k M : ℕ)
    (failure : PositiveLearningParameter) : ℕ :=
  2 ^ (k + 1) * M +
    fourierEstimatorSampleCount (juntaRestrictionMatchAccuracy k) failure

/-- Local work charged for testing all fixed coordinates and selecting the first `M` matches. -/
def juntaRestrictionSampleWork (P : Finset (Fin n)) (k M : ℕ)
    (failure : PositiveLearningParameter) : ℕ :=
  juntaRestrictionSampleCount k M failure * (P.card + 1) + M

/-- Exercise 6.31(b)'s actual finite rejection sampler.  Every oracle call is an ambient random
example; failure is represented explicitly by `none`. -/
def juntaRestrictionSampleProgram (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ)
    (failure : PositiveLearningParameter) :
    LearningProgram n .randomExamples
      (Option (Fin M → MatchedJuntaExample P z)) :=
  .randomExampleBatch (juntaRestrictionSampleCount k M failure) fun samples ↦
    .tick (juntaRestrictionSampleWork P k M failure)
      (.pure (takeMatchingJuntaExamples P z M samples))

/-- Exact pushforward law and constructor-derived cost of the rejection sampler. -/
theorem runWithCost_juntaRestrictionSampleProgram
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ)
    (failure : PositiveLearningParameter) :
    LearningProgram.runWithCost target
        (juntaRestrictionSampleProgram P z k M failure) =
      (uniformPMF
        (Fin (juntaRestrictionSampleCount k M failure) → {−1,1}^[n])).map
        fun sampleInputs ↦
          (takeMatchingJuntaExamples P z M
            (fun i ↦ (sampleInputs i, target (sampleInputs i))),
            ⟨juntaRestrictionSampleCount k M failure, 0,
              juntaRestrictionSampleCount k M failure +
                juntaRestrictionSampleWork P k M failure⟩) := by
  unfold juntaRestrictionSampleProgram LearningProgram.runWithCost
  simp only [LearningProgram.runWithCost, PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  congr 1

/-- Raw-input failure event of the actual rejection sampler. -/
def juntaRestrictionFailureSet
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ)
    (failure : PositiveLearningParameter) :
    Set (Fin (juntaRestrictionSampleCount k M failure) → {−1,1}^[n]) :=
  {sampleInputs |
    takeMatchingJuntaExamples P z M
      (fun i ↦ (sampleInputs i, target (sampleInputs i))) = none}

/-- Failure of finite rejection sampling forces a large empirical deviation of the fixed-prefix
indicator. -/
theorem juntaRestrictionFailureSet_subset_empiricalBad
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ) (hPk : P.card ≤ k)
    (failure : PositiveLearningParameter) :
    juntaRestrictionFailureSet target P z k M failure ⊆
      {sampleInputs |
        (((juntaRestrictionMatchAccuracy k).1 : ℚ) : ℝ) ≤
          |finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs -
            (𝔼 x, juntaMatchObservation P z x)|} := by
  intro sampleInputs hfailure
  change takeMatchingJuntaExamples P z M
      (fun i ↦ (sampleInputs i, target (sampleInputs i))) = none at hfailure
  have hcount : juntaMatchCount P z
      (fun i ↦ (sampleInputs i, target (sampleInputs i))) < M := by
    exact (takeMatchingJuntaExamples_eq_none_iff P z M _).1 hfailure
  let R := juntaRestrictionSampleCount k M failure
  let a : ℝ := (((juntaRestrictionMatchAccuracy k).1 : ℚ) : ℝ)
  let p : ℝ := 1 / (2 : ℝ) ^ P.card
  have hRpos : (0 : ℝ) < R := by
    exact_mod_cast (Nat.add_pos_right _
      (fourierEstimatorSampleCount_pos
        (juntaRestrictionMatchAccuracy k) failure))
  have hRlowerNat : 2 ^ (k + 1) * M ≤ R := by
    simp [R, juntaRestrictionSampleCount]
  have hRlower : (2 : ℝ) ^ (k + 1) * M ≤ R := by
    exact_mod_cast hRlowerNat
  have ha : a = 1 / (2 : ℝ) ^ (k + 1) := by
    simp [a]
  have hempirical :
      finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs < a := by
    rw [finiteUniformEmpiricalMean_juntaMatchObservation target P z]
    have hcountReal :
        (juntaMatchCount P z
          (fun i ↦ (sampleInputs i, target (sampleInputs i))) : ℝ) < M := by
      exact_mod_cast hcount
    have hratio :
        (M : ℝ) / R ≤ 1 / (2 : ℝ) ^ (k + 1) := by
      rw [div_le_div_iff₀ hRpos (pow_pos (by norm_num) _)]
      simpa [mul_comm] using hRlower
    rw [ha]
    exact (div_lt_div_of_pos_right hcountReal hRpos).trans_le hratio
  have hpow : (2 : ℝ) ^ P.card ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hPk
  have hp : 2 * a ≤ p := by
    rw [ha]
    have hinv : 1 / (2 : ℝ) ^ k ≤ p := by
      exact one_div_le_one_div_of_le (pow_pos (by norm_num) _) hpow
    calc
      2 * (1 / (2 : ℝ) ^ (k + 1)) = 1 / (2 : ℝ) ^ k := by
        rw [pow_succ]
        field_simp
      _ ≤ p := hinv
  have ha0 : 0 ≤ a := by
    rw [ha]
    positivity
  have hnonpos :
      finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs - p ≤ 0 := by
    nlinarith [hempirical, hp]
  have hbound :
      a ≤ |finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs - p| := by
    rw [abs_of_nonpos hnonpos]
    nlinarith
  simpa [a, p, expect_juntaMatchObservation] using hbound

/-- Exercise 6.31(b): the actual finite rejection sampler fails with probability at most the
requested confidence parameter. -/
theorem juntaRestrictionSampleProgram_failureProbability_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ) (hPk : P.card ≤ k)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (juntaRestrictionSampleProgram P z k M failure) target
        (fun outcome ↦ outcome.1 = none) ≤
      (failure.1 : ℝ) := by
  let R := juntaRestrictionSampleCount k M failure
  let a : ℝ := (((juntaRestrictionMatchAccuracy k).1 : ℚ) : ℝ)
  have hRpos : 0 < R := Nat.add_pos_right _
    (fourierEstimatorSampleCount_pos
      (juntaRestrictionMatchAccuracy k) failure)
  have hmeasure :
      (uniformPMF (Fin R → {−1,1}^[n])).toMeasure.real
          (juntaRestrictionFailureSet target P z k M failure) ≤
        (failure.1 : ℝ) := by
    let bad : Set (Fin R → {−1,1}^[n]) :=
      {sampleInputs |
        a ≤
          |finiteUniformEmpiricalMean (juntaMatchObservation P z) sampleInputs -
            (𝔼 x, juntaMatchObservation P z x)|}
    have hconcentration :
        (uniformPMF (Fin R → {−1,1}^[n])).toMeasure.real bad ≤
          2 * Real.exp (-(R : ℝ) * a ^ 2 / 2) := by
      exact measure_finiteUniformEmpiricalMean_sub_expect_ge_le
        (juntaMatchObservation P z) (juntaMatchObservation_mem_Icc P z)
        hRpos a (positiveLearningParameter_toReal_mem_Ioc
          (juntaRestrictionMatchAccuracy k) |>.1.le)
    have hsampleLower :
        fourierEstimatorSampleCount (juntaRestrictionMatchAccuracy k) failure ≤ R := by
      simp [R, juntaRestrictionSampleCount]
    have hexp :
        2 * Real.exp (-(R : ℝ) * a ^ 2 / 2) ≤
          2 * Real.exp
            (-(fourierEstimatorSampleCount
                (juntaRestrictionMatchAccuracy k) failure : ℝ) * a ^ 2 / 2) := by
      gcongr
    calc
      (uniformPMF (Fin R → {−1,1}^[n])).toMeasure.real
          (juntaRestrictionFailureSet target P z k M failure) ≤
          (uniformPMF (Fin R → {−1,1}^[n])).toMeasure.real bad :=
        measureReal_mono
          (juntaRestrictionFailureSet_subset_empiricalBad
            target P z k M hPk failure)
      _ ≤ 2 * Real.exp (-(R : ℝ) * a ^ 2 / 2) := hconcentration
      _ ≤ 2 * Real.exp
          (-(fourierEstimatorSampleCount
              (juntaRestrictionMatchAccuracy k) failure : ℝ) * a ^ 2 / 2) := hexp
      _ ≤ (failure.1 : ℝ) := by
        simpa [a] using two_mul_exp_neg_fourierEstimatorSampleCount_le
          (juntaRestrictionMatchAccuracy k) failure
  have hpre :
      (fun sampleInputs :
          Fin (juntaRestrictionSampleCount k M failure) → {−1,1}^[n] ↦
        (takeMatchingJuntaExamples P z M
            (fun i ↦ (sampleInputs i, target (sampleInputs i))),
          (⟨juntaRestrictionSampleCount k M failure, 0,
            juntaRestrictionSampleCount k M failure +
              juntaRestrictionSampleWork P k M failure⟩ : LearningCost))) ⁻¹'
          {outcome | outcome.1 = none} =
        juntaRestrictionFailureSet target P z k M failure := by
    ext sampleInputs
    rfl
  unfold LearningProgram.eventProbability
  rw [runWithCost_juntaRestrictionSampleProgram, PMF.toOuterMeasure_map_apply]
  rw [hpre]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure
    (uniformPMF
      (Fin (juntaRestrictionSampleCount k M failure) → {−1,1}^[n]))
    (juntaRestrictionFailureSet target P z k M failure)]
  change (uniformPMF
      (Fin (juntaRestrictionSampleCount k M failure) → {−1,1}^[n])).toMeasure.real
      (juntaRestrictionFailureSet target P z k M failure) ≤ (failure.1 : ℝ)
  exact hmeasure

/-- Every successful output consists of exactly `M` correctly labeled examples of the requested
restriction. -/
theorem juntaRestrictionSampleProgram_success_labels
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (Fin M → MatchedJuntaExample P z) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (juntaRestrictionSampleProgram P z k M failure)).support)
    (batch : Fin M → MatchedJuntaExample P z) (hbatch : outcome.1 = some batch) :
    ∀ i,
      (matchedJuntaRestrictionExample P z (batch i)).2 =
        juntaRestriction target P z
          (matchedJuntaRestrictionExample P z (batch i)).1 := by
  rw [runWithCost_juntaRestrictionSampleProgram, PMF.mem_support_map_iff] at houtcome
  obtain ⟨sampleInputs, _, houtput⟩ := houtcome
  have htake : takeMatchingJuntaExamples P z M
      (fun i ↦ (sampleInputs i, target (sampleInputs i))) = some batch := by
    simpa [hbatch] using congrArg (fun output ↦ output.1) houtput
  intro i
  apply matchedJuntaRestrictionExample_label
  rw [takeMatchingJuntaExamples] at htake
  split_ifs at htake with henough
  · have hbatchEq := Option.some.inj htake
    rw [← hbatchEq]

/-- Exact pathwise cost of the finite rejection sampler. -/
theorem juntaRestrictionSampleProgram_cost_eq
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (Fin M → MatchedJuntaExample P z) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (juntaRestrictionSampleProgram P z k M failure)).support) :
    outcome.2 =
      ⟨juntaRestrictionSampleCount k M failure, 0,
        juntaRestrictionSampleCount k M failure +
          juntaRestrictionSampleWork P k M failure⟩ := by
  rw [runWithCost_juntaRestrictionSampleProgram, PMF.mem_support_map_iff] at houtcome
  obtain ⟨sampleInputs, _, rfl⟩ := houtcome
  rfl

/-- Explicit polynomial/logarithmic bound for the number of ambient random examples used by the
rejection sampler. -/
theorem juntaRestrictionSampleCount_cast_le
    (k M : ℕ) (failure : PositiveLearningParameter) :
    (juntaRestrictionSampleCount k M failure : ℚ) ≤
      2 ^ (k + 1) * M +
        16 * 4 ^ k * fourierEstimatorFailureBits failure := by
  rw [juntaRestrictionSampleCount]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  calc
    (fourierEstimatorSampleCount
        (juntaRestrictionMatchAccuracy k) failure : ℚ) ≤
        4 * fourierEstimatorFailureBits failure /
          (juntaRestrictionMatchAccuracy k).1 ^ 2 :=
      fourierEstimatorSampleCount_cast_le
        (juntaRestrictionMatchAccuracy k) failure
    _ = 16 * 4 ^ k * fourierEstimatorFailureBits failure := by
      simp only [juntaRestrictionMatchAccuracy]
      rw [div_pow]
      have hkpow : ((2 : ℚ) ^ k) ^ 2 = 4 ^ k := by
        rw [pow_two, show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
      norm_num [pow_add]
      rw [mul_pow, hkpow]
      norm_num
      ring

/-! ## The finite conditional-law combinator -/

/-- Split a finite vector into the coordinates in the range of an injection and the remaining
coordinates, reindexing the first factor by the injection's domain. -/
noncomputable def injectionVectorSplitEquiv {A : Type*} {M R : ℕ}
    (e : Fin M ↪ Fin R) :
    (Fin R → A) ≃
      (Fin M → A) × ({j : Fin R // j ∉ Set.range e} → A) :=
  (Equiv.piEquivPiSubtypeProd (fun j : Fin R ↦ j ∈ Set.range e) (fun _ ↦ A)).trans
    (Equiv.prodCongr
      (Equiv.piCongrLeft' (fun _ : Set.range e ↦ A)
        (Equiv.ofInjective e e.injective).symm)
      (Equiv.refl _))

@[simp] theorem injectionVectorSplitEquiv_fst
    {A : Type*} {M R : ℕ} (e : Fin M ↪ Fin R) (x : Fin R → A) (i : Fin M) :
    (injectionVectorSplitEquiv e x).1 i = x (e i) := by
  simp [injectionVectorSplitEquiv, Equiv.piCongrLeft', Equiv.ofInjective]

/-- The first projection of a finite uniform product is uniform. -/
theorem map_uniformPMF_fst {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] :
    (uniformPMF (A × B)).map Prod.fst = uniformPMF A := by
  classical
  have hB : (Fintype.card B : ℝ≥0∞) ≠ 0 := by positivity
  have hBtop : (Fintype.card B : ℝ≥0∞) ≠ ∞ := by norm_num
  have hAtop : (Fintype.card A : ℝ≥0∞) ≠ ∞ := by norm_num
  ext a
  rw [PMF.map_apply]
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp only [uniformPMF, PMF.uniformOfFintype_apply, Fintype.card_prod]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
  rw [Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr hBtop) (Or.inl hAtop)]
  calc
    (Fintype.card B : ℝ≥0∞) *
          ((Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹) =
        (Fintype.card A : ℝ≥0∞)⁻¹ *
          ((Fintype.card B : ℝ≥0∞) * (Fintype.card B : ℝ≥0∞)⁻¹) := by
      ac_rfl
    _ = (Fintype.card A : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hB hBtop, mul_one]

/-- Restricting an independent uniform vector along any injection again gives an independent
uniform vector.  This is the finite counting fact needed for the rejection sampler's conditional
law; the injection may depend on the fixed-coordinate sequence, but not on the free-coordinate
sequence. -/
theorem map_uniformPMF_injection_projection
    {A : Type*} [Fintype A] [Nonempty A] {M R : ℕ}
    (e : Fin M ↪ Fin R) :
    (uniformPMF (Fin R → A)).map (fun x i ↦ x (e i)) =
      uniformPMF (Fin M → A) := by
  classical
  let split := injectionVectorSplitEquiv (A := A) e
  calc
    (uniformPMF (Fin R → A)).map (fun x i ↦ x (e i)) =
        ((uniformPMF (Fin R → A)).map split).map Prod.fst := by
      rw [PMF.map_comp]
      congr 1
    _ = (uniformPMF
          ((Fin M → A) × ({j : Fin R // j ∉ Set.range e} → A))).map
            Prod.fst := by
      rw [map_uniformPMF_equiv split]
    _ = uniformPMF (Fin M → A) := map_uniformPMF_fst

/-- For a fixed successful fixed-coordinate sequence, select the free parts at exactly the same
accepted indices used by the executable rejection sampler. -/
def selectedJuntaFreeBatch (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (fixed : Fin R → JuntaFixedAssignment P)
    (h : M ≤ (fixedMatchingIndices P z fixed).card)
    (free : Fin R → JuntaFreeAssignment P) :
    Fin M → JuntaFreeAssignment P :=
  fun i ↦ free (fixedMatchingIndexEmbedding P z M fixed h i)

/-- Attach the restricted target labels to a selected free-input batch. -/
def juntaRestrictionLabeledBatch (target : BooleanFunction n)
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P) {M : ℕ}
    (inputs : Fin M → JuntaFreeAssignment P) :
    Fin M → (JuntaFreeAssignment P × Sign) :=
  fun i ↦ (inputs i, juntaRestriction target P z (inputs i))

/-- Ambient target-generated examples reconstructed from their fixed and free coordinate
sequences. -/
def juntaLabeledSamplesFromSplit (target : BooleanFunction n)
    (P : Finset (Fin n)) {R : ℕ}
    (fixed : Fin R → JuntaFixedAssignment P)
    (free : Fin R → JuntaFreeAssignment P) :
    Fin R → ({−1,1}^[n] × Sign) :=
  fun i ↦
    let x := combineJuntaAssignment P (fixed i) (free i)
    (x, target x)

/-- The conditional-law selector is exactly the projection of the executable sampler's successful
output; this ties the finite injection lemma to the real `LearningProgram`, rather than to an
idealized conditional oracle. -/
theorem takeMatchingJuntaExamples_from_split
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (fixed : Fin R → JuntaFixedAssignment P)
    (free : Fin R → JuntaFreeAssignment P)
    (h : M ≤ (fixedMatchingIndices P z fixed).card) :
    Option.map
        (fun batch i ↦ matchedJuntaRestrictionExample P z (batch i))
        (takeMatchingJuntaExamples P z M
          (juntaLabeledSamplesFromSplit target P fixed free)) =
      some (juntaRestrictionLabeledBatch target P z
        (selectedJuntaFreeBatch P z M fixed h free)) := by
  have hfixedParts :
      (fun i ↦ juntaFixedPart P
        (juntaLabeledSamplesFromSplit target P fixed free i).1) = fixed := by
    funext i
    simp [juntaLabeledSamplesFromSplit]
  have hcount : M ≤ juntaMatchCount P z
      (juntaLabeledSamplesFromSplit target P fixed free) := by
    simpa [juntaMatchCount, juntaMatchingIndices, juntaLabeledSamplesFromSplit]
      using h
  have hembedding :
      juntaMatchingIndexEmbedding P z M
          (juntaLabeledSamplesFromSplit target P fixed free) hcount =
        fixedMatchingIndexEmbedding P z M fixed h := by
    apply Function.Embedding.ext
    intro i
    simp [juntaMatchingIndexEmbedding, hfixedParts]
  have hselected (i : Fin M) :
      fixed (fixedMatchingIndexEmbedding P z M fixed h i) = z := by
    have hmem :
        ((fixedMatchingIndices P z fixed).orderEmbOfFin rfl)
            (initialFinEmbedding h i) ∈ fixedMatchingIndices P z fixed :=
      (fixedMatchingIndices P z fixed).orderEmbOfFin_mem rfl _
    have heq := (Finset.mem_filter.mp hmem).2
    simpa [fixedMatchingIndexEmbedding] using heq
  rw [takeMatchingJuntaExamples, dif_pos hcount]
  apply congrArg some
  funext i
  apply Prod.ext
  · simp only [matchedJuntaRestrictionExample, juntaRestrictionLabeledBatch,
      selectedJuntaFreeBatch, juntaLabeledSamplesFromSplit,
      juntaFreePart_combineJuntaAssignment]
    exact congrArg free
      (congrArg (fun e : Fin M ↪ Fin R ↦ e i) hembedding)
  · simp [matchedJuntaRestrictionExample, juntaRestrictionLabeledBatch,
      selectedJuntaFreeBatch, juntaLabeledSamplesFromSplit,
      juntaRestriction, hembedding, hselected i]

/-- Narrow conditional-law lemma for Exercise 6.31(b).  Once the fixed-coordinate sequence is
held fixed and contains at least `M` matches, the first `M` accepted free inputs and labels have
exactly the law of `M` independent uniform random examples from the restriction. -/
theorem map_uniformPMF_selectedJuntaRestrictionBatch
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (fixed : Fin R → JuntaFixedAssignment P)
    (h : M ≤ (fixedMatchingIndices P z fixed).card) :
    (uniformPMF (Fin R → JuntaFreeAssignment P)).map
        (fun free ↦ juntaRestrictionLabeledBatch target P z
          (selectedJuntaFreeBatch P z M fixed h free)) =
      (uniformPMF (Fin M → JuntaFreeAssignment P)).map
        (juntaRestrictionLabeledBatch target P z) := by
  let e := fixedMatchingIndexEmbedding P z M fixed h
  calc
    (uniformPMF (Fin R → JuntaFreeAssignment P)).map
        (fun free ↦ juntaRestrictionLabeledBatch target P z
          (selectedJuntaFreeBatch P z M fixed h free)) =
        ((uniformPMF (Fin R → JuntaFreeAssignment P)).map
          (fun free i ↦ free (e i))).map
            (juntaRestrictionLabeledBatch target P z) := by
      rw [PMF.map_comp]
      rfl
    _ = (uniformPMF (Fin M → JuntaFreeAssignment P)).map
        (juntaRestrictionLabeledBatch target P z) := by
      rw [map_uniformPMF_injection_projection e]

/-! ## Exercise 6.31(b): public elimination rule -/

/-- Project every successful certified ambient batch to the corresponding labeled batch on the
restricted cube. -/
def projectJuntaRestrictionBatch (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) {M : ℕ} :
    Option (Fin M → MatchedJuntaExample P z) →
      Option (Fin M → (JuntaFreeAssignment P × Sign)) :=
  Option.map fun batch i ↦ matchedJuntaRestrictionExample P z (batch i)

/-- Lift a bad event on an ideal restricted batch to the executable sampler output, counting a
failed rejection sample as bad. -/
def JuntaRestrictionSampleBad (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) {M : ℕ}
    (bad : (Fin M → (JuntaFreeAssignment P × Sign)) → Prop)
    (sampled : Option (Fin M → MatchedJuntaExample P z)) : Prop :=
  match projectJuntaRestrictionBatch P z sampled with
  | none => True
  | some batch => bad batch

/-- Split a vector of ambient inputs into its fixed- and free-coordinate vectors. -/
def juntaInputBatchSplitEquiv (P : Finset (Fin n)) (R : ℕ) :
    (Fin R → {−1,1}^[n]) ≃
      (Fin R → JuntaFixedAssignment P) × (Fin R → JuntaFreeAssignment P) where
  toFun inputs :=
    (fun r ↦ juntaFixedPart P (inputs r), fun r ↦ juntaFreePart P (inputs r))
  invFun parts := fun r ↦ combineJuntaAssignment P (parts.1 r) (parts.2 r)
  left_inv inputs := by
    funext r i
    by_cases hi : i ∈ P <;>
      simp [juntaFixedPart, juntaFreePart, combineJuntaAssignment, hi]
  right_inv parts := by
    rcases parts with ⟨fixed, free⟩
    apply Prod.ext
    · funext r i
      simp [juntaFixedPart]
    · funext r i
      simp [juntaFreePart]

@[simp] theorem juntaInputBatchSplitEquiv_symm_apply
    (P : Finset (Fin n)) (R : ℕ)
    (fixed : Fin R → JuntaFixedAssignment P)
    (free : Fin R → JuntaFreeAssignment P) :
    (juntaInputBatchSplitEquiv P R).symm (fixed, free) =
      fun r ↦ combineJuntaAssignment P (fixed r) (free r) := rfl

/-- Pure projection of the executable sampler controller on a raw ambient input vector. -/
def rawProjectedJuntaRestrictionBatch
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M : ℕ) {R : ℕ}
    (inputs : Fin R → {−1,1}^[n]) :
    Option (Fin M → (JuntaFreeAssignment P × Sign)) :=
  projectJuntaRestrictionBatch P z
    (takeMatchingJuntaExamples P z M
      (fun r ↦ (inputs r, target (inputs r))))

/-- Independent uniform fixed and free vectors give the same law as a uniform ambient vector. -/
theorem map_uniformPMF_rawProjectedJuntaRestrictionBatch
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M R : ℕ) :
    (uniformPMF (Fin R → {−1,1}^[n])).map
        (rawProjectedJuntaRestrictionBatch target P z M) =
      (uniformPMF (Fin R → JuntaFixedAssignment P)).bind fun fixed ↦
        (uniformPMF (Fin R → JuntaFreeAssignment P)).map fun free ↦
          rawProjectedJuntaRestrictionBatch target P z M
            (fun r ↦ combineJuntaAssignment P (fixed r) (free r)) := by
  let split := juntaInputBatchSplitEquiv P R
  calc
    (uniformPMF (Fin R → {−1,1}^[n])).map
        (rawProjectedJuntaRestrictionBatch target P z M) =
        ((uniformPMF (Fin R → {−1,1}^[n])).map split).map
          (fun parts ↦ rawProjectedJuntaRestrictionBatch target P z M
            (split.symm parts)) := by
      rw [PMF.map_comp]
      congr 1
      funext inputs
      simp [split]
    _ = (uniformPMF
          ((Fin R → JuntaFixedAssignment P) ×
            (Fin R → JuntaFreeAssignment P))).map
          (fun parts ↦ rawProjectedJuntaRestrictionBatch target P z M
            (split.symm parts)) := by
      rw [map_uniformPMF_equiv split]
    _ = ((uniformPMF (Fin R → JuntaFixedAssignment P)).bind fun fixed ↦
          (uniformPMF (Fin R → JuntaFreeAssignment P)).map fun free ↦
            (fixed, free)).map
          (fun parts ↦ rawProjectedJuntaRestrictionBatch target P z M
            (split.symm parts)) := by
      rw [uniformPMF_bind_map_pair]
    _ = (uniformPMF (Fin R → JuntaFixedAssignment P)).bind fun fixed ↦
        (uniformPMF (Fin R → JuntaFreeAssignment P)).map fun free ↦
          rawProjectedJuntaRestrictionBatch target P z M
            (fun r ↦ combineJuntaAssignment P (fixed r) (free r)) := by
      rw [PMF.map_bind]
      congr 1
      funext fixed
      rw [PMF.map_comp]
      congr 1

/-- A probability mass function assigns finite outer measure to every event. -/
theorem pmfToOuterMeasure_ne_top {α : Type*} (p : PMF α) (event : Set α) :
    p.toOuterMeasure event ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  calc
    p.toOuterMeasure event ≤ p.toOuterMeasure Set.univ :=
      p.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := by simp [PMF.toOuterMeasure_apply, p.tsum_coe]

/-- Pure finite disintegration: after discarding sampler failures, every bad event on the
projected successful batch is no more likely than under ideal independent restricted examples. -/
theorem rawProjectedJuntaRestrictionBatch_successBadProbability_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (M R : ℕ)
    (bad : (Fin M → (JuntaFreeAssignment P × Sign)) → Prop)
    (η : ℝ)
    (hideal :
      (((uniformPMF (Fin M → JuntaFreeAssignment P)).map
        (juntaRestrictionLabeledBatch target P z)).toOuterMeasure
          {batch | bad batch}).toReal ≤ η) :
    (((uniformPMF (Fin R → {−1,1}^[n])).map
      (rawProjectedJuntaRestrictionBatch target P z M)).toOuterMeasure
        {output | match output with
          | none => False
          | some batch => bad batch}).toReal ≤ η := by
  let ideal := (uniformPMF (Fin M → JuntaFreeAssignment P)).map
    (juntaRestrictionLabeledBatch target P z)
  let successBad : Set (Option (Fin M → (JuntaFreeAssignment P × Sign))) :=
    {output | match output with
      | none => False
      | some batch => bad batch}
  have hconditional (fixed : Fin R → JuntaFixedAssignment P) :
      ((uniformPMF (Fin R → JuntaFreeAssignment P)).map fun free ↦
        rawProjectedJuntaRestrictionBatch target P z M
          (fun r ↦ combineJuntaAssignment P (fixed r) (free r))).toOuterMeasure
            successBad ≤ ideal.toOuterMeasure {batch | bad batch} := by
    by_cases hmatches : M ≤ (fixedMatchingIndices P z fixed).card
    · have hlaw :
          (uniformPMF (Fin R → JuntaFreeAssignment P)).map (fun free ↦
            rawProjectedJuntaRestrictionBatch target P z M
              (fun r ↦ combineJuntaAssignment P (fixed r) (free r))) =
            ideal.map some := by
        calc
          (uniformPMF (Fin R → JuntaFreeAssignment P)).map (fun free ↦
              rawProjectedJuntaRestrictionBatch target P z M
                (fun r ↦ combineJuntaAssignment P (fixed r) (free r))) =
              (uniformPMF (Fin R → JuntaFreeAssignment P)).map (fun free ↦
                some (juntaRestrictionLabeledBatch target P z
                  (selectedJuntaFreeBatch P z M fixed hmatches free))) := by
            congr 1
            funext free
            change Option.map
                (fun batch i ↦ matchedJuntaRestrictionExample P z (batch i))
                (takeMatchingJuntaExamples P z M
                  (juntaLabeledSamplesFromSplit target P fixed free)) =
              some (juntaRestrictionLabeledBatch target P z
                (selectedJuntaFreeBatch P z M fixed hmatches free))
            exact takeMatchingJuntaExamples_from_split
              target P z M fixed free hmatches
          _ = ((uniformPMF (Fin R → JuntaFreeAssignment P)).map (fun free ↦
                juntaRestrictionLabeledBatch target P z
                  (selectedJuntaFreeBatch P z M fixed hmatches free))).map some := by
            rw [PMF.map_comp]
            rfl
          _ = ideal.map some := by
            rw [map_uniformPMF_selectedJuntaRestrictionBatch
              target P z M fixed hmatches]
      rw [hlaw, PMF.toOuterMeasure_map_apply]
      rfl
    · have hraw : (fun free : Fin R → JuntaFreeAssignment P ↦
          rawProjectedJuntaRestrictionBatch target P z M
            (fun r ↦ combineJuntaAssignment P (fixed r) (free r))) =
          fun _ ↦ none := by
        funext free
        have hlt : juntaMatchCount P z
            (juntaLabeledSamplesFromSplit target P fixed free) < M := by
          simpa [juntaMatchCount, juntaMatchingIndices,
            juntaLabeledSamplesFromSplit] using Nat.lt_of_not_ge hmatches
        rw [rawProjectedJuntaRestrictionBatch, projectJuntaRestrictionBatch]
        change Option.map _
            (takeMatchingJuntaExamples P z M
              (juntaLabeledSamplesFromSplit target P fixed free)) = none
        rw [(takeMatchingJuntaExamples_eq_none_iff P z M _).2 hlt]
        rfl
      rw [hraw, PMF.toOuterMeasure_map_apply]
      simp [successBad]
  have houter :
      ((uniformPMF (Fin R → {−1,1}^[n])).map
        (rawProjectedJuntaRestrictionBatch target P z M)).toOuterMeasure
          successBad ≤ ideal.toOuterMeasure {batch | bad batch} := by
    rw [map_uniformPMF_rawProjectedJuntaRestrictionBatch target P z M R,
      PMF.toOuterMeasure_bind_apply]
    calc
      (∑' fixed, (uniformPMF (Fin R → JuntaFixedAssignment P)) fixed *
          ((uniformPMF (Fin R → JuntaFreeAssignment P)).map fun free ↦
            rawProjectedJuntaRestrictionBatch target P z M
              (fun r ↦ combineJuntaAssignment P (fixed r) (free r))).toOuterMeasure
                successBad) ≤
          ∑' fixed, (uniformPMF (Fin R → JuntaFixedAssignment P)) fixed *
            ideal.toOuterMeasure {batch | bad batch} := by
        apply ENNReal.tsum_le_tsum
        intro fixed
        exact mul_le_mul_right (hconditional fixed) _
      _ = ideal.toOuterMeasure {batch | bad batch} := by
        rw [ENNReal.tsum_mul_right,
          (uniformPMF (Fin R → JuntaFixedAssignment P)).tsum_coe, one_mul]
  change
    (((uniformPMF (Fin R → {−1,1}^[n])).map
      (rawProjectedJuntaRestrictionBatch target P z M)).toOuterMeasure
        successBad).toReal ≤ η
  exact (ENNReal.toReal_mono
    (pmfToOuterMeasure_ne_top ideal {batch | bad batch}) houter).trans hideal

/-- Exercise 6.31(b)'s public elimination rule.  Any bad-event guarantee proved for an ideal
independent restricted batch transfers to the executable ambient rejection sampler, with only the
sampler's explicit failure budget added. -/
theorem juntaRestrictionSampleProgram_badProbability_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k M : ℕ) (hPk : P.card ≤ k)
    (failure : PositiveLearningParameter)
    (bad : (Fin M → (JuntaFreeAssignment P × Sign)) → Prop)
    (η : ℝ) (hη : 0 ≤ η)
    (hideal :
      (((uniformPMF (Fin M → JuntaFreeAssignment P)).map
        (juntaRestrictionLabeledBatch target P z)).toOuterMeasure
          {batch | bad batch}).toReal ≤ η) :
    LearningProgram.eventProbability
        (juntaRestrictionSampleProgram P z k M failure) target
        (fun outcome ↦ JuntaRestrictionSampleBad P z bad outcome.1) ≤
      (failure.1 : ℝ) + η := by
  let program := juntaRestrictionSampleProgram P z k M failure
  let successEvent :
      (Option (Fin M → MatchedJuntaExample P z) × LearningCost) → Prop :=
    fun outcome ↦
      match projectJuntaRestrictionBatch P z outcome.1 with
      | none => False
      | some batch => bad batch
  have hfailure :
      LearningProgram.eventProbability program target
          (fun outcome ↦ outcome.1 = none) ≤ (failure.1 : ℝ) := by
    simpa only [program] using
      juntaRestrictionSampleProgram_failureProbability_le
        target P z k M hPk failure
  have hsuccess :
      LearningProgram.eventProbability program target successEvent ≤ η := by
    have hpure := rawProjectedJuntaRestrictionBatch_successBadProbability_le
      target P z M (juntaRestrictionSampleCount k M failure) bad η hideal
    unfold LearningProgram.eventProbability
    dsimp only [program]
    rw [runWithCost_juntaRestrictionSampleProgram,
      PMF.toOuterMeasure_map_apply]
    rw [PMF.toOuterMeasure_map_apply] at hpure
    simpa [successEvent, rawProjectedJuntaRestrictionBatch,
      projectJuntaRestrictionBatch] using hpure
  let failureSet :
      Set (Option (Fin M → MatchedJuntaExample P z) × LearningCost) :=
    {outcome | outcome.1 = none}
  let successSet :
      Set (Option (Fin M → MatchedJuntaExample P z) × LearningCost) :=
    {outcome | successEvent outcome}
  have hset :
      {outcome : Option (Fin M → MatchedJuntaExample P z) × LearningCost |
        JuntaRestrictionSampleBad P z bad outcome.1} =
          failureSet ∪ successSet := by
    ext outcome
    rcases outcome with ⟨output, cost⟩
    cases output <;>
      simp [failureSet, successSet, successEvent, JuntaRestrictionSampleBad,
        projectJuntaRestrictionBatch]
  let law := LearningProgram.runWithCost target program
  have hfailureTop : law.toOuterMeasure failureSet ≠ ∞ :=
    pmfToOuterMeasure_ne_top law failureSet
  have hsuccessTop : law.toOuterMeasure successSet ≠ ∞ :=
    pmfToOuterMeasure_ne_top law successSet
  unfold LearningProgram.eventProbability at hfailure hsuccess ⊢
  rw [show LearningProgram.runWithCost target
    (juntaRestrictionSampleProgram P z k M failure) = law by rfl, hset]
  calc
    (law.toOuterMeasure (failureSet ∪ successSet)).toReal ≤
        (law.toOuterMeasure failureSet + law.toOuterMeasure successSet).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.add_ne_top.2 ⟨hfailureTop, hsuccessTop⟩
      · exact measure_union_le _ _
    _ = (law.toOuterMeasure failureSet).toReal +
        (law.toOuterMeasure successSet).toReal := by
      rw [ENNReal.toReal_add hfailureTop hsuccessTop]
    _ ≤ (failure.1 : ℝ) + η := by
      rw [← max_eq_left hη]
      exact add_le_add hfailure (hsuccess.trans (le_max_left _ _))

/-! ## Exercise 6.31(c): the relevant-coordinate reduction -/

/-- A free coordinate is relevant to a restriction when changing only that coordinate can
change the restricted target.  This witness formulation avoids imposing an artificial `Fin m`
enumeration on the complement of `P`. -/
def IsRelevantJuntaRestriction (target : BooleanFunction n)
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (i : JuntaFreeIndex P) : Prop :=
  ∃ y₀ y₁ : JuntaFreeAssignment P,
    (∀ j, j ≠ i → y₀ j = y₁ j) ∧
      juntaRestriction target P z y₀ ≠ juntaRestriction target P z y₁

/-- A coordinate relevant to a restriction of a function depending on `J` must itself lie in
`J`.  Thus a sound relevant-coordinate finder can never spend depth outside a junta witness. -/
theorem mem_of_isRelevantJuntaRestriction_of_dependsOn
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (i : JuntaFreeIndex P)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (hrelevant : IsRelevantJuntaRestriction target P z i) :
    i.1 ∈ J := by
  classical
  by_contra hiJ
  obtain ⟨y₀, y₁, hagree, hne⟩ := hrelevant
  apply hne
  apply hdepends
  intro j hjJ
  by_cases hjP : j ∈ P
  · simp [combineJuntaAssignment, hjP]
  · have hji : (⟨j, hjP⟩ : JuntaFreeIndex P) ≠ i := by
      intro hji
      apply hiJ
      have hval : j = i.1 := congrArg Subtype.val hji
      simpa [hval] using hjJ
    simpa [juntaRestriction, combineJuntaAssignment, hjP] using
      hagree (⟨j, hjP⟩ : JuntaFreeIndex P) hji

/-- Once the fixed coordinates contain a dependence witness, every resulting restriction is
constant.  The displayed value uses the canonical all-`+1` free assignment and hence introduces
no choice operator into the algorithm. -/
theorem juntaRestriction_eq_const_of_dependsOn_of_subset
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P)
    (hdepends : DependsOn target (J : Set (Fin n))) (hJP : J ⊆ P) :
    juntaRestriction target P z =
      fun _ ↦ target (combineJuntaAssignment P z (fun _ ↦ 1)) := by
  funext y
  apply hdepends
  intro i hiJ
  have hiP : i ∈ P := hJP hiJ
  simp [combineJuntaAssignment, hiP]

/-- A successful node analysis either certifies a constant restriction or returns a genuinely
relevant coordinate outside the already-fixed set. -/
inductive JuntaNodeDecision (P : Finset (Fin n)) where
  /-- The restriction is the indicated constant. -/
  | constant (value : Sign)
  /-- Split on a relevant coordinate of the restriction. -/
  | relevant (coordinate : JuntaFreeIndex P)

namespace JuntaNodeDecision

/-- Semantic correctness of one node decision. -/
def IsCorrect (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) : JuntaNodeDecision P → Prop
  | .constant value => juntaRestriction target P z = fun _ ↦ value
  | .relevant coordinate => IsRelevantJuntaRestriction target P z coordinate

/-- Failure event for one node call.  `none` is an explicit algorithmic failure; an incorrect
returned certificate is also counted as failure. -/
def IsBad (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) : Option (JuntaNodeDecision P) → Prop
  | none => True
  | some decision => ¬ decision.IsCorrect target P z

theorem isCorrect_of_not_isBad
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) {decision : JuntaNodeDecision P}
    (hgood : ¬ IsBad target P z (some decision)) :
    decision.IsCorrect target P z := by
  simpa [IsBad] using hgood

end JuntaNodeDecision

/-- The narrow injected algorithmic interface used by Lemma 6.37.  A realization combines the
constant test from part (a), the restriction sampler from part (b), and the assumed algorithm for
finding one relevant coordinate of a nonconstant restriction.  Its program remains ordinary
ambient random-example syntax; the two bounds charge every oracle call and every local step. -/
structure JuntaRelevantCoordinateFinder (n k : ℕ) where
  /-- One adaptive node call at total confidence parameter `failure`. -/
  program : (P : Finset (Fin n)) → JuntaFixedAssignment P →
    PositiveLearningParameter →
      LearningProgram n .randomExamples (Option (JuntaNodeDecision P))
  /-- Uniform random-example bound for one node call. -/
  randomExampleBound : PositiveLearningParameter → ℕ
  /-- Uniform local-work bound for one node call. -/
  workBound : PositiveLearningParameter → ℕ
  /-- The implementation uses only random examples and respects both declared pathwise bounds. -/
  cost_le : ∀ (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (failure : PositiveLearningParameter)
    (outcome : Option (JuntaNodeDecision P) × LearningCost),
    outcome ∈ (LearningProgram.runWithCost target (program P z failure)).support →
      outcome.2.randomExamples ≤ randomExampleBound failure ∧
      outcome.2.queries = 0 ∧ outcome.2.work ≤ workBound failure
  /-- On any `k`-junta witness, one node call fails with probability at most `failure`. -/
  failureProbability_le : ∀ (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (_hJcard : J.card ≤ k)
    (_hdepends : DependsOn target (J : Set (Fin n)))
    (_hPsubset : P ⊆ J)
    (failure : PositiveLearningParameter),
    LearningProgram.eventProbability (program P z failure) target
        (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤
      (failure.1 : ℝ)

/-- Exact number of possible node calls in a full binary recursion of depth `k`. -/
def juntaTreeCallCount : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + 2 * juntaTreeCallCount k

@[simp] theorem juntaTreeCallCount_zero : juntaTreeCallCount 0 = 1 := rfl

@[simp] theorem juntaTreeCallCount_succ (k : ℕ) :
    juntaTreeCallCount (k + 1) = 1 + 2 * juntaTreeCallCount k := rfl

theorem juntaTreeCallCount_pos (k : ℕ) : 0 < juntaTreeCallCount k := by
  cases k <;> simp

/-- Divide a total failure budget equally among all possible recursive node calls. -/
def juntaTreePerCallFailure (k : ℕ) (failure : PositiveLearningParameter) :
    PositiveLearningParameter := by
  refine ⟨failure.1 / juntaTreeCallCount k, ?_, ?_⟩
  · exact div_pos failure.2.1 (by exact_mod_cast juntaTreeCallCount_pos k)
  · calc
      failure.1 / juntaTreeCallCount k ≤ failure.1 := by
        exact div_le_self (le_of_lt failure.2.1)
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (juntaTreeCallCount_pos k).ne'))
      _ ≤ 1 / 2 := failure.2.2

@[simp] theorem juntaTreePerCallFailure_value
    (k : ℕ) (failure : PositiveLearningParameter) :
    (juntaTreePerCallFailure k failure).1 =
      failure.1 / juntaTreeCallCount k := rfl

/-- The allocated per-node budgets sum to the requested total budget. -/
theorem juntaTreeCallCount_mul_perCallFailure
    (k : ℕ) (failure : PositiveLearningParameter) :
    (juntaTreeCallCount k : ℚ) * (juntaTreePerCallFailure k failure).1 =
      failure.1 := by
  have hne : (juntaTreeCallCount k : ℚ) ≠ 0 := by
    exact_mod_cast (juntaTreeCallCount_pos k).ne'
  rw [juntaTreePerCallFailure_value]
  field_simp [hne]

/-! ### Extending partial assignments -/

/-- Extend a fixed assignment by assigning one currently free coordinate. -/
def insertJuntaFixedAssignment (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (i : JuntaFreeIndex P) (value : Sign) :
    JuntaFixedAssignment (insert i.1 P) :=
  fun j ↦ if hji : j.1 = i.1 then value else
    z ⟨j.1, (Finset.mem_insert.mp j.2).resolve_left hji⟩

@[simp] theorem insertJuntaFixedAssignment_apply_new
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (i : JuntaFreeIndex P) (value : Sign) :
    insertJuntaFixedAssignment P z i value
        ⟨i.1, Finset.mem_insert_self i.1 P⟩ = value := by
  simp [insertJuntaFixedAssignment]

@[simp] theorem insertJuntaFixedAssignment_apply_old
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (i : JuntaFreeIndex P) (value : Sign) (j : P) :
    insertJuntaFixedAssignment P z i value
        ⟨j.1, Finset.mem_insert_of_mem j.2⟩ = z j := by
  have hji : j.1 ≠ i.1 := by
    intro h
    apply i.2
    simpa [h] using j.2
  simp [insertJuntaFixedAssignment, hji]

/-- Matching an extended assignment means matching the old assignment and the newly fixed
coordinate. -/
theorem matches_insertJuntaFixedAssignment_iff
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (i : JuntaFreeIndex P) (value : Sign) (x : {−1,1}^[n]) :
    MatchesJuntaAssignment (insert i.1 P)
        (insertJuntaFixedAssignment P z i value) x ↔
      MatchesJuntaAssignment P z x ∧ x i.1 = value := by
  constructor
  · intro h
    constructor
    · intro j
      simpa using h ⟨j.1, Finset.mem_insert_of_mem j.2⟩
    · simpa using h ⟨i.1, Finset.mem_insert_self i.1 P⟩
  · rintro ⟨hP, hi⟩ j
    rcases Finset.mem_insert.mp j.2 with hji | hjP
    · have hj : j = ⟨i.1, Finset.mem_insert_self i.1 P⟩ :=
        Subtype.ext hji
      subst j
      simpa using hi
    · have hji : j.1 ≠ i.1 := by
        intro e
        apply i.2
        simpa [← e] using hjP
      simpa [insertJuntaFixedAssignment, hji] using hP ⟨j.1, hjP⟩

/-! ### Building a dependent decision tree -/

namespace F₂DecisionTree

/-- Transport only the phantom available-coordinate index of a decision tree. -/
def castAvailable {α : Type*} {A B : Finset (Fin n)} (h : A = B)
    (tree : F₂DecisionTree n α A) : F₂DecisionTree n α B :=
  h ▸ tree

@[simp] theorem eval_castAvailable {α : Type*} {A B : Finset (Fin n)}
    (h : A = B) (tree : F₂DecisionTree n α A) (x : F₂Cube n) :
    (castAvailable h tree).eval x = tree.eval x := by
  subst B
  rfl

@[simp] theorem depth_castAvailable {α : Type*} {A B : Finset (Fin n)}
    (h : A = B) (tree : F₂DecisionTree n α A) :
    (castAvailable h tree).depth = tree.depth := by
  subst B
  rfl

end F₂DecisionTree

/-- Join two successfully learned child restrictions at their newly fixed coordinate. -/
def assembleJuntaQuery (P : Finset (Fin n)) (i : JuntaFreeIndex P)
    (zeroTree oneTree :
      Option (F₂DecisionTree n Sign (Finset.univ \ insert i.1 P))) :
    Option (F₂DecisionTree n Sign (Finset.univ \ P)) :=
  match zeroTree, oneTree with
  | some zeroChild, some oneChild =>
      some (.query i.1 (by simp [i.2])
        (F₂DecisionTree.castAvailable (Finset.sdiff_insert _ _ _) zeroChild)
        (F₂DecisionTree.castAvailable (Finset.sdiff_insert _ _ _) oneChild))
  | _, _ => none

/-- At zero fuel, retain exactly a returned constant certificate as a leaf. -/
def juntaNodeLeafOutput (P : Finset (Fin n)) :
    Option (JuntaNodeDecision P) →
      Option (F₂DecisionTree n Sign (Finset.univ \ P))
  | some (.constant value) => some (.leaf value)
  | _ => none

/-- Recursive random-example learner for one partial assignment.  A zero branch fixes the sign
`binarySignEquiv 0 = +1`, while a one branch fixes `binarySignEquiv 1 = -1`; this is the explicit
bridge from sign restrictions to the additive decision-tree convention. -/
def recursiveJuntaLearnerAux {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (failure : PositiveLearningParameter) :
    (fuel : ℕ) → (P : Finset (Fin n)) → JuntaFixedAssignment P →
      LearningProgram n .randomExamples
        (Option (F₂DecisionTree n Sign (Finset.univ \ P)))
  | 0, P, z =>
      LearningProgram.map (juntaNodeLeafOutput P) (finder.program P z failure)
  | fuel + 1, P, z =>
      LearningProgram.bind
        (fun decision ↦ match decision with
          | none => .pure none
          | some (.constant value) => .pure (some (.leaf value))
          | some (.relevant i) =>
              LearningProgram.bind
                (fun zeroTree ↦
                  LearningProgram.map
                    (assembleJuntaQuery P i zeroTree)
                    (recursiveJuntaLearnerAux finder failure fuel
                      (insert i.1 P)
                      (insertJuntaFixedAssignment P z i (binarySignEquiv 1))))
                (recursiveJuntaLearnerAux finder failure fuel
                  (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 0))))
        (finder.program P z failure)

/-- The unique assignment on the empty set of fixed coordinates. -/
def emptyJuntaFixedAssignment : JuntaFixedAssignment (∅ : Finset (Fin n)) :=
  fun i ↦ isEmptyElim i

/-- Exercise 6.31(c)'s learner.  The confidence scheduler allocates the requested total failure
budget across the full binary recursion tree. -/
def recursiveJuntaLearner {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (failure : PositiveLearningParameter) :
    LearningProgram n .randomExamples (Option (DecisionTree n Sign)) :=
  LearningProgram.map
    (Option.map fun tree ↦
      F₂DecisionTree.castAvailable (by simp) tree)
    (recursiveJuntaLearnerAux finder (juntaTreePerCallFailure k failure) k ∅
      emptyJuntaFixedAssignment)

/-! ### Semantic correctness of the assembled tree -/

namespace F₂DecisionTree

/-- A partial decision tree computes the target on every input extending its fixed assignment. -/
def ComputesJuntaRestriction {P : Finset (Fin n)}
    (tree : F₂DecisionTree n Sign (Finset.univ \ P))
    (target : BooleanFunction n) (z : JuntaFixedAssignment P) : Prop :=
  ∀ x : F₂Cube n,
    MatchesJuntaAssignment P z (binaryCubeSignEquiv n x) →
      tree.eval x = target (binaryCubeSignEquiv n x)

/-- A leaf computes a restriction certified to be constant. -/
theorem computesJuntaRestriction_leaf
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (value : Sign)
    (hconstant : juntaRestriction target P z = fun _ ↦ value) :
    (F₂DecisionTree.leaf value :
      F₂DecisionTree n Sign (Finset.univ \ P)).ComputesJuntaRestriction target z := by
  intro x hx
  have hvalue := congrFun hconstant
    (juntaFreePart P (binaryCubeSignEquiv n x))
  rw [juntaRestriction,
    combineJuntaAssignment_freePart_of_matches P z
      (binaryCubeSignEquiv n x) hx] at hvalue
  exact hvalue.symm

end F₂DecisionTree

/-- Failure of the recursive learner is either an explicit `none` or a returned tree that does
not compute the requested restriction. -/
def JuntaTreeOutputBad (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) :
    Option (F₂DecisionTree n Sign (Finset.univ \ P)) → Prop
  | none => True
  | some tree => ¬ tree.ComputesJuntaRestriction target z

/-- A nonbad successful output carries the advertised semantic guarantee. -/
theorem computesJuntaRestriction_of_not_outputBad
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P)
    {tree : F₂DecisionTree n Sign (Finset.univ \ P)}
    (hgood : ¬ JuntaTreeOutputBad target P z (some tree)) :
    tree.ComputesJuntaRestriction target z := by
  classical
  simpa [JuntaTreeOutputBad] using hgood

/-- If both recursively learned restrictions are correct, querying their newly fixed coordinate
produces a correct tree for the parent restriction. -/
theorem not_outputBad_assembleJuntaQuery
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (i : JuntaFreeIndex P)
    (zeroTree oneTree :
      Option (F₂DecisionTree n Sign (Finset.univ \ insert i.1 P)))
    (hzero : ¬ JuntaTreeOutputBad target (insert i.1 P)
      (insertJuntaFixedAssignment P z i (binarySignEquiv 0)) zeroTree)
    (hone : ¬ JuntaTreeOutputBad target (insert i.1 P)
      (insertJuntaFixedAssignment P z i (binarySignEquiv 1)) oneTree) :
    ¬ JuntaTreeOutputBad target P z (assembleJuntaQuery P i zeroTree oneTree) := by
  classical
  cases zeroTree with
  | none => simp [JuntaTreeOutputBad] at hzero
  | some zeroChild =>
      cases oneTree with
      | none => simp [JuntaTreeOutputBad] at hone
      | some oneChild =>
          have hzeroComputes := computesJuntaRestriction_of_not_outputBad
            target (insert i.1 P)
            (insertJuntaFixedAssignment P z i (binarySignEquiv 0)) hzero
          have honeComputes := computesJuntaRestriction_of_not_outputBad
            target (insert i.1 P)
            (insertJuntaFixedAssignment P z i (binarySignEquiv 1)) hone
          have hcomputes : F₂DecisionTree.ComputesJuntaRestriction
              (F₂DecisionTree.query i.1 (by simp [i.2])
                (F₂DecisionTree.castAvailable
                  (Finset.sdiff_insert Finset.univ P i.1) zeroChild)
                (F₂DecisionTree.castAvailable
                  (Finset.sdiff_insert Finset.univ P i.1) oneChild)) target z := by
            intro x hx
            by_cases hxi : x i.1 = 0
            · simp only [F₂DecisionTree.eval, hxi, if_pos,
                F₂DecisionTree.eval_castAvailable]
              apply hzeroComputes x
              rw [matches_insertJuntaFixedAssignment_iff]
              refine ⟨hx, ?_⟩
              rw [binaryCubeSignEquiv_apply, hxi]
              rfl
            · have hxiOne : x i.1 = 1 := Fin.eq_one_of_ne_zero _ hxi
              simp only [F₂DecisionTree.eval, hxi, if_false,
                F₂DecisionTree.eval_castAvailable]
              apply honeComputes x
              rw [matches_insertJuntaFixedAssignment_iff]
              refine ⟨hx, ?_⟩
              rw [binaryCubeSignEquiv_apply, hxiOne]
              rfl
          simpa [assembleJuntaQuery, JuntaTreeOutputBad] using hcomputes

/-! ### The recursion invariant -/

/-- If no coordinate of `J` remains outside `P`, then `P` contains all of `J`. -/
theorem subset_of_card_sdiff_le_zero (J P : Finset (Fin n))
    (hcard : (J \ P).card ≤ 0) : J ⊆ P := by
  intro i hiJ
  by_contra hiP
  have hi : i ∈ J \ P := by simp [hiJ, hiP]
  have hpos : 0 < (J \ P).card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

/-- Splitting on a relevant coordinate consumes exactly one still-unfixed coordinate from the
junta witness. -/
theorem card_sdiff_insert_le_of_mem_of_notMem
    (J P : Finset (Fin n)) (i : Fin n) (fuel : ℕ)
    (hiJ : i ∈ J) (hiP : i ∉ P) (hcard : (J \ P).card ≤ fuel + 1) :
    (J \ insert i P).card ≤ fuel := by
  have hi : i ∈ J \ P := by simp [hiJ, hiP]
  rw [Finset.sdiff_insert, Finset.card_erase_of_mem hi]
  omega

/-- At zero remaining fuel, a semantically correct node decision cannot request another relevant
coordinate. -/
theorem exists_constant_of_correctNode_of_card_sdiff_le_zero
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (decision : JuntaNodeDecision P)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (hcard : (J \ P).card ≤ 0)
    (hcorrect : decision.IsCorrect target P z) :
    ∃ value : Sign, decision = .constant value := by
  cases decision with
  | constant value => exact ⟨value, rfl⟩
  | relevant i =>
      exfalso
      have hiJ := mem_of_isRelevantJuntaRestriction_of_dependsOn
        target J P z i hdepends hcorrect
      exact i.2 (subset_of_card_sdiff_le_zero J P hcard hiJ)

/-! ### Union bound over the adaptive recursion -/

/-- Mapping a pure output controller pulls an output-only event back along that controller. -/
theorem eventProbability_map_output_eq
    {access : LearningAccess} {α β : Type v}
    (target : BooleanFunction n) (program : LearningProgram n access α)
    (output : α → β) (bad : β → Prop) :
    LearningProgram.eventProbability (LearningProgram.map output program) target
        (fun outcome : β × LearningCost ↦ bad outcome.1) =
      LearningProgram.eventProbability program target
        (fun outcome : α × LearningCost ↦ bad (output outcome.1)) := by
  unfold LearningProgram.eventProbability
  rw [LearningProgram.runWithCost_map, PMF.toOuterMeasure_map_apply]
  rfl

/-- A pure output map cannot increase failure probability when every mapped failure was already
a source failure. -/
theorem eventProbability_map_output_le
    {access : LearningAccess} {α β : Type v}
    (target : BooleanFunction n) (program : LearningProgram n access α)
    (output : α → β) (sourceBad : α → Prop) (targetBad : β → Prop)
    (hbad : ∀ value, targetBad (output value) → sourceBad value) :
    LearningProgram.eventProbability (LearningProgram.map output program) target
        (fun outcome : β × LearningCost ↦ targetBad outcome.1) ≤
      LearningProgram.eventProbability program target
        (fun outcome : α × LearningCost ↦ sourceBad outcome.1) := by
  rw [eventProbability_map_output_eq]
  exact LearningProgram.eventProbability_mono program target fun outcome ↦
    hbad outcome.1

/-- A pure successful continuation has zero probability of an output-only failure event. -/
theorem eventProbability_pure_eq_zero_of_not
    {access : LearningAccess} {α : Type*}
    (target : BooleanFunction n) (output : α) (bad : α → Prop)
    (hgood : ¬ bad output) :
    LearningProgram.eventProbability
        (.pure output : LearningProgram n access α) target
        (fun outcome ↦ bad outcome.1) = 0 := by
  simp [LearningProgram.eventProbability, LearningProgram.runWithCost,
    PMF.toOuterMeasure_pure_apply, hgood]

/-- At zero fuel, every bad leaf-controller output comes from a bad node decision. -/
theorem nodeLeafOutput_bad_implies_nodeBad
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (hdepends : DependsOn target (J : Set (Fin n)))
    (hcard : (J \ P).card ≤ 0) (decision : Option (JuntaNodeDecision P))
    (hbad : JuntaTreeOutputBad target P z (juntaNodeLeafOutput P decision)) :
    JuntaNodeDecision.IsBad target P z decision := by
  classical
  by_contra hgood
  cases decision with
  | none => simp [JuntaNodeDecision.IsBad] at hgood
  | some node =>
      have hcorrect := JuntaNodeDecision.isCorrect_of_not_isBad
        target P z hgood
      obtain ⟨value, hnode⟩ :=
        exists_constant_of_correctNode_of_card_sdiff_le_zero
          target J P z node hdepends hcard hcorrect
      subst node
      apply hbad
      exact F₂DecisionTree.computesJuntaRestriction_leaf
        target P z value hcorrect

/-- Recursive failure probability before confidence scheduling.  The only probabilistic input is
the finder guarantee; the factor is exactly the number of possible node calls. -/
theorem recursiveJuntaLearnerAux_failureProbability_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (J : Finset (Fin n))
    (hJcard : J.card ≤ k) (hdepends : DependsOn target (J : Set (Fin n)))
    (failure : PositiveLearningParameter) :
    ∀ (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P),
      P ⊆ J → (J \ P).card ≤ fuel →
      LearningProgram.eventProbability
          (recursiveJuntaLearnerAux finder failure fuel P z) target
          (fun outcome ↦ JuntaTreeOutputBad target P z outcome.1) ≤
        (juntaTreeCallCount fuel : ℝ) * (failure.1 : ℝ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro P z hPsubset hcard
      calc
        LearningProgram.eventProbability
            (recursiveJuntaLearnerAux finder failure 0 P z) target
            (fun outcome ↦ JuntaTreeOutputBad target P z outcome.1) ≤
            LearningProgram.eventProbability (finder.program P z failure) target
              (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) := by
          simpa only [recursiveJuntaLearnerAux] using
            eventProbability_map_output_le target (finder.program P z failure)
              (juntaNodeLeafOutput P)
              (JuntaNodeDecision.IsBad target P z)
              (JuntaTreeOutputBad target P z)
              (nodeLeafOutput_bad_implies_nodeBad
                target J P z hdepends hcard)
        _ ≤ (failure.1 : ℝ) :=
          finder.failureProbability_le target J P z hJcard hdepends hPsubset failure
        _ = (juntaTreeCallCount 0 : ℝ) * (failure.1 : ℝ) := by simp
  | succ fuel ih =>
      intro P z hPsubset hcard
      let childBound : ℝ :=
        (juntaTreeCallCount fuel : ℝ) * (failure.1 : ℝ)
      have hfailureNonneg : 0 ≤ (failure.1 : ℝ) := by
        exact (Rat.cast_nonneg.mpr (le_of_lt failure.2.1))
      have hchildNonneg : 0 ≤ childBound := by
        exact mul_nonneg (Nat.cast_nonneg _) hfailureNonneg
      have hcontinuation : ∀ decision, ¬ JuntaNodeDecision.IsBad target P z decision →
          LearningProgram.eventProbability
            (match decision with
              | none => .pure none
              | some (.constant value) => .pure (some (.leaf value))
              | some (.relevant i) =>
                  LearningProgram.bind
                    (fun zeroTree ↦
                      LearningProgram.map
                        (assembleJuntaQuery P i zeroTree)
                        (recursiveJuntaLearnerAux finder failure fuel
                          (insert i.1 P)
                          (insertJuntaFixedAssignment P z i (binarySignEquiv 1))))
                    (recursiveJuntaLearnerAux finder failure fuel
                      (insert i.1 P)
                      (insertJuntaFixedAssignment P z i (binarySignEquiv 0)))) target
            (fun outcome ↦ JuntaTreeOutputBad target P z outcome.1) ≤
              2 * childBound := by
        intro decision hdecision
        cases decision with
        | none => simp [JuntaNodeDecision.IsBad] at hdecision
        | some node =>
            have hcorrect := JuntaNodeDecision.isCorrect_of_not_isBad
              target P z hdecision
            cases node with
            | constant value =>
                have hleaf : ¬ JuntaTreeOutputBad target P z
                    (some (F₂DecisionTree.leaf value)) := by
                  intro hbad
                  exact hbad (F₂DecisionTree.computesJuntaRestriction_leaf
                    target P z value hcorrect)
                rw [eventProbability_pure_eq_zero_of_not target _ _ hleaf]
                exact mul_nonneg (by norm_num) hchildNonneg
            | relevant i =>
                have hiJ := mem_of_isRelevantJuntaRestriction_of_dependsOn
                  target J P z i hdepends hcorrect
                have hchildCard : (J \ insert i.1 P).card ≤ fuel :=
                  card_sdiff_insert_le_of_mem_of_notMem
                    J P i.1 fuel hiJ i.2 hcard
                have hchildSubset : insert i.1 P ⊆ J :=
                  Finset.insert_subset hiJ hPsubset
                have hzero := ih (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 0))
                  hchildSubset hchildCard
                have hone := ih (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 1))
                  hchildSubset hchildCard
                have hchildren := LearningProgram.eventProbability_bind_le_add
                  target
                  (recursiveJuntaLearnerAux finder failure fuel
                    (insert i.1 P)
                    (insertJuntaFixedAssignment P z i (binarySignEquiv 0)))
                  (fun zeroTree ↦
                    LearningProgram.map
                      (assembleJuntaQuery P i zeroTree)
                      (recursiveJuntaLearnerAux finder failure fuel
                        (insert i.1 P)
                        (insertJuntaFixedAssignment P z i (binarySignEquiv 1))))
                  (JuntaTreeOutputBad target (insert i.1 P)
                    (insertJuntaFixedAssignment P z i (binarySignEquiv 0)))
                  (JuntaTreeOutputBad target P z)
                  childBound childBound hchildNonneg hchildNonneg hzero
                  (by
                    intro zeroTree hzeroGood
                    calc
                      LearningProgram.eventProbability
                          (LearningProgram.map
                            (assembleJuntaQuery P i zeroTree)
                            (recursiveJuntaLearnerAux finder failure fuel
                              (insert i.1 P)
                              (insertJuntaFixedAssignment P z i
                                (binarySignEquiv 1)))) target
                          (fun outcome ↦
                            JuntaTreeOutputBad target P z outcome.1) ≤
                          LearningProgram.eventProbability
                            (recursiveJuntaLearnerAux finder failure fuel
                              (insert i.1 P)
                              (insertJuntaFixedAssignment P z i
                                (binarySignEquiv 1))) target
                            (fun outcome ↦
                              JuntaTreeOutputBad target (insert i.1 P)
                                (insertJuntaFixedAssignment P z i
                                  (binarySignEquiv 1)) outcome.1) := by
                        apply eventProbability_map_output_le
                        intro oneTree hparentBad
                        by_contra honeGood
                        exact (not_outputBad_assembleJuntaQuery
                          target P z i zeroTree oneTree hzeroGood honeGood)
                          hparentBad
                      _ ≤ childBound := hone)
                simpa [childBound, two_mul] using hchildren
      have htop := LearningProgram.eventProbability_bind_le_add
        target (finder.program P z failure)
        (fun decision ↦ match decision with
          | none => .pure none
          | some (.constant value) => .pure (some (.leaf value))
          | some (.relevant i) =>
              LearningProgram.bind
                (fun zeroTree ↦
                  LearningProgram.map
                    (assembleJuntaQuery P i zeroTree)
                    (recursiveJuntaLearnerAux finder failure fuel
                      (insert i.1 P)
                      (insertJuntaFixedAssignment P z i (binarySignEquiv 1))))
                (recursiveJuntaLearnerAux finder failure fuel
                  (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 0))))
        (JuntaNodeDecision.IsBad target P z)
        (JuntaTreeOutputBad target P z)
        (failure.1 : ℝ) (2 * childBound)
        hfailureNonneg (mul_nonneg (by norm_num) hchildNonneg)
        (finder.failureProbability_le target J P z hJcard hdepends hPsubset failure)
        hcontinuation
      calc
        LearningProgram.eventProbability
            (recursiveJuntaLearnerAux finder failure (fuel + 1) P z) target
            (fun outcome ↦ JuntaTreeOutputBad target P z outcome.1) ≤
            (failure.1 : ℝ) + 2 * childBound := by
          simpa only [recursiveJuntaLearnerAux] using htop
        _ = (juntaTreeCallCount (fuel + 1) : ℝ) * (failure.1 : ℝ) := by
          simp only [juntaTreeCallCount_succ, Nat.cast_add, Nat.cast_one,
            Nat.cast_mul, Nat.cast_ofNat, childBound]
          ring

/-! ### Pathwise depth and resource bounds -/

/-- Every successful recursive output has depth at most its recursion fuel. -/
theorem recursiveJuntaLearnerAux_depth_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter) :
    ∀ (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
      (outcome : Option (F₂DecisionTree n Sign (Finset.univ \ P)) × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (recursiveJuntaLearnerAux finder failure fuel P z)).support →
      ∀ tree, outcome.1 = some tree → tree.depth ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro P z outcome houtcome tree htree
      rw [recursiveJuntaLearnerAux, LearningProgram.runWithCost_map,
        PMF.mem_support_map_iff] at houtcome
      obtain ⟨nodeOutcome, _, rfl⟩ := houtcome
      cases hdecision : nodeOutcome.1 with
      | none => simp [juntaNodeLeafOutput, hdecision] at htree
      | some decision =>
          cases decision with
          | constant value =>
              simp [juntaNodeLeafOutput, hdecision] at htree
              subst tree
              rfl
          | relevant i => simp [juntaNodeLeafOutput, hdecision] at htree
  | succ fuel ih =>
      intro P z outcome houtcome tree htree
      rw [recursiveJuntaLearnerAux, LearningProgram.runWithCost_bind,
        PMF.mem_support_bind_iff] at houtcome
      obtain ⟨nodeOutcome, _, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨continuationOutcome, hcontinuation, rfl⟩ := houtcome
      cases hdecision : nodeOutcome.1 with
      | none =>
          rw [hdecision, LearningProgram.runWithCost,
            PMF.mem_support_pure_iff] at hcontinuation
          subst continuationOutcome
          exfalso
          have hnone :
              (none : Option (F₂DecisionTree n Sign (Finset.univ \ P))) =
                some tree := by
            simpa only [LearningProgram.addOutcomeCost] using htree
          cases hnone
      | some decision =>
          cases decision with
          | constant value =>
              rw [hdecision, LearningProgram.runWithCost,
                PMF.mem_support_pure_iff] at hcontinuation
              subst continuationOutcome
              have hsome : some tree =
                  some (F₂DecisionTree.leaf value :
                    F₂DecisionTree n Sign (Finset.univ \ P)) := by
                simpa only [LearningProgram.addOutcomeCost] using htree.symm
              have htreeEq : tree =
                  (F₂DecisionTree.leaf value :
                    F₂DecisionTree n Sign (Finset.univ \ P)) :=
                Option.some.inj hsome
              subst tree
              simp [F₂DecisionTree.depth]
          | relevant i =>
              rw [hdecision, LearningProgram.runWithCost_bind,
                PMF.mem_support_bind_iff] at hcontinuation
              obtain ⟨zeroOutcome, hzero, hcontinuation⟩ := hcontinuation
              rw [PMF.mem_support_map_iff] at hcontinuation
              obtain ⟨mappedOutcome, hmapped, rfl⟩ := hcontinuation
              rw [LearningProgram.runWithCost_map,
                PMF.mem_support_map_iff] at hmapped
              obtain ⟨oneOutcome, hone, rfl⟩ := hmapped
              cases hzeroValue : zeroOutcome.1 with
              | none =>
                  exfalso
                  have hnone :
                      (none : Option
                        (F₂DecisionTree n Sign (Finset.univ \ P))) = some tree := by
                    simpa only [LearningProgram.addOutcomeCost, assembleJuntaQuery,
                      hzeroValue] using htree
                  cases hnone
              | some zeroTree =>
                  cases honeValue : oneOutcome.1 with
                  | none =>
                      exfalso
                      have hnone :
                          (none : Option
                            (F₂DecisionTree n Sign (Finset.univ \ P))) =
                              some tree := by
                        simpa only [LearningProgram.addOutcomeCost,
                          assembleJuntaQuery, hzeroValue, honeValue] using htree
                      cases hnone
                  | some oneTree =>
                      have hzeroDepth := ih (insert i.1 P)
                        (insertJuntaFixedAssignment P z i (binarySignEquiv 0))
                        zeroOutcome hzero zeroTree hzeroValue
                      have honeDepth := ih (insert i.1 P)
                        (insertJuntaFixedAssignment P z i (binarySignEquiv 1))
                        oneOutcome hone oneTree honeValue
                      have htreeEq : tree =
                          F₂DecisionTree.query i.1 (by simp [i.2])
                            (F₂DecisionTree.castAvailable
                              (Finset.sdiff_insert Finset.univ P i.1) zeroTree)
                            (F₂DecisionTree.castAvailable
                              (Finset.sdiff_insert Finset.univ P i.1) oneTree) := by
                        have hsome : some tree =
                            some (F₂DecisionTree.query i.1 (by simp [i.2])
                              (F₂DecisionTree.castAvailable
                                (Finset.sdiff_insert Finset.univ P i.1) zeroTree)
                              (F₂DecisionTree.castAvailable
                                (Finset.sdiff_insert Finset.univ P i.1) oneTree)) := by
                          simpa only [LearningProgram.addOutcomeCost,
                            assembleJuntaQuery, hzeroValue, honeValue] using htree.symm
                        exact Option.some.inj hsome
                      subst tree
                      simp only [F₂DecisionTree.depth,
                        F₂DecisionTree.depth_castAvailable]
                      exact Nat.succ_le_succ (max_le hzeroDepth honeDepth)

/-- Any additive natural-valued cost projection accumulates over exactly the possible recursive
node calls.  This single induction supplies the random-example, query, and local-work bounds. -/
theorem recursiveJuntaLearnerAux_costProjection_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (projection : LearningCost → ℕ) (hzero : projection 0 = 0)
    (hadd : ∀ first second,
      projection (first + second) = projection first + projection second)
    (bound : ℕ)
    (hfinder : ∀ (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
      (outcome : Option (JuntaNodeDecision P) × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (finder.program P z failure)).support →
      projection outcome.2 ≤ bound) :
    ∀ (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
      (outcome : Option (F₂DecisionTree n Sign (Finset.univ \ P)) × LearningCost),
      outcome ∈ (LearningProgram.runWithCost target
        (recursiveJuntaLearnerAux finder failure fuel P z)).support →
      projection outcome.2 ≤ juntaTreeCallCount fuel * bound := by
  intro fuel
  induction fuel with
  | zero =>
      intro P z outcome houtcome
      rw [recursiveJuntaLearnerAux, LearningProgram.runWithCost_map,
        PMF.mem_support_map_iff] at houtcome
      obtain ⟨nodeOutcome, hnode, rfl⟩ := houtcome
      simpa using hfinder P z nodeOutcome hnode
  | succ fuel ih =>
      intro P z outcome houtcome
      rw [recursiveJuntaLearnerAux, LearningProgram.runWithCost_bind,
        PMF.mem_support_bind_iff] at houtcome
      obtain ⟨nodeOutcome, hnode, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨continuationOutcome, hcontinuation, rfl⟩ := houtcome
      have hnodeBound := hfinder P z nodeOutcome hnode
      have hcontinuationBound :
          projection continuationOutcome.2 ≤
            2 * juntaTreeCallCount fuel * bound := by
        cases hdecision : nodeOutcome.1 with
        | none =>
            rw [hdecision, LearningProgram.runWithCost,
              PMF.mem_support_pure_iff] at hcontinuation
            subst continuationOutcome
            simp [hzero]
        | some decision =>
            cases decision with
            | constant value =>
                rw [hdecision, LearningProgram.runWithCost,
                  PMF.mem_support_pure_iff] at hcontinuation
                subst continuationOutcome
                simp [hzero]
            | relevant i =>
                rw [hdecision, LearningProgram.runWithCost_bind,
                  PMF.mem_support_bind_iff] at hcontinuation
                obtain ⟨zeroOutcome, hzeroOutcome, hcontinuation⟩ := hcontinuation
                rw [PMF.mem_support_map_iff] at hcontinuation
                obtain ⟨mappedOutcome, hmapped, rfl⟩ := hcontinuation
                rw [LearningProgram.runWithCost_map,
                  PMF.mem_support_map_iff] at hmapped
                obtain ⟨oneOutcome, honeOutcome, rfl⟩ := hmapped
                have hzeroBound := ih (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 0))
                  zeroOutcome hzeroOutcome
                have honeBound := ih (insert i.1 P)
                  (insertJuntaFixedAssignment P z i (binarySignEquiv 1))
                  oneOutcome honeOutcome
                simp only [LearningProgram.addOutcomeCost, hadd]
                calc
                  projection zeroOutcome.2 + projection oneOutcome.2 ≤
                      juntaTreeCallCount fuel * bound +
                        juntaTreeCallCount fuel * bound :=
                    Nat.add_le_add hzeroBound honeBound
                  _ = 2 * juntaTreeCallCount fuel * bound := by ring
      simp only [LearningProgram.addOutcomeCost, hadd]
      calc
        projection nodeOutcome.2 + projection continuationOutcome.2 ≤
            bound + 2 * juntaTreeCallCount fuel * bound :=
          Nat.add_le_add hnodeBound hcontinuationBound
        _ = juntaTreeCallCount (fuel + 1) * bound := by
          rw [juntaTreeCallCount_succ]
          ring

/-- Pathwise ambient random-example bound of the recursive learner. -/
theorem recursiveJuntaLearnerAux_randomExamples_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (outcome : Option (F₂DecisionTree n Sign (Finset.univ \ P)) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (recursiveJuntaLearnerAux finder failure fuel P z)).support) :
    outcome.2.randomExamples ≤
      juntaTreeCallCount fuel * finder.randomExampleBound failure := by
  refine recursiveJuntaLearnerAux_costProjection_le finder target failure
    LearningCost.randomExamples rfl (fun _ _ ↦ rfl)
    (finder.randomExampleBound failure) ?_ fuel P z outcome houtcome
  intro P' z' nodeOutcome hnode
  exact (finder.cost_le target P' z' failure nodeOutcome hnode).1

/-- The recursive learner issues no membership queries. -/
theorem recursiveJuntaLearnerAux_queries_eq_zero
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (outcome : Option (F₂DecisionTree n Sign (Finset.univ \ P)) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (recursiveJuntaLearnerAux finder failure fuel P z)).support) :
    outcome.2.queries = 0 := by
  apply Nat.eq_zero_of_le_zero
  refine recursiveJuntaLearnerAux_costProjection_le finder target failure
    LearningCost.queries rfl (fun _ _ ↦ rfl) 0 ?_ fuel P z outcome houtcome
  intro P' z' nodeOutcome hnode
  exact (finder.cost_le target P' z' failure nodeOutcome hnode).2.1.le

/-- Pathwise local-work bound of the recursive learner. -/
theorem recursiveJuntaLearnerAux_work_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (fuel : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (outcome : Option (F₂DecisionTree n Sign (Finset.univ \ P)) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (recursiveJuntaLearnerAux finder failure fuel P z)).support) :
    outcome.2.work ≤ juntaTreeCallCount fuel * finder.workBound failure := by
  refine recursiveJuntaLearnerAux_costProjection_le finder target failure
    LearningCost.work rfl (fun _ _ ↦ rfl) (finder.workBound failure) ?_
      fuel P z outcome houtcome
  intro P' z' nodeOutcome hnode
  exact (finder.cost_le target P' z' failure nodeOutcome hnode).2.2

/-! ### Exercise 6.31(c) and Lemma 6.37 -/

/-- A complete decision tree computes the sign-valued target under the explicit additive/sign
cube equivalence. -/
def DecisionTreeComputesTarget (tree : DecisionTree n Sign)
    (target : BooleanFunction n) : Prop :=
  ∀ x : F₂Cube n, tree.eval x = target (binaryCubeSignEquiv n x)

/-- Failure event for the complete learner. -/
def JuntaLearnerOutputBad (target : BooleanFunction n) :
    Option (DecisionTree n Sign) → Prop
  | none => True
  | some tree => ¬ DecisionTreeComputesTarget tree target

/-- A bad root output after the phantom-index cast was already a bad output of the empty
restriction recursion. -/
theorem rootOutput_bad_implies_auxBad
    (target : BooleanFunction n)
    (output : Option
      (F₂DecisionTree n Sign (Finset.univ \ (∅ : Finset (Fin n)))))
    (hbad : JuntaLearnerOutputBad target
      (Option.map (fun tree ↦ F₂DecisionTree.castAvailable (by simp) tree) output)) :
    JuntaTreeOutputBad target ∅ emptyJuntaFixedAssignment output := by
  cases output with
  | none => trivial
  | some tree =>
      intro hcomputes
      apply hbad
      intro x
      rw [F₂DecisionTree.eval_castAvailable]
      apply hcomputes x
      intro i
      exact isEmptyElim i

/-- Exercise 6.31(c) and Lemma 6.37: a `k`-junta is learned by the actual recursive
random-example program with total failure probability at most the requested budget. -/
theorem recursiveJuntaLearner_failureProbability_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (hjunta : IsKJunta target k)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability (recursiveJuntaLearner finder failure) target
        (fun outcome ↦ JuntaLearnerOutputBad target outcome.1) ≤
      (failure.1 : ℝ) := by
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hrootCard : (J \ (∅ : Finset (Fin n))).card ≤ k := by
    simpa using hJcard
  calc
    LearningProgram.eventProbability (recursiveJuntaLearner finder failure) target
        (fun outcome ↦ JuntaLearnerOutputBad target outcome.1) ≤
        LearningProgram.eventProbability
          (recursiveJuntaLearnerAux finder
            (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment) target
          (fun outcome ↦
            JuntaTreeOutputBad target ∅ emptyJuntaFixedAssignment outcome.1) := by
      simpa only [recursiveJuntaLearner] using
        eventProbability_map_output_le target
          (recursiveJuntaLearnerAux finder
            (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment)
          (Option.map fun tree ↦ F₂DecisionTree.castAvailable (by simp) tree)
          (JuntaTreeOutputBad target ∅ emptyJuntaFixedAssignment)
          (JuntaLearnerOutputBad target)
          (rootOutput_bad_implies_auxBad target)
    _ ≤ (juntaTreeCallCount k : ℝ) *
        ((juntaTreePerCallFailure k failure).1 : ℝ) :=
      recursiveJuntaLearnerAux_failureProbability_le finder target J
        hJcard hdepends (juntaTreePerCallFailure k failure) k ∅
        emptyJuntaFixedAssignment (Finset.empty_subset J) hrootCard
    _ = (failure.1 : ℝ) := by
      exact_mod_cast juntaTreeCallCount_mul_perCallFailure k failure

/-- Every successful complete-tree output has depth at most `k`, independently of whether a
finder failure occurred on another execution path. -/
theorem recursiveJuntaLearner_depth_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (outcome : Option (DecisionTree n Sign) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (recursiveJuntaLearner finder failure)).support)
    (tree : DecisionTree n Sign) (htree : outcome.1 = some tree) :
    tree.depth ≤ k := by
  rw [recursiveJuntaLearner, LearningProgram.runWithCost_map,
    PMF.mem_support_map_iff] at houtcome
  obtain ⟨auxOutcome, haux, houtput⟩ := houtcome
  have houtputValue := congrArg Prod.fst houtput
  cases hauxValue : auxOutcome.1 with
  | none => simp [hauxValue, htree] at houtputValue
  | some auxTree =>
      have htreeEq : tree = F₂DecisionTree.castAvailable (by simp) auxTree := by
        simpa [hauxValue, htree] using houtputValue.symm
      subst tree
      rw [F₂DecisionTree.depth_castAvailable]
      exact recursiveJuntaLearnerAux_depth_le finder target
        (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment
        auxOutcome haux auxTree hauxValue

/-- Complete pathwise resource closure for Lemma 6.37. -/
theorem recursiveJuntaLearner_cost_le
    {k : ℕ} (finder : JuntaRelevantCoordinateFinder n k)
    (target : BooleanFunction n) (failure : PositiveLearningParameter)
    (outcome : Option (DecisionTree n Sign) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (recursiveJuntaLearner finder failure)).support) :
    outcome.2.randomExamples ≤
        juntaTreeCallCount k *
          finder.randomExampleBound (juntaTreePerCallFailure k failure) ∧
      outcome.2.queries = 0 ∧
      outcome.2.work ≤ juntaTreeCallCount k *
        finder.workBound (juntaTreePerCallFailure k failure) := by
  rw [recursiveJuntaLearner, LearningProgram.runWithCost_map,
    PMF.mem_support_map_iff] at houtcome
  obtain ⟨auxOutcome, haux, rfl⟩ := houtcome
  exact ⟨
    recursiveJuntaLearnerAux_randomExamples_le finder target
      (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment
      auxOutcome haux,
    recursiveJuntaLearnerAux_queries_eq_zero finder target
      (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment
      auxOutcome haux,
    recursiveJuntaLearnerAux_work_le finder target
      (juntaTreePerCallFailure k failure) k ∅ emptyJuntaFixedAssignment
      auxOutcome haux⟩

end FABL
