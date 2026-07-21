/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.LearningAndTesting.LowDegreeJuntaLearningAlgorithm

/-!
# Whole-tree resources for low-degree junta learning

Book items: Exercise 6.31(c) and Theorem 6.36.

This module closes the resource accounting of the recursive learner.  Its finite budgets multiply
the uniform one-node envelopes by the exact number of possible calls in the depth-`k` binary tree,
and every `runWithCost` support path obeys those budgets.

For asymptotics, a dyadic confidence index records `log₂(1 / failure)` explicitly.  Unconditional
linear-confidence bounds give Mathlib `IsBigO` statements for the whole tree.  The fixed failure
`1 / 16` is then identified with dyadic index three, yielding finite and asymptotic corollaries for
the actual `LearningAlgorithm` cost fields.  A generic pointwise-witness interface remains available
for alternative polynomial envelopes.
-/

open Finset

set_option autoImplicit false

namespace FABL

variable {n : ℕ}

/-! ## Constructor-derived whole-tree budgets -/

/-- Total ambient random-example budget for the complete depth-`k` learner. -/
noncomputable def lowDegreeJuntaTotalRandomExampleBudget
    (n k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  juntaTreeCallCount k *
    lowDegreeJuntaNodeRandomExampleBound n k
      (juntaTreePerCallFailure k failure)

/-- Total charged local-work budget for the complete depth-`k` learner. -/
noncomputable def lowDegreeJuntaTotalWorkBudget
    (n k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  juntaTreeCallCount k *
    lowDegreeJuntaNodeUniformWorkBound n k
      (juntaTreePerCallFailure k failure)

/-- Every execution path of the recursive learner is controlled by the explicit whole-tree
random-example and local-work budgets. -/
theorem lowDegreeJuntaLearnerProgram_cost_le_totalBudget
    (target : BooleanFunction n) (k : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (DecisionTree n Sign) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (lowDegreeJuntaLearnerProgram n k failure)).support) :
    outcome.2.randomExamples ≤
        lowDegreeJuntaTotalRandomExampleBudget n k failure ∧
      outcome.2.queries = 0 ∧
      outcome.2.work ≤ lowDegreeJuntaTotalWorkBudget n k failure := by
  simpa only [lowDegreeJuntaTotalRandomExampleBudget,
    lowDegreeJuntaTotalWorkBudget] using
    lowDegreeJuntaLearnerProgram_cost_le target k failure outcome houtcome

/-! ## Scaling the node runtime ledger -/

/-- The explicit rational envelope for the Fourier-scan term in the node runtime ledger. -/
noncomputable def lowDegreeJuntaFourierScanRuntimeEnvelope
    (n : ℕ) (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter) : ℚ :=
  (((lowDegreeJuntaCutoff k + 1) *
      (n + 1) ^ lowDegreeJuntaCutoff k : ℕ) : ℚ) *
    (4 * fourierEstimatorFailureBits
        (lowDegreeJuntaCoefficientConfidence P k failure) /
      (lowDegreeJuntaCoefficientAccuracy k).1 ^ 2) *
    (lowDegreeJuntaCutoff k + 1)

/-- The explicit natural envelope for the row-reduction term in the node runtime ledger. -/
def lowDegreeJuntaPolynomialRuntimeEnvelope
    (n k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  3 * (2 ^ lowDegreeJuntaPolynomialDegree k *
    (lowDegreeJuntaPolynomialDegree k +
      fourierEstimatorFailureBits (lowDegreeJuntaQuarterFailure failure) + 3)) ^ 3 *
    (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k)

/-- Multiplication by the maximum number of recursive calls preserves both high-degree
inequalities in the verified node runtime ledger.  This is a finite accounting lemma; uniform
control of the sampler and scheduler terms is supplied separately by a polynomial witness below. -/
theorem lowDegreeJuntaNodeRuntimeLedger_mul_treeCallCount
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    (juntaTreeCallCount k : ℚ) *
        (((lowDegreeJuntaFourierFamily P k).card *
          lowDegreeJuntaCoefficientSampleCount P k failure *
          (lowDegreeJuntaCutoff k + 1) : ℕ) : ℚ) ≤
      (juntaTreeCallCount k : ℚ) *
        lowDegreeJuntaFourierScanRuntimeEnvelope n P k failure ∧
      juntaTreeCallCount k *
          lowDegreeF₂PolynomialLearnerWork
            (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
            (lowDegreeJuntaPolynomialSampleCount P k failure)
            (lowDegreeJuntaPolynomialSamples P k failure batch) ≤
        juntaTreeCallCount k *
          lowDegreeJuntaPolynomialRuntimeEnvelope n k failure := by
  obtain ⟨hfourier, hpolynomial, _, _, _⟩ :=
    lowDegreeJuntaNodeRuntimeLedger P k failure batch
  constructor
  · apply mul_le_mul_of_nonneg_left
      (by
        simpa only [lowDegreeJuntaFourierScanRuntimeEnvelope] using hfourier)
    positivity
  · exact Nat.mul_le_mul_left (juntaTreeCallCount k) (by
      simpa only [lowDegreeJuntaPolynomialRuntimeEnvelope] using hpolynomial)

/-! ## Fixed-parameter polynomial closure -/

/-- Dyadic total failure `2⁻⁽ᵇⁱᵗˢ⁺¹⁾`; `bits` is the exact binary-logarithmic
confidence index up to the displayed additive one. -/
def lowDegreeJuntaDyadicFailure (bits : ℕ) : PositiveLearningParameter := by
  refine ⟨1 / (2 : ℚ) ^ (bits + 1), by positivity, ?_⟩
  have hden : (2 : ℚ) ≤ (2 : ℚ) ^ (bits + 1) := by
    calc
      (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ (bits + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  nlinarith

@[simp] theorem lowDegreeJuntaDyadicFailure_value (bits : ℕ) :
    (lowDegreeJuntaDyadicFailure bits).1 =
      1 / (2 : ℚ) ^ (bits + 1) :=
  rfl

/-- The fixed failure parameter of Theorem 6.36 is the dyadic confidence level with index three. -/
theorem lowDegreeJuntaLearningFailure_eq_dyadicFailure :
    lowDegreeJuntaLearningFailure = lowDegreeJuntaDyadicFailure 3 := by
  apply Subtype.ext
  norm_num [lowDegreeJuntaLearningFailure, lowDegreeJuntaDyadicFailure]

/-- The standard confidence scheduler reads the dyadic index as exactly `bits + 2`. -/
@[simp] theorem fourierEstimatorFailureBits_lowDegreeJuntaDyadicFailure
    (bits : ℕ) :
    fourierEstimatorFailureBits (lowDegreeJuntaDyadicFailure bits) = bits + 2 := by
  unfold fourierEstimatorFailureBits
  rw [lowDegreeJuntaDyadicFailure_value]
  rw [show (2 : ℚ) / (1 / (2 : ℚ) ^ (bits + 1)) =
      ((2 ^ (bits + 2) : ℕ) : ℚ) by
    push_cast
    field_simp
    ring]
  rw [Nat.ceil_natCast, Nat.clog_pow 2 (bits + 2) (by omega)]

/-! ## Linear confidence envelopes for one node -/

/-- The failure assigned to one possible node of the depth-`k` recursion under a dyadic total
failure budget. -/
def lowDegreeJuntaDyadicNodeFailure (k confidenceBits : ℕ) :
    PositiveLearningParameter :=
  juntaTreePerCallFailure k (lowDegreeJuntaDyadicFailure confidenceBits)

@[simp] theorem lowDegreeJuntaDyadicNodeFailure_value (k confidenceBits : ℕ) :
    (lowDegreeJuntaDyadicNodeFailure k confidenceBits).1 =
      1 / ((juntaTreeCallCount k * 2 ^ (confidenceBits + 1) : ℕ) : ℚ) := by
  rw [lowDegreeJuntaDyadicNodeFailure, juntaTreePerCallFailure_value,
    lowDegreeJuntaDyadicFailure_value]
  have htree : (juntaTreeCallCount k : ℚ) ≠ 0 := by
    exact_mod_cast (juntaTreeCallCount_pos k).ne'
  field_simp [htree]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem fourierEstimatorFailureBits_eq_clog_two_mul_denominator
    (failure : PositiveLearningParameter) (denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hvalue : failure.1 = 1 / (denominator : ℚ)) :
    fourierEstimatorFailureBits failure = Nat.clog 2 (2 * denominator) := by
  unfold fourierEstimatorFailureBits
  rw [hvalue]
  have hdenominatorRat : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast hdenominator.ne'
  rw [show (2 : ℚ) / (1 / (denominator : ℚ)) =
      ((2 * denominator : ℕ) : ℚ) by
    push_cast
    field_simp [hdenominatorRat]]
  rw [Nat.ceil_natCast]

private theorem lowDegreeJuntaBinaryClog_mul_le (a b : ℕ) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  rw [Nat.clog_le_iff_le_pow (by omega), pow_add]
  exact Nat.mul_le_mul
    (Nat.le_pow_clog (by omega) a)
    (Nat.le_pow_clog (by omega) b)

/-- The binary logarithm of the scanned Fourier-family size grows at most linearly in the
ambient dimension, with a coefficient depending only on the fixed cutoff. -/
theorem clog_card_lowDegreeJuntaFourierFamily_le
    (P : Finset (Fin n)) (k : ℕ) :
    Nat.clog 2 (lowDegreeJuntaFourierFamily P k).card ≤
      (lowDegreeJuntaCutoff k + 1) * (n + 2) := by
  apply Nat.clog_le_of_le_pow
  calc
    (lowDegreeJuntaFourierFamily P k).card ≤
        (lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k :=
      card_lowDegreeJuntaFourierFamily_le P k
    _ ≤ 2 ^ (lowDegreeJuntaCutoff k + 1) *
        (2 ^ (n + 1)) ^ lowDegreeJuntaCutoff k := by
      exact Nat.mul_le_mul
        (Nat.le_of_lt (lowDegreeJuntaCutoff k + 1).lt_two_pow_self)
        (Nat.pow_le_pow_left
          (Nat.le_of_lt (n + 1).lt_two_pow_self) _)
    _ = 2 ^ ((lowDegreeJuntaCutoff k + 1) +
        (n + 1) * lowDegreeJuntaCutoff k) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((lowDegreeJuntaCutoff k + 1) * (n + 2)) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

/-- A fixed-`k` coefficient that absorbs the tree-confidence overhead, the Fourier-family
logarithm, and the constant confidence splits at one node. -/
def lowDegreeJuntaLinearConfidenceCoefficient (k : ℕ) : ℕ :=
  Nat.clog 2 (juntaTreeCallCount k) +
    2 * (lowDegreeJuntaCutoff k + 1) + 5

private theorem lowDegreeJuntaHalfNodeFailureBits_le (k confidenceBits : ℕ) :
    fourierEstimatorFailureBits
        (lowDegreeJuntaHalfFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      lowDegreeJuntaLinearConfidenceCoefficient k * (confidenceBits + 1) := by
  let denominator := juntaTreeCallCount k * 2 ^ (confidenceBits + 2)
  have hdenominator : 0 < denominator :=
    Nat.mul_pos (juntaTreeCallCount_pos k) (pow_pos (by omega) _)
  have hvalue :
      (lowDegreeJuntaHalfFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)).1 =
        1 / (denominator : ℚ) := by
    rw [lowDegreeJuntaHalfFailure_value,
      lowDegreeJuntaDyadicNodeFailure_value]
    dsimp [denominator]
    have htree : (juntaTreeCallCount k : ℚ) ≠ 0 := by
      exact_mod_cast (juntaTreeCallCount_pos k).ne'
    field_simp [htree]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [fourierEstimatorFailureBits_eq_clog_two_mul_denominator
    _ denominator hdenominator hvalue]
  have hargument : 2 * denominator =
      juntaTreeCallCount k * 2 ^ (confidenceBits + 3) := by
    dsimp [denominator]
    rw [show confidenceBits + 3 = (confidenceBits + 2) + 1 by omega,
      pow_succ]
    ring
  rw [hargument]
  calc
    Nat.clog 2 (juntaTreeCallCount k * 2 ^ (confidenceBits + 3)) ≤
        Nat.clog 2 (juntaTreeCallCount k) +
          Nat.clog 2 (2 ^ (confidenceBits + 3)) :=
      lowDegreeJuntaBinaryClog_mul_le _ _
    _ = Nat.clog 2 (juntaTreeCallCount k) + confidenceBits + 3 := by
      rw [Nat.clog_pow 2 (confidenceBits + 3) (by omega)]
      omega
    _ ≤ lowDegreeJuntaLinearConfidenceCoefficient k *
        (confidenceBits + 1) := by
      unfold lowDegreeJuntaLinearConfidenceCoefficient
      nlinarith

private theorem lowDegreeJuntaQuarterNodeFailureBits_le (k confidenceBits : ℕ) :
    fourierEstimatorFailureBits
        (lowDegreeJuntaQuarterFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      lowDegreeJuntaLinearConfidenceCoefficient k * (confidenceBits + 1) := by
  let denominator := juntaTreeCallCount k * 2 ^ (confidenceBits + 3)
  have hdenominator : 0 < denominator :=
    Nat.mul_pos (juntaTreeCallCount_pos k) (pow_pos (by omega) _)
  have hvalue :
      (lowDegreeJuntaQuarterFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)).1 =
        1 / (denominator : ℚ) := by
    rw [lowDegreeJuntaQuarterFailure_value,
      lowDegreeJuntaDyadicNodeFailure_value]
    dsimp [denominator]
    have htree : (juntaTreeCallCount k : ℚ) ≠ 0 := by
      exact_mod_cast (juntaTreeCallCount_pos k).ne'
    field_simp [htree]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [fourierEstimatorFailureBits_eq_clog_two_mul_denominator
    _ denominator hdenominator hvalue]
  have hargument : 2 * denominator =
      juntaTreeCallCount k * 2 ^ (confidenceBits + 4) := by
    dsimp [denominator]
    rw [show confidenceBits + 4 = (confidenceBits + 3) + 1 by omega,
      pow_succ]
    ring
  rw [hargument]
  calc
    Nat.clog 2 (juntaTreeCallCount k * 2 ^ (confidenceBits + 4)) ≤
        Nat.clog 2 (juntaTreeCallCount k) +
          Nat.clog 2 (2 ^ (confidenceBits + 4)) :=
      lowDegreeJuntaBinaryClog_mul_le _ _
    _ = Nat.clog 2 (juntaTreeCallCount k) + confidenceBits + 4 := by
      rw [Nat.clog_pow 2 (confidenceBits + 4) (by omega)]
      omega
    _ ≤ lowDegreeJuntaLinearConfidenceCoefficient k *
        (confidenceBits + 1) := by
      unfold lowDegreeJuntaLinearConfidenceCoefficient
      nlinarith

/-- After the finite family union bound, the coefficient scheduler remains linear in the dyadic
confidence index; the additional family logarithm costs only one power of `n + 1`. -/
theorem lowDegreeJuntaCoefficientFailureBits_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    fourierEstimatorFailureBits
        (lowDegreeJuntaCoefficientConfidence P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      lowDegreeJuntaLinearConfidenceCoefficient k *
        (n + 1) * (confidenceBits + 1) := by
  let familyCard := (lowDegreeJuntaFourierFamily P k).card
  let denominator := juntaTreeCallCount k * familyCard *
    2 ^ (confidenceBits + 3)
  have hfamilyCard : 0 < familyCard := by
    exact Finset.card_pos.mpr (lowDegreeJuntaFourierFamily_nonempty P k)
  have hdenominator : 0 < denominator := by
    exact Nat.mul_pos
      (Nat.mul_pos (juntaTreeCallCount_pos k) hfamilyCard)
      (pow_pos (by omega) _)
  have hvalue :
      (lowDegreeJuntaCoefficientConfidence P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)).1 =
        1 / (denominator : ℚ) := by
    rw [lowDegreeJuntaCoefficientConfidence_value,
      lowDegreeJuntaDyadicNodeFailure_value]
    dsimp [denominator, familyCard]
    have htree : (juntaTreeCallCount k : ℚ) ≠ 0 := by
      exact_mod_cast (juntaTreeCallCount_pos k).ne'
    have hfamily : ((lowDegreeJuntaFourierFamily P k).card : ℚ) ≠ 0 := by
      exact_mod_cast hfamilyCard.ne'
    field_simp [htree, hfamily]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [fourierEstimatorFailureBits_eq_clog_two_mul_denominator
    _ denominator hdenominator hvalue]
  have hargument : 2 * denominator =
      (juntaTreeCallCount k * familyCard) *
        2 ^ (confidenceBits + 4) := by
    dsimp [denominator]
    rw [show confidenceBits + 4 = (confidenceBits + 3) + 1 by omega,
      pow_succ]
    ring
  rw [hargument]
  calc
    Nat.clog 2 ((juntaTreeCallCount k * familyCard) *
        2 ^ (confidenceBits + 4)) ≤
      Nat.clog 2 (juntaTreeCallCount k * familyCard) +
        Nat.clog 2 (2 ^ (confidenceBits + 4)) :=
      lowDegreeJuntaBinaryClog_mul_le _ _
    _ ≤ (Nat.clog 2 (juntaTreeCallCount k) +
          Nat.clog 2 familyCard) + (confidenceBits + 4) := by
      exact Nat.add_le_add
        (lowDegreeJuntaBinaryClog_mul_le _ _)
        (Nat.le_of_eq (Nat.clog_pow 2 (confidenceBits + 4) (by omega)))
    _ ≤ lowDegreeJuntaLinearConfidenceCoefficient k *
        (n + 1) * (confidenceBits + 1) := by
      have hfamily : Nat.clog 2 familyCard ≤
          (lowDegreeJuntaCutoff k + 1) * (n + 2) := by
        simpa only [familyCard] using
          clog_card_lowDegreeJuntaFourierFamily_le P k
      have hn : 1 ≤ n + 1 := by omega
      have hconfidence : 1 ≤ confidenceBits + 1 := by omega
      have htreeTerm : Nat.clog 2 (juntaTreeCallCount k) ≤
          Nat.clog 2 (juntaTreeCallCount k) * (n + 1) *
            (confidenceBits + 1) := by
        calc
          Nat.clog 2 (juntaTreeCallCount k) =
              Nat.clog 2 (juntaTreeCallCount k) * 1 := by ring
          _ ≤ Nat.clog 2 (juntaTreeCallCount k) * (n + 1) :=
            Nat.mul_le_mul_left _ hn
          _ = Nat.clog 2 (juntaTreeCallCount k) * (n + 1) * 1 := by ring
          _ ≤ Nat.clog 2 (juntaTreeCallCount k) * (n + 1) *
              (confidenceBits + 1) :=
            Nat.mul_le_mul_left _ hconfidence
      have hfamilyTerm : Nat.clog 2 familyCard ≤
          2 * (lowDegreeJuntaCutoff k + 1) * (n + 1) *
            (confidenceBits + 1) := by
        calc
          Nat.clog 2 familyCard ≤
              (lowDegreeJuntaCutoff k + 1) * (n + 2) := hfamily
          _ ≤ (lowDegreeJuntaCutoff k + 1) * (2 * (n + 1)) := by
            apply Nat.mul_le_mul_left
            omega
          _ = 2 * (lowDegreeJuntaCutoff k + 1) * (n + 1) * 1 := by
            ring
          _ ≤ 2 * (lowDegreeJuntaCutoff k + 1) * (n + 1) *
              (confidenceBits + 1) :=
            Nat.mul_le_mul_left _ hconfidence
      have hconfidenceTerm : confidenceBits + 4 ≤
          5 * (n + 1) * (confidenceBits + 1) := by
        calc
          confidenceBits + 4 ≤ 5 * (confidenceBits + 1) := by omega
          _ = (5 * 1) * (confidenceBits + 1) := by ring
          _ ≤ (5 * (n + 1)) * (confidenceBits + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 hn)
      calc
        (Nat.clog 2 (juntaTreeCallCount k) + Nat.clog 2 familyCard) +
            (confidenceBits + 4) ≤
          Nat.clog 2 (juntaTreeCallCount k) * (n + 1) *
                (confidenceBits + 1) +
            2 * (lowDegreeJuntaCutoff k + 1) * (n + 1) *
                (confidenceBits + 1) +
            5 * (n + 1) * (confidenceBits + 1) :=
          Nat.add_le_add (Nat.add_le_add htreeTerm hfamilyTerm)
            hconfidenceTerm
        _ = lowDegreeJuntaLinearConfidenceCoefficient k *
            (n + 1) * (confidenceBits + 1) := by
          unfold lowDegreeJuntaLinearConfidenceCoefficient
          ring

/-- The coefficient-estimation row length is an explicit fixed-`k` multiple of its binary
confidence-bit count. -/
theorem lowDegreeJuntaCoefficientSampleCount_le_failureBits
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter) :
    lowDegreeJuntaCoefficientSampleCount P k failure ≤
      36 * 4 ^ k * fourierEstimatorFailureBits
        (lowDegreeJuntaCoefficientConfidence P k failure) := by
  have hsamples := fourierEstimatorSampleCount_cast_le
    (lowDegreeJuntaCoefficientAccuracy k)
    (lowDegreeJuntaCoefficientConfidence P k failure)
  have hcast : (lowDegreeJuntaCoefficientSampleCount P k failure : ℚ) ≤
      ((36 * 4 ^ k * fourierEstimatorFailureBits
        (lowDegreeJuntaCoefficientConfidence P k failure) : ℕ) : ℚ) := by
    calc
      (lowDegreeJuntaCoefficientSampleCount P k failure : ℚ) ≤
          4 * fourierEstimatorFailureBits
              (lowDegreeJuntaCoefficientConfidence P k failure) /
            (lowDegreeJuntaCoefficientAccuracy k).1 ^ 2 := hsamples
      _ = ((36 * 4 ^ k * fourierEstimatorFailureBits
          (lowDegreeJuntaCoefficientConfidence P k failure) : ℕ) : ℚ) := by
        simp only [lowDegreeJuntaCoefficientAccuracy]
        push_cast
        rw [show (4 : ℚ) ^ k = ((2 : ℚ) ^ k) ^ 2 by
          rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow, pow_two]]
        field_simp
        ring
  exact_mod_cast hcast

/-- The largest exponent needed before testing the coordinates of a sampled ambient example. -/
def lowDegreeJuntaNodeBaseResourceExponent (k : ℕ) : ℕ :=
  lowDegreeJuntaCutoff k + 3

/-- The final fixed-parameter exponent, including the linear scan of fixed coordinates in the
rejection sampler. -/
def lowDegreeJuntaNodeWorkResourceExponent (k : ℕ) : ℕ :=
  lowDegreeJuntaCutoff k + 4

/-- Fixed-`k` coefficient for the complete Fourier-estimation batch at one node. -/
def lowDegreeJuntaFourierBatchLinearCoefficient (k : ℕ) : ℕ :=
  (lowDegreeJuntaCutoff k + 1) *
    (36 * 4 ^ k * lowDegreeJuntaLinearConfidenceCoefficient k)

/-- Fixed-`k` coefficient for the low-degree polynomial-learning suffix at one node. -/
def lowDegreeJuntaPolynomialSampleLinearCoefficient (k : ℕ) : ℕ :=
  2 ^ lowDegreeJuntaPolynomialDegree k *
    (lowDegreeJuntaPolynomialDegree k + 1 +
      lowDegreeJuntaLinearConfidenceCoefficient k)

/-- Fixed-`k` coefficient for all restricted examples requested by one node controller. -/
def lowDegreeJuntaRestrictedSampleLinearCoefficient (k : ℕ) : ℕ :=
  lowDegreeJuntaFourierBatchLinearCoefficient k +
    lowDegreeJuntaPolynomialSampleLinearCoefficient k

/-- Fixed-`k` coefficient for the worst-case row-reduction arithmetic at one node. -/
def lowDegreeJuntaPolynomialWorkLinearCoefficient (k : ℕ) : ℕ :=
  let ℓ := lowDegreeJuntaPolynomialDegree k
  let sampleCoefficient := lowDegreeJuntaPolynomialSampleLinearCoefficient k
  sampleCoefficient * (ℓ + 2) +
    (ℓ + 1) * sampleCoefficient * (ℓ + 3) +
    (ℓ + 1) * (ℓ + 2)

/-- Fixed-`k` coefficient for the complete deterministic node analysis. -/
def lowDegreeJuntaNodeAnalysisLinearCoefficient (k : ℕ) : ℕ :=
  lowDegreeJuntaFourierBatchLinearCoefficient k *
      (lowDegreeJuntaCutoff k + 1) +
    lowDegreeJuntaPolynomialWorkLinearCoefficient k +
    (lowDegreeJuntaCutoff k + 1) +
    (lowDegreeJuntaPolynomialDegree k + 1)

/-- Fixed-`k` coefficient for the ambient random examples used by one node. -/
def lowDegreeJuntaNodeRandomExampleLinearCoefficient (k : ℕ) : ℕ :=
  2 ^ (k + 1) * lowDegreeJuntaRestrictedSampleLinearCoefficient k +
    16 * 4 ^ k * lowDegreeJuntaLinearConfidenceCoefficient k

/-- Fixed-`k` coefficient for all charged work at one node. -/
def lowDegreeJuntaNodeWorkLinearCoefficient (k : ℕ) : ℕ :=
  2 * lowDegreeJuntaNodeRandomExampleLinearCoefficient k +
    lowDegreeJuntaRestrictedSampleLinearCoefficient k +
    lowDegreeJuntaNodeAnalysisLinearCoefficient k

/-- All Fourier-estimation rows at one node have the advertised cutoff-degree envelope and remain
linear in the dyadic confidence index. -/
theorem lowDegreeJuntaFourierBatchSize_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    (lowDegreeJuntaFourierFamily P k).card *
        lowDegreeJuntaCoefficientSampleCount P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaFourierBatchLinearCoefficient k *
        (n + 1) ^ (lowDegreeJuntaCutoff k + 1) *
        (confidenceBits + 1) := by
  have hfamily := card_lowDegreeJuntaFourierFamily_le P k
  have hsamples := lowDegreeJuntaCoefficientSampleCount_le_failureBits
    P k (lowDegreeJuntaDyadicNodeFailure k confidenceBits)
  have hbits := lowDegreeJuntaCoefficientFailureBits_le_linearConfidence
    P k confidenceBits
  calc
    (lowDegreeJuntaFourierFamily P k).card *
        lowDegreeJuntaCoefficientSampleCount P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      ((lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k) *
        (36 * 4 ^ k *
          (lowDegreeJuntaLinearConfidenceCoefficient k *
            (n + 1) * (confidenceBits + 1))) := by
      exact Nat.mul_le_mul hfamily (hsamples.trans <|
        Nat.mul_le_mul_left (36 * 4 ^ k) hbits)
    _ = lowDegreeJuntaFourierBatchLinearCoefficient k *
        (n + 1) ^ (lowDegreeJuntaCutoff k + 1) *
        (confidenceBits + 1) := by
      rw [pow_succ]
      simp only [lowDegreeJuntaFourierBatchLinearCoefficient]
      ring

/-- The Exercise 6.30 suffix has a fixed-`k` sample envelope that is linear in the dyadic
confidence index. -/
theorem lowDegreeJuntaPolynomialSampleCount_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaPolynomialSampleCount P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaPolynomialSampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaPolynomialDegree k *
        (confidenceBits + 1) := by
  let ℓ := lowDegreeJuntaPolynomialDegree k
  let dimension := lowDegreeF₂MonomialCount (juntaRestrictionDimension P) ℓ
  let power := (n + 1) ^ ℓ
  let confidenceCoefficient := lowDegreeJuntaLinearConfidenceCoefficient k
  have hdimension : dimension ≤ (ℓ + 1) * power := by
    calc
      dimension ≤ (ℓ + 1) *
          (juntaRestrictionDimension P + 1) ^ ℓ := by
        simpa [dimension] using
          lowDegreeF₂MonomialCount_le (juntaRestrictionDimension P) ℓ
      _ ≤ (ℓ + 1) * power := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left
          (Nat.succ_le_succ (juntaRestrictionDimension_le P)) _
  have hbits : fourierEstimatorFailureBits
      (lowDegreeJuntaQuarterFailure
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      confidenceCoefficient * (confidenceBits + 1) := by
    simpa [confidenceCoefficient] using
      lowDegreeJuntaQuarterNodeFailureBits_le k confidenceBits
  have hpower : 1 ≤ power := by
    dsimp [power]
    exact Nat.one_le_pow _ _ (by omega)
  have hconfidence : 1 ≤ confidenceBits + 1 := by omega
  have hinner : dimension + fourierEstimatorFailureBits
        (lowDegreeJuntaQuarterFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      (ℓ + 1 + confidenceCoefficient) * power *
        (confidenceBits + 1) := by
    calc
      dimension + fourierEstimatorFailureBits
          (lowDegreeJuntaQuarterFailure
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
        (ℓ + 1) * power +
          confidenceCoefficient * (confidenceBits + 1) :=
        Nat.add_le_add hdimension hbits
      _ ≤ (ℓ + 1 + confidenceCoefficient) * power *
          (confidenceBits + 1) := by
        nlinarith
  change 2 ^ ℓ *
      (dimension + fourierEstimatorFailureBits
        (lowDegreeJuntaQuarterFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits))) ≤ _
  calc
    2 ^ ℓ *
        (dimension + fourierEstimatorFailureBits
          (lowDegreeJuntaQuarterFailure
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits))) ≤
      2 ^ ℓ * ((ℓ + 1 + confidenceCoefficient) * power *
        (confidenceBits + 1)) := Nat.mul_le_mul_left _ hinner
    _ = lowDegreeJuntaPolynomialSampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaPolynomialDegree k *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaPolynomialSampleLinearCoefficient,
        ℓ, power, confidenceCoefficient]
      ring

/-- The complete restricted batch requested by one node fits the common pre-scan exponent and is
linear in the dyadic confidence index. -/
theorem lowDegreeJuntaRestrictedSampleCount_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaRestrictedSampleCount P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaRestrictedSampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
  have hfourier := lowDegreeJuntaFourierBatchSize_le_linearConfidence
    P k confidenceBits
  have hpolynomial := lowDegreeJuntaPolynomialSampleCount_le_linearConfidence
    P k confidenceBits
  have hfourierExponent : lowDegreeJuntaCutoff k + 1 ≤
      lowDegreeJuntaNodeBaseResourceExponent k := by
    simp [lowDegreeJuntaNodeBaseResourceExponent]
  have hpolynomialExponent : lowDegreeJuntaPolynomialDegree k ≤
      lowDegreeJuntaNodeBaseResourceExponent k := by
    have hledger := (lowDegreeJuntaRuntimeExponentLedger k).2
    simp only [lowDegreeJuntaNodeBaseResourceExponent]
    omega
  have hbase : 0 < n + 1 := by omega
  have hfourierPower := Nat.pow_le_pow_right hbase hfourierExponent
  have hpolynomialPower := Nat.pow_le_pow_right hbase hpolynomialExponent
  unfold lowDegreeJuntaRestrictedSampleCount
  calc
    (lowDegreeJuntaFourierFamily P k).card *
          lowDegreeJuntaCoefficientSampleCount P k
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits) +
        lowDegreeJuntaPolynomialSampleCount P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaFourierBatchLinearCoefficient k *
          (n + 1) ^ (lowDegreeJuntaCutoff k + 1) *
          (confidenceBits + 1) +
        lowDegreeJuntaPolynomialSampleLinearCoefficient k *
          (n + 1) ^ lowDegreeJuntaPolynomialDegree k *
          (confidenceBits + 1) := Nat.add_le_add hfourier hpolynomial
    _ ≤ lowDegreeJuntaFourierBatchLinearCoefficient k *
          (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
          (confidenceBits + 1) +
        lowDegreeJuntaPolynomialSampleLinearCoefficient k *
          (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
          (confidenceBits + 1) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hfourierPower)
        (Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hpolynomialPower)
    _ = lowDegreeJuntaRestrictedSampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaRestrictedSampleLinearCoefficient]
      ring

/-- Re-expanding the three primitive row-reduction summands preserves a single power of the
confidence index; no cubic confidence envelope is used. -/
theorem lowDegreeJuntaPolynomialWorkBound_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaPolynomialWorkBound P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaPolynomialWorkLinearCoefficient k *
        (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) *
        (confidenceBits + 1) := by
  let ℓ := lowDegreeJuntaPolynomialDegree k
  let dimension := lowDegreeF₂MonomialCount (juntaRestrictionDimension P) ℓ
  let sampleCount := lowDegreeJuntaPolynomialSampleCount P k
    (lowDegreeJuntaDyadicNodeFailure k confidenceBits)
  let power := (n + 1) ^ ℓ
  let sampleCoefficient := lowDegreeJuntaPolynomialSampleLinearCoefficient k
  have hdimension : dimension ≤ (ℓ + 1) * power := by
    calc
      dimension ≤ (ℓ + 1) *
          (juntaRestrictionDimension P + 1) ^ ℓ := by
        simpa [dimension] using
          lowDegreeF₂MonomialCount_le (juntaRestrictionDimension P) ℓ
      _ ≤ (ℓ + 1) * power := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left
          (Nat.succ_le_succ (juntaRestrictionDimension_le P)) _
  have hsamples : sampleCount ≤ sampleCoefficient * power *
      (confidenceBits + 1) := by
    simpa [sampleCount, sampleCoefficient, power, ℓ] using
      lowDegreeJuntaPolynomialSampleCount_le_linearConfidence
        P k confidenceBits
  have hpower : 1 ≤ power := by
    dsimp [power]
    exact Nat.one_le_pow _ _ (by omega)
  have hconfidence : 1 ≤ confidenceBits + 1 := by omega
  have hdimensionOne : dimension + 1 ≤ (ℓ + 2) * power := by
    nlinarith
  have hdimensionTwo : dimension + 2 ≤ (ℓ + 3) * power := by
    nlinarith
  have hfirst : sampleCount * (dimension + 1) ≤
      (sampleCoefficient * power * (confidenceBits + 1)) *
        ((ℓ + 2) * power) :=
    Nat.mul_le_mul hsamples hdimensionOne
  have hfirstCube : sampleCount * (dimension + 1) ≤
      (sampleCoefficient * power * (confidenceBits + 1)) *
        ((ℓ + 2) * power) * power := by
    calc
      sampleCount * (dimension + 1) ≤
          (sampleCoefficient * power * (confidenceBits + 1)) *
            ((ℓ + 2) * power) := hfirst
      _ = ((sampleCoefficient * power * (confidenceBits + 1)) *
          ((ℓ + 2) * power)) * 1 := by ring
      _ ≤ ((sampleCoefficient * power * (confidenceBits + 1)) *
          ((ℓ + 2) * power)) * power :=
        Nat.mul_le_mul_left _ hpower
  have hmiddle : dimension * sampleCount * (dimension + 2) ≤
      ((ℓ + 1) * power) *
        (sampleCoefficient * power * (confidenceBits + 1)) *
        ((ℓ + 3) * power) :=
    Nat.mul_le_mul (Nat.mul_le_mul hdimension hsamples) hdimensionTwo
  have hlast : dimension * (dimension + 1) ≤
      ((ℓ + 1) * power) * ((ℓ + 2) * power) *
        (confidenceBits + 1) := by
    calc
      dimension * (dimension + 1) ≤
          ((ℓ + 1) * power) * ((ℓ + 2) * power) :=
        Nat.mul_le_mul hdimension hdimensionOne
      _ = ((ℓ + 1) * power) * ((ℓ + 2) * power) * 1 := by ring
      _ ≤ ((ℓ + 1) * power) * ((ℓ + 2) * power) *
          (confidenceBits + 1) :=
        Nat.mul_le_mul_left _ hconfidence
  have hlastCube : dimension * (dimension + 1) ≤
      ((ℓ + 1) * power) * ((ℓ + 2) * power) *
        (confidenceBits + 1) * power := by
    calc
      dimension * (dimension + 1) ≤
          ((ℓ + 1) * power) * ((ℓ + 2) * power) *
            (confidenceBits + 1) := hlast
      _ = (((ℓ + 1) * power) * ((ℓ + 2) * power) *
          (confidenceBits + 1)) * 1 := by ring
      _ ≤ (((ℓ + 1) * power) * ((ℓ + 2) * power) *
          (confidenceBits + 1)) * power :=
        Nat.mul_le_mul_left _ hpower
  change sampleCount * (dimension + 1) +
      dimension * sampleCount * (dimension + 2) +
      dimension * (dimension + 1) ≤ _
  calc
    sampleCount * (dimension + 1) +
          dimension * sampleCount * (dimension + 2) +
          dimension * (dimension + 1) ≤
      (sampleCoefficient * power * (confidenceBits + 1)) *
          ((ℓ + 2) * power) * power +
        ((ℓ + 1) * power) *
          (sampleCoefficient * power * (confidenceBits + 1)) *
          ((ℓ + 3) * power) +
        ((ℓ + 1) * power) * ((ℓ + 2) * power) *
          (confidenceBits + 1) * power :=
      Nat.add_le_add (Nat.add_le_add hfirstCube hmiddle) hlastCube
    _ = lowDegreeJuntaPolynomialWorkLinearCoefficient k * power ^ 3 *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaPolynomialWorkLinearCoefficient,
        sampleCoefficient, ℓ]
      ring
    _ = lowDegreeJuntaPolynomialWorkLinearCoefficient k *
        (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) *
        (confidenceBits + 1) := by
      rw [show power ^ 3 = (n + 1) ^ (3 * ℓ) by
        dsimp [power]
        simpa [Nat.mul_comm] using (pow_mul (n + 1) ℓ 3).symm]

/-- The complete deterministic analysis phase at one node has the common pre-scan exponent and
depends linearly on the dyadic confidence index. -/
theorem lowDegreeJuntaNodeAnalysisWorkBound_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaNodeAnalysisWorkBound P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeAnalysisLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
  let basePower := (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k
  have hfourier := lowDegreeJuntaFourierBatchSize_le_linearConfidence
    P k confidenceBits
  have hpolynomial := lowDegreeJuntaPolynomialWorkBound_le_linearConfidence
    P k confidenceBits
  have hfamily := card_lowDegreeJuntaFourierFamily_le P k
  have hdimension : lowDegreeF₂MonomialCount (juntaRestrictionDimension P)
      (lowDegreeJuntaPolynomialDegree k) ≤
      (lowDegreeJuntaPolynomialDegree k + 1) *
        (n + 1) ^ lowDegreeJuntaPolynomialDegree k := by
    calc
      lowDegreeF₂MonomialCount (juntaRestrictionDimension P)
          (lowDegreeJuntaPolynomialDegree k) ≤
        (lowDegreeJuntaPolynomialDegree k + 1) *
          (juntaRestrictionDimension P + 1) ^
            lowDegreeJuntaPolynomialDegree k :=
        lowDegreeF₂MonomialCount_le _ _
      _ ≤ (lowDegreeJuntaPolynomialDegree k + 1) *
          (n + 1) ^ lowDegreeJuntaPolynomialDegree k := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left
          (Nat.succ_le_succ (juntaRestrictionDimension_le P)) _
  have hbase : 0 < n + 1 := by omega
  have hfourierPower : (n + 1) ^ (lowDegreeJuntaCutoff k + 1) ≤
      basePower := by
    apply Nat.pow_le_pow_right hbase
    simp [lowDegreeJuntaNodeBaseResourceExponent]
  have hpolynomialPower :
      (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) ≤ basePower := by
    apply Nat.pow_le_pow_right hbase
    simpa [lowDegreeJuntaNodeBaseResourceExponent] using
      (lowDegreeJuntaRuntimeExponentLedger k).2
  have hfamilyPower : (n + 1) ^ lowDegreeJuntaCutoff k ≤ basePower := by
    apply Nat.pow_le_pow_right hbase
    simp [lowDegreeJuntaNodeBaseResourceExponent]
  have hdimensionExponent : lowDegreeJuntaPolynomialDegree k ≤
      lowDegreeJuntaNodeBaseResourceExponent k := by
    have hledger := (lowDegreeJuntaRuntimeExponentLedger k).2
    simp only [lowDegreeJuntaNodeBaseResourceExponent]
    omega
  have hdimensionPower :
      (n + 1) ^ lowDegreeJuntaPolynomialDegree k ≤ basePower :=
    Nat.pow_le_pow_right hbase hdimensionExponent
  have hconfidence : 1 ≤ confidenceBits + 1 := by omega
  have hfourierLift :
      lowDegreeJuntaFourierBatchLinearCoefficient k *
            (n + 1) ^ (lowDegreeJuntaCutoff k + 1) *
            (confidenceBits + 1) * (lowDegreeJuntaCutoff k + 1) ≤
        lowDegreeJuntaFourierBatchLinearCoefficient k * basePower *
            (confidenceBits + 1) * (lowDegreeJuntaCutoff k + 1) :=
    Nat.mul_le_mul_right _ <| Nat.mul_le_mul_right _ <|
      Nat.mul_le_mul_left _ hfourierPower
  have hpolynomialLift :
      lowDegreeJuntaPolynomialWorkLinearCoefficient k *
            (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) *
            (confidenceBits + 1) ≤
        lowDegreeJuntaPolynomialWorkLinearCoefficient k * basePower *
            (confidenceBits + 1) :=
    Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hpolynomialPower
  have hfamilyLift :
      (lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k ≤
        (lowDegreeJuntaCutoff k + 1) * basePower *
          (confidenceBits + 1) := by
    calc
      (lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k ≤
        (lowDegreeJuntaCutoff k + 1) * basePower :=
          Nat.mul_le_mul_left _ hfamilyPower
      _ = (lowDegreeJuntaCutoff k + 1) * basePower * 1 := by ring
      _ ≤ (lowDegreeJuntaCutoff k + 1) * basePower *
          (confidenceBits + 1) := Nat.mul_le_mul_left _ hconfidence
  have hdimensionLift :
      (lowDegreeJuntaPolynomialDegree k + 1) *
          (n + 1) ^ lowDegreeJuntaPolynomialDegree k ≤
        (lowDegreeJuntaPolynomialDegree k + 1) * basePower *
          (confidenceBits + 1) := by
    calc
      (lowDegreeJuntaPolynomialDegree k + 1) *
          (n + 1) ^ lowDegreeJuntaPolynomialDegree k ≤
        (lowDegreeJuntaPolynomialDegree k + 1) * basePower :=
          Nat.mul_le_mul_left _ hdimensionPower
      _ = (lowDegreeJuntaPolynomialDegree k + 1) * basePower * 1 := by ring
      _ ≤ (lowDegreeJuntaPolynomialDegree k + 1) * basePower *
          (confidenceBits + 1) := Nat.mul_le_mul_left _ hconfidence
  unfold lowDegreeJuntaNodeAnalysisWorkBound
  calc
    (lowDegreeJuntaFourierFamily P k).card *
          lowDegreeJuntaCoefficientSampleCount P k
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits) *
            (lowDegreeJuntaCutoff k + 1) +
        lowDegreeJuntaPolynomialWorkBound P k
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits) +
        (lowDegreeJuntaFourierFamily P k).card +
        lowDegreeF₂MonomialCount (juntaRestrictionDimension P)
          (lowDegreeJuntaPolynomialDegree k) ≤
      lowDegreeJuntaFourierBatchLinearCoefficient k *
            (n + 1) ^ (lowDegreeJuntaCutoff k + 1) *
            (confidenceBits + 1) * (lowDegreeJuntaCutoff k + 1) +
        lowDegreeJuntaPolynomialWorkLinearCoefficient k *
            (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) *
            (confidenceBits + 1) +
        (lowDegreeJuntaCutoff k + 1) *
            (n + 1) ^ lowDegreeJuntaCutoff k +
        (lowDegreeJuntaPolynomialDegree k + 1) *
            (n + 1) ^ lowDegreeJuntaPolynomialDegree k := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_right _ hfourier) hpolynomial)
          hfamily)
        hdimension
    _ ≤ lowDegreeJuntaFourierBatchLinearCoefficient k * basePower *
            (confidenceBits + 1) * (lowDegreeJuntaCutoff k + 1) +
        lowDegreeJuntaPolynomialWorkLinearCoefficient k * basePower *
            (confidenceBits + 1) +
        (lowDegreeJuntaCutoff k + 1) * basePower *
            (confidenceBits + 1) +
        (lowDegreeJuntaPolynomialDegree k + 1) * basePower *
            (confidenceBits + 1) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hfourierLift hpolynomialLift)
          hfamilyLift)
        hdimensionLift
    _ = lowDegreeJuntaNodeAnalysisLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaNodeAnalysisLinearCoefficient, basePower]
      ring

/-- One concrete node invocation has a uniform fixed-`k` random-example envelope linear in the
dyadic confidence index. -/
theorem lowDegreeJuntaNodeRandomExamples_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaNodeRandomExamples P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
  let M := lowDegreeJuntaRestrictedSampleCount P k
    (lowDegreeJuntaDyadicNodeFailure k confidenceBits)
  let basePower := (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k
  have hM : M ≤ lowDegreeJuntaRestrictedSampleLinearCoefficient k *
      basePower * (confidenceBits + 1) := by
    simpa [M, basePower] using
      lowDegreeJuntaRestrictedSampleCount_le_linearConfidence
        P k confidenceBits
  have hbits := lowDegreeJuntaHalfNodeFailureBits_le k confidenceBits
  have hsamplerCast := juntaRestrictionSampleCount_cast_le k M
    (lowDegreeJuntaHalfFailure
      (lowDegreeJuntaDyadicNodeFailure k confidenceBits))
  have hsampler : juntaRestrictionSampleCount k M
      (lowDegreeJuntaHalfFailure
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      2 ^ (k + 1) * M +
        16 * 4 ^ k * fourierEstimatorFailureBits
          (lowDegreeJuntaHalfFailure
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) := by
    exact_mod_cast hsamplerCast
  have hbasePower : 1 ≤ basePower := by
    dsimp [basePower]
    exact Nat.one_le_pow _ _ (by omega)
  have hconfidenceLift :
      lowDegreeJuntaLinearConfidenceCoefficient k * (confidenceBits + 1) ≤
        lowDegreeJuntaLinearConfidenceCoefficient k * basePower *
          (confidenceBits + 1) := by
    apply Nat.mul_le_mul_right
    calc
      lowDegreeJuntaLinearConfidenceCoefficient k =
          lowDegreeJuntaLinearConfidenceCoefficient k * 1 := by ring
      _ ≤ lowDegreeJuntaLinearConfidenceCoefficient k * basePower :=
        Nat.mul_le_mul_left _ hbasePower
  unfold lowDegreeJuntaNodeRandomExamples
  change juntaRestrictionSampleCount k M
      (lowDegreeJuntaHalfFailure
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤ _
  calc
    juntaRestrictionSampleCount k M
        (lowDegreeJuntaHalfFailure
          (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) ≤
      2 ^ (k + 1) * M +
        16 * 4 ^ k * fourierEstimatorFailureBits
          (lowDegreeJuntaHalfFailure
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits)) := hsampler
    _ ≤ 2 ^ (k + 1) *
          (lowDegreeJuntaRestrictedSampleLinearCoefficient k *
            basePower * (confidenceBits + 1)) +
        16 * 4 ^ k *
          (lowDegreeJuntaLinearConfidenceCoefficient k *
            (confidenceBits + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ hM)
        (Nat.mul_le_mul_left _ hbits)
    _ ≤ 2 ^ (k + 1) *
          (lowDegreeJuntaRestrictedSampleLinearCoefficient k *
            basePower * (confidenceBits + 1)) +
        16 * 4 ^ k *
          (lowDegreeJuntaLinearConfidenceCoefficient k *
            basePower * (confidenceBits + 1)) := by
      exact Nat.add_le_add le_rfl
        (Nat.mul_le_mul_left (16 * 4 ^ k) hconfidenceLift)
    _ = lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaNodeRandomExampleLinearCoefficient, basePower]
      ring

/-- One concrete node invocation has a uniform fixed-`k` charged-work envelope linear in the
dyadic confidence index. -/
theorem lowDegreeJuntaNodeWorkBound_le_linearConfidence
    (P : Finset (Fin n)) (k confidenceBits : ℕ) :
    lowDegreeJuntaNodeWorkBound P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeWorkLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k *
        (confidenceBits + 1) := by
  let M := lowDegreeJuntaRestrictedSampleCount P k
    (lowDegreeJuntaDyadicNodeFailure k confidenceBits)
  let randomExamples := lowDegreeJuntaNodeRandomExamples P k
    (lowDegreeJuntaDyadicNodeFailure k confidenceBits)
  let basePower := (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k
  let workPower := (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k
  have hM : M ≤ lowDegreeJuntaRestrictedSampleLinearCoefficient k *
      basePower * (confidenceBits + 1) := by
    simpa [M, basePower] using
      lowDegreeJuntaRestrictedSampleCount_le_linearConfidence
        P k confidenceBits
  have hrandom : randomExamples ≤
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
        basePower * (confidenceBits + 1) := by
    simpa [randomExamples, basePower] using
      lowDegreeJuntaNodeRandomExamples_le_linearConfidence
        P k confidenceBits
  have hanalysis := lowDegreeJuntaNodeAnalysisWorkBound_le_linearConfidence
    P k confidenceBits
  have hcard : P.card + 1 ≤ n + 1 := by
    simpa using Nat.succ_le_succ (Finset.card_le_univ P)
  have hpower : workPower = basePower * (n + 1) := by
    simp only [workPower, basePower, lowDegreeJuntaNodeWorkResourceExponent,
      lowDegreeJuntaNodeBaseResourceExponent]
    rw [show lowDegreeJuntaCutoff k + 4 =
      (lowDegreeJuntaCutoff k + 3) + 1 by omega, pow_succ]
  have hbasePower : basePower ≤ workPower := by
    rw [hpower]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hrandomLift :
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k * basePower *
          (confidenceBits + 1) ≤
        lowDegreeJuntaNodeRandomExampleLinearCoefficient k * workPower *
          (confidenceBits + 1) :=
    Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hbasePower
  have hrandomScanLift :
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k * basePower *
          (confidenceBits + 1) * (n + 1) ≤
        lowDegreeJuntaNodeRandomExampleLinearCoefficient k * workPower *
          (confidenceBits + 1) := by
    apply le_of_eq
    rw [hpower]
    ring
  have hrestrictedLift :
      lowDegreeJuntaRestrictedSampleLinearCoefficient k * basePower *
          (confidenceBits + 1) ≤
        lowDegreeJuntaRestrictedSampleLinearCoefficient k * workPower *
          (confidenceBits + 1) :=
    Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hbasePower
  have hanalysisLift :
      lowDegreeJuntaNodeAnalysisLinearCoefficient k * basePower *
          (confidenceBits + 1) ≤
        lowDegreeJuntaNodeAnalysisLinearCoefficient k * workPower *
          (confidenceBits + 1) :=
    Nat.mul_le_mul_right _ <| Nat.mul_le_mul_left _ hbasePower
  unfold lowDegreeJuntaNodeWorkBound
  change randomExamples +
      (randomExamples * (P.card + 1) + M) +
      lowDegreeJuntaNodeAnalysisWorkBound P k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤ _
  calc
    randomExamples + (randomExamples * (P.card + 1) + M) +
          lowDegreeJuntaNodeAnalysisWorkBound P k
            (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k * basePower *
            (confidenceBits + 1) +
        (lowDegreeJuntaNodeRandomExampleLinearCoefficient k * basePower *
              (confidenceBits + 1) * (n + 1) +
          lowDegreeJuntaRestrictedSampleLinearCoefficient k * basePower *
              (confidenceBits + 1)) +
        lowDegreeJuntaNodeAnalysisLinearCoefficient k * basePower *
            (confidenceBits + 1) := by
      exact Nat.add_le_add
        (Nat.add_le_add hrandom
          (Nat.add_le_add (Nat.mul_le_mul hrandom hcard) hM))
        hanalysis
    _ ≤ lowDegreeJuntaNodeRandomExampleLinearCoefficient k * workPower *
            (confidenceBits + 1) +
        (lowDegreeJuntaNodeRandomExampleLinearCoefficient k * workPower *
              (confidenceBits + 1) +
          lowDegreeJuntaRestrictedSampleLinearCoefficient k * workPower *
              (confidenceBits + 1)) +
        lowDegreeJuntaNodeAnalysisLinearCoefficient k * workPower *
            (confidenceBits + 1) := by
      exact Nat.add_le_add
        (Nat.add_le_add hrandomLift
          (Nat.add_le_add hrandomScanLift hrestrictedLift))
        hanalysisLift
    _ = lowDegreeJuntaNodeWorkLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k *
        (confidenceBits + 1) := by
      simp only [lowDegreeJuntaNodeWorkLinearCoefficient, workPower]
      ring

/-- The finite supremum defining the public node random-example bound obeys the same linear
confidence envelope. -/
theorem lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence
    (n k confidenceBits : ℕ) :
    lowDegreeJuntaNodeRandomExampleBound n k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
  unfold lowDegreeJuntaNodeRandomExampleBound
  apply Finset.sup_le
  intro P _
  exact lowDegreeJuntaNodeRandomExamples_le_linearConfidence P k confidenceBits

/-- The finite supremum defining the public node work bound obeys the same linear confidence
envelope. -/
theorem lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence
    (n k confidenceBits : ℕ) :
    lowDegreeJuntaNodeUniformWorkBound n k
        (lowDegreeJuntaDyadicNodeFailure k confidenceBits) ≤
      lowDegreeJuntaNodeWorkLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k *
        (confidenceBits + 1) := by
  unfold lowDegreeJuntaNodeUniformWorkBound
  apply Finset.sup_le
  intro P _
  exact lowDegreeJuntaNodeWorkBound_le_linearConfidence P k confidenceBits

/-! ## Unconditional whole-tree linear-confidence bounds -/

/-- Every dyadic-confidence whole-tree random-example budget is linear in
`log₂(1 / failure)` and has exponent `⌊3k/4⌋ + 3` in `n + 1`. -/
theorem lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence
    (n k confidenceBits : ℕ) :
    lowDegreeJuntaTotalRandomExampleBudget n k
        (lowDegreeJuntaDyadicFailure confidenceBits) ≤
      juntaTreeCallCount k *
        lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
        (confidenceBits + 1) := by
  unfold lowDegreeJuntaTotalRandomExampleBudget
  simpa only [lowDegreeJuntaDyadicNodeFailure, Nat.mul_assoc] using
    Nat.mul_le_mul_left (juntaTreeCallCount k)
      (lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence
        n k confidenceBits)

/-- Every dyadic-confidence whole-tree charged-work budget is linear in
`log₂(1 / failure)` and has exponent `⌊3k/4⌋ + 4` in `n + 1`. -/
theorem lowDegreeJuntaTotalWorkBudget_le_linearConfidence
    (n k confidenceBits : ℕ) :
    lowDegreeJuntaTotalWorkBudget n k
        (lowDegreeJuntaDyadicFailure confidenceBits) ≤
      juntaTreeCallCount k * lowDegreeJuntaNodeWorkLinearCoefficient k *
        (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k *
        (confidenceBits + 1) := by
  unfold lowDegreeJuntaTotalWorkBudget
  simpa only [lowDegreeJuntaDyadicNodeFailure, Nat.mul_assoc] using
    Nat.mul_le_mul_left (juntaTreeCallCount k)
      (lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence
        n k confidenceBits)

/-! ## Theorem 6.36 algorithm resources -/

/-- The formal Theorem 6.36 algorithm has an explicit finite random-example bound.  Its fixed
dyadic confidence factor `3 + 1` is absorbed into the coefficient depending only on `k`. -/
theorem lowDegreeJuntaLearningAlgorithm_randomExampleCost_le
    (n k : ℕ) (accuracy : LearningAccuracy) :
    (lowDegreeJuntaLearningAlgorithm n k).randomExampleCost accuracy ≤
      (4 * juntaTreeCallCount k *
        lowDegreeJuntaNodeRandomExampleLinearCoefficient k) *
        (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k := by
  change juntaTreeCallCount k *
      lowDegreeJuntaNodeRandomExampleBound n k
        (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure) ≤ _
  calc
    juntaTreeCallCount k *
          lowDegreeJuntaNodeRandomExampleBound n k
            (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure) =
        lowDegreeJuntaTotalRandomExampleBudget n k
          lowDegreeJuntaLearningFailure := rfl
    _ = lowDegreeJuntaTotalRandomExampleBudget n k
        (lowDegreeJuntaDyadicFailure 3) := by
      rw [lowDegreeJuntaLearningFailure_eq_dyadicFailure]
    _ ≤ juntaTreeCallCount k *
          lowDegreeJuntaNodeRandomExampleLinearCoefficient k *
          (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
          (3 + 1) :=
      lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence n k 3
    _ = (4 * juntaTreeCallCount k *
          lowDegreeJuntaNodeRandomExampleLinearCoefficient k) *
          (n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k := by
      ring

/-- The formal Theorem 6.36 algorithm has an explicit finite charged-work bound.  Its fixed
dyadic confidence factor `3 + 1` is absorbed into the coefficient depending only on `k`. -/
theorem lowDegreeJuntaLearningAlgorithm_workCost_le
    (n k : ℕ) (accuracy : LearningAccuracy) :
    (lowDegreeJuntaLearningAlgorithm n k).workCost accuracy ≤
      (4 * juntaTreeCallCount k * lowDegreeJuntaNodeWorkLinearCoefficient k) *
        (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k := by
  change juntaTreeCallCount k *
      lowDegreeJuntaNodeUniformWorkBound n k
        (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure) ≤ _
  calc
    juntaTreeCallCount k *
          lowDegreeJuntaNodeUniformWorkBound n k
            (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure) =
        lowDegreeJuntaTotalWorkBudget n k lowDegreeJuntaLearningFailure := rfl
    _ = lowDegreeJuntaTotalWorkBudget n k
        (lowDegreeJuntaDyadicFailure 3) := by
      rw [lowDegreeJuntaLearningFailure_eq_dyadicFailure]
    _ ≤ juntaTreeCallCount k * lowDegreeJuntaNodeWorkLinearCoefficient k *
          (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k * (3 + 1) :=
      lowDegreeJuntaTotalWorkBudget_le_linearConfidence n k 3
    _ = (4 * juntaTreeCallCount k *
          lowDegreeJuntaNodeWorkLinearCoefficient k) *
          (n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k := by
      ring

/-- For fixed `k`, the actual random-example cost field of the formal Theorem 6.36 algorithm is
polynomial in the ambient dimension with exponent `⌊3k/4⌋ + 3`. -/
theorem lowDegreeJuntaLearningAlgorithm_randomExampleCost_isBigO
    (k : ℕ) (accuracy : LearningAccuracy) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦
        ((lowDegreeJuntaLearningAlgorithm n k).randomExampleCost accuracy : ℝ))
      (fun n : ℕ ↦
        (((n + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (4 * juntaTreeCallCount k *
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k : ℝ))
    (Filter.Eventually.of_forall fun n ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast lowDegreeJuntaLearningAlgorithm_randomExampleCost_le
    n k accuracy

/-- For fixed `k`, the actual charged-work cost field of the formal Theorem 6.36 algorithm is
polynomial in the ambient dimension with exponent `⌊3k/4⌋ + 4`. -/
theorem lowDegreeJuntaLearningAlgorithm_workCost_isBigO
    (k : ℕ) (accuracy : LearningAccuracy) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦
        ((lowDegreeJuntaLearningAlgorithm n k).workCost accuracy : ℝ))
      (fun n : ℕ ↦
        (((n + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (4 * juntaTreeCallCount k *
      lowDegreeJuntaNodeWorkLinearCoefficient k : ℝ))
    (Filter.Eventually.of_forall fun n ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast lowDegreeJuntaLearningAlgorithm_workCost_le n k accuracy

/-- For fixed `k`, the whole-tree random-example budget is jointly polynomial in `n` and linear
in the dyadic index `log₂(1 / failure)`. -/
theorem lowDegreeJuntaTotalRandomExampleBudget_isBigO_linearConfidence (k : ℕ) :
    Asymptotics.IsBigO Filter.atTop
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaTotalRandomExampleBudget input.1 k
          (lowDegreeJuntaDyadicFailure input.2) : ℝ))
      (fun input : ℕ × ℕ ↦
        (((input.1 + 1) ^ lowDegreeJuntaNodeBaseResourceExponent k *
          (input.2 + 1) : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (juntaTreeCallCount k *
      lowDegreeJuntaNodeRandomExampleLinearCoefficient k : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (by
    simpa only [Nat.mul_assoc] using
      lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence
        input.1 k input.2)

/-- For fixed `k`, the whole-tree charged work is jointly polynomial in `n` and linear in the
dyadic index `log₂(1 / failure)`. -/
theorem lowDegreeJuntaTotalWorkBudget_isBigO_linearConfidence (k : ℕ) :
    Asymptotics.IsBigO Filter.atTop
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaTotalWorkBudget input.1 k
          (lowDegreeJuntaDyadicFailure input.2) : ℝ))
      (fun input : ℕ × ℕ ↦
        (((input.1 + 1) ^ lowDegreeJuntaNodeWorkResourceExponent k *
          (input.2 + 1) : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (juntaTreeCallCount k *
      lowDegreeJuntaNodeWorkLinearCoefficient k : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (by
    simpa only [Nat.mul_assoc] using
      lowDegreeJuntaTotalWorkBudget_le_linearConfidence
        input.1 k input.2)

/-- A genuine polynomial comparison scale in the dimension and the dyadic confidence index. -/
def lowDegreeJuntaPolynomialResourceScale
    (n confidenceBits dimensionExponent confidenceExponent : ℕ) : ℕ :=
  (n + 1) ^ dimensionExponent *
    (confidenceBits + 1) ^ confidenceExponent

/-- Finite evidence that, for fixed `k`, both uniform node envelopes are bounded by one polynomial
in the ambient dimension and the dyadic confidence index.  This pointwise witness is strictly
stronger than the whole-tree `IsBigO` conclusions derived from it. -/
structure LowDegreeJuntaNodePolynomialWitness
    (k dimensionExponent confidenceExponent : ℕ) where
  /-- Common coefficient for the two node-resource bounds. -/
  constant : ℕ
  /-- Uniform node random examples obey the advertised polynomial. -/
  randomExamples_le : ∀ n confidenceBits,
    lowDegreeJuntaNodeRandomExampleBound n k
        (juntaTreePerCallFailure k
          (lowDegreeJuntaDyadicFailure confidenceBits)) ≤
      constant * lowDegreeJuntaPolynomialResourceScale
        n confidenceBits dimensionExponent confidenceExponent
  /-- Uniform node local work obeys the advertised polynomial. -/
  work_le : ∀ n confidenceBits,
    lowDegreeJuntaNodeUniformWorkBound n k
        (juntaTreePerCallFailure k
          (lowDegreeJuntaDyadicFailure confidenceBits)) ≤
      constant * lowDegreeJuntaPolynomialResourceScale
        n confidenceBits dimensionExponent confidenceExponent

/-- A fixed-`k` node witness gives a nonasymptotic polynomial bound for the whole-tree
random-example budget. -/
theorem lowDegreeJuntaTotalRandomExampleBudget_le_of_polynomialWitness
    {k dimensionExponent confidenceExponent : ℕ}
    (witness : LowDegreeJuntaNodePolynomialWitness
      k dimensionExponent confidenceExponent)
    (n confidenceBits : ℕ) :
    lowDegreeJuntaTotalRandomExampleBudget n k
        (lowDegreeJuntaDyadicFailure confidenceBits) ≤
      juntaTreeCallCount k * witness.constant *
        lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent := by
  unfold lowDegreeJuntaTotalRandomExampleBudget
  calc
    juntaTreeCallCount k *
        lowDegreeJuntaNodeRandomExampleBound n k
          (juntaTreePerCallFailure k
            (lowDegreeJuntaDyadicFailure confidenceBits)) ≤
      juntaTreeCallCount k *
        (witness.constant * lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent) :=
        Nat.mul_le_mul_left _ (witness.randomExamples_le n confidenceBits)
    _ = juntaTreeCallCount k * witness.constant *
        lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent := by ring

/-- A fixed-`k` node witness gives a nonasymptotic polynomial bound for the whole-tree local-work
budget. -/
theorem lowDegreeJuntaTotalWorkBudget_le_of_polynomialWitness
    {k dimensionExponent confidenceExponent : ℕ}
    (witness : LowDegreeJuntaNodePolynomialWitness
      k dimensionExponent confidenceExponent)
    (n confidenceBits : ℕ) :
    lowDegreeJuntaTotalWorkBudget n k
        (lowDegreeJuntaDyadicFailure confidenceBits) ≤
      juntaTreeCallCount k * witness.constant *
        lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent := by
  unfold lowDegreeJuntaTotalWorkBudget
  calc
    juntaTreeCallCount k *
        lowDegreeJuntaNodeUniformWorkBound n k
          (juntaTreePerCallFailure k
            (lowDegreeJuntaDyadicFailure confidenceBits)) ≤
      juntaTreeCallCount k *
        (witness.constant * lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent) :=
        Nat.mul_le_mul_left _ (witness.work_le n confidenceBits)
    _ = juntaTreeCallCount k * witness.constant *
        lowDegreeJuntaPolynomialResourceScale
          n confidenceBits dimensionExponent confidenceExponent := by ring

/-- For fixed `k`, the whole-tree random-example budget is jointly polynomial in `n` and the
dyadic index `log₂(1 / failure)`, provided by a finite node witness. -/
theorem lowDegreeJuntaTotalRandomExampleBudget_isBigO_of_polynomialWitness
    {k dimensionExponent confidenceExponent : ℕ}
    (witness : LowDegreeJuntaNodePolynomialWitness
      k dimensionExponent confidenceExponent) :
    Asymptotics.IsBigO Filter.atTop
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaTotalRandomExampleBudget input.1 k
          (lowDegreeJuntaDyadicFailure input.2) : ℝ))
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaPolynomialResourceScale input.1 input.2
          dimensionExponent confidenceExponent : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (juntaTreeCallCount k * witness.constant : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast
    lowDegreeJuntaTotalRandomExampleBudget_le_of_polynomialWitness
      witness input.1 input.2

/-- For fixed `k`, the whole-tree charged work is jointly polynomial in `n` and the dyadic index
`log₂(1 / failure)`, provided by a finite node witness. -/
theorem lowDegreeJuntaTotalWorkBudget_isBigO_of_polynomialWitness
    {k dimensionExponent confidenceExponent : ℕ}
    (witness : LowDegreeJuntaNodePolynomialWitness
      k dimensionExponent confidenceExponent) :
    Asymptotics.IsBigO Filter.atTop
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaTotalWorkBudget input.1 k
          (lowDegreeJuntaDyadicFailure input.2) : ℝ))
      (fun input : ℕ × ℕ ↦
        (lowDegreeJuntaPolynomialResourceScale input.1 input.2
          dimensionExponent confidenceExponent : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (juntaTreeCallCount k * witness.constant : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast lowDegreeJuntaTotalWorkBudget_le_of_polynomialWitness
    witness input.1 input.2

end FABL
