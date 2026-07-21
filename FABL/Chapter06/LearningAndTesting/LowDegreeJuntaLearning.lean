/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter03.QueryLearning
import FABL.Chapter06.F₂Polynomials.Affine
import FABL.Chapter06.F₂Polynomials.Siegenthaler
import FABL.Chapter06.LearningAndTesting.JuntaFourierGap
import FABL.Chapter06.LearningAndTesting.JuntaLearningReduction
import FABL.Chapter06.LearningAndTesting.LowDegreeF₂PolynomialLearning
import FABL.Chapter06.LearningAndTesting.RestrictionWeights

/-!
# Exact random-example learning of low-degree juntas

Book items: Theorem 6.36, Lemma 6.37, and the matrix-exponent refinement following
Theorem 6.36.

The node program estimates every Fourier coefficient through the balanced cutoff, and otherwise
applies the actual Exercise 6.30 row-reduction learner.  Exercise 6.31 transports the resulting
relevant-coordinate finder to a complete depth-bounded decision-tree learner.
-/

open Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal

set_option autoImplicit false

@[expose] public section

namespace FABL

universe u

variable {n : ℕ}

local instance lowDegreeJuntaSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance lowDegreeJuntaSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Balanced cutoffs and confidence budgets -/

/-- The Fourier-enumeration cutoff `⌊3k/4⌋` in Theorem 6.36. -/
def lowDegreeJuntaCutoff (k : ℕ) : ℕ := 3 * k / 4

/-- The complementary algebraic-degree budget after the Fourier scan. -/
def lowDegreeJuntaPolynomialDegree (k : ℕ) : ℕ := k - lowDegreeJuntaCutoff k

theorem lowDegreeJuntaCutoff_le (k : ℕ) : lowDegreeJuntaCutoff k ≤ k := by
  unfold lowDegreeJuntaCutoff
  omega

theorem lowDegreeJuntaPolynomialDegree_pos {k : ℕ} (hk : 0 < k) :
    0 < lowDegreeJuntaPolynomialDegree k := by
  unfold lowDegreeJuntaPolynomialDegree lowDegreeJuntaCutoff
  omega

theorem three_mul_lowDegreeJuntaPolynomialDegree_le_cutoff_add_three (k : ℕ) :
    3 * lowDegreeJuntaPolynomialDegree k ≤ lowDegreeJuntaCutoff k + 3 := by
  unfold lowDegreeJuntaPolynomialDegree lowDegreeJuntaCutoff
  omega

theorem lowDegreeJuntaCutoff_le_three_mul_polynomialDegree (k : ℕ) :
    lowDegreeJuntaCutoff k ≤ 3 * lowDegreeJuntaPolynomialDegree k := by
  unfold lowDegreeJuntaPolynomialDegree lowDegreeJuntaCutoff
  omega

/-- Divide a positive learning parameter by a positive natural denominator. -/
def dividePositiveLearningParameter (failure : PositiveLearningParameter)
    (denominator : ℕ) (hdenominator : 0 < denominator) : PositiveLearningParameter := by
  have hdenominatorRat : (0 : ℚ) < denominator := by exact_mod_cast hdenominator
  refine ⟨failure.1 / denominator, div_pos failure.2.1 hdenominatorRat, ?_⟩
  calc
    failure.1 / denominator ≤ failure.1 := by
      exact div_le_self failure.2.1.le (by exact_mod_cast hdenominator)
    _ ≤ 1 / 2 := failure.2.2

/-- One half of the node failure budget. -/
def lowDegreeJuntaHalfFailure (failure : PositiveLearningParameter) :
    PositiveLearningParameter :=
  dividePositiveLearningParameter failure 2 (by omega)

/-- One quarter of the node failure budget. -/
def lowDegreeJuntaQuarterFailure (failure : PositiveLearningParameter) :
    PositiveLearningParameter :=
  dividePositiveLearningParameter failure 4 (by omega)

@[simp] theorem lowDegreeJuntaHalfFailure_value
    (failure : PositiveLearningParameter) :
    (lowDegreeJuntaHalfFailure failure).1 = failure.1 / 2 := rfl

@[simp] theorem lowDegreeJuntaQuarterFailure_value
    (failure : PositiveLearningParameter) :
    (lowDegreeJuntaQuarterFailure failure).1 = failure.1 / 4 := rfl

/-- Accuracy `(1/3)2⁻ᵏ` used to distinguish zero from nonzero junta coefficients. -/
def lowDegreeJuntaCoefficientAccuracy (k : ℕ) : PositiveLearningParameter := by
  refine ⟨1 / (3 * (2 : ℚ) ^ k), by positivity, ?_⟩
  have hpow : (1 : ℚ) ≤ (2 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < 3 * 2 ^ k)]
  nlinarith

/-- Midpoint threshold between the zero coefficient and the `2⁻ᵏ` junta Fourier gap. -/
def lowDegreeJuntaDetectionThreshold (k : ℕ) : ℚ :=
  1 / (2 * (2 : ℚ) ^ k)

theorem lowDegreeJuntaAccuracy_lt_detectionThreshold (k : ℕ) :
    (lowDegreeJuntaCoefficientAccuracy k).1 <
      lowDegreeJuntaDetectionThreshold k := by
  unfold lowDegreeJuntaCoefficientAccuracy lowDegreeJuntaDetectionThreshold
  rw [div_lt_div_iff₀ (by positivity : (0 : ℚ) < 3 * 2 ^ k)
    (by positivity : (0 : ℚ) < 2 * 2 ^ k)]
  have hpow : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  nlinarith

/-! ## Standard-cube representation of a partial restriction -/

/-- Number of coordinates left free by a partial junta assignment. -/
def juntaRestrictionDimension (P : Finset (Fin n)) : ℕ :=
  Fintype.card (JuntaFreeIndex P)

/-- Reindex a partial restriction by a standard Boolean cube. -/
noncomputable def reindexedJuntaRestriction (target : BooleanFunction n)
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P) :
    BooleanFunction (juntaRestrictionDimension P) :=
  fun y ↦ juntaRestriction target P z (fixedSignCubeEquiv P y)

@[simp] theorem reindexedJuntaRestriction_apply
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P)
    (y : {−1,1}^[juntaRestrictionDimension P]) :
    reindexedJuntaRestriction target P z y =
      juntaRestriction target P z (fixedSignCubeEquiv P y) :=
  rfl

/-- Reindex one labeled restriction example by the standard free cube. -/
noncomputable def reindexedJuntaRestrictionExample
    (P : Finset (Fin n))
    (sample : JuntaFreeAssignment P × Sign) :
    {−1,1}^[juntaRestrictionDimension P] × Sign :=
  ((fixedSignCubeEquiv P).symm sample.1, sample.2)

/-! ## Constructor-derived node schedule -/

/-- All standard-cube frequencies of size at most the balanced cutoff. -/
noncomputable def lowDegreeJuntaFourierFamily
    (P : Finset (Fin n)) (k : ℕ) :
    Finset (Finset (Fin (juntaRestrictionDimension P))) :=
  lowDegreeFourierFamily (juntaRestrictionDimension P) (lowDegreeJuntaCutoff k)

theorem lowDegreeJuntaFourierFamily_nonempty
    (P : Finset (Fin n)) (k : ℕ) :
    (lowDegreeJuntaFourierFamily P k).Nonempty :=
  lowDegreeFourierFamily_nonempty _ _

@[simp] theorem mem_lowDegreeJuntaFourierFamily
    (P : Finset (Fin n)) (k : ℕ)
    (S : Finset (Fin (juntaRestrictionDimension P))) :
    S ∈ lowDegreeJuntaFourierFamily P k ↔ S.card ≤ lowDegreeJuntaCutoff k := by
  exact mem_lowDegreeFourierFamily S (lowDegreeJuntaCutoff k)

/-- The per-coefficient confidence obtained by a union bound over the Fourier family. -/
noncomputable def lowDegreeJuntaCoefficientConfidence
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) :
    PositiveLearningParameter := by
  let family := lowDegreeJuntaFourierFamily P k
  have hfamily : family.Nonempty := lowDegreeJuntaFourierFamily_nonempty P k
  have hcard : 0 < family.card := Finset.card_pos.mpr hfamily
  exact dividePositiveLearningParameter (lowDegreeJuntaQuarterFailure failure)
    family.card hcard

@[simp] theorem lowDegreeJuntaCoefficientConfidence_value
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) :
    (lowDegreeJuntaCoefficientConfidence P k failure).1 =
      failure.1 / 4 / (lowDegreeJuntaFourierFamily P k).card := by
  rfl

/-- Proposition 3.30 samples used for each scanned coefficient. -/
noncomputable def lowDegreeJuntaCoefficientSampleCount
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  fourierEstimatorSampleCount (lowDegreeJuntaCoefficientAccuracy k)
    (lowDegreeJuntaCoefficientConfidence P k failure)

/-- Exercise 6.30 samples reserved for the low-degree fallback. -/
def lowDegreeJuntaPolynomialSampleCount
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  lowDegreeF₂LearningSampleCount (juntaRestrictionDimension P)
    (lowDegreeJuntaPolynomialDegree k) (lowDegreeJuntaQuarterFailure failure)

/-- Number of independent restricted examples consumed by one node controller. -/
noncomputable def lowDegreeJuntaRestrictedSampleCount
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  (lowDegreeJuntaFourierFamily P k).card *
      lowDegreeJuntaCoefficientSampleCount P k failure +
    lowDegreeJuntaPolynomialSampleCount P k failure

/-- Rank of a frequency in the canonical sorted enumeration of the finite family. -/
noncomputable def lowDegreeJuntaFrequencyRank
    (P : Finset (Fin n)) (k : ℕ)
    (S : lowDegreeJuntaFourierFamily P k) :
    Fin (lowDegreeJuntaFourierFamily P k).card :=
  (lowDegreeJuntaFourierFamily P k).equivFin S

/-- Flat accepted-batch position of one Fourier-estimation sample. -/
noncomputable def lowDegreeJuntaCoefficientSampleIndex
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (S : lowDegreeJuntaFourierFamily P k)
    (i : Fin (lowDegreeJuntaCoefficientSampleCount P k failure)) :
    Fin (lowDegreeJuntaRestrictedSampleCount P k failure) := by
  let m := lowDegreeJuntaCoefficientSampleCount P k failure
  let rank := lowDegreeJuntaFrequencyRank P k S
  refine ⟨rank.1 * m + i.1, ?_⟩
  unfold lowDegreeJuntaRestrictedSampleCount
  have hrank : rank.1 < (lowDegreeJuntaFourierFamily P k).card := rank.2
  have hi : i.1 < m := i.2
  change rank.1 * m + i.1 <
    (lowDegreeJuntaFourierFamily P k).card * m +
      lowDegreeJuntaPolynomialSampleCount P k failure
  calc
    rank.1 * m + i.1 < rank.1 * m + m := Nat.add_lt_add_left hi _
    _ = (rank.1 + 1) * m := by simp [Nat.add_mul]
    _ ≤ (lowDegreeJuntaFourierFamily P k).card * m :=
      Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hrank)
    _ ≤ (lowDegreeJuntaFourierFamily P k).card * m +
        lowDegreeJuntaPolynomialSampleCount P k failure := Nat.le_add_right _ _

/-- Flat accepted-batch position of one low-degree polynomial-learning sample. -/
noncomputable def lowDegreeJuntaPolynomialSampleIndex
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (i : Fin (lowDegreeJuntaPolynomialSampleCount P k failure)) :
    Fin (lowDegreeJuntaRestrictedSampleCount P k failure) := by
  refine ⟨(lowDegreeJuntaFourierFamily P k).card *
      lowDegreeJuntaCoefficientSampleCount P k failure + i.1, ?_⟩
  unfold lowDegreeJuntaRestrictedSampleCount
  exact Nat.add_lt_add_left i.2 _

/-- The Fourier row occupies an injective block of the flat restricted batch. -/
noncomputable def lowDegreeJuntaCoefficientSampleEmbedding
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (S : lowDegreeJuntaFourierFamily P k) :
    Fin (lowDegreeJuntaCoefficientSampleCount P k failure) ↪
      Fin (lowDegreeJuntaRestrictedSampleCount P k failure) where
  toFun := lowDegreeJuntaCoefficientSampleIndex P k failure S
  inj' := by
    intro i j hij
    apply Fin.ext
    have hvalue := congrArg Fin.val hij
    simp only [lowDegreeJuntaCoefficientSampleIndex] at hvalue
    exact Nat.add_left_cancel hvalue

/-- The Exercise 6.30 suffix occupies an injective block of the flat restricted batch. -/
noncomputable def lowDegreeJuntaPolynomialSampleEmbedding
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) :
    Fin (lowDegreeJuntaPolynomialSampleCount P k failure) ↪
      Fin (lowDegreeJuntaRestrictedSampleCount P k failure) where
  toFun := lowDegreeJuntaPolynomialSampleIndex P k failure
  inj' := by
    intro i j hij
    apply Fin.ext
    have hvalue := congrArg Fin.val hij
    simp only [lowDegreeJuntaPolynomialSampleIndex] at hvalue
    omega

/-- Pointwise reindexing of a free-input batch by the standard Boolean cube. -/
noncomputable def juntaFreeInputBatchEquiv
    (P : Finset (Fin n)) (M : ℕ) :
    (Fin M → JuntaFreeAssignment P) ≃
      (Fin M → {−1,1}^[juntaRestrictionDimension P]) :=
  Equiv.piCongrRight fun _ ↦ (fixedSignCubeEquiv P).symm

/-- The standard-cube input row assigned to one scanned Fourier coefficient. -/
noncomputable def lowDegreeJuntaCoefficientInputRow
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (S : lowDegreeJuntaFourierFamily P k)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P) :
    Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
      {−1,1}^[juntaRestrictionDimension P] :=
  fun i ↦ (fixedSignCubeEquiv P).symm
    (inputs (lowDegreeJuntaCoefficientSampleEmbedding P k failure S i))

/-- The standard-cube input suffix assigned to the Exercise 6.30 learner. -/
noncomputable def lowDegreeJuntaPolynomialInputRow
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P) :
    Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
      {−1,1}^[juntaRestrictionDimension P] :=
  fun i ↦ (fixedSignCubeEquiv P).symm
    (inputs (lowDegreeJuntaPolynomialSampleEmbedding P k failure i))

/-- Every Fourier row selected from a uniform flat free-input batch is itself uniform. -/
theorem map_uniformPMF_lowDegreeJuntaCoefficientInputRow
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter)
    (S : lowDegreeJuntaFourierFamily P k) :
    (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)).map
        (lowDegreeJuntaCoefficientInputRow P k failure S) =
      uniformPMF (Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P]) := by
  let standardize := juntaFreeInputBatchEquiv P
    (lowDegreeJuntaRestrictedSampleCount P k failure)
  let project := fun inputs :
      Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P] ↦
      fun i ↦ inputs (lowDegreeJuntaCoefficientSampleEmbedding P k failure S i)
  calc
    (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
          (lowDegreeJuntaCoefficientInputRow P k failure S) =
        ((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          JuntaFreeAssignment P)).map standardize).map project := by
      rw [PMF.map_comp]
      congr 1
    _ = (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          {−1,1}^[juntaRestrictionDimension P])).map project := by
      rw [map_uniformPMF_equiv standardize]
    _ = uniformPMF (Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
          {−1,1}^[juntaRestrictionDimension P]) := by
      exact map_uniformPMF_injection_projection
        (lowDegreeJuntaCoefficientSampleEmbedding P k failure S)

/-- The Exercise 6.30 suffix selected from a uniform flat free-input batch is itself uniform. -/
theorem map_uniformPMF_lowDegreeJuntaPolynomialInputRow
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) :
    (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)).map
        (lowDegreeJuntaPolynomialInputRow P k failure) =
      uniformPMF (Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P]) := by
  let standardize := juntaFreeInputBatchEquiv P
    (lowDegreeJuntaRestrictedSampleCount P k failure)
  let project := fun inputs :
      Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P] ↦
      fun i ↦ inputs (lowDegreeJuntaPolynomialSampleEmbedding P k failure i)
  calc
    (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
          (lowDegreeJuntaPolynomialInputRow P k failure) =
        ((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          JuntaFreeAssignment P)).map standardize).map project := by
      rw [PMF.map_comp]
      congr 1
    _ = (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          {−1,1}^[juntaRestrictionDimension P])).map project := by
      rw [map_uniformPMF_equiv standardize]
    _ = uniformPMF (Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
          {−1,1}^[juntaRestrictionDimension P]) := by
      exact map_uniformPMF_injection_projection
        (lowDegreeJuntaPolynomialSampleEmbedding P k failure)

/-- The row of accepted samples assigned to one Fourier coefficient. -/
noncomputable def lowDegreeJuntaCoefficientSamples
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (S : lowDegreeJuntaFourierFamily P k) :
    Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
      ({−1,1}^[juntaRestrictionDimension P] × Sign) :=
  fun i ↦ reindexedJuntaRestrictionExample P
    (batch (lowDegreeJuntaCoefficientSampleIndex P k failure S i))

/-- The accepted samples assigned to the Exercise 6.30 fallback. -/
noncomputable def lowDegreeJuntaPolynomialSamples
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
      ({−1,1}^[juntaRestrictionDimension P] × Sign) :=
  fun i ↦ reindexedJuntaRestrictionExample P
    (batch (lowDegreeJuntaPolynomialSampleIndex P k failure i))

/-- Rational empirical estimate for one scanned coefficient. -/
noncomputable def lowDegreeJuntaCoefficientEstimate
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (S : lowDegreeJuntaFourierFamily P k) : ℚ :=
  empiricalFourierCoeff S.1
    (lowDegreeJuntaCoefficientSamples P k failure batch S)

/-- Frequencies whose estimates cross the midpoint threshold. -/
noncomputable def lowDegreeJuntaDetectedFrequencies
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
  (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    Finset (Finset (Fin (juntaRestrictionDimension P))) :=
  (lowDegreeJuntaFourierFamily P k).filter fun S ↦
    S.Nonempty ∧ ∃ hS : S ∈ lowDegreeJuntaFourierFamily P k,
      lowDegreeJuntaDetectionThreshold k ≤
        |lowDegreeJuntaCoefficientEstimate P k failure batch ⟨S, hS⟩|

/-- Canonical detected nonempty frequency, when the low-degree scan finds one. -/
noncomputable def firstLowDegreeJuntaDetectedFrequency
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    Option {S : Finset (Fin (juntaRestrictionDimension P)) // S.Nonempty} := by
  let detected := lowDegreeJuntaDetectedFrequencies P k failure batch
  if hdetected : detected.Nonempty then
    let S : detected := detected.equivFin.symm
      ⟨0, Finset.card_pos.mpr hdetected⟩
    exact some ⟨S.1, (Finset.mem_filter.mp S.2).2.1⟩
  else
    exact none

/-- Exercise 6.30's actual row-reduction output on the reserved accepted samples. -/
noncomputable def lowDegreeJuntaPolynomialHypothesis
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    LowDegreeF₂Hypothesis (juntaRestrictionDimension P)
      (lowDegreeJuntaPolynomialDegree k) :=
  lowDegreeF₂PolynomialLearnerLabeledOutput
    (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
    (lowDegreeJuntaPolynomialSampleCount P k failure)
    (lowDegreeJuntaPolynomialSamples P k failure batch)

theorem lowDegreeJuntaCoefficientSamples_ideal
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)
    (S : lowDegreeJuntaFourierFamily P k) :
    lowDegreeJuntaCoefficientSamples P k failure
        (juntaRestrictionLabeledBatch target P z inputs) S =
      fun i ↦
        let x := lowDegreeJuntaCoefficientInputRow P k failure S inputs i
        (x, reindexedJuntaRestriction target P z x) := by
  funext i
  simp [lowDegreeJuntaCoefficientSamples,
    lowDegreeJuntaCoefficientInputRow, lowDegreeJuntaCoefficientSampleEmbedding,
    juntaRestrictionLabeledBatch, reindexedJuntaRestrictionExample,
    reindexedJuntaRestriction]

theorem lowDegreeJuntaPolynomialSamples_ideal
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P) :
    lowDegreeJuntaPolynomialSamples P k failure
        (juntaRestrictionLabeledBatch target P z inputs) =
      fun i ↦
        let x := lowDegreeJuntaPolynomialInputRow P k failure inputs i
        (x, reindexedJuntaRestriction target P z x) := by
  funext i
  simp [lowDegreeJuntaPolynomialSamples, lowDegreeJuntaPolynomialInputRow,
    lowDegreeJuntaPolynomialSampleEmbedding, juntaRestrictionLabeledBatch,
    reindexedJuntaRestrictionExample, reindexedJuntaRestriction]

theorem lowDegreeJuntaCoefficientEstimate_cast_ideal
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)
    (S : lowDegreeJuntaFourierFamily P k) :
    (lowDegreeJuntaCoefficientEstimate P k failure
      (juntaRestrictionLabeledBatch target P z inputs) S : ℝ) =
      realEmpiricalFourierCoeff (reindexedJuntaRestriction target P z) S.1
        (lowDegreeJuntaCoefficientInputRow P k failure S inputs) := by
  rw [lowDegreeJuntaCoefficientEstimate,
    lowDegreeJuntaCoefficientSamples_ideal target P z k failure inputs S,
    empiricalFourierCoeff_cast]

theorem lowDegreeJuntaPolynomialHypothesis_ideal
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (inputs : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P) :
    lowDegreeJuntaPolynomialHypothesis P k failure
        (juntaRestrictionLabeledBatch target P z inputs) =
      lowDegreeF₂PolynomialLearnerLabeledOutput
        (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
        (lowDegreeJuntaPolynomialSampleCount P k failure)
        (fun i ↦
          let x := lowDegreeJuntaPolynomialInputRow P k failure inputs i
          (x, reindexedJuntaRestriction target P z x)) := by
  rw [lowDegreeJuntaPolynomialHypothesis,
    lowDegreeJuntaPolynomialSamples_ideal target P z k failure inputs]

/-! ## Coefficient-level semantic classifier for an exact low-degree hypothesis -/

/-- Convert a binary-cube hypothesis back to the sign-valued Boolean-function convention. -/
def f₂HypothesisBooleanFunction {r : ℕ} (hypothesis : F₂BooleanFunction r) :
    BooleanFunction r :=
  fun x ↦ binarySignEquiv (hypothesis ((binaryCubeSignEquiv r).symm x))

@[simp] theorem f₂HypothesisBooleanFunction_encoding
    {r : ℕ} (g : BooleanFunction r) :
    f₂HypothesisBooleanFunction (booleanFunctionF₂Encoding g) = g := by
  funext x
  simp [f₂HypothesisBooleanFunction, booleanFunctionF₂Encoding]

/-- Nonconstant monomials with nonzero learned coefficients. -/
noncomputable def nonconstantLowDegreeMonomials {r ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients r ℓ) :
    Finset (LowDegreeMonomial r ℓ) :=
  Finset.univ.filter fun S ↦ S.1.Nonempty ∧ coefficient S ≠ 0

/-- Canonical nonconstant learned monomial, when one exists. -/
noncomputable def firstNonconstantLowDegreeMonomial {r ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients r ℓ) :
    Option {S : LowDegreeMonomial r ℓ // S.1.Nonempty ∧ coefficient S ≠ 0} := by
  let support := nonconstantLowDegreeMonomials coefficient
  if hsupport : support.Nonempty then
    let S : support := support.equivFin.symm
      ⟨0, Finset.card_pos.mpr hsupport⟩
    exact some ⟨S.1, (Finset.mem_filter.mp S.2).2⟩
  else
    exact none

/-- A function invariant under one binary coordinate has zero ANF coefficients containing that
coordinate. -/
theorem anfCoeff_eq_zero_of_update_eq
    {r : ℕ} (f : F₂BooleanFunction r) (S : Finset (Fin r)) (i : Fin r)
    (hiS : i ∈ S)
    (hinvariant : ∀ x : F₂Cube r,
      f (Function.update x i 1) = f (Function.update x i 0)) :
    anfCoeff f S = 0 := by
  classical
  let R := S.erase i
  have hiR : i ∉ R := Finset.notMem_erase i S
  have hS : S = insert i R := by
    exact (Finset.insert_erase hiS).symm
  have hdisjoint : Disjoint R.powerset (R.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]
    intro T hTR hTimage
    have hiT : i ∉ T :=
      Finset.notMem_of_mem_powerset_of_notMem hTR hiR
    obtain ⟨U, hUR, hUT⟩ := Finset.mem_image.mp hTimage
    subst T
    exact hiT (Finset.mem_insert_self i U)
  have hinjective : Set.InjOn (insert i) (R.powerset : Set (Finset (Fin r))) := by
    intro A hAR B hBR hAB
    have hiA : i ∉ A :=
      Finset.notMem_of_mem_powerset_of_notMem hAR hiR
    have hiB : i ∉ B :=
      Finset.notMem_of_mem_powerset_of_notMem hBR hiR
    have herase := congrArg (fun T : Finset (Fin r) ↦ T.erase i) hAB
    simpa [hiA, hiB] using herase
  have hpoint (T : Finset (Fin r)) (hTR : T ∈ R.powerset) :
      f (f₂CubeOfFinset (insert i T)) = f (f₂CubeOfFinset T) := by
    have hiT : i ∉ T :=
      Finset.notMem_of_mem_powerset_of_notMem hTR hiR
    have hone : Function.update (f₂CubeOfFinset T) i 1 =
        f₂CubeOfFinset (insert i T) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [f₂CubeOfFinset_apply]
      · simp [f₂CubeOfFinset_apply, hji]
    have hzero : Function.update (f₂CubeOfFinset T) i 0 =
        f₂CubeOfFinset T := by
      apply Function.update_eq_self_iff.mpr
      simp [f₂CubeOfFinset_apply, hiT]
    simpa [hone, hzero] using hinvariant (f₂CubeOfFinset T)
  rw [anfCoeff, hS, Finset.powerset_insert, Finset.sum_union hdisjoint]
  rw [Finset.sum_image hinjective]
  have heq : (∑ T ∈ R.powerset, f (f₂CubeOfFinset (insert i T))) =
      ∑ T ∈ R.powerset, f (f₂CubeOfFinset T) := by
    apply Finset.sum_congr rfl
    intro T hTR
    exact hpoint T hTR
  rw [heq, CharTwo.add_self_eq_zero]

/-- Every coordinate occurring in a nonzero ANF monomial is relevant to the associated sign
function. -/
theorem isRelevant_f₂HypothesisBooleanFunction_of_anfCoeff_ne_zero
    {r : ℕ} (f : F₂BooleanFunction r) (S : Finset (Fin r)) (i : Fin r)
    (hiS : i ∈ S) (hcoeff : anfCoeff f S ≠ 0) :
    IsRelevant (f₂HypothesisBooleanFunction f).toReal i := by
  rw [isRelevant_iff_exists_setCoordinate_ne]
  by_contra hnot
  push Not at hnot
  have hinvariant : ∀ x : F₂Cube r,
      f (Function.update x i 1) = f (Function.update x i 0) := by
    intro x
    let y := binaryCubeSignEquiv r x
    have hsign := hnot y
    have hone : (binaryCubeSignEquiv r).symm (setCoordinate y i (-1)) =
        Function.update x i 1 := by
      apply (binaryCubeSignEquiv r).injective
      rw [(binaryCubeSignEquiv r).apply_symm_apply (setCoordinate y i (-1))]
      funext j
      by_cases hji : j = i
      · subst j
        simp only [setCoordinate_apply_self,
          binaryCubeSignEquiv_apply, Function.update_self, signEncode_one]
      · simp only [setCoordinate_apply_of_ne y hji,
          Function.update_of_ne hji, y, binaryCubeSignEquiv_apply]
    have hzero : (binaryCubeSignEquiv r).symm (setCoordinate y i 1) =
        Function.update x i 0 := by
      apply (binaryCubeSignEquiv r).injective
      rw [(binaryCubeSignEquiv r).apply_symm_apply (setCoordinate y i 1)]
      funext j
      by_cases hji : j = i
      · subst j
        simp only [setCoordinate_apply_self,
          binaryCubeSignEquiv_apply, Function.update_self, signEncode_zero]
      · simp only [setCoordinate_apply_of_ne y hji,
          Function.update_of_ne hji, y, binaryCubeSignEquiv_apply]
    unfold BooleanFunction.toReal f₂HypothesisBooleanFunction at hsign
    rw [hzero, hone] at hsign
    exact binarySignEquiv.injective (signValue_injective hsign.symm)
  exact hcoeff (anfCoeff_eq_zero_of_update_eq f S i hiS hinvariant)

/-- With no nonconstant learned coefficient, low-degree evaluation is the constant term. -/
theorem lowDegreeF₂Eval_eq_const_of_nonconstantSupport_empty
    {r ℓ : ℕ} (coefficient : LowDegreeF₂Coefficients r ℓ)
    (hsupport : ¬(nonconstantLowDegreeMonomials coefficient).Nonempty) :
    lowDegreeF₂Eval coefficient =
      fun _ ↦ coefficient ⟨∅, by simp⟩ := by
  funext x
  classical
  unfold lowDegreeF₂Eval
  let emptyMonomial : LowDegreeMonomial r ℓ := ⟨∅, by simp⟩
  rw [Finset.sum_eq_single emptyMonomial]
  · simp [emptyMonomial]
  · intro S _ hS
    have hSnonempty : S.1.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hS
      apply Subtype.ext
      exact hempty
    have hzero : coefficient S = 0 := by
      by_contra hne
      apply hsupport
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hSnonempty, hne⟩⟩
    simp [hzero]
  · simp

/-- Coefficient inspection either certifies the constant term or returns a genuinely relevant
coordinate. -/
theorem firstNonconstantLowDegreeMonomial_sound
    {r ℓ : ℕ} (coefficient : LowDegreeF₂Coefficients r ℓ) :
    match firstNonconstantLowDegreeMonomial coefficient with
    | none => lowDegreeF₂Eval coefficient =
        fun _ ↦ coefficient ⟨∅, by simp⟩
    | some S => IsRelevant
        (f₂HypothesisBooleanFunction (lowDegreeF₂Eval coefficient)).toReal
        (S.1.1.min' S.2.1) := by
  classical
  let support := nonconstantLowDegreeMonomials coefficient
  by_cases hsupport : support.Nonempty
  · let selected : support := support.equivFin.symm
      ⟨0, Finset.card_pos.mpr hsupport⟩
    let S : {S : LowDegreeMonomial r ℓ //
        S.1.Nonempty ∧ coefficient S ≠ 0} :=
      ⟨selected.1, (Finset.mem_filter.mp selected.2).2⟩
    have hfirst : firstNonconstantLowDegreeMonomial coefficient = some S := by
      simp only [firstNonconstantLowDegreeMonomial, support,
        dif_pos hsupport, selected, S]
    rw [hfirst]
    apply isRelevant_f₂HypothesisBooleanFunction_of_anfCoeff_ne_zero
      (lowDegreeF₂Eval coefficient) S.1.1 (S.1.1.min' S.2.1)
      (S.1.1.min'_mem S.2.1)
    rw [anfCoeff_lowDegreeF₂Eval]
    simpa [extendLowDegreeF₂Coefficients, S.1.2] using S.2.2
  · have hfirst : firstNonconstantLowDegreeMonomial coefficient = none := by
      simp only [firstNonconstantLowDegreeMonomial, support,
        dif_neg hsupport]
    rw [hfirst]
    exact lowDegreeF₂Eval_eq_const_of_nonconstantSupport_empty coefficient
      (by simpa only [support] using hsupport)

/-! ## Pure node controller and charged work -/

/-- Transport a standard free coordinate back to the partial restriction's coordinate subtype. -/
noncomputable def juntaFreeCoordinateOfFin
    (P : Finset (Fin n)) (i : Fin (juntaRestrictionDimension P)) :
    JuntaFreeIndex P :=
  (Fintype.equivFin (FixedIndex P)).symm i

/-- Deterministic node decision from the Fourier scan and low-degree row-reduction output. -/
noncomputable def lowDegreeJuntaNodeDecisionFromBatch
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) : JuntaNodeDecision P :=
  match firstLowDegreeJuntaDetectedFrequency P k failure batch with
  | some S =>
      .relevant (juntaFreeCoordinateOfFin P (S.1.min' S.2))
  | none =>
      let hypothesis := lowDegreeJuntaPolynomialHypothesis P k failure batch
      match firstNonconstantLowDegreeMonomial hypothesis.coefficient with
      | none => .constant (binarySignEquiv (hypothesis.coefficient ⟨∅, by simp⟩))
      | some S =>
          .relevant (juntaFreeCoordinateOfFin P (S.1.1.min' S.2.1))

/-- Input-independent upper bound for the actual Exercise 6.30 elimination trace. -/
def lowDegreeJuntaPolynomialWorkBound
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  let r := juntaRestrictionDimension P
  let ℓ := lowDegreeJuntaPolynomialDegree k
  let m := lowDegreeJuntaPolynomialSampleCount P k failure
  let dimension := lowDegreeF₂MonomialCount r ℓ
  m * (dimension + 1) + dimension * m * (dimension + 2) +
    dimension * (dimension + 1)

/-- Local work computed from the same accepted batch that determines the node output. -/
noncomputable def lowDegreeJuntaNodeAnalysisWork
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) : ℕ :=
  (lowDegreeJuntaFourierFamily P k).card *
      lowDegreeJuntaCoefficientSampleCount P k failure *
        (lowDegreeJuntaCutoff k + 1) +
    lowDegreeF₂PolynomialLearnerWork
      (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
      (lowDegreeJuntaPolynomialSampleCount P k failure)
      (lowDegreeJuntaPolynomialSamples P k failure batch) +
    (lowDegreeJuntaFourierFamily P k).card +
    lowDegreeF₂MonomialCount (juntaRestrictionDimension P)
      (lowDegreeJuntaPolynomialDegree k)

/-- Uniform node-analysis bound, including the Fourier scan and coefficient inspection. -/
noncomputable def lowDegreeJuntaNodeAnalysisWorkBound
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  (lowDegreeJuntaFourierFamily P k).card *
      lowDegreeJuntaCoefficientSampleCount P k failure *
        (lowDegreeJuntaCutoff k + 1) +
    lowDegreeJuntaPolynomialWorkBound P k failure +
    (lowDegreeJuntaFourierFamily P k).card +
    lowDegreeF₂MonomialCount (juntaRestrictionDimension P)
      (lowDegreeJuntaPolynomialDegree k)

theorem lowDegreeJuntaNodeAnalysisWork_le
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    lowDegreeJuntaNodeAnalysisWork P k failure batch ≤
      lowDegreeJuntaNodeAnalysisWorkBound P k failure := by
  unfold lowDegreeJuntaNodeAnalysisWork lowDegreeJuntaNodeAnalysisWorkBound
  gcongr
  exact lowDegreeF₂PolynomialLearnerWork_le
    (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
    (lowDegreeJuntaPolynomialSampleCount P k failure)
    (lowDegreeJuntaPolynomialSamples P k failure batch)

/-- Deterministic continuation applied to the finite restricted batch returned by the ambient
sampler. -/
noncomputable def lowDegreeJuntaNodeContinuation
    (P : Finset (Fin n)) (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (sampled : Option
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        MatchedJuntaExample P z)) :
    LearningProgram n .randomExamples (Option (JuntaNodeDecision P)) :=
  match sampled with
  | none => .pure none
  | some ambientBatch =>
      let batch := fun i ↦ matchedJuntaRestrictionExample P z (ambientBatch i)
      .tick (lowDegreeJuntaNodeAnalysisWork P k failure batch)
        (.pure (some (lowDegreeJuntaNodeDecisionFromBatch P k failure batch)))

/-- Actual ambient random-example node program.  One finite rejection batch feeds both the
Fourier scan and the Exercise 6.30 fallback. -/
noncomputable def lowDegreeJuntaRelevantCoordinateProgram
    (k : ℕ) (P : Finset (Fin n)) (z : JuntaFixedAssignment P)
    (failure : PositiveLearningParameter) :
    LearningProgram n .randomExamples (Option (JuntaNodeDecision P)) :=
  LearningProgram.bind
    (lowDegreeJuntaNodeContinuation P z k failure)
    (juntaRestrictionSampleProgram P z k
      (lowDegreeJuntaRestrictedSampleCount P k failure)
      (lowDegreeJuntaHalfFailure failure))

/-- Random-example cost of one concrete node call at a fixed partial assignment. -/
noncomputable def lowDegreeJuntaNodeRandomExamples
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  juntaRestrictionSampleCount k
    (lowDegreeJuntaRestrictedSampleCount P k failure)
    (lowDegreeJuntaHalfFailure failure)

/-- Local-work bound of one concrete node call at a fixed partial assignment. -/
noncomputable def lowDegreeJuntaNodeWorkBound
    (P : Finset (Fin n)) (k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  let M := lowDegreeJuntaRestrictedSampleCount P k failure
  juntaRestrictionSampleCount k M (lowDegreeJuntaHalfFailure failure) +
    juntaRestrictionSampleWork P k M (lowDegreeJuntaHalfFailure failure) +
    lowDegreeJuntaNodeAnalysisWorkBound P k failure

/-- Uniform random-example bound required by `JuntaRelevantCoordinateFinder`. -/
noncomputable def lowDegreeJuntaNodeRandomExampleBound
    (n k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  (Finset.univ : Finset (Finset (Fin n))).sup fun P ↦
    lowDegreeJuntaNodeRandomExamples P k failure

/-- Uniform local-work bound required by `JuntaRelevantCoordinateFinder`. -/
noncomputable def lowDegreeJuntaNodeUniformWorkBound
    (n k : ℕ) (failure : PositiveLearningParameter) : ℕ :=
  (Finset.univ : Finset (Finset (Fin n))).sup fun P ↦
    lowDegreeJuntaNodeWorkBound P k failure

/-! ## Restriction semantics and the junta Fourier gap -/

/-- Standard free coordinates corresponding to a junta witness after fixing `P`. -/
noncomputable def reindexedJuntaWitnessCoordinates
    (P J : Finset (Fin n)) :
    Finset (Fin (juntaRestrictionDimension P)) :=
  Finset.univ.filter fun q ↦
    ((Fintype.equivFin (FixedIndex P)).symm q : FixedIndex P).1 ∈ J

theorem card_reindexedJuntaWitnessCoordinates_le
    (P J : Finset (Fin n)) :
    (reindexedJuntaWitnessCoordinates P J).card ≤ J.card := by
  classical
  let coordinate : Fin (juntaRestrictionDimension P) → Fin n := fun q ↦
    ((Fintype.equivFin (FixedIndex P)).symm q : FixedIndex P).1
  apply Finset.card_le_card_of_injOn coordinate
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq q' hq' heq
    apply (Fintype.equivFin (FixedIndex P)).symm.injective
    apply Subtype.ext
    exact heq

/-- A restriction of a function depending on `J` is a standard-cube junta on the residual
coordinates of `J`. -/
theorem reindexedJuntaRestriction_isKJunta
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n))) :
    IsKJunta (reindexedJuntaRestriction target P z) k := by
  classical
  refine ⟨reindexedJuntaWitnessCoordinates P J,
    (card_reindexedJuntaWitnessCoordinates_le P J).trans hJcard, ?_⟩
  intro x y hxy
  apply hdepends
  intro i hiJ
  by_cases hiP : i ∈ P
  · simp [combineJuntaAssignment, hiP]
  · let free : FixedIndex P := ⟨i, hiP⟩
    let q : Fin (juntaRestrictionDimension P) :=
      Fintype.equivFin (FixedIndex P) free
    have hq : q ∈ reindexedJuntaWitnessCoordinates P J := by
      simpa [reindexedJuntaWitnessCoordinates, q, free] using hiJ
    have hxyq := hxy q hq
    simpa [combineJuntaAssignment, fixedSignCubeEquiv, hiP, q, free] using hxyq

/-- Standard-cube relevance transports back to the witness formulation used by Exercise 6.31. -/
theorem isRelevantJuntaRestriction_of_reindexed
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (i : Fin (juntaRestrictionDimension P))
    (hi : IsRelevant (reindexedJuntaRestriction target P z).toReal i) :
    IsRelevantJuntaRestriction target P z (juntaFreeCoordinateOfFin P i) := by
  classical
  rw [isRelevant_iff_exists_setCoordinate_ne] at hi
  obtain ⟨x, hx⟩ := hi
  let freeCoordinate := juntaFreeCoordinateOfFin P i
  let y₀ : JuntaFreeAssignment P := fixedSignCubeEquiv P (setCoordinate x i 1)
  let y₁ : JuntaFreeAssignment P := fixedSignCubeEquiv P (setCoordinate x i (-1))
  refine ⟨y₀, y₁, ?_, ?_⟩
  · intro j hji
    have hindex : Fintype.equivFin (FixedIndex P) j ≠ i := by
      intro h
      apply hji
      apply (Fintype.equivFin (FixedIndex P)).injective
      simpa [freeCoordinate, juntaFreeCoordinateOfFin] using h
    simp [y₀, y₁, fixedSignCubeEquiv, setCoordinate,
      Function.update_of_ne hindex]
  · intro heq
    apply hx
    unfold BooleanFunction.toReal reindexedJuntaRestriction
    change signValue (juntaRestriction target P z y₀) =
      signValue (juntaRestriction target P z y₁)
    exact congrArg signValue heq

/-- Simultaneous strict accuracy of every scanned empirical coefficient. -/
def LowDegreeJuntaFourierEstimatesAccurate
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) : Prop :=
  ∀ S : lowDegreeJuntaFourierFamily P k,
    |(lowDegreeJuntaCoefficientEstimate P k failure batch S : ℝ) -
      fourierCoeff (reindexedJuntaRestriction target P z).toReal S.1| <
        ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ)

/-- Exactness of the Exercise 6.30 output reserved in one restricted batch. -/
def LowDegreeJuntaPolynomialHypothesisExact
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) : Prop :=
  (lowDegreeJuntaPolynomialHypothesis P k failure batch).evaluate =
    booleanFunctionF₂Encoding (reindexedJuntaRestriction target P z)

/-- Proposition 3.30 applied to one block selected from the flat ideal restricted batch. -/
theorem measure_lowDegreeJuntaCoefficientEstimate_bad_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (S : lowDegreeJuntaFourierFamily P k) :
    (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)).toMeasure.real
        {inputs |
          ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ) ≤
            |(lowDegreeJuntaCoefficientEstimate P k failure
                (juntaRestrictionLabeledBatch target P z inputs) S : ℝ) -
              fourierCoeff (reindexedJuntaRestriction target P z).toReal S.1|} ≤
      ((lowDegreeJuntaCoefficientConfidence P k failure).1 : ℝ) := by
  simp_rw [lowDegreeJuntaCoefficientEstimate_cast_ideal]
  let row := lowDegreeJuntaCoefficientInputRow P k failure S
  let badRow : Set
      (Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P]) :=
    {sampleInputs |
      ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ) ≤
        |realEmpiricalFourierCoeff (reindexedJuntaRestriction target P z) S.1
            sampleInputs -
          fourierCoeff (reindexedJuntaRestriction target P z).toReal S.1|}
  have hmap :
      (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map row =
        uniformPMF (Fin (lowDegreeJuntaCoefficientSampleCount P k failure) →
          {−1,1}^[juntaRestrictionDimension P]) := by
    exact map_uniformPMF_lowDegreeJuntaCoefficientInputRow P k failure S
  have hmeasure :
      ((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          JuntaFreeAssignment P)).map row).toMeasure.real badRow =
        (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
          JuntaFreeAssignment P)).toMeasure.real (row ⁻¹' badRow) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply row _ badRow (measurable_of_finite row)
        (Set.toFinite badRow).measurableSet)
  rw [hmap] at hmeasure
  change (uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)).toMeasure.real (row ⁻¹' badRow) ≤ _
  rw [← hmeasure]
  exact (measure_realEmpiricalFourierCoeff_sub_ge_le
    (reindexedJuntaRestriction target P z) S.1
    (fourierEstimatorSampleCount_pos (lowDegreeJuntaCoefficientAccuracy k)
      (lowDegreeJuntaCoefficientConfidence P k failure))
    ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ)
    (positiveLearningParameter_toReal_mem_Ioc
      (lowDegreeJuntaCoefficientAccuracy k)).1.le).trans
        (two_mul_exp_neg_fourierEstimatorSampleCount_le
          (lowDegreeJuntaCoefficientAccuracy k)
          (lowDegreeJuntaCoefficientConfidence P k failure))

/-- A union bound makes every scanned Fourier estimate simultaneously accurate under the ideal
independent restricted-example law. -/
theorem idealLowDegreeJuntaFourierInaccuracyProbability_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter) :
    (((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
      (juntaRestrictionLabeledBatch target P z)).toOuterMeasure
        {batch | ¬ LowDegreeJuntaFourierEstimatesAccurate
          target P z k failure batch}).toReal ≤
      ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
  classical
  let inputLaw := uniformPMF
    (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)
  let bad (S : lowDegreeJuntaFourierFamily P k) :
      Set (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P) :=
    {inputs |
      ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ) ≤
        |(lowDegreeJuntaCoefficientEstimate P k failure
            (juntaRestrictionLabeledBatch target P z inputs) S : ℝ) -
          fourierCoeff (reindexedJuntaRestriction target P z).toReal S.1|}
  have hsubset :
      {inputs | ¬ LowDegreeJuntaFourierEstimatesAccurate target P z k failure
        (juntaRestrictionLabeledBatch target P z inputs)} ⊆
        ⋃ S : lowDegreeJuntaFourierFamily P k, bad S := by
    intro inputs hinaccurate
    by_contra hnotBad
    apply hinaccurate
    intro S
    have hSnotBad : inputs ∉ bad S := by
      intro hSbad
      exact hnotBad (Set.mem_iUnion.mpr ⟨S, hSbad⟩)
    exact lt_of_not_ge hSnotBad
  rw [PMF.toOuterMeasure_map_apply]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure inputLaw]
  change inputLaw.toMeasure.real
      {inputs | ¬ LowDegreeJuntaFourierEstimatesAccurate target P z k failure
        (juntaRestrictionLabeledBatch target P z inputs)} ≤ _
  calc
    inputLaw.toMeasure.real
        {inputs | ¬ LowDegreeJuntaFourierEstimatesAccurate target P z k failure
          (juntaRestrictionLabeledBatch target P z inputs)} ≤
        inputLaw.toMeasure.real
          (⋃ S : lowDegreeJuntaFourierFamily P k, bad S) :=
      measureReal_mono hsubset
    _ ≤ ∑ S : lowDegreeJuntaFourierFamily P k,
        inputLaw.toMeasure.real (bad S) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : lowDegreeJuntaFourierFamily P k,
        ((lowDegreeJuntaCoefficientConfidence P k failure).1 : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_lowDegreeJuntaCoefficientEstimate_bad_le
        target P z k failure S
    _ = ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
      have hcardNat : 0 < (lowDegreeJuntaFourierFamily P k).card :=
        Finset.card_pos.mpr (lowDegreeJuntaFourierFamily_nonempty P k)
      have hcardReal :
          ((lowDegreeJuntaFourierFamily P k).card : ℝ) ≠ 0 := by
        exact_mod_cast hcardNat.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, lowDegreeJuntaCoefficientConfidence_value,
        lowDegreeJuntaQuarterFailure_value, Rat.cast_div, Rat.cast_natCast]
      field_simp [hcardReal]

/-- Exercise 6.30 exactly learns the no-detection branch under the ideal independent restricted
sample law whenever Siegenthaler's degree bound applies. -/
theorem idealLowDegreeJuntaPolynomialFailureProbability_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (hdegree : functionAlgebraicDegree
        (booleanFunctionF₂Encoding (reindexedJuntaRestriction target P z)) ≤
      lowDegreeJuntaPolynomialDegree k) :
    (((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
      (juntaRestrictionLabeledBatch target P z)).toOuterMeasure
        {batch | ¬ LowDegreeJuntaPolynomialHypothesisExact
          target P z k failure batch}).toReal ≤
      ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
  let inputLaw := uniformPMF
    (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      JuntaFreeAssignment P)
  let row := lowDegreeJuntaPolynomialInputRow P k failure
  let g := reindexedJuntaRestriction target P z
  let badRow : Set
      (Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P]) :=
    {sampleInputs |
      (lowDegreeF₂PolynomialLearnerLabeledOutput
        (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
        (lowDegreeJuntaPolynomialSampleCount P k failure)
        (fun i ↦ (sampleInputs i, g (sampleInputs i)))).evaluate ≠
          booleanFunctionF₂Encoding g}
  have hmap : inputLaw.map row =
      uniformPMF (Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P]) := by
    exact map_uniformPMF_lowDegreeJuntaPolynomialInputRow P k failure
  have hmeasure :
      (inputLaw.map row).toMeasure.real badRow =
        inputLaw.toMeasure.real (row ⁻¹' badRow) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply row _ badRow (measurable_of_finite row)
        (Set.toFinite badRow).measurableSet)
  have hbadRow :
      (uniformPMF (Fin (lowDegreeJuntaPolynomialSampleCount P k failure) →
        {−1,1}^[juntaRestrictionDimension P])).toMeasure.real badRow ≤
          ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
    apply (MeasureTheory.measureReal_mono
      (lowDegreeF₂PolynomialLearner_failure_subset_separationFailure
        (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
        (lowDegreeJuntaPolynomialSampleCount P k failure) g hdegree)).trans
    change
      (uniformPMF
        (Fin (lowDegreeF₂LearningSampleCount (juntaRestrictionDimension P)
            (lowDegreeJuntaPolynomialDegree k)
            (lowDegreeJuntaQuarterFailure failure)) →
          {−1,1}^[juntaRestrictionDimension P])).toMeasure.real
          (signSampleLowDegreeF₂SeparationFailureSet
            (n := juntaRestrictionDimension P)
            (ℓ := lowDegreeJuntaPolynomialDegree k)
            (m := lowDegreeF₂LearningSampleCount (juntaRestrictionDimension P)
              (lowDegreeJuntaPolynomialDegree k)
              (lowDegreeJuntaQuarterFailure failure))) ≤
        ((lowDegreeJuntaQuarterFailure failure).1 : ℝ)
    exact measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le
      (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
      (lowDegreeJuntaQuarterFailure failure)
  have hpreimage :
      (juntaRestrictionLabeledBatch target P z) ⁻¹'
          {batch | ¬ LowDegreeJuntaPolynomialHypothesisExact
            target P z k failure batch} =
        row ⁻¹' badRow := by
    ext inputs
    simp only [Set.mem_preimage, Set.mem_setOf_eq, badRow, row, g,
      LowDegreeJuntaPolynomialHypothesisExact,
      lowDegreeJuntaPolynomialHypothesis_ideal]
  rw [PMF.toOuterMeasure_map_apply]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure inputLaw]
  rw [hpreimage]
  change inputLaw.toMeasure.real (row ⁻¹' badRow) ≤ _
  rw [← hmeasure, hmap]
  exact hbadRow

/-- Under accurate estimates, every detected frequency has a genuinely nonzero Fourier
coefficient. -/
theorem fourierCoeff_ne_zero_of_mem_lowDegreeJuntaDetectedFrequencies
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (S : Finset (Fin (juntaRestrictionDimension P)))
    (hS : S ∈ lowDegreeJuntaDetectedFrequencies P k failure batch) :
    fourierCoeff (reindexedJuntaRestriction target P z).toReal S ≠ 0 := by
  classical
  obtain ⟨hSfamily, _hSnonempty, hSestimate⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSfamily', hthreshold⟩ := hSestimate
  let indexed : lowDegreeJuntaFourierFamily P k := ⟨S, hSfamily⟩
  have hthresholdIndexed : lowDegreeJuntaDetectionThreshold k ≤
      |lowDegreeJuntaCoefficientEstimate P k failure batch indexed| := by
    simpa only [indexed] using hthreshold
  intro hzero
  have hclose := haccurate indexed
  rw [hzero, sub_zero] at hclose
  have hstrict := lowDegreeJuntaAccuracy_lt_detectionThreshold k
  have hcast :
      ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ) <
        (lowDegreeJuntaDetectionThreshold k : ℝ) := by
    exact_mod_cast hstrict
  have hthresholdReal :
      (lowDegreeJuntaDetectionThreshold k : ℝ) ≤
        |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| := by
    exact_mod_cast hthresholdIndexed
  linarith

/-- If no frequency is detected and all estimates are accurate, every nonempty Fourier
coefficient through the cutoff vanishes. -/
theorem fourierCoeff_eq_zero_of_no_lowDegreeJuntaDetection
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (hnone : firstLowDegreeJuntaDetectedFrequency P k failure batch = none)
    (S : Finset (Fin (juntaRestrictionDimension P)))
    (hSnonempty : S.Nonempty) (hScard : S.card ≤ lowDegreeJuntaCutoff k) :
    fourierCoeff (reindexedJuntaRestriction target P z).toReal S = 0 := by
  classical
  let g := reindexedJuntaRestriction target P z
  have hjunta : IsKJunta g k :=
    reindexedJuntaRestriction_isKJunta target J P z k hJcard hdepends
  rcases fourierCoeff_eq_zero_or_inv_two_pow_le_abs_of_isKJunta g hjunta S with
    hzero | hgap
  · exact hzero
  · exfalso
    have hSfamily : S ∈ lowDegreeJuntaFourierFamily P k :=
      (mem_lowDegreeJuntaFourierFamily P k S).2 hScard
    let indexed : lowDegreeJuntaFourierFamily P k := ⟨S, hSfamily⟩
    have hclose := haccurate indexed
    have habs : |fourierCoeff g.toReal S| ≤
        |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| +
          |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ) -
            fourierCoeff g.toReal S| := by
      calc
        |fourierCoeff g.toReal S| =
            |(fourierCoeff g.toReal S -
                (lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)) +
              (lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| := by
            ring_nf
        _ ≤ |fourierCoeff g.toReal S -
              (lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| +
              |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| :=
            abs_add_le _ _
        _ = |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| +
              |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ) -
                fourierCoeff g.toReal S| := by
            rw [abs_sub_comm]
            ring
    have hthreshold :
        (lowDegreeJuntaDetectionThreshold k : ℝ) <
          |(lowDegreeJuntaCoefficientEstimate P k failure batch indexed : ℝ)| := by
      have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have haccuracy : ((lowDegreeJuntaCoefficientAccuracy k).1 : ℝ) =
          1 / (3 * (2 : ℝ) ^ k) := by
        norm_num [lowDegreeJuntaCoefficientAccuracy]
      have hdetect : (lowDegreeJuntaDetectionThreshold k : ℝ) =
          1 / (2 * (2 : ℝ) ^ k) := by
        norm_num [lowDegreeJuntaDetectionThreshold]
      have hbudget :
          1 / (2 * (2 : ℝ) ^ k) + 1 / (3 * (2 : ℝ) ^ k) <
            1 / (2 : ℝ) ^ k := by
        calc
          1 / (2 * (2 : ℝ) ^ k) + 1 / (3 * (2 : ℝ) ^ k) =
              ((1 : ℝ) / 2 + 1 / 3) / (2 : ℝ) ^ k := by
                field_simp [hpow.ne']
          _ < 1 / (2 : ℝ) ^ k :=
            (div_lt_div_iff_of_pos_right hpow).2 (by norm_num)
      rw [haccuracy] at hclose
      rw [hdetect]
      nlinarith [hgap, habs, hclose, hbudget]
    have hdetected :
        S ∈ lowDegreeJuntaDetectedFrequencies P k failure batch := by
      rw [lowDegreeJuntaDetectedFrequencies, Finset.mem_filter]
      refine ⟨hSfamily, hSnonempty, ⟨hSfamily, ?_⟩⟩
      exact_mod_cast hthreshold.le
    have hdetectedNonempty :
        (lowDegreeJuntaDetectedFrequencies P k failure batch).Nonempty :=
      ⟨S, hdetected⟩
    simp [firstLowDegreeJuntaDetectedFrequency, hdetectedNonempty] at hnone

/-- The no-detection branch is correlation immune through the balanced cutoff. -/
theorem isCorrelationImmune_of_no_lowDegreeJuntaDetection
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (hnone : firstLowDegreeJuntaDetectedFrequency P k failure batch = none) :
    IsCorrelationImmune (lowDegreeJuntaCutoff k)
      (reindexedJuntaRestriction target P z) := by
  intro S hSnonempty hScard
  rw [fourierCoeff_eq_zero_of_no_lowDegreeJuntaDetection
    target J P z k failure hJcard hdepends batch haccurate hnone
    S hSnonempty hScard]
  norm_num

/-! ## The junta-specialized Siegenthaler bridge -/

/-- Coordinate embedding of a finite dependence witness into its ambient standard cube. -/
noncomputable def juntaWitnessCoordinateEmbedding
    {r : ℕ} (J : Finset (Fin r)) : Fin J.card ↪ Fin r :=
  J.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

/-- Restrict a function to the coordinates in a dependence witness and reindex by `Fin J.card`. -/
noncomputable def juntaWitnessCore
    {r : ℕ} (g : BooleanFunction r) (J : Finset (Fin r)) :
    BooleanFunction J.card :=
  fun y ↦ signRestriction g J (fun _ ↦ 1) (fun i ↦ y (J.equivFin i))

/-- Pulling a binary function back along a coordinate embedding cannot increase algebraic
degree. -/
theorem functionAlgebraicDegree_coordinatePullback_le
    {r s : ℕ} (f : F₂BooleanFunction s) (e : Fin s ↪ Fin r) :
    functionAlgebraicDegree (fun x : F₂Cube r ↦ f (fun i ↦ x (e i))) ≤
      functionAlgebraicDegree f := by
  classical
  let term : Finset (Fin s) → F₂BooleanFunction r := fun S x ↦
    anfCoeff f S * anfMonomial (S.map e) x
  have hsum : (fun x : F₂Cube r ↦ f (fun i ↦ x (e i))) = ∑ S, term S := by
    funext x
    simp only [Fintype.sum_apply, term]
    rw [← congrFun (anfEval_anfCoeff f) (fun i ↦ x (e i))]
    unfold anfEval anfMonomial
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    rw [Finset.prod_map]
  rw [hsum]
  apply functionAlgebraicDegree_finset_sum_le Finset.univ term
    (functionAlgebraicDegree f)
  intro S _
  by_cases hS : anfCoeff f S = 0
  · have hterm : term S = 0 := by
      funext x
      simp [term, hS]
    rw [hterm, functionAlgebraicDegree_zero]
    exact Nat.zero_le _
  · have hSone : anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
    have hterm : term S = anfMonomial (S.map e) := by
      funext x
      simp [term, hSone]
    rw [hterm, functionAlgebraicDegree_anfMonomial, Finset.card_map]
    exact (algebraicDegree_le_iff (anfCoeff f) _).mp le_rfl S hS

/-- A function depending on `J` is the coordinate pullback of its compact witness core. -/
theorem booleanFunctionF₂Encoding_eq_juntaWitnessCore_pullback
    {r : ℕ} (g : BooleanFunction r) (J : Finset (Fin r))
    (hdepends : DependsOn g (J : Set (Fin r))) :
    booleanFunctionF₂Encoding g = fun x : F₂Cube r ↦
      booleanFunctionF₂Encoding (juntaWitnessCore g J)
        (fun q ↦ x (juntaWitnessCoordinateEmbedding J q)) := by
  funext x
  apply binarySignEquiv.injective
  simp only [booleanFunctionF₂Encoding, binarySignEquiv.apply_symm_apply]
  apply hdepends
  intro i hiJ
  let j : J := ⟨i, hiJ⟩
  change (binaryCubeSignEquiv r x) i =
    combineSignCube J
      (fun p ↦ binaryCubeSignEquiv J.card
        (fun q ↦ x (juntaWitnessCoordinateEmbedding J q)) (J.equivFin p))
      (fun _ ↦ 1) i
  rw [combineSignCube_apply_free J _ _ j]
  simp [juntaWitnessCoordinateEmbedding, j,
    binaryCubeSignEquiv_apply]

/-- Compacting to a dependence witness does not decrease the degree needed for the ambient
function. -/
theorem functionAlgebraicDegree_encoding_le_juntaWitnessCore
    {r : ℕ} (g : BooleanFunction r) (J : Finset (Fin r))
    (hdepends : DependsOn g (J : Set (Fin r))) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding g) ≤
      functionAlgebraicDegree (booleanFunctionF₂Encoding (juntaWitnessCore g J)) := by
  rw [booleanFunctionF₂Encoding_eq_juntaWitnessCore_pullback g J hdepends]
  exact functionAlgebraicDegree_coordinatePullback_le
    (booleanFunctionF₂Encoding (juntaWitnessCore g J))
    (juntaWitnessCoordinateEmbedding J)

/-- Fourier coefficients of the compact witness core are the corresponding ambient
coefficients. -/
theorem fourierCoeff_juntaWitnessCore
    {r : ℕ} (g : BooleanFunction r) (J : Finset (Fin r))
    (hdepends : DependsOn g (J : Set (Fin r)))
    (T : Finset (Fin J.card)) :
    fourierCoeff (juntaWitnessCore g J).toReal T =
      fourierCoeff g.toReal
        (T.map (juntaWitnessCoordinateEmbedding J)) := by
  classical
  let A : Finset J := T.map J.equivFin.symm.toEmbedding
  let z₀ : FixedSignCube J := fun _ ↦ 1
  have hTlift : liftFreeFrequency A =
      T.map (juntaWitnessCoordinateEmbedding J) := by
    simp only [A, liftFreeFrequency, Finset.map_map,
      juntaWitnessCoordinateEmbedding]
  have hreindex :
      fourierCoeff (juntaWitnessCore g J).toReal T =
        indexedFourierCoeff (signRestriction g.toReal J z₀) A := by
    let reindex : {−1,1}^[J.card] ≃ FreeSignCube J :=
      Equiv.arrowCongr J.equivFin.symm (Equiv.refl Sign)
    unfold fourierCoeff indexedFourierCoeff
    apply Fintype.expect_equiv reindex
    intro y
    congr 1
    dsimp only [A]
    rw [monomial, indexedMonomial, Finset.prod_map]
    simp [reindex, Equiv.arrowCongr, Function.comp_def]
  have hrestriction (z : FixedSignCube J) :
      signRestriction g.toReal J z = signRestriction g.toReal J z₀ := by
    funext y
    change signValue (g (combineSignCube J y z)) =
      signValue (g (combineSignCube J y z₀))
    congr 1
    apply hdepends
    intro i hiJ
    exact (combineSignCube_apply_free J y z ⟨i, hiJ⟩).trans
      (combineSignCube_apply_free J y z₀ ⟨i, hiJ⟩).symm
  calc
    fourierCoeff (juntaWitnessCore g J).toReal T =
        restrictionFourierCoeff g.toReal J A z₀ := hreindex
    _ = 𝔼 z : FixedSignCube J,
        restrictionFourierCoeff g.toReal J A z := by
      calc
        restrictionFourierCoeff g.toReal J A z₀ =
            𝔼 _z : FixedSignCube J,
              restrictionFourierCoeff g.toReal J A z₀ :=
          (Fintype.expect_const _).symm
        _ = 𝔼 z : FixedSignCube J,
              restrictionFourierCoeff g.toReal J A z := by
          apply Finset.expect_congr rfl
          intro z _
          change indexedFourierCoeff (signRestriction g.toReal J z₀) A =
            indexedFourierCoeff (signRestriction g.toReal J z) A
          rw [hrestriction z]
    _ = fourierCoeff g.toReal (liftFreeFrequency A) :=
      expect_restrictionFourierCoeff g.toReal J A
    _ = fourierCoeff g.toReal
        (T.map (juntaWitnessCoordinateEmbedding J)) := by rw [hTlift]

/-- Correlation immunity passes to the compact dependence-witness core. -/
theorem juntaWitnessCore_isCorrelationImmune
    {r : ℕ} (g : BooleanFunction r) (J : Finset (Fin r)) (d : ℕ)
    (hdepends : DependsOn g (J : Set (Fin r)))
    (himmune : IsCorrelationImmune d g) :
    IsCorrelationImmune d (juntaWitnessCore g J) := by
  intro T hTnonempty hTcard
  rw [fourierCoeff_juntaWitnessCore g J hdepends T]
  apply himmune
  · obtain ⟨i, hi⟩ := hTnonempty
    exact ⟨juntaWitnessCoordinateEmbedding J i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
  · simpa using hTcard

/-- The binary encoding of a constant sign function has algebraic degree zero. -/
theorem functionAlgebraicDegree_encoding_eq_zero_of_eq_const
    {r : ℕ} (g : BooleanFunction r) (value : Sign)
    (hg : g = fun _ ↦ value) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding g) = 0 := by
  subst g
  have hencoding : booleanFunctionF₂Encoding (fun _ : {−1,1}^[r] ↦ value) =
      fun _ ↦ binarySignEquiv.symm value := by
    funext x
    rfl
  rw [hencoding]
  by_cases hvalue : binarySignEquiv.symm value = 0
  · have hzero : (fun _ : F₂Cube r ↦ binarySignEquiv.symm value) = 0 := by
      funext x
      simp [hvalue]
    rw [hzero, functionAlgebraicDegree_zero]
  · have hone : binarySignEquiv.symm value = 1 :=
      Fin.eq_one_of_ne_zero _ hvalue
    have hconstOne : (fun _ : F₂Cube r ↦ binarySignEquiv.symm value) = 1 := by
      funext x
      simp [hone]
    rw [hconstOne, functionAlgebraicDegree_one]

/-- A correlation-immune `k`-junta has binary algebraic degree at most `k-d`.  This is the
compact-representation specialization of Siegenthaler's theorem used in Theorem 6.36. -/
theorem functionAlgebraicDegree_encoding_le_sub_of_isKJunta_of_isCorrelationImmune
    {r : ℕ} (g : BooleanFunction r) (k d : ℕ)
    (hjunta : IsKJunta g k) (himmune : IsCorrelationImmune d g) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding g) ≤ k - d := by
  classical
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  let core := juntaWitnessCore g J
  have hcoreImmune : IsCorrelationImmune d core :=
    juntaWitnessCore_isCorrelationImmune g J d hdepends himmune
  have hdegreeToCore :=
    functionAlgebraicDegree_encoding_le_juntaWitnessCore g J hdepends
  by_cases hdJ : d < J.card
  · have hcoreDegree :
        functionAlgebraicDegree (booleanFunctionF₂Encoding core) ≤ J.card - d :=
      functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isCorrelationImmune
        core d hcoreImmune hdJ
    exact hdegreeToCore.trans
      (hcoreDegree.trans (Nat.sub_le_sub_right hJcard d))
  · have hregular : IsFourierRegular 0 core.toReal := by
      rw [← isLowDegreeFourierRegular_dimension_iff]
      intro S hSnonempty hScard
      exact hcoreImmune S hSnonempty (hScard.trans (Nat.le_of_not_gt hdJ))
    obtain ⟨c, hc⟩ := (isFourierRegular_zero_iff_exists_const core.toReal).mp hregular
    let value := core (fun _ ↦ 1)
    have hcoreConst : core = fun _ ↦ value := by
      funext x
      apply signValue_injective
      change core.toReal x = core.toReal (fun _ ↦ 1)
      rw [hc]
    have hzero :=
      functionAlgebraicDegree_encoding_eq_zero_of_eq_const core value hcoreConst
    rw [hzero] at hdegreeToCore
    exact hdegreeToCore.trans (Nat.zero_le _)

/-- The no-detection branch satisfies the Exercise 6.30 degree budget. -/
theorem functionAlgebraicDegree_reindexedJuntaRestriction_le_of_no_detection
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (hnone : firstLowDegreeJuntaDetectedFrequency P k failure batch = none) :
    functionAlgebraicDegree
        (booleanFunctionF₂Encoding (reindexedJuntaRestriction target P z)) ≤
      lowDegreeJuntaPolynomialDegree k := by
  apply functionAlgebraicDegree_encoding_le_sub_of_isKJunta_of_isCorrelationImmune
  · exact reindexedJuntaRestriction_isKJunta target J P z k hJcard hdepends
  · exact isCorrelationImmune_of_no_lowDegreeJuntaDetection
      target J P z k failure hJcard hdepends batch haccurate hnone

/-! ## Correctness of the pure node controller -/

theorem mem_detectedFrequencies_of_firstDetected_eq_some
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (S : {S : Finset (Fin (juntaRestrictionDimension P)) // S.Nonempty})
    (hS : firstLowDegreeJuntaDetectedFrequency P k failure batch = some S) :
    S.1 ∈ lowDegreeJuntaDetectedFrequencies P k failure batch := by
  classical
  have hdetected :
      (lowDegreeJuntaDetectedFrequencies P k failure batch).Nonempty := by
    by_contra hempty
    have hnone : firstLowDegreeJuntaDetectedFrequency P k failure batch = none := by
      simp [firstLowDegreeJuntaDetectedFrequency, hempty]
    rw [hnone] at hS
    contradiction
  let selected : lowDegreeJuntaDetectedFrequencies P k failure batch :=
    (lowDegreeJuntaDetectedFrequencies P k failure batch).equivFin.symm
    ⟨0, Finset.card_pos.mpr hdetected⟩
  have hvalue : selected.1 = S.1 := by
    have hmapped := congrArg
      (fun result ↦ result.map (fun T ↦ T.1)) hS
    simpa only [firstLowDegreeJuntaDetectedFrequency, dif_pos hdetected,
      Option.map_some, Option.some.injEq, selected] using hmapped
  rw [← hvalue]
  exact selected.2

/-- Reindexing a constant standard-cube restriction yields a constant subtype-indexed
restriction. -/
theorem juntaRestriction_eq_const_of_reindexed_eq_const
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (value : Sign)
    (hconstant : reindexedJuntaRestriction target P z = fun _ ↦ value) :
    juntaRestriction target P z = fun _ ↦ value := by
  funext y
  have h := congrFun hconstant ((fixedSignCubeEquiv P).symm y)
  simpa [reindexedJuntaRestriction] using h

/-- An accurately detected nonempty Fourier frequency yields a genuinely relevant coordinate. -/
theorem lowDegreeJuntaNodeDecisionFromBatch_isCorrect_of_firstDetected_eq_some
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (S : {S : Finset (Fin (juntaRestrictionDimension P)) // S.Nonempty})
    (hS : firstLowDegreeJuntaDetectedFrequency P k failure batch = some S) :
    (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect
      target P z := by
  let g := reindexedJuntaRestriction target P z
  have hSmem := mem_detectedFrequencies_of_firstDetected_eq_some
    P k failure batch S hS
  have hcoeff :=
    fourierCoeff_ne_zero_of_mem_lowDegreeJuntaDetectedFrequencies
      target P z k failure batch haccurate S.1 hSmem
  have hrelevant : IsRelevant g.toReal (S.1.min' S.2) :=
    isRelevant_toReal_of_fourierCoeff_ne_zero g hcoeff (S.1.min'_mem S.2)
  rw [lowDegreeJuntaNodeDecisionFromBatch, hS]
  exact isRelevantJuntaRestriction_of_reindexed target P z _ hrelevant

/-- Simultaneous coefficient accuracy and an exact Exercise 6.30 output make the pure node
decision semantically correct. -/
theorem lowDegreeJuntaNodeDecisionFromBatch_isCorrect
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (_hJcard : J.card ≤ k)
    (_hdepends : DependsOn target (J : Set (Fin n)))
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign))
    (haccurate : LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch)
    (hexact : LowDegreeJuntaPolynomialHypothesisExact
      target P z k failure batch) :
    (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect
      target P z := by
  classical
  let g := reindexedJuntaRestriction target P z
  cases hdetected : firstLowDegreeJuntaDetectedFrequency P k failure batch with
  | some S =>
      exact lowDegreeJuntaNodeDecisionFromBatch_isCorrect_of_firstDetected_eq_some
        target P z k failure batch haccurate S hdetected
  | none =>
    let hypothesis := lowDegreeJuntaPolynomialHypothesis P k failure batch
    have hlearnedSign : f₂HypothesisBooleanFunction hypothesis.evaluate = g := by
      rw [hexact]
      exact f₂HypothesisBooleanFunction_encoding g
    cases hmonomial : firstNonconstantLowDegreeMonomial hypothesis.coefficient with
    | some S =>
        have hsound := firstNonconstantLowDegreeMonomial_sound hypothesis.coefficient
        rw [hmonomial] at hsound
        change IsRelevant
          (f₂HypothesisBooleanFunction hypothesis.evaluate).toReal
          (S.1.1.min' S.2.1) at hsound
        rw [hlearnedSign] at hsound
        have hrelevant :=
          isRelevantJuntaRestriction_of_reindexed target P z _ hsound
        have hfirst : firstNonconstantLowDegreeMonomial
            (lowDegreeJuntaPolynomialHypothesis P k failure batch).coefficient =
            some S := hmonomial
        have hdecision : lowDegreeJuntaNodeDecisionFromBatch P k failure batch =
            .relevant (juntaFreeCoordinateOfFin P (S.1.1.min' S.2.1)) := by
          simp [lowDegreeJuntaNodeDecisionFromBatch, hdetected, hfirst]
        rw [hdecision]
        exact hrelevant
    | none =>
        have hsound := firstNonconstantLowDegreeMonomial_sound hypothesis.coefficient
        rw [hmonomial] at hsound
        have hlearnedConstant :
            f₂HypothesisBooleanFunction hypothesis.evaluate =
              fun _ ↦ binarySignEquiv (hypothesis.coefficient ⟨∅, by simp⟩) := by
          funext x
          change binarySignEquiv
              (lowDegreeF₂Eval hypothesis.coefficient
                ((binaryCubeSignEquiv _).symm x)) = _
          rw [hsound]
        have hgConstant : g =
            fun _ ↦ binarySignEquiv (hypothesis.coefficient ⟨∅, by simp⟩) := by
          rw [← hlearnedSign]
          exact hlearnedConstant
        have hconstant := juntaRestriction_eq_const_of_reindexed_eq_const
          target P z _ hgConstant
        have hfirst : firstNonconstantLowDegreeMonomial
            (lowDegreeJuntaPolynomialHypothesis P k failure batch).coefficient =
            none := hmonomial
        have hdecision : lowDegreeJuntaNodeDecisionFromBatch P k failure batch =
            .constant (binarySignEquiv
              ((lowDegreeJuntaPolynomialHypothesis P k failure batch).coefficient
                ⟨∅, by simp⟩)) := by
          simp [lowDegreeJuntaNodeDecisionFromBatch, hdetected, hfirst]
        rw [hdecision]
        exact hconstant

/-! ## Ideal and executable node guarantees -/

/-- Bad semantic output of the deterministic controller on a projected restricted batch. -/
def LowDegreeJuntaNodeBatchBad
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) : Prop :=
  ¬ (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect target P z

/-- Transferred source event: rejection failure or a semantically bad projected node batch. -/
def lowDegreeJuntaNodeSourceBad
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (sampled : Option
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        MatchedJuntaExample P z)) : Prop :=
  JuntaRestrictionSampleBad P z
    (LowDegreeJuntaNodeBatchBad target P z k failure) sampled

/-- Under ideal independent examples of the current restriction, the concrete Fourier/ANF
controller returns a correct node decision except with half of its total node budget. -/
theorem idealLowDegreeJuntaNodeBatchBadProbability_le
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n))) :
    (((uniformPMF (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
      (juntaRestrictionLabeledBatch target P z)).toOuterMeasure
        {batch | LowDegreeJuntaNodeBatchBad target P z k failure batch}).toReal ≤
      ((lowDegreeJuntaHalfFailure failure).1 : ℝ) := by
  classical
  let law := (uniformPMF
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        JuntaFreeAssignment P)).map
    (juntaRestrictionLabeledBatch target P z)
  let inaccurate : Set
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        (JuntaFreeAssignment P × Sign)) :=
    {batch | ¬ LowDegreeJuntaFourierEstimatesAccurate
      target P z k failure batch}
  let polynomialFailure : Set
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        (JuntaFreeAssignment P × Sign)) :=
    {batch | ¬ LowDegreeJuntaPolynomialHypothesisExact
      target P z k failure batch}
  let bad : Set
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        (JuntaFreeAssignment P × Sign)) :=
    {batch | LowDegreeJuntaNodeBatchBad target P z k failure batch}
  have hFourier : law.toMeasure.real inaccurate ≤
      ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
    have hmeasure : law.toMeasure.real inaccurate =
        (law.toOuterMeasure inaccurate).toReal := by
      exact congrArg ENNReal.toReal
        (PMF.toMeasure_apply_eq_toOuterMeasure law inaccurate)
    rw [hmeasure]
    exact idealLowDegreeJuntaFourierInaccuracyProbability_le
      target P z k failure
  by_cases hspectrum : ∃ S : lowDegreeJuntaFourierFamily P k,
      S.1.Nonempty ∧
        fourierCoeff (reindexedJuntaRestriction target P z).toReal S.1 ≠ 0
  · obtain ⟨S, hSnonempty, hScoeff⟩ := hspectrum
    have hsubset : bad ⊆ inaccurate := by
      intro batch hbad
      change ¬ (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect
        target P z at hbad
      change ¬ LowDegreeJuntaFourierEstimatesAccurate target P z k failure batch
      intro haccurate
      have hnotNone :
          firstLowDegreeJuntaDetectedFrequency P k failure batch ≠ none := by
        intro hnone
        apply hScoeff
        exact fourierCoeff_eq_zero_of_no_lowDegreeJuntaDetection
          target J P z k failure hJcard hdepends batch haccurate hnone
          S.1 hSnonempty ((mem_lowDegreeJuntaFourierFamily P k S.1).1 S.2)
      generalize hfirst :
          firstLowDegreeJuntaDetectedFrequency P k failure batch = first at hnotNone
      cases first with
      | none => exact (hnotNone rfl).elim
      | some detected =>
          apply hbad
          exact lowDegreeJuntaNodeDecisionFromBatch_isCorrect_of_firstDetected_eq_some
            target P z k failure batch haccurate detected hfirst
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure law]
    exact (measureReal_mono hsubset).trans
      (hFourier.trans (by
        have hfailure : (0 : ℝ) ≤ (failure.1 : ℝ) := by
          exact_mod_cast failure.2.1.le
        simp only [lowDegreeJuntaQuarterFailure_value,
          lowDegreeJuntaHalfFailure_value, Rat.cast_div]
        nlinarith))
  · have himmune : IsCorrelationImmune (lowDegreeJuntaCutoff k)
        (reindexedJuntaRestriction target P z) := by
      intro S hSnonempty hScard
      have hSfamily : S ∈ lowDegreeJuntaFourierFamily P k :=
        (mem_lowDegreeJuntaFourierFamily P k S).2 hScard
      have hzero : fourierCoeff
          (reindexedJuntaRestriction target P z).toReal S = 0 := by
        by_contra hnonzero
        exact hspectrum ⟨⟨S, hSfamily⟩, hSnonempty, hnonzero⟩
      rw [hzero, abs_zero]
    have hdegree : functionAlgebraicDegree
        (booleanFunctionF₂Encoding (reindexedJuntaRestriction target P z)) ≤
        lowDegreeJuntaPolynomialDegree k := by
      exact functionAlgebraicDegree_encoding_le_sub_of_isKJunta_of_isCorrelationImmune
        (reindexedJuntaRestriction target P z) k (lowDegreeJuntaCutoff k)
        (reindexedJuntaRestriction_isKJunta target J P z k hJcard hdepends)
        himmune
    have hPolynomial : law.toMeasure.real polynomialFailure ≤
        ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) := by
      have hmeasure : law.toMeasure.real polynomialFailure =
          (law.toOuterMeasure polynomialFailure).toReal := by
        exact congrArg ENNReal.toReal
          (PMF.toMeasure_apply_eq_toOuterMeasure law polynomialFailure)
      rw [hmeasure]
      exact idealLowDegreeJuntaPolynomialFailureProbability_le
        target P z k failure hdegree
    have hsubset : bad ⊆ inaccurate ∪ polynomialFailure := by
      intro batch hbad
      change ¬ (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect
        target P z at hbad
      change (¬ LowDegreeJuntaFourierEstimatesAccurate target P z k failure batch) ∨
        (¬ LowDegreeJuntaPolynomialHypothesisExact target P z k failure batch)
      by_cases haccurate : LowDegreeJuntaFourierEstimatesAccurate
          target P z k failure batch
      · right
        intro hexact
        exact hbad (lowDegreeJuntaNodeDecisionFromBatch_isCorrect
          target J P z k failure hJcard hdepends batch haccurate hexact)
      · exact Or.inl haccurate
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure law]
    calc
      law.toMeasure.real bad ≤
          law.toMeasure.real (inaccurate ∪ polynomialFailure) :=
        measureReal_mono hsubset
      _ ≤ law.toMeasure.real inaccurate +
          law.toMeasure.real polynomialFailure :=
        measureReal_union_le inaccurate polynomialFailure
      _ ≤ ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) +
          ((lowDegreeJuntaQuarterFailure failure).1 : ℝ) :=
        add_le_add hFourier hPolynomial
      _ = ((lowDegreeJuntaHalfFailure failure).1 : ℝ) := by
        simp only [lowDegreeJuntaQuarterFailure_value,
          lowDegreeJuntaHalfFailure_value, Rat.cast_div]
        ring

/-- A continuation reached outside the transferred source bad event cannot return a bad node
decision. -/
theorem lowDegreeJuntaNodeContinuation_badProbability_le_zero
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (sampled : Option
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        MatchedJuntaExample P z))
    (hgood : ¬ lowDegreeJuntaNodeSourceBad target P z k failure sampled) :
    LearningProgram.eventProbability
        (lowDegreeJuntaNodeContinuation P z k failure sampled)
        target
        (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤ 0 := by
  classical
  cases sampled with
  | none =>
      simp [lowDegreeJuntaNodeSourceBad, JuntaRestrictionSampleBad,
        projectJuntaRestrictionBatch] at hgood
  | some ambientBatch =>
      let batch := fun i ↦ matchedJuntaRestrictionExample P z (ambientBatch i)
      have hcorrect :
          (lowDegreeJuntaNodeDecisionFromBatch P k failure batch).IsCorrect
            target P z := by
        change ¬ LowDegreeJuntaNodeBatchBad target P z k failure batch at hgood
        unfold LowDegreeJuntaNodeBatchBad at hgood
        exact Classical.not_not.mp hgood
      change LearningProgram.eventProbability
          (.tick (lowDegreeJuntaNodeAnalysisWork P k failure batch)
            (.pure (some
              (lowDegreeJuntaNodeDecisionFromBatch P k failure batch))))
          target
          (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤ 0
      simp [LearningProgram.eventProbability, LearningProgram.runWithCost,
        LearningProgram.addOutcomeCost, PMF.toOuterMeasure_pure_apply,
        JuntaNodeDecision.IsBad, hcorrect]

/-- The executable ambient rejection sampler and deterministic controller satisfy the node
failure contract required by Exercise 6.31. -/
theorem lowDegreeJuntaRelevantCoordinateProgram_failureProbability_le
    (target : BooleanFunction n) (J P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (hJcard : J.card ≤ k)
    (hdepends : DependsOn target (J : Set (Fin n)))
    (hPsubset : P ⊆ J)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (lowDegreeJuntaRelevantCoordinateProgram k P z failure) target
        (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤
      (failure.1 : ℝ) := by
  classical
  let next : Option
      (Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
        MatchedJuntaExample P z) →
      LearningProgram n .randomExamples (Option (JuntaNodeDecision P)) :=
    lowDegreeJuntaNodeContinuation P z k failure
  have hPk : P.card ≤ k :=
    (Finset.card_le_card hPsubset).trans hJcard
  have hideal := idealLowDegreeJuntaNodeBatchBadProbability_le
    target J P z k failure hJcard hdepends
  have hsourceRaw := juntaRestrictionSampleProgram_badProbability_le
    target P z k (lowDegreeJuntaRestrictedSampleCount P k failure) hPk
    (lowDegreeJuntaHalfFailure failure)
    (LowDegreeJuntaNodeBatchBad target P z k failure)
    ((lowDegreeJuntaHalfFailure failure).1 : ℝ)
    (by exact (positiveLearningParameter_toReal_mem_Ioc
      (lowDegreeJuntaHalfFailure failure)).1.le)
    hideal
  have hsource : LearningProgram.eventProbability
      (juntaRestrictionSampleProgram P z k
        (lowDegreeJuntaRestrictedSampleCount P k failure)
        (lowDegreeJuntaHalfFailure failure))
      target
      (fun outcome ↦ JuntaRestrictionSampleBad P z
        (LowDegreeJuntaNodeBatchBad target P z k failure) outcome.1) ≤
      (failure.1 : ℝ) := by
    have hsum :
        ((lowDegreeJuntaHalfFailure failure).1 : ℝ) +
            ((lowDegreeJuntaHalfFailure failure).1 : ℝ) =
          (failure.1 : ℝ) := by
      simp only [lowDegreeJuntaHalfFailure_value, Rat.cast_div]
      ring
    rw [hsum] at hsourceRaw
    exact hsourceRaw
  have hnext : ∀ sampled,
      ¬ JuntaRestrictionSampleBad P z
        (LowDegreeJuntaNodeBatchBad target P z k failure) sampled →
      LearningProgram.eventProbability (next sampled) target
        (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤ 0 := by
    intro sampled hgood
    change ¬ lowDegreeJuntaNodeSourceBad target P z k failure sampled at hgood
    change LearningProgram.eventProbability
        (lowDegreeJuntaNodeContinuation P z k failure sampled) target
        (fun outcome ↦ JuntaNodeDecision.IsBad target P z outcome.1) ≤ 0
    exact lowDegreeJuntaNodeContinuation_badProbability_le_zero
      target P z k failure sampled hgood
  have hbound := LearningProgram.eventProbability_bind_le_add
    target
    (juntaRestrictionSampleProgram P z k
      (lowDegreeJuntaRestrictedSampleCount P k failure)
      (lowDegreeJuntaHalfFailure failure))
    next
    (JuntaRestrictionSampleBad P z
      (LowDegreeJuntaNodeBatchBad target P z k failure))
    (JuntaNodeDecision.IsBad target P z)
    (failure.1 : ℝ) 0
    (by exact (positiveLearningParameter_toReal_mem_Ioc failure).1.le)
    le_rfl hsource hnext
  have hprogram : lowDegreeJuntaRelevantCoordinateProgram k P z failure =
      LearningProgram.bind next
        (juntaRestrictionSampleProgram P z k
          (lowDegreeJuntaRestrictedSampleCount P k failure)
          (lowDegreeJuntaHalfFailure failure)) := by
    unfold lowDegreeJuntaRelevantCoordinateProgram
    rfl
  rw [hprogram]
  simpa only [add_zero] using hbound

/-- Root-level failure for the relevant-coordinate task: rejection, a constant certificate, or
an alleged coordinate that is not relevant to the original target. -/
def LowDegreeJuntaRootFinderBad
    (target : BooleanFunction n) :
    Option (JuntaNodeDecision (∅ : Finset (Fin n))) → Prop
  | none => True
  | some (.constant _) => True
  | some (.relevant coordinate) => ¬ IsRelevant target.toReal coordinate.1

/-- At the root restriction, restricting the free part of an ambient input recovers the original
target value. -/
theorem juntaRestriction_empty_juntaFreePart
    (target : BooleanFunction n)
    (z : JuntaFixedAssignment (∅ : Finset (Fin n)))
    (x : {−1,1}^[n]) :
    juntaRestriction target ∅ z (juntaFreePart ∅ x) = target x := by
  have hx : MatchesJuntaAssignment (∅ : Finset (Fin n)) z x := by
    intro i
    exact isEmptyElim i
  unfold juntaRestriction
  exact congrArg target
    (combineJuntaAssignment_freePart_of_matches ∅ z x hx)

/-- Relevance in the empty partial restriction is relevance of the corresponding ambient
coordinate. -/
theorem isRelevant_of_isRelevantJuntaRestriction_empty
    (target : BooleanFunction n)
    (z : JuntaFixedAssignment (∅ : Finset (Fin n)))
    (i : JuntaFreeIndex (∅ : Finset (Fin n)))
    (hrelevant : IsRelevantJuntaRestriction target ∅ z i) :
    IsRelevant target.toReal i.1 := by
  classical
  obtain ⟨y₀, y₁, hagree, hne⟩ := hrelevant
  let x₀ := combineJuntaAssignment (∅ : Finset (Fin n)) z y₀
  let x₁ := combineJuntaAssignment (∅ : Finset (Fin n)) z y₁
  change target x₀ ≠ target x₁ at hne
  have hx₀i : x₀ i.1 = y₀ i :=
    combineJuntaAssignment_apply_free ∅ z y₀ i
  have hx₁i : x₁ i.1 = y₁ i :=
    combineJuntaAssignment_apply_free ∅ z y₁ i
  have hagreeAmbient : ∀ j, j ≠ i.1 → x₀ j = x₁ j := by
    intro j hji
    let q : JuntaFreeIndex (∅ : Finset (Fin n)) := ⟨j, by simp⟩
    have hqi : q ≠ i := by
      intro h
      exact hji (congrArg Subtype.val h)
    change y₀ q = y₁ q
    exact hagree q hqi
  have hcoordinate : y₀ i ≠ y₁ i := by
    intro heq
    apply hne
    congr 1
    funext j
    by_cases hji : j = i.1
    · subst j
      exact hx₀i.trans (heq.trans hx₁i.symm)
    · exact hagreeAmbient j hji
  have hsetSelf (b : Sign) (hb : x₀ i.1 = b) :
      setCoordinate x₀ i.1 b = x₀ := by
    rw [← hb]
    exact setCoordinate_eq_self x₀ i.1
  have hsetOther (b : Sign) (hb : x₁ i.1 = b) :
      setCoordinate x₀ i.1 b = x₁ := by
    funext j
    by_cases hji : j = i.1
    · subst j
      rw [setCoordinate_apply_self]
      exact hb.symm
    · rw [setCoordinate_apply_of_ne x₀ hji]
      exact hagreeAmbient j hji
  rw [isRelevant_iff_exists_setCoordinate_ne]
  refine ⟨x₀, ?_⟩
  rcases Int.units_eq_one_or (y₀ i) with hy₀ | hy₀ <;>
    rcases Int.units_eq_one_or (y₁ i) with hy₁ | hy₁
  · exact (hcoordinate (hy₀.trans hy₁.symm)).elim
  · rw [hsetSelf 1 (hx₀i.trans hy₀),
      hsetOther (-1) (hx₁i.trans hy₁)]
    intro heq
    exact hne (signValue_injective heq)
  · rw [hsetOther 1 (hx₁i.trans hy₁),
      hsetSelf (-1) (hx₀i.trans hy₀)]
    intro heq
    exact hne (signValue_injective heq.symm)
  · exact (hcoordinate (hy₀.trans hy₁.symm)).elim

/-- Every root-finder failure is a failure of the already verified node semantics when the target
is nonconstant. -/
theorem juntaNodeDecision_isBad_empty_of_rootFinderBad
    (target : BooleanFunction n)
    (hnonconstant : ¬ ∀ x y, target x = target y)
    (outcome : Option (JuntaNodeDecision (∅ : Finset (Fin n))))
    (hbad : LowDegreeJuntaRootFinderBad target outcome) :
    JuntaNodeDecision.IsBad target ∅ (fun _ ↦ 1) outcome := by
  cases outcome with
  | none => trivial
  | some decision =>
      cases decision with
      | constant value =>
          change ¬ juntaRestriction target ∅ (fun _ ↦ 1) = fun _ ↦ value
          intro hconstant
          apply hnonconstant
          intro x y
          calc
            target x = juntaRestriction target ∅ (fun _ ↦ 1)
                (juntaFreePart ∅ x) :=
              (juntaRestriction_empty_juntaFreePart target (fun _ ↦ 1) x).symm
            _ = value := congrFun hconstant (juntaFreePart ∅ x)
            _ = juntaRestriction target ∅ (fun _ ↦ 1)
                (juntaFreePart ∅ y) :=
              (congrFun hconstant (juntaFreePart ∅ y)).symm
            _ = target y :=
              juntaRestriction_empty_juntaFreePart target (fun _ ↦ 1) y
      | relevant coordinate =>
          change ¬ IsRelevant target.toReal coordinate.1 at hbad
          change ¬ IsRelevantJuntaRestriction target ∅ (fun _ ↦ 1) coordinate
          intro hrelevant
          exact hbad (isRelevant_of_isRelevantJuntaRestriction_empty
            target (fun _ ↦ 1) coordinate hrelevant)

/-- The root invocation of the concrete learner returns a genuinely relevant coordinate except
with probability at most `failure`; `none` and constant certificates both count as failures. -/
theorem lowDegreeJuntaRelevantCoordinateProgram_root_failureProbability_le
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (hnonconstant : ¬ ∀ x y, target x = target y)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (lowDegreeJuntaRelevantCoordinateProgram k ∅ (fun _ ↦ 1) failure) target
        (fun outcome ↦ LowDegreeJuntaRootFinderBad target outcome.1) ≤
      (failure.1 : ℝ) := by
  classical
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hnode := lowDegreeJuntaRelevantCoordinateProgram_failureProbability_le
    target J (∅ : Finset (Fin n)) (fun _ ↦ 1) k hJcard hdepends
      (Finset.empty_subset J) failure
  exact (LearningProgram.eventProbability_mono
    (lowDegreeJuntaRelevantCoordinateProgram k ∅ (fun _ ↦ 1) failure) target
      (fun outcome hbad ↦
        juntaNodeDecision_isBad_empty_of_rootFinderBad
          target hnonconstant outcome.1 hbad)).trans hnode

/-- Every execution follows the constructor-derived random-example and local-work envelopes. -/
theorem lowDegreeJuntaRelevantCoordinateProgram_cost_le
    (target : BooleanFunction n) (P : Finset (Fin n))
    (z : JuntaFixedAssignment P) (k : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (JuntaNodeDecision P) × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (lowDegreeJuntaRelevantCoordinateProgram k P z failure)).support) :
    outcome.2.randomExamples ≤
        lowDegreeJuntaNodeRandomExampleBound n k failure ∧
      outcome.2.queries = 0 ∧
      outcome.2.work ≤ lowDegreeJuntaNodeUniformWorkBound n k failure := by
  classical
  let M := lowDegreeJuntaRestrictedSampleCount P k failure
  let sampler := juntaRestrictionSampleProgram P z k M
    (lowDegreeJuntaHalfFailure failure)
  let projected := fun batch : Fin M → MatchedJuntaExample P z ↦
    fun i ↦ matchedJuntaRestrictionExample P z (batch i)
  let next : Option (Fin M → MatchedJuntaExample P z) →
      LearningProgram n .randomExamples (Option (JuntaNodeDecision P)) :=
    lowDegreeJuntaNodeContinuation P z k failure
  have hprogram : lowDegreeJuntaRelevantCoordinateProgram k P z failure =
      LearningProgram.bind next sampler := by
    unfold lowDegreeJuntaRelevantCoordinateProgram
    rfl
  rw [hprogram, LearningProgram.runWithCost_bind,
    PMF.mem_support_bind_iff] at houtcome
  obtain ⟨samplerOutcome, hsampler, houtcome⟩ := houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨continuationOutcome, hcontinuation, rfl⟩ := houtcome
  have hsamplerCost := juntaRestrictionSampleProgram_cost_eq
    target P z k M (lowDegreeJuntaHalfFailure failure) samplerOutcome hsampler
  have hRandomSup : lowDegreeJuntaNodeRandomExamples P k failure ≤
      lowDegreeJuntaNodeRandomExampleBound n k failure := by
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun Q ↦ lowDegreeJuntaNodeRandomExamples Q k failure)
      (Finset.mem_univ P)
  have hWorkSup : lowDegreeJuntaNodeWorkBound P k failure ≤
      lowDegreeJuntaNodeUniformWorkBound n k failure := by
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun Q ↦ lowDegreeJuntaNodeWorkBound Q k failure)
      (Finset.mem_univ P)
  cases hsampled : samplerOutcome.1 with
  | none =>
      rw [hsampled] at hcontinuation
      simp only [next, lowDegreeJuntaNodeContinuation, LearningProgram.runWithCost,
        PMF.mem_support_pure_iff] at hcontinuation
      subst continuationOutcome
      rw [hsamplerCost]
      constructor
      · change juntaRestrictionSampleCount k M
            (lowDegreeJuntaHalfFailure failure) ≤ _
        simpa [lowDegreeJuntaNodeRandomExamples, M] using hRandomSup
      · constructor
        · rfl
        · change juntaRestrictionSampleCount k M
              (lowDegreeJuntaHalfFailure failure) +
              juntaRestrictionSampleWork P k M
                (lowDegreeJuntaHalfFailure failure) ≤ _
          apply (Nat.le_add_right
              (juntaRestrictionSampleCount k M (lowDegreeJuntaHalfFailure failure) +
                juntaRestrictionSampleWork P k M
                  (lowDegreeJuntaHalfFailure failure))
              (lowDegreeJuntaNodeAnalysisWorkBound P k failure)).trans
          simpa [lowDegreeJuntaNodeWorkBound, M] using hWorkSup
  | some batch =>
      rw [hsampled] at hcontinuation
      simp only [next, lowDegreeJuntaNodeContinuation,
        LearningProgram.runWithCost, PMF.pure_map,
        PMF.mem_support_pure_iff] at hcontinuation
      subst continuationOutcome
      rw [hsamplerCost]
      constructor
      · change juntaRestrictionSampleCount k M
            (lowDegreeJuntaHalfFailure failure) ≤ _
        simpa [lowDegreeJuntaNodeRandomExamples, M] using hRandomSup
      · constructor
        · rfl
        · change
            juntaRestrictionSampleCount k M (lowDegreeJuntaHalfFailure failure) +
                juntaRestrictionSampleWork P k M (lowDegreeJuntaHalfFailure failure) +
                lowDegreeJuntaNodeAnalysisWork P k failure (projected batch) ≤ _
          calc
            juntaRestrictionSampleCount k M (lowDegreeJuntaHalfFailure failure) +
                juntaRestrictionSampleWork P k M (lowDegreeJuntaHalfFailure failure) +
                lowDegreeJuntaNodeAnalysisWork P k failure (projected batch) ≤
              juntaRestrictionSampleCount k M (lowDegreeJuntaHalfFailure failure) +
                juntaRestrictionSampleWork P k M (lowDegreeJuntaHalfFailure failure) +
                lowDegreeJuntaNodeAnalysisWorkBound P k failure := by
              gcongr
              exact lowDegreeJuntaNodeAnalysisWork_le P k failure (projected batch)
            _ = lowDegreeJuntaNodeWorkBound P k failure := by
              rfl
            _ ≤ lowDegreeJuntaNodeUniformWorkBound n k failure := hWorkSup

/-! ## Lemma 6.37 and Theorem 6.36 -/

/-- Lemma 6.37's concrete relevant-coordinate finder obtained from the Fourier/ANF node
controller and Exercise 6.31's finite rejection sampler. -/
noncomputable def lowDegreeJuntaRelevantCoordinateFinder
    (n k : ℕ) : JuntaRelevantCoordinateFinder n k where
  program := fun P z failure ↦
    lowDegreeJuntaRelevantCoordinateProgram k P z failure
  randomExampleBound := lowDegreeJuntaNodeRandomExampleBound n k
  workBound := lowDegreeJuntaNodeUniformWorkBound n k
  cost_le := by
    intro target P z failure outcome houtcome
    exact lowDegreeJuntaRelevantCoordinateProgram_cost_le
      target P z k failure outcome houtcome
  failureProbability_le := by
    intro target J P z hJcard hdepends hPsubset failure
    exact lowDegreeJuntaRelevantCoordinateProgram_failureProbability_le
      target J P z k hJcard hdepends hPsubset failure

/-- Theorem 6.36's complete exact learner, obtained by the Exercise 6.31 recursion from the
concrete Lemma 6.37 finder. -/
noncomputable def lowDegreeJuntaLearnerProgram
    (n k : ℕ) (failure : PositiveLearningParameter) :
    LearningProgram n .randomExamples (Option (DecisionTree n Sign)) :=
  recursiveJuntaLearner (lowDegreeJuntaRelevantCoordinateFinder n k) failure

/-- The complete learner exactly computes every `k`-junta except with the requested total failure
probability. -/
theorem lowDegreeJuntaLearnerProgram_failureProbability_le
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (failure : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (lowDegreeJuntaLearnerProgram n k failure) target
        (fun outcome ↦ JuntaLearnerOutputBad target outcome.1) ≤
      (failure.1 : ℝ) := by
  exact recursiveJuntaLearner_failureProbability_le
    (lowDegreeJuntaRelevantCoordinateFinder n k) target hjunta failure

/-- Every successful exact hypothesis has decision-tree depth at most `k`. -/
theorem lowDegreeJuntaLearnerProgram_depth_le
    (target : BooleanFunction n) (k : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (DecisionTree n Sign) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (lowDegreeJuntaLearnerProgram n k failure)).support)
    (tree : DecisionTree n Sign) (htree : outcome.1 = some tree) :
    tree.depth ≤ k := by
  exact recursiveJuntaLearner_depth_le
    (lowDegreeJuntaRelevantCoordinateFinder n k) target failure
    outcome houtcome tree htree

/-- Constructor-derived pathwise oracle and local-work closure for the complete learner. -/
theorem lowDegreeJuntaLearnerProgram_cost_le
    (target : BooleanFunction n) (k : ℕ)
    (failure : PositiveLearningParameter)
    (outcome : Option (DecisionTree n Sign) × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (lowDegreeJuntaLearnerProgram n k failure)).support) :
    outcome.2.randomExamples ≤
        juntaTreeCallCount k *
          lowDegreeJuntaNodeRandomExampleBound n k
            (juntaTreePerCallFailure k failure) ∧
      outcome.2.queries = 0 ∧
      outcome.2.work ≤
        juntaTreeCallCount k *
          lowDegreeJuntaNodeUniformWorkBound n k
            (juntaTreePerCallFailure k failure) := by
  exact recursiveJuntaLearner_cost_le
    (lowDegreeJuntaRelevantCoordinateFinder n k) target failure outcome houtcome

/-! ## Explicit fixed-parameter runtime ledger -/

theorem juntaRestrictionDimension_le (P : Finset (Fin n)) :
    juntaRestrictionDimension P ≤ n := by
  unfold juntaRestrictionDimension
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun i : Fin n ↦ i ∉ P))

/-- The scanned family contributes only the enumeration exponent `d = ⌊3k/4⌋`. -/
theorem card_lowDegreeJuntaFourierFamily_le
    (P : Finset (Fin n)) (k : ℕ) :
    (lowDegreeJuntaFourierFamily P k).card ≤
      (lowDegreeJuntaCutoff k + 1) *
        (n + 1) ^ lowDegreeJuntaCutoff k := by
  calc
    (lowDegreeJuntaFourierFamily P k).card ≤
      (lowDegreeJuntaCutoff k + 1) *
          (juntaRestrictionDimension P + 1) ^ lowDegreeJuntaCutoff k := by
      exact card_lowDegreeFourierFamily_le
        (juntaRestrictionDimension P) (lowDegreeJuntaCutoff k)
    _ ≤ (lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k := by
      gcongr
      exact juntaRestrictionDimension_le P

/-- The coefficient-union scheduler uses the explicit binary logarithm of
`8 |family| / failure`. -/
theorem lowDegreeJuntaCoefficientFailureBits_eq
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter) :
    fourierEstimatorFailureBits
        (lowDegreeJuntaCoefficientConfidence P k failure) =
      Nat.clog 2 (Nat.ceil
        ((8 : ℚ) * (lowDegreeJuntaFourierFamily P k).card / failure.1)) := by
  unfold fourierEstimatorFailureBits
  apply congrArg (Nat.clog 2)
  apply congrArg Nat.ceil
  rw [lowDegreeJuntaCoefficientConfidence_value]
  have hcard : ((lowDegreeJuntaFourierFamily P k).card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr
      (lowDegreeJuntaFourierFamily_nonempty P k)).ne'
  have hfailure : failure.1 ≠ 0 := failure.2.1.ne'
  field_simp [hcard, hfailure]
  ring

/-- Proposition 3.30's charged Fourier scan is a family-size factor times its explicit
accuracy/confidence scheduler. -/
theorem lowDegreeJuntaFourierScanWork_cast_le
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter) :
    (((lowDegreeJuntaFourierFamily P k).card *
        lowDegreeJuntaCoefficientSampleCount P k failure *
        (lowDegreeJuntaCutoff k + 1) : ℕ) : ℚ) ≤
      (((lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k : ℕ) : ℚ) *
        (4 * fourierEstimatorFailureBits
            (lowDegreeJuntaCoefficientConfidence P k failure) /
          (lowDegreeJuntaCoefficientAccuracy k).1 ^ 2) *
        (lowDegreeJuntaCutoff k + 1) := by
  have hfamily : ((lowDegreeJuntaFourierFamily P k).card : ℚ) ≤
      ((lowDegreeJuntaCutoff k + 1) *
        (n + 1) ^ lowDegreeJuntaCutoff k : ℕ) := by
    exact_mod_cast card_lowDegreeJuntaFourierFamily_le P k
  have hsamples := fourierEstimatorSampleCount_cast_le
    (lowDegreeJuntaCoefficientAccuracy k)
    (lowDegreeJuntaCoefficientConfidence P k failure)
  calc
    (((lowDegreeJuntaFourierFamily P k).card *
        lowDegreeJuntaCoefficientSampleCount P k failure *
        (lowDegreeJuntaCutoff k + 1) : ℕ) : ℚ) =
        ((lowDegreeJuntaFourierFamily P k).card : ℚ) *
          (lowDegreeJuntaCoefficientSampleCount P k failure : ℚ) *
          (lowDegreeJuntaCutoff k + 1 : ℚ) := by norm_num
    _ ≤ (((lowDegreeJuntaCutoff k + 1) *
          (n + 1) ^ lowDegreeJuntaCutoff k : ℕ) : ℚ) *
        (4 * fourierEstimatorFailureBits
            (lowDegreeJuntaCoefficientConfidence P k failure) /
          (lowDegreeJuntaCoefficientAccuracy k).1 ^ 2) *
        (lowDegreeJuntaCutoff k + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hfamily hsamples (by positivity) (by positivity))
        (by positivity)

/-- Exercise 6.30's actual elimination trace has the advertised
`(n+1)^(3(k-d))` fixed-parameter envelope. -/
theorem lowDegreeJuntaPolynomialWork_le_fixedParameterEnvelope
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    lowDegreeF₂PolynomialLearnerWork
        (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
        (lowDegreeJuntaPolynomialSampleCount P k failure)
        (lowDegreeJuntaPolynomialSamples P k failure batch) ≤
      3 * (2 ^ lowDegreeJuntaPolynomialDegree k *
        (lowDegreeJuntaPolynomialDegree k +
          fourierEstimatorFailureBits (lowDegreeJuntaQuarterFailure failure) + 3)) ^ 3 *
        (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) := by
  let coefficient := 3 * (2 ^ lowDegreeJuntaPolynomialDegree k *
    (lowDegreeJuntaPolynomialDegree k +
      fourierEstimatorFailureBits (lowDegreeJuntaQuarterFailure failure) + 3)) ^ 3
  have hwork := scheduledLowDegreeF₂PolynomialLearnerWork_le_fixedParameterEnvelope
    (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
    (lowDegreeJuntaQuarterFailure failure)
    (lowDegreeJuntaPolynomialSamples P k failure batch)
  apply hwork.trans
  apply Nat.mul_le_mul_left coefficient
  exact Nat.pow_le_pow_left
    (Nat.succ_le_succ (juntaRestrictionDimension_le P)) _

/-- The integer-balanced standard schedule has both `n`-exponents at most
`⌊3k/4⌋ + 3`; the additive constant is absorbed by the theorem's `poly(n)` factor. -/
theorem lowDegreeJuntaRuntimeExponentLedger (k : ℕ) :
    lowDegreeJuntaCutoff k ≤ lowDegreeJuntaCutoff k + 3 ∧
      3 * lowDegreeJuntaPolynomialDegree k ≤
        lowDegreeJuntaCutoff k + 3 := by
  exact ⟨Nat.le_add_right _ _,
    three_mul_lowDegreeJuntaPolynomialDegree_le_cutoff_add_three k⟩

/-- The node runtime ledger: the two genuine high-degree terms have exponents `d` and
`3(k-d)`, their confidence dependence is the explicit `clog₂`, and both fit the
`n^((3/4)k) poly(n) log(1/failure)` book bound for fixed `k`. -/
theorem lowDegreeJuntaNodeRuntimeLedger
    (P : Finset (Fin n)) (k : ℕ)
    (failure : PositiveLearningParameter)
    (batch : Fin (lowDegreeJuntaRestrictedSampleCount P k failure) →
      (JuntaFreeAssignment P × Sign)) :
    (((lowDegreeJuntaFourierFamily P k).card *
        lowDegreeJuntaCoefficientSampleCount P k failure *
        (lowDegreeJuntaCutoff k + 1) : ℕ) : ℚ) ≤
        (((lowDegreeJuntaCutoff k + 1) *
            (n + 1) ^ lowDegreeJuntaCutoff k : ℕ) : ℚ) *
          (4 * fourierEstimatorFailureBits
              (lowDegreeJuntaCoefficientConfidence P k failure) /
            (lowDegreeJuntaCoefficientAccuracy k).1 ^ 2) *
          (lowDegreeJuntaCutoff k + 1) ∧
      lowDegreeF₂PolynomialLearnerWork
          (juntaRestrictionDimension P) (lowDegreeJuntaPolynomialDegree k)
          (lowDegreeJuntaPolynomialSampleCount P k failure)
          (lowDegreeJuntaPolynomialSamples P k failure batch) ≤
        3 * (2 ^ lowDegreeJuntaPolynomialDegree k *
          (lowDegreeJuntaPolynomialDegree k +
            fourierEstimatorFailureBits (lowDegreeJuntaQuarterFailure failure) + 3)) ^ 3 *
          (n + 1) ^ (3 * lowDegreeJuntaPolynomialDegree k) ∧
      fourierEstimatorFailureBits
          (lowDegreeJuntaCoefficientConfidence P k failure) =
        Nat.clog 2 (Nat.ceil
          ((8 : ℚ) * (lowDegreeJuntaFourierFamily P k).card / failure.1)) ∧
      lowDegreeJuntaCutoff k ≤ lowDegreeJuntaCutoff k + 3 ∧
      3 * lowDegreeJuntaPolynomialDegree k ≤
        lowDegreeJuntaCutoff k + 3 := by
  exact ⟨lowDegreeJuntaFourierScanWork_cast_le P k failure,
    lowDegreeJuntaPolynomialWork_le_fixedParameterEnvelope P k failure batch,
    lowDegreeJuntaCoefficientFailureBits_eq P k failure,
    lowDegreeJuntaRuntimeExponentLedger k⟩

/-! ## Matrix-multiplication exponent refinement -/

/-- A positive exponent `ω` for the algebraic row-reduction routine. -/
abbrev PositiveMatrixExponent := Set.Ioi (0 : ℚ)

theorem positiveMatrixExponent_add_one_pos (ω : PositiveMatrixExponent) :
    0 < ω.1 + 1 := by
  have hω : (0 : ℚ) < ω.1 := ω.2
  linarith

/-- The real-valued balance point solving `ω(k-d) = d`. -/
def matrixExponentJuntaBalancedExponent
    (ω : PositiveMatrixExponent) (k : ℕ) : ℚ :=
  ω.1 * k / (ω.1 + 1)

/-- The integer Fourier cutoff `⌈ωk/(ω+1)⌉`. -/
def matrixExponentJuntaCutoff
    (ω : PositiveMatrixExponent) (k : ℕ) : ℕ :=
  Nat.ceil (matrixExponentJuntaBalancedExponent ω k)

/-- The row-reduction exponent after using the rounded cutoff. -/
def matrixExponentJuntaSolverExponent
    (ω : PositiveMatrixExponent) (k : ℕ) : ℚ :=
  ω.1 * ((k : ℚ) - matrixExponentJuntaCutoff ω k)

theorem matrixExponentJuntaBalancedExponent_nonneg
    (ω : PositiveMatrixExponent) (k : ℕ) :
    0 ≤ matrixExponentJuntaBalancedExponent ω k := by
  unfold matrixExponentJuntaBalancedExponent
  exact div_nonneg (mul_nonneg ω.2.le (by positivity))
    (positiveMatrixExponent_add_one_pos ω).le

theorem matrixExponentJuntaBalancedExponent_le_k
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaBalancedExponent ω k ≤ k := by
  unfold matrixExponentJuntaBalancedExponent
  rw [div_le_iff₀ (positiveMatrixExponent_add_one_pos ω)]
  have hk : (0 : ℚ) ≤ k := by positivity
  nlinarith

/-- At the unrounded balance point the enumeration and row-reduction exponents agree. -/
theorem matrixExponentJuntaBalancedExponent_balance
    (ω : PositiveMatrixExponent) (k : ℕ) :
    ω.1 * ((k : ℚ) - matrixExponentJuntaBalancedExponent ω k) =
      matrixExponentJuntaBalancedExponent ω k := by
  unfold matrixExponentJuntaBalancedExponent
  field_simp [(positiveMatrixExponent_add_one_pos ω).ne']; ring

/-- The balanced exponent has the coefficient `ω/(ω+1)`. -/
theorem matrixExponentJuntaBalancedExponent_eq_fraction
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaBalancedExponent ω k =
      (ω.1 / (ω.1 + 1)) * k := by
  unfold matrixExponentJuntaBalancedExponent
  ring

theorem matrixExponentJuntaBalancedExponent_le_cutoff
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaBalancedExponent ω k ≤
      (matrixExponentJuntaCutoff ω k : ℚ) := by
  unfold matrixExponentJuntaCutoff
  exact Nat.le_ceil _

theorem matrixExponentJuntaCutoff_le_k
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaCutoff ω k ≤ k := by
  unfold matrixExponentJuntaCutoff
  exact Nat.ceil_le.mpr (matrixExponentJuntaBalancedExponent_le_k ω k)

theorem matrixExponentJuntaSolverExponent_nonneg
    (ω : PositiveMatrixExponent) (k : ℕ) :
    0 ≤ matrixExponentJuntaSolverExponent ω k := by
  have hcutoff : (matrixExponentJuntaCutoff ω k : ℚ) ≤ k := by
    exact_mod_cast matrixExponentJuntaCutoff_le_k ω k
  unfold matrixExponentJuntaSolverExponent
  exact mul_nonneg ω.2.le (sub_nonneg.mpr hcutoff)

/-- Rounding costs less than one in the enumeration exponent. -/
theorem matrixExponentJuntaCutoff_lt_balancedExponent_add_one
    (ω : PositiveMatrixExponent) (k : ℕ) :
    (matrixExponentJuntaCutoff ω k : ℚ) <
      matrixExponentJuntaBalancedExponent ω k + 1 := by
  unfold matrixExponentJuntaCutoff
  exact Nat.ceil_lt_add_one
    (matrixExponentJuntaBalancedExponent_nonneg ω k)

/-- With the ceiling cutoff, the row-reduction exponent remains below the enumeration
exponent. -/
theorem matrixExponentJuntaSolverExponent_le_cutoff
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaSolverExponent ω k ≤
      (matrixExponentJuntaCutoff ω k : ℚ) := by
  unfold matrixExponentJuntaSolverExponent
  calc
    ω.1 * ((k : ℚ) - matrixExponentJuntaCutoff ω k) ≤
        ω.1 * ((k : ℚ) - matrixExponentJuntaBalancedExponent ω k) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left
          (matrixExponentJuntaBalancedExponent_le_cutoff ω k) (k : ℚ))
        ω.2.le
    _ = matrixExponentJuntaBalancedExponent ω k :=
      matrixExponentJuntaBalancedExponent_balance ω k
    _ ≤ (matrixExponentJuntaCutoff ω k : ℚ) :=
      matrixExponentJuntaBalancedExponent_le_cutoff ω k

/-- The maximum of the Fourier and solver exponents is
`(ω/(ω+1))k + O(1)`; the strict `+1` is absorbed by `poly(n)`. -/
theorem matrixExponentJuntaCombinedExponent_lt_fraction_add_one
    (ω : PositiveMatrixExponent) (k : ℕ) :
    max (matrixExponentJuntaSolverExponent ω k)
        (matrixExponentJuntaCutoff ω k : ℚ) <
      (ω.1 / (ω.1 + 1)) * k + 1 := by
  rw [max_eq_right (matrixExponentJuntaSolverExponent_le_cutoff ω k)]
  rw [← matrixExponentJuntaBalancedExponent_eq_fraction]
  exact matrixExponentJuntaCutoff_lt_balancedExponent_add_one ω k

/-- Canonical cubic row-reduction exponent. -/
def cubicMatrixExponent : PositiveMatrixExponent := ⟨3, by norm_num⟩

/-- The cubic case specializes the balanced exponent to `3k/4`. -/
theorem matrixExponentJuntaBalancedExponent_cubic (k : ℕ) :
    matrixExponentJuntaBalancedExponent cubicMatrixExponent k =
      (3 : ℚ) * k / 4 := by
  change (3 : ℚ) * (k : ℚ) / ((3 : ℚ) + 1) = 3 * k / 4
  norm_num

/-- The complete matrix-exponent ledger records the exact fraction, rounded solver
bound, and the single-unit rounding loss. -/
theorem matrixExponentJuntaRuntimeExponentLedger
    (ω : PositiveMatrixExponent) (k : ℕ) :
    matrixExponentJuntaBalancedExponent ω k =
        (ω.1 / (ω.1 + 1)) * k ∧
      0 ≤ matrixExponentJuntaSolverExponent ω k ∧
      matrixExponentJuntaSolverExponent ω k ≤
          (matrixExponentJuntaCutoff ω k : ℚ) ∧
      max (matrixExponentJuntaSolverExponent ω k)
          (matrixExponentJuntaCutoff ω k : ℚ) <
        (ω.1 / (ω.1 + 1)) * k + 1 := by
  exact ⟨matrixExponentJuntaBalancedExponent_eq_fraction ω k,
    matrixExponentJuntaSolverExponent_nonneg ω k,
    matrixExponentJuntaSolverExponent_le_cutoff ω k,
    matrixExponentJuntaCombinedExponent_lt_fraction_add_one ω k⟩

end FABL
