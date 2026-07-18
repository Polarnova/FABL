/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.LearningTheory.FourierEstimation

/-!
# Learning algorithms and sparse hypotheses

Book items: Definition 3.27, Definition 3.28, Proposition 3.31, Theorem 3.29.

Finite hypothesis representations, spectral concentration, and sparse Fourier hypotheses.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

universe u v

variable {n : ℕ}

local instance learningModelSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance learningModelSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- An executable hypothesis language with finite binary encodings and explicit evaluation cost.
The decoding law makes every code produced by a learner an honest finite representation. -/
structure FiniteHypothesisRepresentation (n : ℕ) where
  /-- Structured hypotheses represented by this language. -/
  Code : Type u
  /-- Finite binary encoding. -/
  encode : Code → List Bool
  /-- Decoder for finite binary strings. -/
  decode : List Bool → Option Code
  /-- Encoding followed by decoding recovers the structured hypothesis. -/
  decode_encode : ∀ code, decode (encode code) = some code
  /-- Total evaluator of a structured hypothesis. -/
  evaluate : Code → BooleanFunction n
  /-- Explicit work used to evaluate a hypothesis at an input. -/
  evaluationWork : Code → {−1,1}^[n] → ℕ

/-- A Definition 3.27 learning algorithm consists of a real program, an exact success-probability
field tied to its semantics, and verified pathwise resource bounds. -/
structure LearningAlgorithm (n : ℕ) (access : LearningAccess)
    (hypotheses : FiniteHypothesisRepresentation n) where
  /-- Program selected by the requested accuracy. -/
  program : LearningAccuracy → LearningProgram n access hypotheses.Code
  /-- Exact success probability on each target and accuracy. -/
  successProbability : BooleanFunction n → LearningAccuracy → ℝ
  /-- Uniform bound on random-example calls at each accuracy, independent of the target. -/
  randomExampleCost : LearningAccuracy → ℕ
  /-- Uniform bound on membership queries at each accuracy, independent of the target. -/
  queryCost : LearningAccuracy → ℕ
  /-- Uniform bound on local work at each accuracy, independent of the target. -/
  workCost : LearningAccuracy → ℕ
  /-- The advertised probability is the actual probability of outputting an accurate hypothesis. -/
  successProbability_eq :
    ∀ target ε,
      successProbability target ε =
        LearningProgram.eventProbability (program ε) target fun outcome ↦
          relativeHammingDist target (hypotheses.evaluate outcome.1) ≤ (ε.1 : ℝ)
  /-- Every execution path obeys all advertised resource bounds. -/
  cost_le :
    ∀ target ε outcome,
      outcome ∈ (LearningProgram.runWithCost target (program ε)).support →
        outcome.2.randomExamples ≤ randomExampleCost ε ∧
        outcome.2.queries ≤ queryCost ε ∧
        outcome.2.work ≤ workCost ε

/-- O'Donnell, Definition 3.27: the algorithm PAC-learns the concept class with error ε under the
uniform distribution, with high probability fixed to at least 9/10. -/
def LearnsConceptClassWithError {access : LearningAccess}
    {hypotheses : FiniteHypothesisRepresentation n}
    (algorithm : LearningAlgorithm n access hypotheses)
    (conceptClass : Set (BooleanFunction n)) (ε : LearningAccuracy) : Prop :=
  ∀ target ∈ conceptClass, (9 / 10 : ℝ) ≤ algorithm.successProbability target ε

/-- Fourier weight outside an arbitrary collection of characters. -/
noncomputable def fourierWeightOutside
    (f : {−1,1}^[n] → ℝ) (𝓕 : Set (Finset (Fin n))) : ℝ :=
  by
    classical
    exact ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕), fourierWeight f S

/-- O'Donnell, Definition 3.28: the Fourier spectrum is ε-concentrated on an arbitrary
collection. -/
def IsFourierSpectrumConcentratedOn
    (f : {−1,1}^[n] → ℝ) (ε : ℝ) (𝓕 : Set (Finset (Fin n))) : Prop :=
  fourierWeightOutside f 𝓕 ≤ ε

/-- A Boolean function's spectrum cannot be `ε/2`-concentrated on the empty family for the
learning-accuracy range `0 < ε ≤ 1/2`. -/
theorem not_isFourierSpectrumConcentratedOn_empty
    (target : BooleanFunction n) (ε : PositiveLearningParameter) :
    ¬ IsFourierSpectrumConcentratedOn target.toReal ((ε.1 : ℝ) / 2)
      (∅ : Set (Finset (Fin n))) := by
  intro hconcentration
  have htotal : fourierWeightOutside target.toReal
      (∅ : Set (Finset (Fin n))) = 1 := by
    simp [fourierWeightOutside, fourierWeight, sum_sq_fourierCoeff_eq_one]
  have hone : (1 : ℝ) ≤ (ε.1 : ℝ) / 2 := by
    simpa [IsFourierSpectrumConcentratedOn, htotal] using hconcentration
  rcases positiveLearningParameter_toReal_mem_Ioc ε with ⟨hεpos, hεle⟩
  nlinarith

/-- Every finite family satisfying Theorem 3.29's concentration premise is nonempty. -/
theorem finiteFamily_nonempty_of_spectrum_concentrated
    (target : BooleanFunction n) (𝓕 : Finset (Finset (Fin n)))
    (ε : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑𝓕 : Set (Finset (Fin n)))) :
    𝓕.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hconcentration
  apply not_isFourierSpectrumConcentratedOn_empty target ε
  simpa using hconcentration

/-- Probability that the spectral sample lies outside an arbitrary collection. -/
noncomputable def spectralSampleOutsideProbability
    (f : BooleanFunction n) (𝓕 : Set (Finset (Fin n))) : ℝ :=
  by
    classical
    exact ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
      (spectralSample f S).toReal

/-- For Boolean functions, spectral-sample mass outside a collection is exactly its Fourier
weight outside that collection. -/
theorem spectralSampleOutsideProbability_eq_fourierWeightOutside
    (f : BooleanFunction n) (𝓕 : Set (Finset (Fin n))) :
    spectralSampleOutsideProbability f 𝓕 = fourierWeightOutside f.toReal 𝓕 := by
  simp [spectralSampleOutsideProbability, fourierWeightOutside,
    spectralSample_apply_toReal]

/-- The spectral-sample formulation in O'Donnell, Definition 3.28. -/
theorem isFourierSpectrumConcentratedOn_iff_spectralSampleOutsideProbability_le
    (f : BooleanFunction n) (ε : ℝ) (𝓕 : Set (Finset (Fin n))) :
    IsFourierSpectrumConcentratedOn f.toReal ε 𝓕 ↔
      spectralSampleOutsideProbability f 𝓕 ≤ ε := by
  rw [IsFourierSpectrumConcentratedOn,
    spectralSampleOutsideProbability_eq_fourierWeightOutside]

/-- Pointwise sign rounding has disagreement indicator at most squared approximation error. -/
theorem indicator_ne_thresholdSign_le_sq
    (s : Sign) (t : ℝ) :
    (if s ≠ thresholdSign t then (1 : ℝ) else 0) ≤ (signValue s - t) ^ 2 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · by_cases ht : 0 ≤ t
    · have heq : (1 : Sign) = thresholdSign t := by
        rw [thresholdSign_of_nonneg ht]
      rw [if_neg (fun hne ↦ hne heq)]
      exact sq_nonneg _
    · have hneg : t < 0 := lt_of_not_ge ht
      have hne : (1 : Sign) ≠ thresholdSign t := by
        rw [thresholdSign_of_neg hneg]
        norm_num
      rw [if_pos hne, signValue_one]
      nlinarith [sq_nonneg t]
  · by_cases ht : 0 ≤ t
    · have hne : (-1 : Sign) ≠ thresholdSign t := by
        rw [thresholdSign_of_nonneg ht]
        norm_num
      rw [if_pos hne, signValue_neg_one]
      nlinarith [sq_nonneg t]
    · have hneg : t < 0 := lt_of_not_ge ht
      have heq : (-1 : Sign) = thresholdSign t := by
        rw [thresholdSign_of_neg hneg]
      rw [if_neg (fun hne ↦ hne heq)]
      exact sq_nonneg _

/-- The normalized squared L² error controls relative Hamming distance after sign rounding. -/
theorem relativeHammingDist_thresholdSign_le_uniformLpNorm_two_sq
    (f : BooleanFunction n) (g : {−1,1}^[n] → ℝ) :
    relativeHammingDist f (fun x ↦ thresholdSign (g x)) ≤
      uniformLpNorm 2 (fun x ↦ f.toReal x - g x) ^ 2 := by
  classical
  rw [← uniformProbability_ne_eq_relativeHammingDist]
  calc
    uniformProbability (fun x ↦ f x ≠ thresholdSign (g x)) =
        𝔼 x, if f x ≠ thresholdSign (g x) then (1 : ℝ) else 0 := rfl
    _ ≤ 𝔼 x, (f.toReal x - g x) ^ 2 := by
      apply Finset.expect_le_expect
      intro x _
      exact indicator_ne_thresholdSign_le_sq (f x) (g x)
    _ = uniformLpNorm 2 (fun x ↦ f.toReal x - g x) ^ 2 := by
      rw [uniformLpNorm_two_sq_eq_uniformInner, uniformInner,
        RCLike.wInner_cWeight_eq_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp [pow_two]

/-- O'Donnell, Proposition 3.31: sign rounding converts normalized squared L² error into
classification error. -/
theorem relativeHammingDist_thresholdSign_le_of_uniformLpNorm_two_sq_le
    (f : BooleanFunction n) (g : {−1,1}^[n] → ℝ) (ε : ℝ)
    (herror : uniformLpNorm 2 (fun x ↦ f.toReal x - g x) ^ 2 ≤ ε) :
    relativeHammingDist f (fun x ↦ thresholdSign (g x)) ≤ ε :=
  (relativeHammingDist_thresholdSign_le_uniformLpNorm_two_sq f g).trans herror

/-- A finite sparse Fourier hypothesis with rational coefficients. -/
structure SparseFourierHypothesis (n : ℕ) where
  /-- Characters used by the hypothesis. -/
  support : Finset (Finset (Fin n))
  /-- Rational coefficient of each character in the support. -/
  coefficient : support → ℚ

/-- A sparse hypothesis is constructively encodable as its finite support together with its
support-indexed rational coefficient vector. -/
def sparseFourierHypothesisSigmaEquiv :
    SparseFourierHypothesis n ≃
      (Σ support : Finset (Finset (Fin n)), support → ℚ) where
  toFun hypothesis := ⟨hypothesis.support, hypothesis.coefficient⟩
  invFun data := ⟨data.1, data.2⟩
  left_inv hypothesis := by cases hypothesis; rfl
  right_inv data := by cases data; rfl

/-- Constructive encodability of sparse rational Fourier hypotheses. -/
instance sparseFourierHypothesisEncodable : Encodable (SparseFourierHypothesis n) :=
  Encodable.ofEquiv _ sparseFourierHypothesisSigmaEquiv

namespace SparseFourierHypothesis

/-- Rational value of a sparse Fourier expansion at an input. -/
def value (hypothesis : SparseFourierHypothesis n) (x : {−1,1}^[n]) : ℚ :=
  ∑ S : hypothesis.support,
    hypothesis.coefficient S * ∏ i ∈ S.1, (((x i : Sign) : ℤ) : ℚ)

/-- Executable sign-threshold evaluator of a sparse rational Fourier hypothesis. -/
def evaluate (hypothesis : SparseFourierHypothesis n) : BooleanFunction n :=
  fun x ↦ if 0 ≤ hypothesis.value x then 1 else -1

/-- Real-valued sparse Fourier expansion associated to a rational hypothesis. -/
noncomputable def realValue
    (hypothesis : SparseFourierHypothesis n) (x : {−1,1}^[n]) : ℝ :=
  ∑ S : hypothesis.support,
    (hypothesis.coefficient S : ℝ) * monomial S.1 x

/-- Casting the executable rational expansion to the reals gives its mathematical Fourier
expansion. -/
theorem value_cast_eq_realValue
    (hypothesis : SparseFourierHypothesis n) (x : {−1,1}^[n]) :
    (hypothesis.value x : ℝ) = hypothesis.realValue x := by
  classical
  simp [value, realValue, monomial, signValue]

/-- The executable rational evaluator agrees with the book's real threshold-sign convention. -/
theorem evaluate_eq_thresholdSign_realValue
    (hypothesis : SparseFourierHypothesis n) :
    hypothesis.evaluate = fun x ↦ thresholdSign (hypothesis.realValue x) := by
  funext x
  rw [evaluate, thresholdSign, ← value_cast_eq_realValue]
  norm_cast

/-- Decode a little-endian list of bits as a natural number. -/
def natOfBits : List Bool → ℕ
  | [] => 0
  | bit :: bits => Nat.bit bit (natOfBits bits)

/-- Decoding the canonical bit list of a natural number recovers that number. -/
@[simp] theorem natOfBits_bits (k : ℕ) : natOfBits k.bits = k := by
  induction k using Nat.binaryRec' with
  | zero => simp [natOfBits]
  | bit bit k hcanonical ih =>
      rw [Nat.bits_append_bit k bit hcanonical]
      simp [natOfBits, ih]

/-- Canonical finite binary encoding of a sparse rational Fourier hypothesis. -/
def encode (hypothesis : SparseFourierHypothesis n) : List Bool :=
  (Encodable.encode hypothesis).bits

/-- Decoder for the canonical finite binary encoding. -/
def decode (bits : List Bool) : Option (SparseFourierHypothesis n) :=
  Encodable.decode (natOfBits bits)

/-- The sparse hypothesis binary decoder is a left inverse of its encoder. -/
@[simp] theorem decode_encode (hypothesis : SparseFourierHypothesis n) :
    decode (encode hypothesis) = some hypothesis := by
  simp [decode, encode]

/-- Explicit structural work bound for evaluating a sparse Fourier hypothesis. -/
def evaluationWork (hypothesis : SparseFourierHypothesis n) (_x : {−1,1}^[n]) : ℕ :=
  hypothesis.support.card * (n + 1)

/-- Sparse rational Fourier hypotheses form an honest finite binary hypothesis language with a
total executable evaluator. -/
def finiteRepresentation : FiniteHypothesisRepresentation n where
  Code := SparseFourierHypothesis n
  encode := encode
  decode := decode
  decode_encode := decode_encode
  evaluate := evaluate
  evaluationWork := evaluationWork

end SparseFourierHypothesis

/-- A real sparse Fourier approximation on a prescribed finite family. -/
noncomputable def sparseFourierApproximation
    (𝓕 : Finset (Finset (Fin n))) (coefficient : Finset (Fin n) → ℝ) :
    {−1,1}^[n] → ℝ :=
  fun x ↦ ∑ S ∈ 𝓕, coefficient S * monomial S x

/-- A sparse Fourier approximation has exactly its prescribed coefficients on its family and zero
coefficients off the family. -/
theorem fourierCoeff_sparseFourierApproximation
    (𝓕 : Finset (Finset (Fin n))) (coefficient : Finset (Fin n) → ℝ)
    (T : Finset (Fin n)) :
    fourierCoeff (sparseFourierApproximation 𝓕 coefficient) T =
      if T ∈ 𝓕 then coefficient T else 0 := by
  classical
  unfold fourierCoeff sparseFourierApproximation
  calc
    (𝔼 x, (∑ S ∈ 𝓕, coefficient S * monomial S x) * monomial T x) =
        𝔼 x, ∑ S ∈ 𝓕, (coefficient S * monomial S x) * monomial T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ S ∈ 𝓕, 𝔼 x, (coefficient S * monomial S x) * monomial T x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S ∈ 𝓕, coefficient S * (if S = T then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← expect_monomial_mul S T, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = if T ∈ 𝓕 then coefficient T else 0 := by
      by_cases hT : T ∈ 𝓕 <;> simp [hT]

/-- Fourier coefficients of the residual of a sparse approximation. -/
theorem fourierCoeff_sub_sparseFourierApproximation
    (f : {−1,1}^[n] → ℝ) (𝓕 : Finset (Finset (Fin n)))
    (coefficient : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f x - sparseFourierApproximation 𝓕 coefficient x) T =
      if T ∈ 𝓕 then fourierCoeff f T - coefficient T else fourierCoeff f T := by
  classical
  have hlinear :
      fourierCoeff (fun x ↦ f x - sparseFourierApproximation 𝓕 coefficient x) T =
        fourierCoeff f T -
          fourierCoeff (sparseFourierApproximation 𝓕 coefficient) T := by
    unfold fourierCoeff
    rw [show (fun x : {−1,1}^[n] ↦
        (f x - sparseFourierApproximation 𝓕 coefficient x) * monomial T x) =
        fun x ↦ f x * monomial T x -
          sparseFourierApproximation 𝓕 coefficient x * monomial T x by
      funext x
      ring]
    rw [Finset.expect_sub_distrib]
  rw [hlinear, fourierCoeff_sparseFourierApproximation]
  by_cases hT : T ∈ 𝓕 <;> simp [hT]

/-- The deterministic Parseval error decomposition used in the proof of O'Donnell,
Theorem 3.29. -/
theorem uniformLpNorm_sub_sparseFourierApproximation_sq
    (f : {−1,1}^[n] → ℝ) (𝓕 : Finset (Finset (Fin n)))
    (coefficient : Finset (Fin n) → ℝ) :
    uniformLpNorm 2 (fun x ↦ f x - sparseFourierApproximation 𝓕 coefficient x) ^ 2 =
      (∑ S ∈ 𝓕, (fourierCoeff f S - coefficient S) ^ 2) +
      ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
        fourierCoeff f S ^ 2 := by
  classical
  rw [uniformLpNorm_two_sq_eq_uniformInner, parseval]
  simp_rw [fourierCoeff_sub_sparseFourierApproximation, ite_pow]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n)))
    (fun S : Finset (Fin n) ↦ S ∈ 𝓕)
    (fun S ↦ if S ∈ 𝓕 then
      (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2)
  have hyes :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∈ 𝓕),
        if S ∈ 𝓕 then
          (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2) =
        ∑ S ∈ 𝓕, (fourierCoeff f S - coefficient S) ^ 2 := by
    have hfilter :
        (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∈ 𝓕) = 𝓕 := by
      ext S
      simp
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro S hS
    rw [if_pos hS]
  have hno :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
        if S ∈ 𝓕 then
          (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2) =
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
          fourierCoeff f S ^ 2 := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [if_neg (Finset.mem_filter.mp hS).2]
  calc
    (∑ S, if S ∈ 𝓕 then
      (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2) =
        (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∈ 𝓕),
          if S ∈ 𝓕 then
            (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2) +
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
          if S ∈ 𝓕 then
            (fourierCoeff f S - coefficient S) ^ 2 else fourierCoeff f S ^ 2 :=
      hsplit.symm
    _ = (∑ S ∈ 𝓕, (fourierCoeff f S - coefficient S) ^ 2) +
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
          fourierCoeff f S ^ 2 := by rw [hyes, hno]

/-- The per-coefficient accuracy budget used in Theorem 3.29. -/
def finiteFamilyCoefficientAccuracy (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) : PositiveLearningParameter := by
  have hcard : 0 < 𝓕.card := Finset.card_pos.mpr h𝓕
  have hdenominator : (0 : ℚ) < 2 * 𝓕.card := by positivity
  refine ⟨ε.1 / (2 * 𝓕.card), div_pos ε.2.1 hdenominator, ?_⟩
  rw [div_le_iff₀ hdenominator]
  have hcardOne : (1 : ℚ) ≤ 𝓕.card := by exact_mod_cast hcard
  nlinarith [ε.2.2]

/-- The per-coefficient confidence budget used for the `1/10` union bound. -/
def finiteFamilyCoefficientConfidence (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) : PositiveLearningParameter := by
  have hcard : 0 < 𝓕.card := Finset.card_pos.mpr h𝓕
  have hdenominator : (0 : ℚ) < 10 * 𝓕.card := by positivity
  refine ⟨(1 : ℚ) / (10 * 𝓕.card), div_pos zero_lt_one hdenominator, ?_⟩
  rw [div_le_iff₀ hdenominator]
  have hcardOne : (1 : ℚ) ≤ 𝓕.card := by exact_mod_cast hcard
  nlinarith

/-- Samples per Fourier coefficient in the finite-family learner. -/
def finiteFamilySamplesPerCoefficient (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : 𝓕.Nonempty) (ε : PositiveLearningParameter) : ℕ :=
  fourierEstimatorSampleCount (finiteFamilyCoefficientAccuracy 𝓕 h𝓕 ε)
    (finiteFamilyCoefficientConfidence 𝓕 h𝓕)

namespace SparseFourierHypothesis

/-- Build a sparse rational Fourier hypothesis from coefficients indexed by its support. -/
def ofCoefficients (𝓕 : Finset (Finset (Fin n))) (coefficient : 𝓕 → ℚ) :
    SparseFourierHypothesis n :=
  ⟨𝓕, coefficient⟩

/-- Extend support-indexed rational coefficients by zero to all characters. -/
noncomputable def realCoefficientOfCoefficients
    (𝓕 : Finset (Finset (Fin n))) (coefficient : 𝓕 → ℚ)
    (S : Finset (Fin n)) : ℝ :=
  if hS : S ∈ 𝓕 then (coefficient ⟨S, hS⟩ : ℝ) else 0

/-- The real value of `ofCoefficients` is its zero-extended sparse Fourier expansion. -/
theorem realValue_ofCoefficients
    (𝓕 : Finset (Finset (Fin n))) (coefficient : 𝓕 → ℚ) :
    (ofCoefficients 𝓕 coefficient).realValue =
      sparseFourierApproximation 𝓕
        (realCoefficientOfCoefficients 𝓕 coefficient) := by
  classical
  funext x
  change (∑ S : 𝓕, (coefficient S : ℝ) * monomial S.1 x) =
    ∑ S ∈ 𝓕, realCoefficientOfCoefficients 𝓕 coefficient S * monomial S x
  calc
    (∑ S : 𝓕, (coefficient S : ℝ) * monomial S.1 x) =
        ∑ S ∈ 𝓕.attach,
          realCoefficientOfCoefficients 𝓕 coefficient S.1 * monomial S.1 x := by
      rw [Finset.attach_eq_univ]
      apply Finset.sum_congr rfl
      intro S _
      simp [realCoefficientOfCoefficients, S.2]
    _ = ∑ S ∈ 𝓕,
        realCoefficientOfCoefficients 𝓕 coefficient S * monomial S x :=
      Finset.sum_attach 𝓕 (fun S : Finset (Fin n) ↦
        realCoefficientOfCoefficients 𝓕 coefficient S * monomial S x)

end SparseFourierHypothesis

end FABL
