/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.LearningTheory.FiniteFamily

/-!
# Low-degree learning

Book items: Low-Degree Algorithm, Theorem 3.36, Corollary 3.32, Corollary 3.33, Corollary 3.34,
Corollary 3.35, Exercise 3.36.

The Low-Degree Algorithm and the structural learning corollaries of Section 3.4.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

universe u v

variable {n : ℕ}

local instance lowDegreeSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance lowDegreeSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## The Low-Degree Algorithm and its structural corollaries -/

/-- The family of all Fourier frequencies of degree at most `k`. -/
noncomputable def lowDegreeFourierFamily (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (k + 1)).biUnion fun j ↦
    Finset.powersetCard j (Finset.univ : Finset (Fin n))

@[simp] theorem mem_lowDegreeFourierFamily (S : Finset (Fin n)) (k : ℕ) :
    S ∈ lowDegreeFourierFamily n k ↔ S.card ≤ k := by
  classical
  simp [lowDegreeFourierFamily]

/-- The low-degree family always contains the empty frequency. -/
theorem lowDegreeFourierFamily_nonempty (n k : ℕ) :
    (lowDegreeFourierFamily n k).Nonempty := by
  exact ⟨∅, by simp⟩

/-- The number of degree-at-most-`k` frequencies is the sum of the first binomial coefficients. -/
theorem card_lowDegreeFourierFamily_eq_sum_choose (n k : ℕ) :
    (lowDegreeFourierFamily n k).card =
      ∑ j ∈ Finset.range (k + 1), Nat.choose n j := by
  classical
  have hdisjoint :
      ((Finset.range (k + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun j ↦ Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
    intro i hi j hj hij
    change Disjoint
      (Finset.powersetCard i (Finset.univ : Finset (Fin n)))
      (Finset.powersetCard j (Finset.univ : Finset (Fin n)))
    rw [Finset.disjoint_left]
    intro S hSi hSj
    have hiCard := (Finset.mem_powersetCard.mp hSi).2
    have hjCard := (Finset.mem_powersetCard.mp hSj).2
    exact hij (hiCard.symm.trans hjCard)
  rw [lowDegreeFourierFamily, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- An explicit polynomial bound on the number of low-degree frequencies. -/
theorem card_lowDegreeFourierFamily_le (n k : ℕ) :
    (lowDegreeFourierFamily n k).card ≤
      (k + 1) * (n + 1) ^ k := by
  rw [card_lowDegreeFourierFamily_eq_sum_choose]
  calc
    (∑ j ∈ Finset.range (k + 1), Nat.choose n j) ≤
        ∑ _j ∈ Finset.range (k + 1), (n + 1) ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by simpa using hj
      exact (Nat.choose_le_pow n j).trans
        ((Nat.pow_le_pow_left (Nat.le_succ n) j).trans
          (Nat.pow_le_pow_right (Nat.succ_pos n) hjk))
    _ = (k + 1) * (n + 1) ^ k := by
      simp

/-- Fourier weight outside the low-degree family is exactly the usual high-degree tail. -/
theorem fourierWeightOutside_lowDegreeFourierFamily
    (f : {−1,1}^[n] → ℝ) (k : ℕ) :
    fourierWeightOutside f (↑(lowDegreeFourierFamily n k) : Set (Finset (Fin n))) =
      fourierWeightAbove k f := by
  classical
  unfold fourierWeightOutside fourierWeightAbove
  congr 1
  ext S
  simp

/-- Concentration on the low-degree family is the natural-cutoff form of Definition 3.1. -/
theorem isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff
    (f : {−1,1}^[n] → ℝ) (ε : ℝ) (k : ℕ) :
    IsFourierSpectrumConcentratedOn f ε
        (↑(lowDegreeFourierFamily n k) : Set (Finset (Fin n))) ↔
      IsFourierSpectrumConcentratedUpTo f ε k := by
  rw [IsFourierSpectrumConcentratedOn, IsFourierSpectrumConcentratedUpTo,
    fourierWeightOutside_lowDegreeFourierFamily, fourierWeightAboveReal_natCast]

/-- Raising the degree cutoff can only decrease the Fourier tail. -/
theorem fourierWeightAboveReal_antitone (f : {−1,1}^[n] → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    fourierWeightAboveReal b f ≤ fourierWeightAboveReal a f := by
  classical
  unfold fourierWeightAboveReal
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    exact ⟨Finset.mem_univ S, hab.trans_lt hS.2⟩
  · intro S _ _
    exact sq_nonneg (fourierCoeff f S)

/-- Fourier concentration persists when the degree cutoff is increased. -/
theorem IsFourierSpectrumConcentratedUpTo.mono_cutoff
    {f : {−1,1}^[n] → ℝ} {ε a b : ℝ}
    (h : IsFourierSpectrumConcentratedUpTo f ε a) (hab : a ≤ b) :
    IsFourierSpectrumConcentratedUpTo f ε b := by
  exact (fourierWeightAboveReal_antitone f hab).trans h

/-- Fourier concentration persists when the permitted error is increased. -/
theorem IsFourierSpectrumConcentratedUpTo.mono_error
    {f : {−1,1}^[n] → ℝ} {ε ε' k : ℝ}
    (h : IsFourierSpectrumConcentratedUpTo f ε k) (hε : ε ≤ ε') :
    IsFourierSpectrumConcentratedUpTo f ε' k :=
  h.trans hε

/-- Explicit integral degree cutoff used for the bounded-total-influence learner. -/
noncomputable def totalInfluenceLearningDegree (t : ℝ)
    (ε : PositiveLearningParameter) : ℕ :=
  ⌈2 * t / (ε.1 : ℝ)⌉₊

/-- Proposition 3.2 supplies the concentration premise for the total-influence learner. -/
theorem isFourierSpectrumConcentratedUpTo_totalInfluenceLearningDegree
    (target : BooleanFunction n) (t : ℝ) (ε : PositiveLearningParameter)
    (ht : totalInfluence target.toReal ≤ t) :
    IsFourierSpectrumConcentratedUpTo target.toReal ((ε.1 : ℝ) / 2)
      (totalInfluenceLearningDegree t ε) := by
  have hε : 0 < (ε.1 : ℝ) :=
    (positiveLearningParameter_toReal_mem_Ioc ε).1
  have hbase := isFourierSpectrumConcentratedUpTo_totalInfluence_div
    target.toReal (half_pos hε)
  apply hbase.mono_cutoff
  calc
    totalInfluence target.toReal / ((ε.1 : ℝ) / 2) =
        2 * totalInfluence target.toReal / (ε.1 : ℝ) := by field_simp
    _ ≤ 2 * t / (ε.1 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (by norm_num)) hε.le
    _ ≤ (totalInfluenceLearningDegree t ε : ℕ) := by
      exact Nat.le_ceil _

/-- Explicit integral degree cutoff used for the noise-sensitivity learner. -/
noncomputable def noiseSensitivityLearningDegree (δ : ℝ) : ℕ :=
  ⌈1 / δ⌉₊

/-- Proposition 3.3 supplies the concentration premise for the noise-sensitivity learner. -/
theorem isFourierSpectrumConcentratedUpTo_noiseSensitivityLearningDegree
    (target : BooleanFunction n) (δ : ℝ) (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (ε : PositiveLearningParameter)
    (hnoise : noiseSensitivity δ ⟨hδpos.le, by linarith⟩ target ≤ (ε.1 : ℝ) / 6) :
    IsFourierSpectrumConcentratedUpTo target.toReal ((ε.1 : ℝ) / 2)
      (noiseSensitivityLearningDegree δ) := by
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδpos.le, by linarith⟩
  have hbase := isFourierSpectrumConcentratedUpTo_noiseSensitivity
    target hδpos hδhalf
  have hfactor := two_div_one_sub_exp_neg_two_mul_noiseSensitivity_le_three
    target hδ
  have herror :
      2 / (1 - Real.exp (-2)) * noiseSensitivity δ hδ target ≤
        (ε.1 : ℝ) / 2 := by
    calc
      2 / (1 - Real.exp (-2)) * noiseSensitivity δ hδ target ≤
          3 * noiseSensitivity δ hδ target := hfactor
      _ ≤ (ε.1 : ℝ) / 2 := by
        have hnoise' : noiseSensitivity δ hδ target ≤ (ε.1 : ℝ) / 6 := by
          simpa [hδ] using hnoise
        nlinarith
  apply (hbase.mono_error herror).mono_cutoff
  exact Nat.le_ceil _

/-- The finite random-example program implementing the Low-Degree Algorithm. -/
noncomputable def lowDegreeFourierEstimatorProgram
    (n k : ℕ) (ε : PositiveLearningParameter) :
    LearningProgram n .randomExamples (SparseFourierHypothesis n) :=
  finiteFamilyFourierEstimatorProgram (lowDegreeFourierFamily n k)
    (lowDegreeFourierFamily_nonempty n k) ε

/-- The Low-Degree Algorithm fails with probability at most `1/10` under its concentration
premise. -/
theorem lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
    (target : BooleanFunction n) (k : ℕ) (ε : PositiveLearningParameter)
    (hconcentration : IsFourierSpectrumConcentratedUpTo target.toReal
      ((ε.1 : ℝ) / 2) k) :
    LearningProgram.eventProbability
        (lowDegreeFourierEstimatorProgram n k ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  apply finiteFamilyFourierEstimatorProgram_failureProbability_le_one_tenth
  exact (isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff
    target.toReal ((ε.1 : ℝ) / 2) k).2 hconcentration

/-- Explicit resource bound for every execution of the Low-Degree Algorithm. -/
theorem lowDegreeFourierEstimatorProgram_cost_polyBound
    (target : BooleanFunction n) (k : ℕ) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (lowDegreeFourierEstimatorProgram n k ε)).support) :
    (outcome.2.randomExamples : ℚ) ≤
        16 * ((lowDegreeFourierFamily n k).card : ℚ) ^ 3 *
          Nat.clog 2 (20 * (lowDegreeFourierFamily n k).card) / ε.1 ^ 2 ∧
      outcome.2.queries = 0 ∧
      (outcome.2.work : ℚ) ≤
        16 * ((lowDegreeFourierFamily n k).card : ℚ) ^ 3 * (n + 2) *
          Nat.clog 2 (20 * (lowDegreeFourierFamily n k).card) / ε.1 ^ 2 := by
  exact finiteFamilyFourierEstimatorProgram_cost_polyBound target
    (lowDegreeFourierFamily n k) (lowDegreeFourierFamily_nonempty n k) ε
    outcome houtcome

/-- Corollary 3.32: bounded total influence gives a Low-Degree learner. -/
theorem lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth
    (target : BooleanFunction n) (t : ℝ) (ε : PositiveLearningParameter)
    (ht : totalInfluence target.toReal ≤ t) :
    LearningProgram.eventProbability
        (lowDegreeFourierEstimatorProgram n (totalInfluenceLearningDegree t ε) ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  exact lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
    target (totalInfluenceLearningDegree t ε) ε
      (isFourierSpectrumConcentratedUpTo_totalInfluenceLearningDegree target t ε ht)

/-- Corollary 3.34: small noise sensitivity gives a Low-Degree learner. -/
theorem lowDegreeFourierEstimatorProgram_of_noiseSensitivity_failure_le_one_tenth
    (target : BooleanFunction n) (δ : ℝ) (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (ε : PositiveLearningParameter)
    (hnoise : noiseSensitivity δ ⟨hδpos.le, by linarith⟩ target ≤ (ε.1 : ℝ) / 6) :
    LearningProgram.eventProbability
        (lowDegreeFourierEstimatorProgram n (noiseSensitivityLearningDegree δ) ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  exact lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
    target (noiseSensitivityLearningDegree δ) ε
      (isFourierSpectrumConcentratedUpTo_noiseSensitivityLearningDegree
        target δ hδpos hδhalf ε hnoise)

/-- Degree cutoff used by the monotone-function specialization. -/
noncomputable def monotoneLearningDegree (n : ℕ)
    (ε : PositiveLearningParameter) : ℕ :=
  totalInfluenceLearningDegree (totalInfluence (majority n).toReal) ε

/-- Corollary 3.33: Theorem 2.33 gives the Low-Degree learner for monotone functions. -/
theorem lowDegreeFourierEstimatorProgram_of_monotone_failure_le_one_tenth
    (target : BooleanFunction n) (htarget : Monotone target)
    (ε : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (lowDegreeFourierEstimatorProgram n (monotoneLearningDegree n ε) ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  exact lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth
    target (totalInfluence (majority n).toReal) ε
      (totalInfluence_toReal_le_majority_of_monotone target htarget)

/-- Exact integer cutoff used by the decision-tree specialization. -/
noncomputable def decisionTreeLearningDegree
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (ε : PositiveLearningParameter) : ℕ :=
  F₂DecisionTree.decisionTreeTruncationDegree T.leafCount ((ε.1 : ℝ) / 2)

/-- Corollary 3.35: a small decision tree supplies the Low-Degree concentration premise. -/
theorem lowDegreeFourierEstimatorProgram_of_decisionTree_failure_le_one_tenth
    (target : BooleanFunction n) {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes fun x ↦ target.toReal (binaryCubeSignEquiv n x))
    (ε : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (lowDegreeFourierEstimatorProgram n (decisionTreeLearningDegree T ε) ε) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      (1 / 10 : ℝ) := by
  apply lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  have hεHalfLeOne : (ε.1 : ℝ) / 2 ≤ 1 := by
    calc
      (ε.1 : ℝ) / 2 ≤ (1 / 2 : ℝ) / 2 :=
        div_le_div_of_nonneg_right hε.2 (by norm_num)
      _ ≤ 1 := by norm_num
  have hconcentration := F₂DecisionTree.isFourierSpectrumConcentratedUpTo_of_decisionTree
    T (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) hT
    ⟨half_pos hε.1, hεHalfLeOne⟩
    (fun x ↦ by
      simpa [BooleanFunction.toReal] using
        signValue_eq_neg_one_or_one (target (binaryCubeSignEquiv n x)))
  have hbridge :
      binaryFunctionOnSignCube
          (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) =
        target.toReal := by
    funext x
    simp [binaryFunctionOnSignCube]
  rw [hbridge] at hconcentration
  simpa [decisionTreeLearningDegree] using hconcentration

/-- Fourier coefficients of a degree-`k` sign-valued function lie on this rational lattice. -/
def degreeFourierGranularity (k : ℕ) : ℚ :=
  2 * (2 : ℚ)⁻¹ ^ k

/-- The degree-`k` Fourier granularity is strictly positive. -/
theorem degreeFourierGranularity_pos (k : ℕ) :
    0 < degreeFourierGranularity k := by
  unfold degreeFourierGranularity
  exact mul_pos (by norm_num) (pow_pos (by norm_num) k)

/-- Coercing the rational Fourier granularity gives the corresponding real lattice spacing. -/
theorem degreeFourierGranularity_cast (k : ℕ) :
    (degreeFourierGranularity k : ℝ) = 2 * (2 : ℝ)⁻¹ ^ k := by
  norm_num [degreeFourierGranularity]

/-- Round a rational coefficient estimate to the nearest degree-`k` Fourier lattice point. -/
def roundToDegreeFourierGranularity (k : ℕ) (q : ℚ) : ℚ :=
  (round (q / degreeFourierGranularity k) : ℚ) * degreeFourierGranularity k

/-- Any estimate within half a lattice spacing rounds to the prescribed lattice point. -/
theorem roundToDegreeFourierGranularity_eq_of_close
    (k : ℕ) (q : ℚ) (z : ℤ)
    (hclose : |(q : ℝ) - (z : ℝ) * (degreeFourierGranularity k : ℝ)| <
      (degreeFourierGranularity k : ℝ) / 2) :
    roundToDegreeFourierGranularity k q =
      (z : ℚ) * degreeFourierGranularity k := by
  have hgq : (0 : ℚ) < degreeFourierGranularity k := degreeFourierGranularity_pos k
  have hgr : (0 : ℝ) < (degreeFourierGranularity k : ℝ) := by
    exact_mod_cast hgq
  have hinterval :
      (q : ℝ) / (degreeFourierGranularity k : ℝ) ∈
        Set.Ico ((z : ℝ) - 1 / 2) ((z : ℝ) + 1 / 2) := by
    rw [abs_lt] at hclose
    constructor
    · rw [le_div_iff₀ hgr]
      nlinarith [hclose.1]
    · rw [div_lt_iff₀ hgr]
      nlinarith [hclose.2]
  have hroundReal :
      round ((q : ℝ) / (degreeFourierGranularity k : ℝ)) = z :=
    round_eq_iff.mpr hinterval
  have hroundRat : round (q / degreeFourierGranularity k) = z := by
    rw [← Rat.round_cast (α := ℝ)]
    norm_num only [Rat.cast_div]
    exact hroundReal
  rw [roundToDegreeFourierGranularity, hroundRat]

/-- Per-coefficient accuracy sufficient for exact recovery on the degree-`k` Fourier lattice. -/
def degreeFourierCoefficientAccuracy (k : ℕ) : PositiveLearningParameter := by
  refine ⟨degreeFourierGranularity k / 4,
    div_pos (degreeFourierGranularity_pos k) (by norm_num), ?_⟩
  have hpow : (2 : ℚ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold degreeFourierGranularity
  nlinarith

/-- The exact-recovery accuracy is `2⁻(k+1)`. -/
theorem degreeFourierCoefficientAccuracy_value (k : ℕ) :
    (degreeFourierCoefficientAccuracy k).1 = (2 : ℚ)⁻¹ ^ (k + 1) := by
  simp [degreeFourierCoefficientAccuracy, degreeFourierGranularity, pow_succ]
  ring

/-- Samples per low-degree coefficient used by the exact Fourier learner. -/
noncomputable def exactDegreeSamplesPerCoefficient (n k : ℕ) : ℕ :=
  fourierEstimatorSampleCount (degreeFourierCoefficientAccuracy k)
    (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
      (lowDegreeFourierFamily_nonempty n k))

/-- Rounded sparse Fourier output reconstructed from a matrix of unlabeled sample inputs. -/
noncomputable def exactDegreeFourierEstimatorOutput
    (target : BooleanFunction n) (k : ℕ)
    (sampleInputs :
      lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n]) :
    SparseFourierHypothesis n :=
  SparseFourierHypothesis.ofCoefficients (lowDegreeFourierFamily n k) fun S ↦
    roundToDegreeFourierGranularity k
      (empiricalFourierCoeff S.1 fun i ↦
        (sampleInputs S i, target (sampleInputs S i)))

/-- If every empirical coefficient is accurate, rounding recovers each true degree-`k`
coefficient exactly. -/
theorem exactDegreeFourierEstimatorOutput_coefficient_cast_eq
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : fourierDegree target.toReal ≤ k)
    (sampleInputs :
      lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n])
    (hgood : ∀ S : lowDegreeFourierFamily n k,
      sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target
        (lowDegreeFourierFamily n k) (degreeFourierCoefficientAccuracy k)
        (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
          (lowDegreeFourierFamily_nonempty n k)) S)
    (S : lowDegreeFourierFamily n k) :
    ((exactDegreeFourierEstimatorOutput target k sampleInputs).coefficient S : ℝ) =
      fourierCoeff target.toReal S.1 := by
  have hgranular := isFourierGranular_signValue_of_fourierDegree_le target hk (by
    simpa [BooleanFunction.toReal] using hdegree)
  obtain ⟨z, hz⟩ := hgranular S.1
  have hz' : fourierCoeff target.toReal S.1 =
      (z : ℝ) * (2 * (2 : ℝ)⁻¹ ^ k) := by
    simpa [BooleanFunction.toReal] using hz
  have hgoodS := hgood S
  change ¬((degreeFourierCoefficientAccuracy k).1 : ℝ) ≤
    |realEmpiricalFourierCoeff target S.1 (sampleInputs S) -
      fourierCoeff target.toReal S.1| at hgoodS
  have hcloseRaw := lt_of_not_ge hgoodS
  have haccuracy : ((degreeFourierCoefficientAccuracy k).1 : ℝ) =
      (degreeFourierGranularity k : ℝ) / 4 := by
    norm_num [degreeFourierCoefficientAccuracy]
  have hgranularity : (0 : ℝ) < (degreeFourierGranularity k : ℝ) := by
    exact_mod_cast degreeFourierGranularity_pos k
  have hclose :
      |(empiricalFourierCoeff S.1 (fun i ↦
          (sampleInputs S i, target (sampleInputs S i))) : ℝ) -
        (z : ℝ) * (degreeFourierGranularity k : ℝ)| <
          (degreeFourierGranularity k : ℝ) / 2 := by
    rw [empiricalFourierCoeff_cast, degreeFourierGranularity_cast, ← hz']
    rw [haccuracy] at hcloseRaw
    rw [degreeFourierGranularity_cast] at hcloseRaw hgranularity
    nlinarith
  have hround := roundToDegreeFourierGranularity_eq_of_close k
    (empiricalFourierCoeff S.1 fun i ↦
      (sampleInputs S i, target (sampleInputs S i))) z hclose
  change (roundToDegreeFourierGranularity k
    (empiricalFourierCoeff S.1 fun i ↦
      (sampleInputs S i, target (sampleInputs S i))) : ℝ) = _
  rw [hround]
  norm_num only [Rat.cast_mul, Rat.cast_intCast]
  rw [degreeFourierGranularity_cast]
  exact hz'.symm

/-- Exact recovery of every low-degree coefficient recovers the target's real Fourier
expansion. -/
theorem exactDegreeFourierEstimatorOutput_realValue_eq
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : fourierDegree target.toReal ≤ k)
    (sampleInputs :
      lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n])
    (hgood : ∀ S : lowDegreeFourierFamily n k,
      sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target
        (lowDegreeFourierFamily n k) (degreeFourierCoefficientAccuracy k)
        (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
          (lowDegreeFourierFamily_nonempty n k)) S) :
    (exactDegreeFourierEstimatorOutput target k sampleInputs).realValue =
      target.toReal := by
  funext x
  change (∑ S : lowDegreeFourierFamily n k,
    ((exactDegreeFourierEstimatorOutput target k sampleInputs).coefficient S : ℝ) *
      monomial S.1 x) = target.toReal x
  calc
    (∑ S : lowDegreeFourierFamily n k,
      ((exactDegreeFourierEstimatorOutput target k sampleInputs).coefficient S : ℝ) *
        monomial S.1 x) =
        ∑ S : lowDegreeFourierFamily n k,
          fourierCoeff target.toReal S.1 * monomial S.1 x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [exactDegreeFourierEstimatorOutput_coefficient_cast_eq
        target k hk hdegree sampleInputs hgood S]
    _ = ∑ S ∈ lowDegreeFourierFamily n k,
          fourierCoeff target.toReal S * monomial S x := by
      symm
      exact Finset.sum_subtype (lowDegreeFourierFamily n k)
        (fun S ↦ Iff.rfl) (fun S ↦ fourierCoeff target.toReal S * monomial S x)
    _ = ∑ S : Finset (Fin n), fourierCoeff target.toReal S * monomial S x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : k < S.card := by
        simpa using hS
      rw [(fourierDegree_le_iff target.toReal k).1 hdegree S hcard, zero_mul]
    _ = target.toReal x := (fourier_expansion target.toReal x).symm

/-- Exact recovery of the real expansion recovers the Boolean target pointwise. -/
theorem exactDegreeFourierEstimatorOutput_evaluate_eq
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : fourierDegree target.toReal ≤ k)
    (sampleInputs :
      lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n])
    (hgood : ∀ S : lowDegreeFourierFamily n k,
      sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target
        (lowDegreeFourierFamily n k) (degreeFourierCoefficientAccuracy k)
        (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
          (lowDegreeFourierFamily_nonempty n k)) S) :
    (exactDegreeFourierEstimatorOutput target k sampleInputs).evaluate = target := by
  rw [SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue,
    exactDegreeFourierEstimatorOutput_realValue_eq target k hk hdegree sampleInputs hgood]
  funext x
  apply signValue_injective
  rcases signValue_eq_neg_one_or_one (target x) with h | h <;>
    simp [BooleanFunction.toReal, h]

/-- Rounded sparse Fourier output computed from a matrix of labeled random examples. -/
noncomputable def exactDegreeFourierEstimatorLabeledOutput
    (n k : ℕ)
    (samples : lowDegreeFourierFamily n k →
      Fin (exactDegreeSamplesPerCoefficient n k) → ({−1,1}^[n] × Sign)) :
    SparseFourierHypothesis n :=
  SparseFourierHypothesis.ofCoefficients (lowDegreeFourierFamily n k) fun S ↦
    roundToDegreeFourierGranularity k (empiricalFourierCoeff S.1 (samples S))

/-- The random-example exact learner for sign functions of Fourier degree at most `k`. -/
noncomputable def exactDegreeFourierEstimatorProgram (n k : ℕ) :
    LearningProgram n .randomExamples (SparseFourierHypothesis n) :=
  .randomExampleMatrixOutput (lowDegreeFourierFamily n k)
    (exactDegreeSamplesPerCoefficient n k)
    ((lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k * (n + 1))
    (exactDegreeFourierEstimatorLabeledOutput n k)

/-- The exact learner is interpreted by the corresponding finite matrix-output law. -/
theorem runWithCost_exactDegreeFourierEstimatorProgram
    (target : BooleanFunction n) (k : ℕ) :
    LearningProgram.runWithCost target (exactDegreeFourierEstimatorProgram n k) =
      LearningProgram.randomExampleMatrixOutputLaw target
        (lowDegreeFourierFamily n k) (exactDegreeSamplesPerCoefficient n k)
        ((lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k * (n + 1))
        (exactDegreeFourierEstimatorLabeledOutput n k) := by
  rfl

/-- Every execution of the exact learner has the stated target-independent resource cost. -/
theorem exactDegreeFourierEstimatorProgram_cost_eq
    (target : BooleanFunction n) (k : ℕ)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (exactDegreeFourierEstimatorProgram n k)).support) :
    outcome.2 =
      ⟨(lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k, 0,
        (lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k +
          (lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k *
            (n + 1)⟩ := by
  rw [runWithCost_exactDegreeFourierEstimatorProgram] at houtcome
  unfold LearningProgram.randomExampleMatrixOutputLaw at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  rcases houtcome with ⟨sampleInputs, _, rfl⟩
  rfl

/-- Direct scheduler bound for the number of samples used to estimate one exact coefficient. -/
theorem exactDegreeSamplesPerCoefficient_cast_le (n k : ℕ) :
    (exactDegreeSamplesPerCoefficient n k : ℚ) ≤
      4 * fourierEstimatorFailureBits
        (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
          (lowDegreeFourierFamily_nonempty n k)) /
        (degreeFourierCoefficientAccuracy k).1 ^ 2 := by
  simpa [exactDegreeSamplesPerCoefficient] using fourierEstimatorSampleCount_cast_le
    (degreeFourierCoefficientAccuracy k)
    (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
      (lowDegreeFourierFamily_nonempty n k))

/-- With probability at least `9/10`, rounded empirical coefficients recover a bounded-degree
target exactly. -/
theorem measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : fourierDegree target.toReal ≤ k) :
    (LearningProgram.randomExampleMatrixInputLaw (lowDegreeFourierFamily n k)
      (exactDegreeSamplesPerCoefficient n k)).toMeasure.real
        {sampleInputs |
          (exactDegreeFourierEstimatorOutput target k sampleInputs).evaluate ≠ target} ≤
      (1 / 10 : ℝ) := by
  let failure : Set
      (lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n]) :=
    {sampleInputs |
      (exactDegreeFourierEstimatorOutput target k sampleInputs).evaluate ≠ target}
  have hsubset : failure ⊆
      ⋃ S : lowDegreeFourierFamily n k,
        finiteFamilyCoefficientBadSetWithParameters target (lowDegreeFourierFamily n k)
          (degreeFourierCoefficientAccuracy k)
          (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
            (lowDegreeFourierFamily_nonempty n k)) S := by
    intro sampleInputs hfailure
    by_contra hnotBad
    have hgood : ∀ S : lowDegreeFourierFamily n k,
        sampleInputs ∉ finiteFamilyCoefficientBadSetWithParameters target
          (lowDegreeFourierFamily n k) (degreeFourierCoefficientAccuracy k)
          (finiteFamilyCoefficientConfidence (lowDegreeFourierFamily n k)
            (lowDegreeFourierFamily_nonempty n k)) S := by
      intro S hbad
      exact hnotBad (Set.mem_iUnion.mpr ⟨S, hbad⟩)
    exact hfailure
      (exactDegreeFourierEstimatorOutput_evaluate_eq
        target k hk hdegree sampleInputs hgood)
  change (LearningProgram.randomExampleMatrixInputLaw (lowDegreeFourierFamily n k)
    (exactDegreeSamplesPerCoefficient n k)).toMeasure.real failure ≤ (1 / 10 : ℝ)
  exact (MeasureTheory.measureReal_mono hsubset).trans
    (measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth
      target (lowDegreeFourierFamily n k) (lowDegreeFourierFamily_nonempty n k)
      (degreeFourierCoefficientAccuracy k))

/-- The exact learner fails to return the target with probability at most `1/10`. -/
theorem exactDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    (hdegree : fourierDegree target.toReal ≤ k) :
    LearningProgram.eventProbability (exactDegreeFourierEstimatorProgram n k) target
        (fun outcome ↦ outcome.1.evaluate ≠ target) ≤ (1 / 10 : ℝ) := by
  unfold LearningProgram.eventProbability
  rw [runWithCost_exactDegreeFourierEstimatorProgram]
  rw [LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply]
  let failure : Set
      (lowDegreeFourierFamily n k → Fin (exactDegreeSamplesPerCoefficient n k) →
        {−1,1}^[n]) :=
    {sampleInputs |
      (exactDegreeFourierEstimatorOutput target k sampleInputs).evaluate ≠ target}
  have hpreimage :
      LearningProgram.randomExampleMatrixOutcome target (lowDegreeFourierFamily n k)
        (exactDegreeSamplesPerCoefficient n k)
        ((lowDegreeFourierFamily n k).card * exactDegreeSamplesPerCoefficient n k * (n + 1))
        (exactDegreeFourierEstimatorLabeledOutput n k) ⁻¹'
          {outcome | outcome.1.evaluate ≠ target} = failure := by
    rfl
  rw [hpreimage]
  have hmeasure :
      ((LearningProgram.randomExampleMatrixInputLaw (lowDegreeFourierFamily n k)
        (exactDegreeSamplesPerCoefficient n k)).toOuterMeasure failure).toReal =
        (LearningProgram.randomExampleMatrixInputLaw (lowDegreeFourierFamily n k)
          (exactDegreeSamplesPerCoefficient n k)).toMeasure.real failure := by
    exact congrArg ENNReal.toReal
      ((LearningProgram.randomExampleMatrixInputLaw (lowDegreeFourierFamily n k)
        (exactDegreeSamplesPerCoefficient n k)).toMeasure_apply_eq_toOuterMeasure
          failure).symm
  rw [hmeasure]
  exact measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth
    target k hk hdegree

/-- A Boolean target computed by a decision tree has Fourier degree at most the tree depth. -/
theorem fourierDegree_toReal_le_depth_of_decisionTree
    (target : BooleanFunction n) {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes fun x ↦ target.toReal (binaryCubeSignEquiv n x)) :
    fourierDegree target.toReal ≤ T.depth := by
  have hdegree := F₂DecisionTree.vectorFourierDegree_le_depth_of_computes
    T (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) hT
  have hbridge :
      binaryFunctionOnSignCube
          (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) =
        target.toReal := by
    funext x
    simp [binaryFunctionOnSignCube]
  simpa [vectorFourierDegree, hbridge] using hdegree

/-- Theorem 3.36: a decision tree of depth at most `k` is exactly learnable from random examples
with success probability at least `9/10`. -/
theorem exactDegreeFourierEstimatorProgram_of_decisionTree_failureProbability_le_one_tenth
    (target : BooleanFunction n) (k : ℕ) (hk : 1 ≤ k)
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes fun x ↦ target.toReal (binaryCubeSignEquiv n x))
    (hdepth : T.depth ≤ k) :
    LearningProgram.eventProbability (exactDegreeFourierEstimatorProgram n k) target
        (fun outcome ↦ outcome.1.evaluate ≠ target) ≤ (1 / 10 : ℝ) := by
  apply exactDegreeFourierEstimatorProgram_failureProbability_le_one_tenth target k hk
  exact (fourierDegree_toReal_le_depth_of_decisionTree target T hT).trans hdepth

end FABL
