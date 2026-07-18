/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.FourierCoefficientsOfMajority
import FABL.Chapter05.GaussianIsoperimetric
import FABL.Chapter05.RademacherFirstMoment

/-!
# Hamming-ball limits

Book items: Exercise 5.30 and Proposition 5.25.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal Topology

namespace FABL

variable {n : ℕ}

/-- The normalized sum of the coordinates of a sign-cube input. -/
noncomputable def normalizedRademacherSum
    (n : ℕ) (x : {−1,1}^[n]) : ℝ :=
  linearForm (fun _ ↦ (Real.sqrt (n : ℝ))⁻¹) x

/-- The real indicator of the strict upper level set of the normalized
Rademacher sum. -/
noncomputable def hammingUpperTailIndicator
    (t : ℝ) (n : ℕ) (x : {−1,1}^[n]) : ℝ :=
  if t < normalizedRademacherSum n x then 1 else 0

private noncomputable def normalizedRademacherCoefficient (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

private theorem normalizedRademacherCoefficient_nonneg (n : ℕ) :
    0 ≤ normalizedRademacherCoefficient n := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem normalizedRademacherSum_eq_linearForm (n : ℕ) :
    normalizedRademacherSum n =
      linearForm (fun _ ↦ normalizedRademacherCoefficient n) := by
  rfl

private theorem normalizedRademacherSum_permuteInput
    (π : Equiv.Perm (Fin n)) (x : {−1,1}^[n]) :
    normalizedRademacherSum n (permuteInput π x) =
      normalizedRademacherSum n x := by
  unfold normalizedRademacherSum linearForm permuteInput
  exact Equiv.sum_comp π
    (fun i ↦ (Real.sqrt (n : ℝ))⁻¹ * signValue (x i))

private theorem signValue_neg_hammingBall (s : Sign) :
    signValue (-s) = -signValue s := by
  rcases Int.units_eq_one_or s with hs | hs <;> simp [hs, signValue]

private theorem normalizedRademacherSum_neg
    (x : {−1,1}^[n]) :
    normalizedRademacherSum n (-x) =
      -normalizedRademacherSum n x := by
  unfold normalizedRademacherSum linearForm
  simp only [Pi.neg_apply, signValue_neg_hammingBall, mul_neg,
    Finset.sum_neg_distrib]

/-- The Hamming upper-tail indicator is invariant under coordinate
permutations. -/
theorem hammingUpperTailIndicator_isSymmetric (t : ℝ) (n : ℕ) :
    IsSymmetric (hammingUpperTailIndicator t n) := by
  intro π x
  unfold hammingUpperTailIndicator
  rw [normalizedRademacherSum_permuteInput]

private theorem expect_mul_linearForm_eq_singletonCoeffs
    (f : {−1,1}^[n] → ℝ) (a : Fin n → ℝ) :
    (𝔼 x, f x * linearForm a x) =
      ∑ i, a i * fourierCoeff f {i} := by
  rw [show
      (fun x : {−1,1}^[n] ↦ f x * linearForm a x) =
        fun x ↦ ∑ i, a i * (f x * monomial {i} x) by
    funext x
    rw [linearForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [monomial]
    ring]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_expect]
  rfl

private theorem sum_normalizedRademacherCoefficient_sq (m : ℕ) :
    ∑ _i : Fin (m + 1), normalizedRademacherCoefficient (m + 1) ^ 2 = 1 := by
  have hN : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ _i : Fin (m + 1),
        normalizedRademacherCoefficient (m + 1) ^ 2) =
        ((m + 1 : ℕ) : ℝ) *
          normalizedRademacherCoefficient (m + 1) ^ 2 := by
            simp
    _ = ((m + 1 : ℕ) : ℝ) /
          Real.sqrt (((m + 1 : ℕ) : ℝ)) ^ 2 := by
            rw [normalizedRademacherCoefficient, inv_pow]
            rfl
    _ = ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          rw [Real.sq_sqrt hN.le]
    _ = 1 := div_self hN.ne'

/-- Exercise 5.30: every singleton Fourier coefficient of the Hamming
upper-tail indicator is the normalized truncated first moment. -/
theorem fourierCoeff_hammingUpperTailIndicator_singleton
    (t : ℝ) (m : ℕ) (i : Fin (m + 1)) :
    fourierCoeff (hammingUpperTailIndicator t (m + 1)) {i} =
      (𝔼 x : {−1,1}^[m + 1],
          hammingUpperTailIndicator t (m + 1) x *
            normalizedRademacherSum (m + 1) x) /
        Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
  let f : {−1,1}^[m + 1] → ℝ :=
    hammingUpperTailIndicator t (m + 1)
  let c : ℝ := fourierCoeff f {i}
  let r : ℝ := Real.sqrt (((m + 1 : ℕ) : ℝ))
  have hN : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hr : 0 < r := Real.sqrt_pos.2 hN
  have hcoeff (j : Fin (m + 1)) :
      fourierCoeff f {j} = c := by
    exact fourierCoeff_eq_of_card_eq_of_isSymmetric
      (hammingUpperTailIndicator_isSymmetric t (m + 1))
      (by simp)
  have hmoment :
      (𝔼 x : {−1,1}^[m + 1],
          f x * normalizedRademacherSum (m + 1) x) =
        r * c := by
    rw [normalizedRademacherSum_eq_linearForm,
      expect_mul_linearForm_eq_singletonCoeffs]
    calc
      (∑ j : Fin (m + 1),
          normalizedRademacherCoefficient (m + 1) *
            fourierCoeff f {j}) =
          ∑ _j : Fin (m + 1),
            normalizedRademacherCoefficient (m + 1) * c := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hcoeff j]
      _ = ((m + 1 : ℕ) : ℝ) *
          normalizedRademacherCoefficient (m + 1) * c := by
            simp
            ring
      _ = r * c := by
        have hrSq : r ^ 2 = ((m + 1 : ℕ) : ℝ) :=
          Real.sq_sqrt hN.le
        rw [normalizedRademacherCoefficient]
        change ((m + 1 : ℕ) : ℝ) * r⁻¹ * c = r * c
        rw [← hrSq]
        field_simp [hr.ne']
  change c =
    (𝔼 x : {−1,1}^[m + 1],
      f x * normalizedRademacherSum (m + 1) x) / r
  rw [hmoment]
  exact (mul_div_cancel_left₀ c hr.ne').symm

/-- Exercise 5.30: the level-one Fourier weight of the Hamming upper-tail
indicator is the square of its truncated first moment. -/
theorem fourierWeightAtLevel_one_hammingUpperTailIndicator
    (t : ℝ) (m : ℕ) :
    fourierWeightAtLevel 1 (hammingUpperTailIndicator t (m + 1)) =
      (𝔼 x : {−1,1}^[m + 1],
          hammingUpperTailIndicator t (m + 1) x *
            normalizedRademacherSum (m + 1) x) ^ 2 := by
  let M : ℝ :=
    𝔼 x : {−1,1}^[m + 1],
      hammingUpperTailIndicator t (m + 1) x *
        normalizedRademacherSum (m + 1) x
  have hN : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hr : 0 < Real.sqrt (((m + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hN
  rw [fourierWeightAtLevel_one_eq_sum_singleton]
  simp_rw [fourierCoeff_hammingUpperTailIndicator_singleton]
  change (∑ _i : Fin (m + 1),
      (M / Real.sqrt (((m + 1 : ℕ) : ℝ))) ^ 2) = M ^ 2
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hr.ne']
  nlinarith [Real.sq_sqrt hN.le]

local instance hammingBallSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance hammingBallSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

private noncomputable def hammingBallRademacherMeasure (n : ℕ) :
    Measure {−1,1}^[n] :=
  (uniformPMF {−1,1}^[n]).toMeasure

private instance hammingBallRademacherMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (hammingBallRademacherMeasure n) := by
  unfold hammingBallRademacherMeasure
  infer_instance

private noncomputable def hammingBallRademacherSummand
    (n : ℕ) (i : Fin n) (x : {−1,1}^[n]) : ℝ :=
  normalizedRademacherCoefficient n * signValue (x i)

private theorem sum_hammingBallRademacherSummand
    (n : ℕ) (x : {−1,1}^[n]) :
    ∑ i, hammingBallRademacherSummand n i x =
      normalizedRademacherSum n x := by
  rfl

private theorem hammingBallRademacherMeasure_eq_pi :
    hammingBallRademacherMeasure n =
      Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure := by
  exact uniformSample_toMeasure_eq_pi Sign n

private theorem integral_hammingBallSignCoordinate_eq_zero (i : Fin n) :
    ∫ x, signValue (x i) ∂hammingBallRademacherMeasure n = 0 := by
  rw [hammingBallRademacherMeasure, integral_uniformPMF_eq_expect]
  have hmonomial :
      (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} := by
    funext x
    simp [monomial]
  rw [hmonomial, expect_monomial]
  simp

private theorem integral_hammingBallRademacherSummand_eq_zero
    (n : ℕ) (i : Fin n) :
    ∫ x, hammingBallRademacherSummand n i x
        ∂hammingBallRademacherMeasure n = 0 := by
  simp only [hammingBallRademacherSummand, integral_const_mul,
    integral_hammingBallSignCoordinate_eq_zero, mul_zero]

private theorem hammingBallRademacherSummands_iIndep (n : ℕ) :
    iIndepFun (hammingBallRademacherSummand n)
      (hammingBallRademacherMeasure n) := by
  rw [hammingBallRademacherMeasure_eq_pi]
  change iIndepFun
    (fun i x ↦
      (fun s : Sign ↦ normalizedRademacherCoefficient n * signValue s) (x i))
    (Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure)
  exact iIndepFun_pi fun i ↦
    (measurable_of_finite fun s : Sign ↦
      normalizedRademacherCoefficient n * signValue s).aemeasurable

private theorem hammingBallRademacherSummand_memLp
    (n : ℕ) (i : Fin n) (p : ℝ≥0∞) :
    MemLp (hammingBallRademacherSummand n i) p
      (hammingBallRademacherMeasure n) := by
  refine MemLp.of_bound
    (measurable_of_finite
      (hammingBallRademacherSummand n i)).aestronglyMeasurable
    (normalizedRademacherCoefficient n)
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, hammingBallRademacherSummand, abs_mul]
  rcases signValue_eq_neg_one_or_one (x i) with h | h <;>
    simp [h, abs_of_nonneg (normalizedRademacherCoefficient_nonneg n)]

private theorem variance_hammingBallRademacherSummand
    (n : ℕ) (i : Fin n) :
    ProbabilityTheory.variance (hammingBallRademacherSummand n i)
        (hammingBallRademacherMeasure n) =
      normalizedRademacherCoefficient n ^ 2 := by
  rw [variance_of_integral_eq_zero
    (measurable_of_finite
      (hammingBallRademacherSummand n i)).aemeasurable
    (integral_hammingBallRademacherSummand_eq_zero n i)]
  rw [hammingBallRademacherMeasure, integral_uniformPMF_eq_expect]
  rw [show
      (fun x : {−1,1}^[n] ↦
        hammingBallRademacherSummand n i x ^ 2) =
        fun _ ↦ normalizedRademacherCoefficient n ^ 2 by
    funext x
    rw [hammingBallRademacherSummand]
    rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]]
  exact Fintype.expect_const _

private theorem hammingBallUniformMeasure_real_event
    (P : {−1,1}^[n] → Prop) [DecidablePred P] :
    (hammingBallRademacherMeasure n).real {x | P x} =
      uniformProbability P := by
  rw [← integral_indicator_one (Set.toFinite {x | P x}).measurableSet]
  rw [hammingBallRademacherMeasure, integral_uniformPMF_eq_expect,
    uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

private theorem expect_hammingUpperTailIndicator_eq_uniformProbability
    (t : ℝ) (n : ℕ) :
    (𝔼 x : {−1,1}^[n], hammingUpperTailIndicator t n x) =
      uniformProbability
        (fun x : {−1,1}^[n] ↦ t < normalizedRademacherSum n x) := by
  unfold hammingUpperTailIndicator uniformProbability
  rfl

/-- The uniform Berry--Esseen bound for the upper level set of a normalized
equal-weight Rademacher sum. -/
theorem abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le
    (t : ℝ) (m : ℕ) :
    |(𝔼 x : {−1,1}^[m + 1],
        hammingUpperTailIndicator t (m + 1) x) -
        standardGaussianUpperTail t| ≤
      2 * thirdMomentBerryEsseenConstant *
        (Real.sqrt (((m + 1 : ℕ) : ℝ)))⁻¹ := by
  change
    |(𝔼 x : {−1,1}^[m + 1],
        hammingUpperTailIndicator t (m + 1) x) -
        standardGaussianUpperTail t| ≤
      2 * thirdMomentBerryEsseenConstant *
        normalizedRademacherCoefficient (m + 1)
  let μ : Measure {−1,1}^[m + 1] :=
    hammingBallRademacherMeasure (m + 1)
  let X : Fin (m + 1) → {−1,1}^[m + 1] → ℝ :=
    hammingBallRademacherSummand (m + 1)
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_of_finite (X i)
  have hX2 : ∀ i, MemLp (X i) 2 μ := by
    intro i
    simpa only [X, μ] using
      hammingBallRademacherSummand_memLp (m + 1) i 2
  have hXindep : iIndepFun X μ := by
    simpa only [X, μ] using
      hammingBallRademacherSummands_iIndep (m + 1)
  have hXmean : ∀ i, ∫ x, X i x ∂μ = 0 := by
    intro i
    simpa only [X, μ] using
      integral_hammingBallRademacherSummand_eq_zero (m + 1) i
  have hvar : ∑ i, ProbabilityTheory.variance (X i) μ = 1 := by
    simpa only [X, μ, variance_hammingBallRademacherSummand] using
      sum_normalizedRademacherCoefficient_sq m
  have hX3 : ∀ i, Integrable (fun x ↦ |X i x| ^ 3) μ := by
    intro i
    exact Integrable.of_finite
  have hthird :
      thirdMomentSum X μ ≤
        normalizedRademacherCoefficient (m + 1) := by
    apply sum_integral_abs_cube_le_of_ae_abs_le X μ hX2 hXmean hvar
    intro i
    exact ae_of_all _ fun x ↦ by
      dsimp only [X, hammingBallRademacherSummand]
      rw [abs_mul]
      rcases signValue_eq_neg_one_or_one (x i) with h | h <;>
        simp [h,
          abs_of_nonneg
            (normalizedRademacherCoefficient_nonneg (m + 1))]
  have hinterval :=
    exercise5_16_interval hX2 hXmeas hXindep hXmean hvar hX3
      (.above false t)
  have hmap :
      (μ.map (sumX X)).real (Ioi t) =
        uniformProbability
          (fun x : {−1,1}^[m + 1] ↦
            t < normalizedRademacherSum (m + 1) x) := by
    rw [map_measureReal_apply (measurable_sumX hXmeas) measurableSet_Ioi]
    change (hammingBallRademacherMeasure (m + 1)).real
        {x | t < normalizedRademacherSum (m + 1) x} = _
    exact hammingBallUniformMeasure_real_event _
  have hbound :
      |(μ.map (sumX X)).real (Ioi t) -
          (gaussianReal 0 1).real (Ioi t)| ≤
        2 * thirdMomentBerryEsseenConstant *
          normalizedRademacherCoefficient (m + 1) := by
    exact hinterval.trans <|
      mul_le_mul_of_nonneg_left hthird
        (mul_nonneg (by norm_num)
          thirdMomentBerryEsseenConstant_pos.le)
  rw [hmap, ← standardGaussianUpperTail_eq_measureReal_Ioi,
    ← expect_hammingUpperTailIndicator_eq_uniformProbability] at hbound
  exact hbound

private theorem tendsto_normalizedRademacherCoefficient_succ :
    Tendsto (fun m : ℕ ↦ normalizedRademacherCoefficient (m + 1))
      atTop (𝓝 0) := by
  have hbase :
      Tendsto normalizedRademacherCoefficient atTop (𝓝 0) := by
    unfold normalizedRademacherCoefficient
    exact tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact hbase.comp (tendsto_add_atTop_nat 1)

/-- Exercise 5.30: the expectations of the Hamming upper-tail indicators
converge to the corresponding standard Gaussian upper tail. -/
theorem tendsto_expect_hammingUpperTailIndicator (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          hammingUpperTailIndicator t (m + 1) x)
      atTop (𝓝 (standardGaussianUpperTail t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero
  · intro m
    exact dist_nonneg
  · intro m
    simpa only [Real.dist_eq] using
      abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le
        t m
  · simpa only [normalizedRademacherCoefficient, mul_zero] using
      tendsto_normalizedRademacherCoefficient_succ.const_mul
        (2 * thirdMomentBerryEsseenConstant)

private theorem expect_normalizedRademacherSum_eq_zero (n : ℕ) :
    (𝔼 x : {−1,1}^[n], normalizedRademacherSum n x) = 0 := by
  have hneg :
      (𝔼 x : {−1,1}^[n], normalizedRademacherSum n (-x)) =
        𝔼 x : {−1,1}^[n], normalizedRademacherSum n x := by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    rfl
  rw [show
      (fun x : {−1,1}^[n] ↦ normalizedRademacherSum n (-x)) =
        fun x ↦ -normalizedRademacherSum n x by
      funext x
      rw [normalizedRademacherSum_neg],
    Finset.expect_neg_distrib] at hneg
  linarith

private theorem posPart_eq_self_add_neg_posPart (u : ℝ) :
    u⁺ = u + (-u)⁺ := by
  by_cases hu : 0 ≤ u
  · simp [PosPart.posPart, hu]
  · have hu' : u ≤ 0 := le_of_not_ge hu
    simp [PosPart.posPart, hu']

private theorem expect_normalizedRademacherStopLoss_reflection
    (t : ℝ) (n : ℕ) :
    (𝔼 x : {−1,1}^[n], (normalizedRademacherSum n x - t)⁺) =
      -t +
        𝔼 x : {−1,1}^[n],
          (normalizedRademacherSum n x - (-t))⁺ := by
  have hreflect :
      (𝔼 x : {−1,1}^[n], (t - normalizedRademacherSum n x)⁺) =
        𝔼 x : {−1,1}^[n],
          (normalizedRademacherSum n x - (-t))⁺ := by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    rw [Equiv.neg_apply, normalizedRademacherSum_neg]
    congr 1
    ring
  rw [show
      (fun x : {−1,1}^[n] ↦
        (normalizedRademacherSum n x - t)⁺) =
        fun x ↦
          (normalizedRademacherSum n x - t) +
            (t - normalizedRademacherSum n x)⁺ by
      funext x
      simpa only [neg_sub] using
        posPart_eq_self_add_neg_posPart
          (normalizedRademacherSum n x - t),
    Finset.expect_add_distrib, Finset.expect_sub_distrib,
    Fintype.expect_const, expect_normalizedRademacherSum_eq_zero,
    hreflect]
  ring

private theorem gaussianPDFReal_zero_one_neg (t : ℝ) :
    gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, neg_sq]

private theorem standardGaussianStopLoss_reflection (t : ℝ) :
    standardGaussianStopLoss t =
      -t + standardGaussianStopLoss (-t) := by
  rw [standardGaussianStopLoss_eq, standardGaussianStopLoss_eq,
    gaussianPDFReal_zero_one_neg, standardGaussianUpperTail_neg]
  ring

private theorem exists_normalizedRademacherStopLoss_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (t : ℝ),
        |(𝔼 x : {−1,1}^[m + 1],
            (normalizedRademacherSum (m + 1) x - t)⁺) -
            standardGaussianStopLoss t| ≤
          C * normalizedRademacherCoefficient (m + 1) := by
  obtain ⟨C, hC, hstop⟩ :=
    exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular
  refine ⟨C, hC, ?_⟩
  intro m t
  have hnormalized :
      ∑ _i : Fin (m + 1),
          normalizedRademacherCoefficient (m + 1) ^ 2 = 1 :=
    sum_normalizedRademacherCoefficient_sq m
  have hregular :
      ∀ _i : Fin (m + 1),
        |normalizedRademacherCoefficient (m + 1)| ≤
          normalizedRademacherCoefficient (m + 1) := by
    intro i
    rw [abs_of_nonneg
      (normalizedRademacherCoefficient_nonneg (m + 1))]
  by_cases ht : 0 ≤ t
  · change
      |(𝔼 x : {−1,1}^[m + 1],
          (linearForm
              (fun _ ↦ normalizedRademacherCoefficient (m + 1)) x -
            t)⁺) -
          ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1| ≤
        C * normalizedRademacherCoefficient (m + 1)
    exact hstop
      (fun _ ↦ normalizedRademacherCoefficient (m + 1))
      hnormalized hregular ht
  · have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hpositive :=
      hstop
        (fun _ : Fin (m + 1) ↦
          normalizedRademacherCoefficient (m + 1))
        hnormalized hregular hneg
    change
      |(𝔼 x : {−1,1}^[m + 1],
          (normalizedRademacherSum (m + 1) x - (-t))⁺) -
          standardGaussianStopLoss (-t)| ≤
        C * normalizedRademacherCoefficient (m + 1) at hpositive
    rw [expect_normalizedRademacherStopLoss_reflection,
      standardGaussianStopLoss_reflection]
    simpa only [add_sub_add_left_eq_sub] using hpositive

private theorem tendsto_expect_normalizedRademacherStopLoss (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          (normalizedRademacherSum (m + 1) x - t)⁺)
      atTop (𝓝 (standardGaussianStopLoss t)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalizedRademacherStopLoss_bound
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero
  · intro m
    exact dist_nonneg
  · intro m
    simpa only [Real.dist_eq] using hbound m t
  · simpa only [mul_zero] using
      tendsto_normalizedRademacherCoefficient_succ.const_mul C

private theorem hammingUpperTailIndicator_mul_normalizedRademacherSum
    (t : ℝ) (n : ℕ) (x : {−1,1}^[n]) :
    hammingUpperTailIndicator t n x * normalizedRademacherSum n x =
      (normalizedRademacherSum n x - t)⁺ +
        t * hammingUpperTailIndicator t n x := by
  by_cases hx : t < normalizedRademacherSum n x
  · simp [hammingUpperTailIndicator, hx, PosPart.posPart,
      sub_nonneg.mpr hx.le]
  · have hx' : normalizedRademacherSum n x ≤ t := le_of_not_gt hx
    simp [hammingUpperTailIndicator, hx, PosPart.posPart,
      sub_nonpos.mpr hx']

private theorem expect_hammingUpperTailIndicator_mul_normalizedRademacherSum
    (t : ℝ) (n : ℕ) :
    (𝔼 x : {−1,1}^[n],
        hammingUpperTailIndicator t n x *
          normalizedRademacherSum n x) =
      (𝔼 x : {−1,1}^[n],
          (normalizedRademacherSum n x - t)⁺) +
        t * (𝔼 x : {−1,1}^[n],
          hammingUpperTailIndicator t n x) := by
  rw [show
      (fun x : {−1,1}^[n] ↦
        hammingUpperTailIndicator t n x *
          normalizedRademacherSum n x) =
        fun x ↦
          (normalizedRademacherSum n x - t)⁺ +
            t * hammingUpperTailIndicator t n x by
      funext x
      exact
        hammingUpperTailIndicator_mul_normalizedRademacherSum t n x,
    Finset.expect_add_distrib, ← Finset.mul_expect]

/-- Exercise 5.30: the truncated first moment of the normalized Rademacher
sum converges to the standard Gaussian density at the threshold. -/
theorem
    tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum
    (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          hammingUpperTailIndicator t (m + 1) x *
            normalizedRademacherSum (m + 1) x)
      atTop (𝓝 (gaussianPDFReal 0 1 t)) := by
  have hsum :=
    (tendsto_expect_normalizedRademacherStopLoss t).add
      ((tendsto_expect_hammingUpperTailIndicator t).const_mul t)
  rw [show
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          hammingUpperTailIndicator t (m + 1) x *
            normalizedRademacherSum (m + 1) x) =
        fun m ↦
          (𝔼 x : {−1,1}^[m + 1],
            (normalizedRademacherSum (m + 1) x - t)⁺) +
          t * (𝔼 x : {−1,1}^[m + 1],
            hammingUpperTailIndicator t (m + 1) x) by
      funext m
      exact
        expect_hammingUpperTailIndicator_mul_normalizedRademacherSum
          t (m + 1)]
  rw [standardGaussianStopLoss_eq] at hsum
  simpa only [sub_add_cancel] using hsum

private theorem tendsto_fourierWeightAtLevel_one_hammingUpperTailIndicator
    (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        fourierWeightAtLevel 1
          (hammingUpperTailIndicator t (m + 1)))
      atTop (𝓝 (gaussianPDFReal 0 1 t ^ 2)) := by
  have hmoment :=
    tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum t
  have hsquare := hmoment.pow 2
  simpa only [
    fourierWeightAtLevel_one_hammingUpperTailIndicator] using hsquare

/-- O'Donnell, Proposition 5.25: Hamming upper-tail indicators converge in
expectation to the Gaussian upper tail, and their level-one Fourier weights
converge to the squared Gaussian density. -/
theorem proposition5_25 (t : ℝ) :
    Tendsto
        (fun m : ℕ ↦
          𝔼 x : {−1,1}^[m + 1],
            hammingUpperTailIndicator t (m + 1) x)
        atTop (𝓝 (standardGaussianUpperTail t)) ∧
      Tendsto
        (fun m : ℕ ↦
          fourierWeightAtLevel 1
            (hammingUpperTailIndicator t (m + 1)))
        atTop (𝓝 (gaussianPDFReal 0 1 t ^ 2)) := by
  exact ⟨tendsto_expect_hammingUpperTailIndicator t,
    tendsto_fourierWeightAtLevel_one_hammingUpperTailIndicator t⟩

end FABL
