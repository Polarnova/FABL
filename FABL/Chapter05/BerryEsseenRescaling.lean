/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Centering and rescaling Berry--Esseen

Book item: Exercise 5.17.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace FABL

/-- O'Donnell, Exercise 5.17: the uniform third-moment Berry--Esseen estimate for
independent summands with arbitrary finite means and positive total variance. -/
theorem exercise5_17
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hXmeas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (h3 : ∀ i, Integrable
      (fun ω ↦ |X i ω - ∫ ω, X i ω ∂μ| ^ 3) μ)
    (hvariance : 0 < ∑ i, variance (X i) μ)
    (x : ℝ) :
    |cdf (μ.map (sumX X)) x -
      cdf
        (gaussianReal
          (∑ i, ∫ ω, X i ω ∂μ)
          ⟨∑ i, variance (X i) μ, hvariance.le⟩) x| ≤
      thirdMomentBerryEsseenConstant *
        (∑ i, ∫ ω, |X i ω - ∫ ω, X i ω ∂μ| ^ 3 ∂μ) /
          Real.sqrt (∑ i, variance (X i) μ) ^ 3 := by
  classical
  let m : ι → ℝ := fun i ↦ ∫ ω, X i ω ∂μ
  let v : ℝ := ∑ i, variance (X i) μ
  let σ : ℝ := Real.sqrt v
  let Y : ι → Ω → ℝ := fun i ω ↦ (X i ω - m i) / σ
  let M : ℝ := ∑ i, m i
  have hv : 0 < v := by
    simpa only [v] using hvariance
  have hσ : 0 < σ := by
    exact Real.sqrt_pos.2 hv
  have hσne : σ ≠ 0 := hσ.ne'
  have hσsq : σ ^ 2 = v := by
    exact Real.sq_sqrt hv.le
  have hY : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    simpa only [Y, Pi.sub_apply, div_eq_inv_mul] using
      (((hX i).sub (memLp_const (m i))).const_mul σ⁻¹)
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    exact (hXmeas i).sub_const (m i) |>.div_const σ
  have hYindep : iIndepFun Y μ := by
    change iIndepFun (fun i ↦ (fun z ↦ (z - m i) / σ) ∘ X i) μ
    exact h_indep.comp (fun i z ↦ (z - m i) / σ) fun _ ↦ by fun_prop
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [show Y i = fun ω ↦ (X i ω - m i) / σ by rfl, integral_div,
      integral_sub ((hX i).integrable one_le_two) (integrable_const (m i)),
      integral_const]
    simp [m]
  have hYvariance : ∑ i, variance (Y i) μ = 1 := by
    have hvariance_each (i : ι) :
        variance (Y i) μ = σ⁻¹ ^ 2 * variance (X i) μ := by
      rw [show Y i = fun ω ↦ σ⁻¹ * (X i ω - m i) by
        funext ω
        simp only [Y, div_eq_mul_inv, mul_comm]]
      rw [variance_const_mul, variance_sub_const (hXmeas i).aestronglyMeasurable]
    simp_rw [hvariance_each]
    rw [← mul_sum]
    change σ⁻¹ ^ 2 * v = 1
    rw [← hσsq]
    field_simp
  have hY3 : ∀ i, Integrable (fun ω ↦ |Y i ω| ^ 3) μ := by
    intro i
    have hi := (h3 i).div_const (σ ^ 3)
    simpa only [Y, abs_div, abs_of_pos hσ, div_pow] using hi
  have hBE :=
    uniformBerryEsseen_thirdMoment hY hYmeas hYindep hYmean hYvariance hY3
      ((x - M) / σ)
  have hsumY (ω : Ω) : sumX Y ω = (sumX X ω - M) / σ := by
    change (∑ i, (X i ω - m i) / σ) =
      (∑ i, X i ω - ∑ i, m i) / σ
    rw [← sum_div, sum_sub_distrib]
  letI : IsProbabilityMeasure (μ.map (sumX Y)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := Y)
      fun i ↦ (hYmeas i).aemeasurable
  letI : IsProbabilityMeasure (μ.map (sumX X)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X)
      fun i ↦ (hXmeas i).aemeasurable
  have hcdfSum :
      cdf (μ.map (sumX Y)) ((x - M) / σ) =
        cdf (μ.map (sumX X)) x := by
    rw [cdf_eq_real, cdf_eq_real,
      map_measureReal_apply (measurable_sumX hYmeas) measurableSet_Iic,
      map_measureReal_apply (measurable_sumX hXmeas) measurableSet_Iic]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, hsumY]
    rw [div_le_div_iff_of_pos_right hσ]
    exact sub_le_sub_iff_right M
  have hgaussianMap :
      (gaussianReal 0 1).map (fun z : ℝ ↦ σ * z + M) =
        gaussianReal M ⟨v, hv.le⟩ := by
    rw [show (fun z : ℝ ↦ σ * z + M) = (fun z ↦ z + M) ∘ (fun z ↦ σ * z) by
      funext z
      rfl]
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, gaussianReal_map_add_const]
    simp only [mul_zero, zero_add, mul_one]
    congr 1
    ext
    exact hσsq
  letI : IsProbabilityMeasure
      ((gaussianReal 0 1).map (fun z : ℝ ↦ σ * z + M)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcdfGaussian :
      cdf (gaussianReal 0 1) ((x - M) / σ) =
        cdf (gaussianReal M ⟨v, hv.le⟩) x := by
    rw [← hgaussianMap, cdf_eq_real, cdf_eq_real,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hz
      have := (le_div_iff₀ hσ).1 hz
      nlinarith
    · intro hz
      exact (le_div_iff₀ hσ).2 (by nlinarith)
  have hthird :
      thirdMomentSum (X := Y) μ =
        (∑ i, ∫ ω, |X i ω - m i| ^ 3 ∂μ) / σ ^ 3 := by
    simp only [thirdMomentSum, Y, abs_div, abs_of_pos hσ, div_pow, integral_div,
      sum_div]
  change
    |cdf (μ.map (sumX Y)) ((x - M) / σ) -
        cdf (gaussianReal 0 1) ((x - M) / σ)| ≤
      thirdMomentBerryEsseenConstant * thirdMomentSum (X := Y) μ at hBE
  rw [hcdfSum, hcdfGaussian, hthird, ← mul_div_assoc] at hBE
  simpa only [M, m, v, σ] using hBE

end FABL
