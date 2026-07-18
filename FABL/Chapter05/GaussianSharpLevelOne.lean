/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.GaussianIsoperimetric
import FABL.Chapter05.RademacherFirstMoment

/-!
# A Gaussian-sharp Level-1 bound

Book item: Exercise 5.44, with the printed codomain corrected to `[0,1]`.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube

namespace FABL

variable {n : ℕ}

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

private theorem mul_le_threshold_add_posPart
    {r y t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * y ≤ t * r + (y - t)⁺ := by
  by_cases hy : y ≤ t
  · have hproduct : 0 ≤ r * (t - y) :=
      mul_nonneg hr0 (sub_nonneg.mpr hy)
    simp only [PosPart.posPart, max_eq_right (sub_nonpos.mpr hy)]
    nlinarith
  · have hty : t ≤ y := le_of_not_ge hy
    have hproduct : 0 ≤ (1 - r) * (y - t) :=
      mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hty)
    simp only [PosPart.posPart, max_eq_left (sub_nonneg.mpr hty)]
    nlinarith

/-- O'Donnell, Exercise 5.44, with the printed codomain corrected from
`[-1,1]` to `[0,1]`: bounded nonnegative functions with small singleton
coefficients have Gaussian-sharp Level-1 Fourier weight. -/
theorem exercise5_44
    (α : ℝ) (hαpos : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ {n : ℕ} (f : {−1,1}^[n] → ℝ) {ε : ℝ},
        (∀ x, 0 ≤ f x) →
        (∀ x, f x ≤ 1) →
        (𝔼 x, f x) ≤ α →
        (∀ i, |fourierCoeff f {i}| ≤ ε) →
        0 ≤ ε →
        fourierWeightAtLevel 1 f ≤
          gaussianIsoperimetric
              ⟨α, hαpos.le, by linarith⟩ ^ 2 +
            Cα * ε := by
  obtain ⟨C, hC, hstop⟩ :=
    exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n f ε hf0 hf1 hmean hregular hε
  let αUnit : unitInterval :=
    ⟨α, hαpos.le, by linarith⟩
  let αOpen : Ioo (0 : ℝ) 1 :=
    ⟨α, hαpos, by linarith⟩
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f {i}
  let W : ℝ := fourierWeightAtLevel 1 f
  let U : ℝ := gaussianIsoperimetric αUnit
  change W ≤ U ^ 2 + (2 * C) * ε
  have haSum : ∑ i, a i ^ 2 = W := by
    exact (fourierWeightAtLevel_one_eq_sum_singleton f).symm
  have hWnonneg : 0 ≤ W := by
    rw [← haSum]
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (a i)
  have hUnonneg : 0 ≤ U := by
    exact (gaussianIsoperimetric_mem_Icc αUnit).1
  by_cases hWzero : W = 0
  · rw [hWzero]
    positivity
  · have hWpos : 0 < W :=
      lt_of_le_of_ne hWnonneg (Ne.symm hWzero)
    let σ : ℝ := Real.sqrt W
    let b : Fin n → ℝ := fun i ↦ a i / σ
    let t : ℝ := standardGaussianUpperQuantile αOpen
    have hσpos : 0 < σ := Real.sqrt_pos.2 hWpos
    have hσsq : σ ^ 2 = W := Real.sq_sqrt hWnonneg
    have hbNormalized : ∑ i, b i ^ 2 = 1 := by
      calc
        (∑ i, b i ^ 2) = (∑ i, a i ^ 2) / σ ^ 2 := by
          simp_rw [b, div_pow]
          exact
            (Finset.sum_div Finset.univ
              (fun i ↦ a i ^ 2) (σ ^ 2)).symm
        _ = W / σ ^ 2 := by rw [haSum]
        _ = 1 := by
          rw [hσsq, div_self hWzero]
    have hbRegular : ∀ i, |b i| ≤ ε / σ := by
      intro i
      dsimp only [b]
      rw [abs_div, abs_of_pos hσpos]
      exact div_le_div_of_nonneg_right (hregular i) hσpos.le
    have htailZero : standardGaussianUpperTail 0 = 1 / 2 := by
      have hreflection := standardGaussianUpperTail_neg 0
      norm_num at hreflection ⊢
      linarith
    have htailQuantile :
        standardGaussianUpperTail t = α := by
      simpa only [t, αOpen] using
        standardGaussianUpperTail_quantile αOpen
    have htpos : 0 < t := by
      by_contra ht
      have htle : t ≤ 0 := le_of_not_gt ht
      have hanti :=
        standardGaussianUpperTail_strictAnti.antitone htle
      rw [htailZero, htailQuantile] at hanti
      linarith
    have hUformula :
        U = gaussianPDFReal 0 1 t := by
      simpa only [U, t, αUnit, αOpen] using
        gaussianIsoperimetric_apply_of_mem_Ioo αUnit
          (show (αUnit : ℝ) ∈ Ioo (0 : ℝ) 1 by
            exact ⟨hαpos, by linarith⟩)
    have hGaussianStopLoss :
        standardGaussianStopLoss t = U - t * α := by
      calc
        standardGaussianStopLoss t =
            gaussianPDFReal 0 1 t -
              t * standardGaussianUpperTail t :=
          standardGaussianStopLoss_eq t
        _ = U - t * α := by
          rw [← hUformula, htailQuantile]
    have hstopBound :
        |(𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺) -
            standardGaussianStopLoss t| ≤
          C * (ε / σ) := by
      change
        |(𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺) -
            ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1| ≤
          C * (ε / σ)
      exact hstop b hbNormalized hbRegular htpos.le
    have hstopUpper :
        (𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺) ≤
          standardGaussianStopLoss t + C * (ε / σ) := by
      linarith [le_abs_self
        ((𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺) -
          standardGaussianStopLoss t)]
    have hinner :
        (𝔼 x : {−1,1}^[n], f x * linearForm b x) = σ := by
      rw [expect_mul_linearForm_eq_singletonCoeffs]
      calc
        (∑ i, b i * fourierCoeff f {i}) =
            (∑ i, a i ^ 2) / σ := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [a, b]
          ring
        _ = W / σ := by rw [haSum]
        _ = σ := by
          apply (div_eq_iff hσpos.ne').2
          nlinarith
    have hvariational :
        (𝔼 x : {−1,1}^[n], f x * linearForm b x) ≤
          t * (𝔼 x : {−1,1}^[n], f x) +
            𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺ := by
      calc
        (𝔼 x : {−1,1}^[n], f x * linearForm b x) ≤
            (𝔼 x : {−1,1}^[n],
              (t * f x + (linearForm b x - t)⁺)) := by
          apply Finset.expect_le_expect
          intro x _
          exact mul_le_threshold_add_posPart (hf0 x) (hf1 x)
        _ = t * (𝔼 x : {−1,1}^[n], f x) +
            𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺ := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    have hσBound :
        σ ≤ U + C * (ε / σ) := by
      calc
        σ = 𝔼 x : {−1,1}^[n], f x * linearForm b x :=
          hinner.symm
        _ ≤ t * (𝔼 x : {−1,1}^[n], f x) +
            𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺ :=
          hvariational
        _ ≤ t * α +
            𝔼 x : {−1,1}^[n], (linearForm b x - t)⁺ :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left hmean htpos.le) _
        _ ≤ t * α +
            (standardGaussianStopLoss t + C * (ε / σ)) :=
          add_le_add_right hstopUpper _
        _ = U + C * (ε / σ) := by
          rw [hGaussianStopLoss]
          ring
    have hquad :
        σ ^ 2 ≤ U * σ + C * ε := by
      calc
        σ ^ 2 = σ * σ := by ring
        _ ≤ (U + C * (ε / σ)) * σ :=
          mul_le_mul_of_nonneg_right hσBound hσpos.le
        _ = U * σ + C * ((ε / σ) * σ) := by ring
        _ = U * σ + C * ε := by
          rw [div_mul_cancel₀ ε hσpos.ne']
    rw [← hσsq]
    by_cases hσU : σ ≤ U
    · nlinarith
    · have hUσ : U ≤ σ := le_of_not_ge hσU
      have hgap : 0 ≤ σ - U := sub_nonneg.mpr hUσ
      have hUgap :
          U * (σ - U) ≤ σ * (σ - U) :=
        mul_le_mul_of_nonneg_right hUσ hgap
      have hσgap :
          σ * (σ - U) ≤ C * ε := by
        nlinarith
      have hUgapError :
          U * (σ - U) ≤ C * ε :=
        hUgap.trans hσgap
      nlinarith

end FABL
