/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.SharpLevelOneInequality
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The Level-1 inequality for nearly constant Boolean functions

Book items: Exercise 5.37 and Corollary 5.32.

The minority-value indicator supplies the `[0,1]`-valued function to which the
sharp Level-1 inequality applies.
-/

open Finset Set
open scoped BigOperators BooleanCube

namespace FABL

variable {n : ℕ}

/-- The indicator of the minority output value, with the nearer constant sign
chosen from the sign of the mean. -/
noncomputable def nearlyConstantMinorityIndicator
    (f : BooleanFunction n) : {−1,1}^[n] → ℝ :=
  if 0 ≤ mean f.toReal then
    fun x ↦ (1 - f.toReal x) / 2
  else
    fun x ↦ (1 + f.toReal x) / 2

/-- The minority-value indicator is `[0,1]`-valued. -/
theorem nearlyConstantMinorityIndicator_mem_Icc
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    nearlyConstantMinorityIndicator f x ∈ Icc (0 : ℝ) 1 := by
  by_cases hmean : 0 ≤ mean f.toReal
  · rcases Int.units_eq_one_or (f x) with hx | hx <;>
      simp [nearlyConstantMinorityIndicator, hmean, BooleanFunction.toReal, hx]
  · rcases Int.units_eq_one_or (f x) with hx | hx <;>
      simp [nearlyConstantMinorityIndicator, hmean, BooleanFunction.toReal, hx]

private theorem abs_mean_toReal_le_one (f : BooleanFunction n) :
    |mean f.toReal| ≤ 1 := by
  have hlower : (-1 : ℝ) ≤ mean f.toReal := by
    calc
      (-1 : ℝ) = 𝔼 _x : {−1,1}^[n], (-1 : ℝ) :=
        (Fintype.expect_const (-1 : ℝ)).symm
      _ ≤ 𝔼 x : {−1,1}^[n], f.toReal x := by
        apply Finset.expect_le_expect
        intro x _
        rcases Int.units_eq_one_or (f x) with hx | hx <;>
          simp [BooleanFunction.toReal, hx]
      _ = mean f.toReal := rfl
  have hupper : mean f.toReal ≤ 1 := by
    calc
      mean f.toReal = 𝔼 x : {−1,1}^[n], f.toReal x := rfl
      _ ≤ 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
        apply Finset.expect_le_expect
        intro x _
        rcases Int.units_eq_one_or (f x) with hx | hx <;>
          simp [BooleanFunction.toReal, hx]
      _ = 1 := Fintype.expect_const (1 : ℝ)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The chosen indicator has mean `(1 - |𝔼[f]|) / 2`. -/
theorem mean_nearlyConstantMinorityIndicator
    (f : BooleanFunction n) :
    mean (nearlyConstantMinorityIndicator f) =
      (1 - |mean f.toReal|) / 2 := by
  by_cases hmean : 0 ≤ mean f.toReal
  · calc
      mean (nearlyConstantMinorityIndicator f) =
          𝔼 x, (1 - f.toReal x) / 2 := by
        rw [mean]
        apply Finset.expect_congr rfl
        intro x _
        simp [nearlyConstantMinorityIndicator, hmean]
      _ = (1 - mean f.toReal) / 2 := by
        rw [← Finset.expect_div, Finset.expect_sub_distrib,
          Fintype.expect_const]
        rfl
      _ = (1 - |mean f.toReal|) / 2 := by
        rw [abs_of_nonneg hmean]
  · have hmean' : mean f.toReal < 0 := lt_of_not_ge hmean
    calc
      mean (nearlyConstantMinorityIndicator f) =
          𝔼 x, (1 + f.toReal x) / 2 := by
        rw [mean]
        apply Finset.expect_congr rfl
        intro x _
        simp [nearlyConstantMinorityIndicator, hmean]
      _ = (1 + mean f.toReal) / 2 := by
        rw [← Finset.expect_div, Finset.expect_add_distrib,
          Fintype.expect_const]
        rfl
      _ = (1 - |mean f.toReal|) / 2 := by
        rw [abs_of_neg hmean']
        ring

/-- The chosen minority-value indicator has nonnegative mean. -/
theorem mean_nearlyConstantMinorityIndicator_nonneg
    (f : BooleanFunction n) :
    0 ≤ mean (nearlyConstantMinorityIndicator f) := by
  rw [mean_nearlyConstantMinorityIndicator]
  linarith [abs_mean_toReal_le_one f]

/-- Under the nearly constant hypothesis, the minority-value indicator has
mean at most `δ / 2`. -/
theorem mean_nearlyConstantMinorityIndicator_le
    (f : BooleanFunction n) {δ : ℝ}
    (hmean : 1 - δ ≤ |mean f.toReal|) :
    mean (nearlyConstantMinorityIndicator f) ≤ δ / 2 := by
  rw [mean_nearlyConstantMinorityIndicator]
  linarith

/-- Singleton Fourier coefficients of the minority indicator are the
corresponding coefficients of `f`, scaled by one half and possibly negated. -/
theorem fourierCoeff_nearlyConstantMinorityIndicator_singleton
    (f : BooleanFunction n) (i : Fin n) :
    fourierCoeff (nearlyConstantMinorityIndicator f) {i} =
      if 0 ≤ mean f.toReal then
        -(fourierCoeff f.toReal {i}) / 2
      else
        fourierCoeff f.toReal {i} / 2 := by
  by_cases hmean : 0 ≤ mean f.toReal
  · rw [if_pos hmean]
    unfold fourierCoeff
    rw [show
        (fun x : {−1,1}^[n] ↦
          nearlyConstantMinorityIndicator f x * monomial {i} x) =
          fun x ↦
            (monomial {i} x - f.toReal x * monomial {i} x) / 2 by
      funext x
      rw [nearlyConstantMinorityIndicator, if_pos hmean]
      ring]
    rw [← Finset.expect_div, Finset.expect_sub_distrib, expect_monomial]
    simp
  · rw [if_neg hmean]
    unfold fourierCoeff
    rw [show
        (fun x : {−1,1}^[n] ↦
          nearlyConstantMinorityIndicator f x * monomial {i} x) =
          fun x ↦
            (monomial {i} x + f.toReal x * monomial {i} x) / 2 by
      funext x
      rw [nearlyConstantMinorityIndicator, if_neg hmean]
      ring]
    rw [← Finset.expect_div, Finset.expect_add_distrib, expect_monomial]
    simp

/-- Passing to the minority indicator divides Level-1 Fourier weight by four. -/
theorem fourierWeightAtLevel_one_eq_four_mul_nearlyConstantMinorityIndicator
    (f : BooleanFunction n) :
    fourierWeightAtLevel 1 f.toReal =
      4 * fourierWeightAtLevel 1 (nearlyConstantMinorityIndicator f) := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton,
    fourierWeightAtLevel_one_eq_sum_singleton, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierCoeff_nearlyConstantMinorityIndicator_singleton]
  by_cases hmean : 0 ≤ mean f.toReal <;> simp [hmean] <;> ring

private theorem sq_mul_log_inv_mono
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    x ^ 2 * Real.log (1 / x) ≤
      y ^ 2 * Real.log (1 / y) := by
  have hypos : 0 < y := hx.trans_le hxy
  have hxhalf : x ≤ 1 / 2 := hxy.trans hy
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hxmem : x ^ 2 ∈ Icc (0 : ℝ) (Real.exp (-1)) := by
    constructor
    · positivity
    · nlinarith [Real.exp_neg_one_gt_d9]
  have hymem : y ^ 2 ∈ Icc (0 : ℝ) (Real.exp (-1)) := by
    constructor
    · positivity
    · nlinarith [Real.exp_neg_one_gt_d9]
  have hanti :
      y ^ 2 * Real.log (y ^ 2) ≤
        x ^ 2 * Real.log (x ^ 2) :=
    Real.mul_log_strictAntiOn.antitoneOn hxmem hymem hsq
  have hreindex (z : ℝ) (hz : 0 < z) :
      z ^ 2 * Real.log (1 / z) =
        (1 / 2) * (-(z ^ 2 * Real.log (z ^ 2))) := by
    rw [Real.log_div one_ne_zero hz.ne', Real.log_one, Real.log_pow]
    ring
  rw [hreindex x hx, hreindex y hypos]
  exact mul_le_mul_of_nonneg_left (neg_le_neg hanti) (by norm_num)

/-- Corollary 5.32: a Boolean function whose mean is within `δ` of a
constant has Level-1 weight at most `4 δ² log₂(2 / δ)`. -/
theorem fourierWeightAtLevel_one_le_of_abs_mean_ge
    (f : BooleanFunction n) {δ : ℝ}
    (hmean : 1 - δ ≤ |mean f.toReal|)
    (hδ : 0 ≤ 1 - δ) :
    fourierWeightAtLevel 1 f.toReal ≤
      4 * δ ^ 2 * Real.logb 2 (2 / δ) := by
  have hδle : δ ≤ 1 := by linarith
  have hδnonneg : 0 ≤ δ := by
    linarith [abs_mean_toReal_le_one f]
  have hweight :=
    fourierWeightAtLevel_one_eq_four_mul_nearlyConstantMinorityIndicator f
  by_cases hδzero : δ = 0
  · have habs : |mean f.toReal| = 1 := by
      apply le_antisymm (abs_mean_toReal_le_one f)
      simpa [hδzero] using hmean
    have hminorityMean :
        mean (nearlyConstantMinorityIndicator f) = 0 := by
      rw [mean_nearlyConstantMinorityIndicator, habs]
      norm_num
    have hminorityWeight :
        fourierWeightAtLevel 1 (nearlyConstantMinorityIndicator f) = 0 :=
      sharpLevelOneInequality_eq_zero
        (nearlyConstantMinorityIndicator f)
        (nearlyConstantMinorityIndicator_mem_Icc f)
        hminorityMean
    rw [hweight, hminorityWeight, hδzero]
    norm_num
  · have hδpos : 0 < δ := lt_of_le_of_ne hδnonneg (Ne.symm hδzero)
    have hargOne : 1 ≤ 2 / δ := by
      rw [le_div_iff₀ hδpos]
      linarith
    have hlogbNonneg : 0 ≤ Real.logb 2 (2 / δ) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hargOne
    let α : ℝ := mean (nearlyConstantMinorityIndicator f)
    have hαnonneg : 0 ≤ α := by
      simpa only [α] using mean_nearlyConstantMinorityIndicator_nonneg f
    have hαle : α ≤ δ / 2 := by
      simpa only [α] using
        mean_nearlyConstantMinorityIndicator_le f hmean
    have hαhalf : α ≤ 1 / 2 := by
      linarith
    have hδhalf : δ / 2 ≤ 1 / 2 := by
      linarith
    by_cases hαzero : α = 0
    · have hminorityWeight :
          fourierWeightAtLevel 1 (nearlyConstantMinorityIndicator f) = 0 :=
        sharpLevelOneInequality_eq_zero
          (nearlyConstantMinorityIndicator f)
          (nearlyConstantMinorityIndicator_mem_Icc f)
          (by simpa only [α] using hαzero)
      calc
        fourierWeightAtLevel 1 f.toReal =
            4 * fourierWeightAtLevel 1
              (nearlyConstantMinorityIndicator f) := hweight
        _ = 0 := by rw [hminorityWeight]; ring
        _ ≤ 4 * δ ^ 2 * Real.logb 2 (2 / δ) :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg δ))
            hlogbNonneg
    · have hαpos : 0 < α :=
        lt_of_le_of_ne hαnonneg (Ne.symm hαzero)
      have hsharp :
          fourierWeightAtLevel 1
              (nearlyConstantMinorityIndicator f) ≤
            2 * α ^ 2 * Real.log (1 / α) :=
        sharpLevelOneInequality
          (nearlyConstantMinorityIndicator f)
          (nearlyConstantMinorityIndicator_mem_Icc f)
          (by rfl)
          hαpos
          hαhalf
      have hmono :
          α ^ 2 * Real.log (1 / α) ≤
            (δ / 2) ^ 2 * Real.log (1 / (δ / 2)) :=
        sq_mul_log_inv_mono hαpos hαle hδhalf
      have harg :
          1 / (δ / 2) = 2 / δ := by
        field_simp [hδpos.ne']
      have hnatural :
          fourierWeightAtLevel 1 f.toReal ≤
            2 * δ ^ 2 * Real.log (2 / δ) := by
        calc
          fourierWeightAtLevel 1 f.toReal =
              4 * fourierWeightAtLevel 1
                (nearlyConstantMinorityIndicator f) := hweight
          _ ≤ 4 * (2 * α ^ 2 * Real.log (1 / α)) :=
            mul_le_mul_of_nonneg_left hsharp (by norm_num)
          _ ≤ 8 * ((δ / 2) ^ 2 * Real.log (1 / (δ / 2))) := by
            nlinarith
          _ = 2 * δ ^ 2 * Real.log (2 / δ) := by
            rw [harg]
            ring
      have hlogArgNonneg : 0 ≤ Real.log (2 / δ) :=
        Real.log_nonneg hargOne
      have hlogTwoPos : 0 < Real.log 2 :=
        Real.log_pos (by norm_num)
      have hfactor : (2 : ℝ) ≤ 4 / Real.log 2 := by
        rw [le_div_iff₀ hlogTwoPos]
        nlinarith [Real.log_two_lt_d9]
      have hconvert :
          2 * δ ^ 2 * Real.log (2 / δ) ≤
            4 * δ ^ 2 * Real.logb 2 (2 / δ) := by
        calc
          2 * δ ^ 2 * Real.log (2 / δ) =
              2 * (δ ^ 2 * Real.log (2 / δ)) := by ring
          _ ≤ (4 / Real.log 2) *
              (δ ^ 2 * Real.log (2 / δ)) :=
            mul_le_mul_of_nonneg_right hfactor
              (mul_nonneg (sq_nonneg δ) hlogArgNonneg)
          _ = 4 * δ ^ 2 * Real.logb 2 (2 / δ) := by
            rw [Real.logb]
            ring
      exact hnatural.trans hconvert

end FABL
