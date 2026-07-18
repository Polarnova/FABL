/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.CorrelatedMajority
import FABL.Chapter05.GaussianThresholds
import FABL.Chapter02.NoiseStability.NoiseOperator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ProbabilityApproximation.Bentkus.Induction

/-!
# Noise stability of regular linear threshold functions

Book items: Exercise 5.33 and Theorem 5.17.

The two-dimensional Berry--Esseen argument for unbiased homogeneous regular
linear threshold functions.
-/

open Finset Matrix MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators BooleanCube ENNReal Matrix MatrixOrder RealInnerProductSpace

namespace FABL

local instance regularThresholdSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance regularThresholdSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The covariance matrix of two standard random variables with correlation `ρ`. -/
def correlationMatrix (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, ρ; ρ, 1]

/-- O'Donnell, Exercise 5.33(a): the inverse of the bivariate correlation matrix in the
factorization used to evaluate its quadratic form. -/
theorem exercise5_33a
    {ρ : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) :
    (correlationMatrix ρ)⁻¹ =
      !![1, -ρ; 0, 1] *
        !![1, 0; 0, (1 - ρ ^ 2)⁻¹] *
          !![1, 0; -ρ, 1] := by
  have hminus : 0 < 1 - ρ := by linarith [hρ.2]
  have hplus : 0 < 1 + ρ := by linarith [hρ.1]
  have hdenom : 1 - ρ ^ 2 ≠ 0 := by
    nlinarith [mul_pos hminus hplus]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [correlationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
    <;> field_simp [hdenom]
    <;> ring

/-- O'Donnell, Exercise 5.33(b), equal-sign case: the inverse-covariance quadratic form of
`(±a, ±a)` is `2a² / (1 + ρ)`. -/
theorem exercise5_33b_sameSigns
    {ρ a : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) (s : Sign) :
    let y : Fin 2 → ℝ := ![signValue s * a, signValue s * a]
    y ⬝ᵥ ((correlationMatrix ρ)⁻¹ *ᵥ y) = 2 * a ^ 2 / (1 + ρ) := by
  have hplus : 1 + ρ ≠ 0 := by linarith [hρ.1]
  have hminus : 1 - ρ ≠ 0 := by linarith [hρ.2]
  have hdenom : 1 - ρ ^ 2 ≠ 0 := by
    rw [show 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) by ring]
    exact mul_ne_zero hminus hplus
  rw [exercise5_33a hρ]
  rcases signValue_eq_neg_one_or_one s with hs | hs <;>
    simp [hs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> field_simp [hplus, hdenom]
    <;> ring

/-- O'Donnell, Exercise 5.33(b), opposite-sign case: the inverse-covariance quadratic form
of `(±a, ∓a)` is `2a² / (1 - ρ)`. -/
theorem exercise5_33b_oppositeSigns
    {ρ a : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) (s : Sign) :
    let y : Fin 2 → ℝ := ![signValue s * a, -(signValue s * a)]
    y ⬝ᵥ ((correlationMatrix ρ)⁻¹ *ᵥ y) = 2 * a ^ 2 / (1 - ρ) := by
  have hminus : 1 - ρ ≠ 0 := by linarith [hρ.2]
  have hplus : 1 + ρ ≠ 0 := by linarith [hρ.1]
  have hdenom : 1 - ρ ^ 2 ≠ 0 := by
    rw [show 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) by ring]
    exact mul_ne_zero hminus hplus
  rw [exercise5_33a hρ]
  rcases signValue_eq_neg_one_or_one s with hs | hs <;>
    simp [hs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> field_simp [hminus, hdenom]
    <;> ring

/-- The bivariate correlation matrix is positive definite away from the degenerate
correlations `±1`. -/
theorem correlationMatrix_posDef
    {ρ : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) :
    (correlationMatrix ρ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [correlationMatrix]
  · intro x hx
    have hplus : 0 < (1 + ρ) / 2 := by linarith [hρ.1]
    have hminus : 0 < (1 - ρ) / 2 := by linarith [hρ.2]
    have hsplit :
        star x ⬝ᵥ (correlationMatrix ρ *ᵥ x) =
          (1 + ρ) / 2 * (x 0 + x 1) ^ 2 +
            (1 - ρ) / 2 * (x 0 - x 1) ^ 2 := by
      simp [correlationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    rw [hsplit]
    have hpair : x 0 + x 1 ≠ 0 ∨ x 0 - x 1 ≠ 0 := by
      by_contra h
      push Not at h
      have hx₀ : x 0 = 0 := by linarith [h.1, h.2]
      have hx₁ : x 1 = 0 := by linarith [h.1, h.2]
      apply hx
      ext i
      fin_cases i <;> simp [hx₀, hx₁]
    rcases hpair with hsum | hdiff
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hplus (sq_pos_of_ne_zero hsum))
        (mul_nonneg hminus.le (sq_nonneg _))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg hplus.le (sq_nonneg _))
        (mul_pos hminus (sq_pos_of_ne_zero hdiff))

/-- A single correlated sign pair scaled by one threshold coefficient. -/
noncomputable def regularCorrelatedSignSummand
    (c : ℝ) (z : Sign × Sign) :
    EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![c * signValue z.1, c * signValue z.2]

/-- The `i`th planar summand attached to a correlated pair and a coefficient vector. -/
noncomputable def regularThresholdPairSummand
    {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    EuclideanSpace ℝ (Fin 2) :=
  regularCorrelatedSignSummand (a i) (xy.1 i, xy.2 i)

/-- The planar pair of homogeneous linear forms is the sum of its coordinate summands. -/
noncomputable def regularThresholdPairSum
    {n : ℕ} (a : Fin n → ℝ)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    EuclideanSpace ℝ (Fin 2) :=
  ∑ i, regularThresholdPairSummand a i xy

@[simp] theorem regularThresholdPairSum_apply_zero
    {n : ℕ} (a : Fin n → ℝ)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    regularThresholdPairSum a xy 0 = linearForm a xy.1 := by
  simp [regularThresholdPairSum, regularThresholdPairSummand,
    regularCorrelatedSignSummand, linearForm]

@[simp] theorem regularThresholdPairSum_apply_one
    {n : ℕ} (a : Fin n → ℝ)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    regularThresholdPairSum a xy 1 = linearForm a xy.2 := by
  simp [regularThresholdPairSum, regularThresholdPairSummand,
    regularCorrelatedSignSummand, linearForm]

private theorem regularThresholdPairSummand_memLp
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) (i : Fin n) :
    MemLp (regularThresholdPairSummand a i) 3
      (correlatedPairPMF ρ hρ).toMeasure := by
  obtain ⟨C, hC⟩ :=
    Finite.exists_le (fun xy : {−1,1}^[n] × {−1,1}^[n] ↦
      ‖regularThresholdPairSummand a i xy‖)
  exact MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable C
    (ae_of_all _ hC)

private theorem regularThresholdPairSummand_iIndep
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) :
    iIndepFun (regularThresholdPairSummand a)
      (correlatedPairPMF ρ hρ).toMeasure := by
  let p : PMF (Sign × Sign) := correlatedSignPairPMF ρ hρ
  let μprod : Measure (Fin n → Sign × Sign) :=
    Measure.pi fun _ : Fin n ↦ p.toMeasure
  let X : Fin n → (Fin n → Sign × Sign) → EuclideanSpace ℝ (Fin 2) :=
    fun i z ↦ regularCorrelatedSignSummand (a i) (z i)
  have hXmeas : ∀ i, Measurable (fun z : Sign × Sign ↦
      regularCorrelatedSignSummand (a i) z) :=
    fun _ ↦ measurable_of_finite _
  have hXindep : iIndepFun X μprod := by
    dsimp only [X, μprod]
    exact iIndepFun_pi fun i ↦ (hXmeas i).aemeasurable
  have hmap :
      (correlatedPairPMF (n := n) ρ hρ).toMeasure.map
          (pairCoordinatesEquiv n) = μprod := by
    calc
      (correlatedPairPMF (n := n) ρ hρ).toMeasure.map
          (pairCoordinatesEquiv n) =
          ((correlatedPairPMF (n := n) ρ hρ).map
            (pairCoordinatesEquiv n)).toMeasure := by
              exact PMF.toMeasure_map (f := pairCoordinatesEquiv n)
                (correlatedPairPMF (n := n) ρ hρ) (measurable_of_finite _)
      _ = (independentProductPMF
          (fun _ : Fin n ↦ correlatedSignPairPMF ρ hρ)).toMeasure := by
            rw [correlatedPairPMF_map_pairCoordinatesEquiv]
      _ = μprod := by
            rw [independentProductPMF_toMeasure]
  have hpres :
      MeasurePreserving (pairCoordinatesEquiv n)
        (correlatedPairPMF (n := n) ρ hρ).toMeasure μprod :=
    ⟨measurable_of_finite _, hmap⟩
  have hcomp := ProbabilityTheory.iIndepFun_comp_measurePreserving
    (fun i ↦ by
      dsimp only [X]
      exact (hXmeas i).comp (measurable_pi_apply i))
    hXindep hpres
  have hfun :
      (fun i ↦ X i ∘ (pairCoordinatesEquiv n : _ → _)) =
        regularThresholdPairSummand a := by
    funext i xy
    rfl
  rw [← hfun]
  exact hcomp

private theorem integral_regularThresholdPairSummand_eq_zero
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) (i : Fin n) :
    ∫ xy, regularThresholdPairSummand a i xy
        ∂(correlatedPairPMF ρ hρ).toMeasure = 0 := by
  have hint :
      Integrable (regularThresholdPairSummand a i)
        (correlatedPairPMF ρ hρ).toMeasure :=
    (regularThresholdPairSummand_memLp ρ hρ a i).integrable (by norm_num)
  ext j
  rw [eval_integral_piLp (fun k ↦ hint.eval_piLp k)]
  fin_cases j
  · change (∫ xy, a i * signValue (xy.1 i)
        ∂(correlatedPairPMF ρ hρ).toMeasure) = 0
    rw [← pmfExpectation_eq_integral, pmfExpectation_const_mul,
      correlatedPairPMF_expect_signValue_fst, mul_zero]
  · change (∫ xy, a i * signValue (xy.2 i)
        ∂(correlatedPairPMF ρ hρ).toMeasure) = 0
    rw [← pmfExpectation_eq_integral, pmfExpectation_const_mul,
      correlatedPairPMF_expect_signValue_snd, mul_zero]

private theorem integral_regularThresholdPairSum_eq_zero
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) :
    ∫ xy, regularThresholdPairSum a xy
        ∂(correlatedPairPMF ρ hρ).toMeasure = 0 := by
  rw [show regularThresholdPairSum a =
      fun xy ↦ ∑ i, regularThresholdPairSummand a i xy from rfl]
  rw [integral_finsetSum]
  · simp_rw [integral_regularThresholdPairSummand_eq_zero ρ hρ a]
    simp
  · intro i _
    exact (regularThresholdPairSummand_memLp ρ hρ a i).integrable (by norm_num)

private theorem covarianceBilin_regularThresholdPairSum
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) (hnorm : ∑ i, a i ^ 2 = 1)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin
        ((correlatedPairPMF ρ hρ).toMeasure.map (regularThresholdPairSum a)) x y =
      x ⬝ᵥ correlationMatrix ρ *ᵥ y := by
  let μ : Measure ({−1,1}^[n] × {−1,1}^[n]) :=
    (correlatedPairPMF ρ hρ).toMeasure
  have hsum3 : MemLp (regularThresholdPairSum a) 3 μ := by
    exact memLp_finsetSum Finset.univ fun i _ ↦
      regularThresholdPairSummand_memLp ρ hρ a i
  have hsum2 : MemLp (regularThresholdPairSum a) 2 μ :=
    hsum3.mono_exponent (by norm_num)
  rw [covarianceBilin_map_apply_eq_cov_projection hsum2]
  rw [covariance_eq_sub (hsum2.const_inner x) (hsum2.const_inner y)]
  have hmean (u : EuclideanSpace ℝ (Fin 2)) :
      ∫ xy, inner ℝ u (regularThresholdPairSum a xy) ∂μ = 0 := by
    change ∫ xy, (innerSL ℝ u) (regularThresholdPairSum a xy) ∂μ = 0
    rw [(innerSL ℝ u).integral_comp_comm
      (hsum2.integrable (by norm_num))]
    rw [integral_regularThresholdPairSum_eq_zero ρ hρ a]
    simp
  rw [hmean x, hmean y, mul_zero, sub_zero]
  have hfirst :
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ linearForm a xy.1 * linearForm a xy.1) =
        ∑ i, a i ^ 2 := by
    rw [show (fun xy : {−1,1}^[n] × {−1,1}^[n] ↦
        linearForm a xy.1 * linearForm a xy.1) =
        fun xy ↦ linearForm a xy.1 ^ 2 by
          funext xy
          ring]
    rw [pmfExpectation_correlatedPairPMF_fst ρ hρ
        (fun z ↦ linearForm a z ^ 2),
      pmfExpectation_uniformPMF_eq_expect, expect_linearForm_sq]
  have hsecond :
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ linearForm a xy.2 * linearForm a xy.2) =
        ∑ i, a i ^ 2 := by
    rw [show (fun xy : {−1,1}^[n] × {−1,1}^[n] ↦
        linearForm a xy.2 * linearForm a xy.2) =
        fun xy ↦ linearForm a xy.2 ^ 2 by
          funext xy
          ring]
    rw [pmfExpectation_correlatedPairPMF_snd ρ hρ
        (fun z ↦ linearForm a z ^ 2),
      pmfExpectation_uniformPMF_eq_expect, expect_linearForm_sq]
  have hcross :
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ linearForm a xy.1 * linearForm a xy.2) =
        ρ * ∑ i, a i ^ 2 :=
    pmfExpectation_correlatedPairPMF_linearForm_mul ρ hρ a
  rw [← pmfExpectation_eq_integral]
  change pmfExpectation (correlatedPairPMF ρ hρ)
      (fun xy ↦
        inner ℝ x (regularThresholdPairSum a xy) *
          inner ℝ y (regularThresholdPairSum a xy)) =
    x ⬝ᵥ correlationMatrix ρ *ᵥ y
  rw [show (fun xy ↦
      inner ℝ x (regularThresholdPairSum a xy) *
        inner ℝ y (regularThresholdPairSum a xy)) =
      fun xy ↦
        (x 0 * y 0) * (linearForm a xy.1 * linearForm a xy.1) +
        (x 0 * y 1) * (linearForm a xy.1 * linearForm a xy.2) +
        (x 1 * y 0) * (linearForm a xy.2 * linearForm a xy.1) +
        (x 1 * y 1) * (linearForm a xy.2 * linearForm a xy.2) by
    funext xy
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ]
    ring]
  rw [pmfExpectation_add, pmfExpectation_add, pmfExpectation_add]
  rw [pmfExpectation_const_mul, pmfExpectation_const_mul,
    pmfExpectation_const_mul, pmfExpectation_const_mul]
  rw [hfirst, hcross,
    show pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ linearForm a xy.2 * linearForm a xy.1) =
          ρ * ∑ i, a i ^ 2 by
      calc
        pmfExpectation (correlatedPairPMF ρ hρ)
            (fun xy ↦ linearForm a xy.2 * linearForm a xy.1) =
            pmfExpectation (correlatedPairPMF ρ hρ)
              (fun xy ↦ linearForm a xy.1 * linearForm a xy.2) := by
                apply congrArg (pmfExpectation (correlatedPairPMF ρ hρ))
                funext xy
                ring
        _ = ρ * ∑ i, a i ^ 2 := hcross,
    hsecond, hnorm]
  simp [correlationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem bentkusWhitening_norm_sq_eq_inv_quadraticForm
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (z : EuclideanSpace ℝ (Fin d)) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) z‖ ^ 2 =
      z ⬝ᵥ S⁻¹ *ᵥ z := by
  let R := CFC.sqrt S
  let T := R⁻¹
  have hR : R * R = S :=
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hTR : T * R = 1 := by
    simpa only [T, R, bentkusWhiteningMatrix] using
      bentkusWhiteningMatrix_mul_sqrt S hS
  have hTinv : S⁻¹ = T * T := by
    apply Matrix.inv_eq_left_inv
    calc
      (T * T) * S = T * ((T * R) * R) := by
        rw [← hR]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTR]; simp [hTR]
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    toEuclideanCLM (𝕜 := ℝ) T
  change ‖L z‖ ^ 2 = z ⬝ᵥ S⁻¹ *ᵥ z
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  rw [show L.adjoint = L by
    simpa only [L, T, R, bentkusWhiteningCLM, bentkusWhiteningMatrix] using
      adjoint_bentkusWhiteningCLM S]
  have hcomp :
      (L ∘L L) z = toEuclideanCLM (𝕜 := ℝ) S⁻¹ z := by
    dsimp only [L]
    rw [ContinuousLinearMap.comp_apply]
    change toEuclideanCLM (𝕜 := ℝ) T
        (toEuclideanCLM (𝕜 := ℝ) T z) =
      toEuclideanCLM (𝕜 := ℝ) S⁻¹ z
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul]
    rw [← hTinv]
  rw [hcomp]
  simpa using (Matrix.inner_toEuclideanCLM S⁻¹ z z)

private theorem bentkusWhitening_norm_sameSigns_le
    {ρ c : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) (s : Sign) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
        (toLp 2 ![signValue s * c, signValue s * c])‖ ≤
      Real.sqrt 2 * |c| / Real.sqrt (1 + ρ) := by
  have hplus : 0 < 1 + ρ := by linarith [hρ.1]
  have hsq :
      ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
          (toLp 2 ![signValue s * c, signValue s * c])‖ ^ 2 =
        2 * c ^ 2 / (1 + ρ) := by
    rw [bentkusWhitening_norm_sq_eq_inv_quadraticForm
      (correlationMatrix ρ) (correlationMatrix_posDef hρ)]
    simpa using exercise5_33b_sameSigns hρ s
  rw [← sq_le_sq₀ (norm_nonneg _)
    (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (Real.sqrt_nonneg _))]
  rw [hsq, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_abs, Real.sq_sqrt hplus.le]

private theorem bentkusWhitening_norm_oppositeSigns_le
    {ρ c : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) (s : Sign) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
        (toLp 2 ![signValue s * c, -(signValue s * c)])‖ ≤
      Real.sqrt 2 * |c| / Real.sqrt (1 - ρ) := by
  have hminus : 0 < 1 - ρ := by linarith [hρ.2]
  have hsq :
      ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
          (toLp 2 ![signValue s * c, -(signValue s * c)])‖ ^ 2 =
        2 * c ^ 2 / (1 - ρ) := by
    rw [bentkusWhitening_norm_sq_eq_inv_quadraticForm
      (correlationMatrix ρ) (correlationMatrix_posDef hρ)]
    simpa using exercise5_33b_oppositeSigns hρ s
  rw [← sq_le_sq₀ (norm_nonneg _)
    (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (Real.sqrt_nonneg _))]
  rw [hsq, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_abs, Real.sq_sqrt hminus.le]

private theorem regularThresholdPairSummand_whitening_norm_cube_le
    {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1)
    (a : Fin n → ℝ) (i : Fin n)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
        (regularThresholdPairSummand a i xy)‖ ^ 3 ≤
      if xy.1 i = xy.2 i then
        (Real.sqrt 2 * |a i| / Real.sqrt (1 + ρ)) ^ 3
      else
        (Real.sqrt 2 * |a i| / Real.sqrt (1 - ρ)) ^ 3 := by
  by_cases hsame : xy.1 i = xy.2 i
  · rw [if_pos hsame]
    have hv :
        regularThresholdPairSummand a i xy =
          toLp 2 ![signValue (xy.1 i) * a i,
            signValue (xy.1 i) * a i] := by
      ext j
      fin_cases j <;>
        simp [regularThresholdPairSummand, regularCorrelatedSignSummand,
          hsame, mul_comm]
    rw [hv]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (bentkusWhitening_norm_sameSigns_le hρ (xy.1 i) (c := a i)) 3
  · rw [if_neg hsame]
    have hopposite : xy.2 i = -(xy.1 i) := by
      rcases Int.units_eq_one_or (xy.1 i) with hx | hx <;>
        rcases Int.units_eq_one_or (xy.2 i) with hy | hy <;>
        simp_all
    have hle := bentkusWhitening_norm_oppositeSigns_le hρ (xy.1 i)
      (c := a i)
    have hv :
        regularThresholdPairSummand a i xy =
          toLp 2 ![signValue (xy.1 i) * a i,
            -(signValue (xy.1 i) * a i)] := by
      change toLp 2 ![a i * signValue (xy.1 i),
          a i * signValue (xy.2 i)] =
        toLp 2 ![signValue (xy.1 i) * a i,
          -(signValue (xy.1 i) * a i)]
      apply congrArg (toLp 2)
      funext j
      fin_cases j
      · simp [mul_comm]
      · rw [hopposite]
        rcases Int.units_eq_one_or (xy.1 i) with hs | hs <;>
          simp [hs, mul_comm]
    rw [hv]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 3

private theorem pmfExpectation_if_coordinate_signs_eq
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (i : Fin n) (u v : ℝ) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ if xy.1 i = xy.2 i then u else v) =
      (1 + ρ) / 2 * u + (1 - ρ) / 2 * v := by
  have hfun :
      (fun xy : {−1,1}^[n] × {−1,1}^[n] ↦
        if xy.1 i = xy.2 i then u else v) =
      fun xy ↦
        (u + v) / 2 +
          ((u - v) / 2) *
            (signValue (xy.1 i) * signValue (xy.2 i)) := by
    funext xy
    rcases Int.units_eq_one_or (xy.1 i) with hx | hx <;>
      rcases Int.units_eq_one_or (xy.2 i) with hy | hy <;>
      simp [hx, hy] <;> ring
  rw [hfun, pmfExpectation_add, pmfExpectation_const,
    pmfExpectation_const_mul, correlatedPairPMF_expect_signValue_mul]
  ring

private theorem weighted_whitening_scale_cube_le
    {ρ c : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1) :
    (1 + ρ) / 2 *
          (Real.sqrt 2 * |c| / Real.sqrt (1 + ρ)) ^ 3 +
        (1 - ρ) / 2 *
          (Real.sqrt 2 * |c| / Real.sqrt (1 - ρ)) ^ 3 ≤
      4 * |c| ^ 3 / Real.sqrt (1 - ρ ^ 2) := by
  have hplus : 0 < 1 + ρ := by linarith [hρ.1]
  have hminus : 0 < 1 - ρ := by linarith [hρ.2]
  have hquad : 0 < 1 - ρ ^ 2 := by
    nlinarith [mul_pos hplus hminus]
  have hsqrtPlus : 0 < Real.sqrt (1 + ρ) := Real.sqrt_pos.2 hplus
  have hsqrtMinus : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.2 hminus
  have hsqrtQuad : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.2 hquad
  have hquadSqrt :
      Real.sqrt (1 - ρ ^ 2) =
        Real.sqrt (1 + ρ) * Real.sqrt (1 - ρ) := by
    rw [show 1 - ρ ^ 2 = (1 + ρ) * (1 - ρ) by ring,
      Real.sqrt_mul hplus.le]
  have hsqrtTwoSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsame :
      (1 + ρ) / 2 *
          (Real.sqrt 2 * |c| / Real.sqrt (1 + ρ)) ^ 3 =
        Real.sqrt 2 * |c| ^ 3 / Real.sqrt (1 + ρ) := by
    field_simp [hsqrtPlus.ne']
    rw [hsqrtTwoSq, Real.sq_sqrt hplus.le]
    ring
  have hopposite :
      (1 - ρ) / 2 *
          (Real.sqrt 2 * |c| / Real.sqrt (1 - ρ)) ^ 3 =
        Real.sqrt 2 * |c| ^ 3 / Real.sqrt (1 - ρ) := by
    field_simp [hsqrtMinus.ne']
    rw [hsqrtTwoSq, Real.sq_sqrt hminus.le]
    ring
  rw [hsame, hopposite]
  have hsqrtTwoMinus :
      Real.sqrt 2 * Real.sqrt (1 - ρ) ≤ 2 := by
    rw [← sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_pow, hsqrtTwoSq, Real.sq_sqrt hminus.le]
    nlinarith [hρ.1]
  have hsqrtTwoPlus :
      Real.sqrt 2 * Real.sqrt (1 + ρ) ≤ 2 := by
    rw [← sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_pow, hsqrtTwoSq, Real.sq_sqrt hplus.le]
    nlinarith [hρ.2]
  have hrecipPlus :
      Real.sqrt 2 / Real.sqrt (1 + ρ) ≤
        2 / Real.sqrt (1 - ρ ^ 2) := by
    rw [hquadSqrt]
    calc
      Real.sqrt 2 / Real.sqrt (1 + ρ) =
          (Real.sqrt 2 * Real.sqrt (1 - ρ)) /
            (Real.sqrt (1 + ρ) * Real.sqrt (1 - ρ)) := by
              field_simp [hsqrtPlus.ne', hsqrtMinus.ne']
      _ ≤ 2 / (Real.sqrt (1 + ρ) * Real.sqrt (1 - ρ)) :=
        (div_le_div_iff_of_pos_right
          (mul_pos hsqrtPlus hsqrtMinus)).2 hsqrtTwoMinus
  have hrecipMinus :
      Real.sqrt 2 / Real.sqrt (1 - ρ) ≤
        2 / Real.sqrt (1 - ρ ^ 2) := by
    rw [hquadSqrt]
    calc
      Real.sqrt 2 / Real.sqrt (1 - ρ) =
          (Real.sqrt 2 * Real.sqrt (1 + ρ)) /
            (Real.sqrt (1 + ρ) * Real.sqrt (1 - ρ)) := by
              field_simp [hsqrtPlus.ne', hsqrtMinus.ne']
      _ ≤ 2 / (Real.sqrt (1 + ρ) * Real.sqrt (1 - ρ)) :=
        (div_le_div_iff_of_pos_right
          (mul_pos hsqrtPlus hsqrtMinus)).2 hsqrtTwoPlus
  calc
    Real.sqrt 2 * |c| ^ 3 / Real.sqrt (1 + ρ) +
          Real.sqrt 2 * |c| ^ 3 / Real.sqrt (1 - ρ) =
        |c| ^ 3 * (Real.sqrt 2 / Real.sqrt (1 + ρ) +
          Real.sqrt 2 / Real.sqrt (1 - ρ)) := by ring
    _ ≤ |c| ^ 3 * (2 / Real.sqrt (1 - ρ ^ 2) +
          2 / Real.sqrt (1 - ρ ^ 2)) := by
      gcongr
    _ = 4 * |c| ^ 3 / Real.sqrt (1 - ρ ^ 2) := by ring

private theorem integral_regularThresholdPairSummand_whitening_cube_le
    {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1)
    (a : Fin n → ℝ) (i : Fin n) :
    ∫ xy,
        ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
          (regularThresholdPairSummand a i xy)‖ ^ 3
    ∂(correlatedPairPMF ρ ⟨hρ.1.le, hρ.2.le⟩).toMeasure ≤
      4 * |a i| ^ 3 / Real.sqrt (1 - ρ ^ 2) := by
  have hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  rw [← pmfExpectation_eq_integral]
  calc
    pmfExpectation (correlatedPairPMF ρ hρclosed)
        (fun xy ↦
          ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
            (regularThresholdPairSummand a i xy)‖ ^ 3) ≤
        pmfExpectation (correlatedPairPMF ρ hρclosed)
          (fun xy ↦ if xy.1 i = xy.2 i then
            (Real.sqrt 2 * |a i| / Real.sqrt (1 + ρ)) ^ 3
          else
            (Real.sqrt 2 * |a i| / Real.sqrt (1 - ρ)) ^ 3) := by
      unfold pmfExpectation
      apply Finset.sum_le_sum
      intro xy _
      exact mul_le_mul_of_nonneg_left
        (regularThresholdPairSummand_whitening_norm_cube_le hρ a i xy)
        ENNReal.toReal_nonneg
    _ = (1 + ρ) / 2 *
          (Real.sqrt 2 * |a i| / Real.sqrt (1 + ρ)) ^ 3 +
        (1 - ρ) / 2 *
          (Real.sqrt 2 * |a i| / Real.sqrt (1 - ρ)) ^ 3 :=
      pmfExpectation_if_coordinate_signs_eq ρ hρclosed i _ _
    _ ≤ 4 * |a i| ^ 3 / Real.sqrt (1 - ρ ^ 2) :=
      weighted_whitening_scale_cube_le hρ

private theorem sum_integral_regularThresholdPairSummand_whitening_cube_le
    {n : ℕ} {ρ ε : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1)
    (a : Fin n → ℝ) (hnorm : ∑ i, a i ^ 2 = 1)
    (hregular : ∀ i, |a i| ≤ ε) :
    ∑ i, ∫ xy,
        ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
          (regularThresholdPairSummand a i xy)‖ ^ 3
        ∂(correlatedPairPMF ρ ⟨hρ.1.le, hρ.2.le⟩).toMeasure ≤
      4 * ε / Real.sqrt (1 - ρ ^ 2) := by
  have hsqrt : 0 < Real.sqrt (1 - ρ ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [mul_pos (show 0 < 1 + ρ by linarith [hρ.1])
      (show 0 < 1 - ρ by linarith [hρ.2])]
  calc
    ∑ i, ∫ xy,
          ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (correlationMatrix ρ))⁻¹)
            (regularThresholdPairSummand a i xy)‖ ^ 3
          ∂(correlatedPairPMF ρ ⟨hρ.1.le, hρ.2.le⟩).toMeasure ≤
        ∑ i, 4 * |a i| ^ 3 / Real.sqrt (1 - ρ ^ 2) :=
      Finset.sum_le_sum fun i _ ↦
        integral_regularThresholdPairSummand_whitening_cube_le hρ a i
    _ ≤ ∑ i, 4 * (ε * a i ^ 2) / Real.sqrt (1 - ρ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hmul := mul_le_mul_of_nonneg_right (hregular i) (sq_nonneg (a i))
      have hc : |a i| ^ 3 ≤ ε * a i ^ 2 := by
        calc
          |a i| ^ 3 = |a i| * |a i| ^ 2 := by ring
          _ = |a i| * a i ^ 2 := by rw [sq_abs]
          _ ≤ ε * a i ^ 2 := hmul
      exact (div_le_div_iff_of_pos_right hsqrt).2
        (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = 4 * ε / Real.sqrt (1 - ρ ^ 2) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum, hnorm]
      ring

/-- A closed quadrant indexed by the desired signs of its two coordinates. -/
def signQuadrant (s t : Sign) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | 0 ≤ signValue s * z 0 ∧ 0 ≤ signValue t * z 1}

theorem measurableSet_signQuadrant (s t : Sign) :
    MeasurableSet (signQuadrant s t) := by
  have hs : Continuous (fun z : EuclideanSpace ℝ (Fin 2) ↦ signValue s * z 0) := by
    fun_prop
  have ht : Continuous (fun z : EuclideanSpace ℝ (Fin 2) ↦ signValue t * z 1) := by
    fun_prop
  exact ((isClosed_le continuous_const hs).inter
    (isClosed_le continuous_const ht)).measurableSet

local instance regularThresholdConvexSpace :
    Convexity.ConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.ConvexSpace.ofModule

local instance regularThresholdModuleConvexSpace :
    Convexity.IsModuleConvexSpace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Convexity.IsModuleConvexSpace.ofModule

theorem isConvexSet_signQuadrant (s t : Sign) :
    Convexity.IsConvexSet ℝ (signQuadrant s t) := by
  apply Convexity.IsConvexSet.of_convexCombPair_mem
  intro α β hα hβ hαβ x hx y hy
  rcases hx with ⟨hx₀, hx₁⟩
  rcases hy with ⟨hy₀, hy₁⟩
  constructor
  · rw [Convexity.convexCombPair_eq_sum]
    change 0 ≤ signValue s * (α * x 0 + β * y 0)
    calc
      0 ≤ α * (signValue s * x 0) + β * (signValue s * y 0) :=
        add_nonneg (mul_nonneg hα hx₀) (mul_nonneg hβ hy₀)
      _ = signValue s * (α * x 0 + β * y 0) := by ring
  · rw [Convexity.convexCombPair_eq_sum]
    change 0 ≤ signValue t * (α * x 1 + β * y 1)
    calc
      0 ≤ α * (signValue t * x 1) + β * (signValue t * y 1) :=
        add_nonneg (mul_nonneg hα hx₁) (mul_nonneg hβ hy₁)
      _ = signValue t * (α * x 1 + β * y 1) := by ring

/-- The coordinate identification from the correlated Gaussian plane to the
two-dimensional Euclidean space used by Bentkus's theorem. -/
private noncomputable def correlationEuclideanCoordinates
    (z : CorrelationPlane) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ![(ofLp z).1, (ofLp z).2]

private noncomputable def euclideanCorrelationCoordinates
    (z : EuclideanSpace ℝ (Fin 2)) : CorrelationPlane :=
  toLp 2 (z 0, z 1)

private theorem continuous_correlationEuclideanCoordinates :
    Continuous correlationEuclideanCoordinates := by
  unfold correlationEuclideanCoordinates
  fun_prop

private theorem inner_correlationEuclideanCoordinates
    (z : CorrelationPlane) (t : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (correlationEuclideanCoordinates z) t =
      inner ℝ z (euclideanCorrelationCoordinates t) := by
  simp [correlationEuclideanCoordinates, euclideanCorrelationCoordinates,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ,
    prod_inner_apply, RCLike.inner_apply]

private theorem correlationQuadraticForm_euclideanCorrelationCoordinates
    (ρ : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    correlationQuadraticForm ρ (euclideanCorrelationCoordinates t) =
      t ⬝ᵥ correlationMatrix ρ *ᵥ t := by
  simp [correlationQuadraticForm, euclideanCorrelationCoordinates,
    correlationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem correlatedGaussianMeasure_map_correlationEuclideanCoordinates
    (ρ : ℝ) (hρ : ρ ∈ Ioo (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).map
        correlationEuclideanCoordinates =
      multivariateGaussian 0 (correlationMatrix ρ) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map
    continuous_correlationEuclideanCoordinates.aemeasurable]
  · rw [show (fun z : CorrelationPlane ↦
        Complex.exp
          (inner ℝ (correlationEuclideanCoordinates z) t * Complex.I)) =
        fun z ↦ Complex.exp
          (inner ℝ z (euclideanCorrelationCoordinates t) * Complex.I) by
      funext z
      rw [inner_correlationEuclideanCoordinates]]
    rw [← charFun_apply,
      charFun_correlatedGaussianMeasure ρ ⟨hρ.1.le, hρ.2.le⟩,
      charFun_multivariateGaussian (correlationMatrix_posDef hρ).posSemidef]
    rw [correlationQuadraticForm_euclideanCorrelationCoordinates]
    simp
    congr 1
    ring
  · fun_prop

private theorem multivariateGaussian_lowerLeftQuadrant
    (ρ : ℝ) (hρ : ρ ∈ Ioo (-1 : ℝ) 1) :
    (multivariateGaussian 0 (correlationMatrix ρ)
        (signQuadrant (-1) (-1))).toReal =
      1 / 2 - (1 / 2) * (Real.arccos ρ / Real.pi) := by
  have hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  rw [← correlatedGaussianMeasure_map_correlationEuclideanCoordinates ρ hρ]
  rw [Measure.map_apply
    continuous_correlationEuclideanCoordinates.measurable
    (measurableSet_signQuadrant (-1) (-1))]
  have hpreimage :
      correlationEuclideanCoordinates ⁻¹' signQuadrant (-1) (-1) =
        {z | correlationFirstCoordinate z ≤ 0 ∧
          correlationSecondCoordinate z ≤ 0} := by
    ext z
    simp [correlationEuclideanCoordinates, signQuadrant,
      correlationFirstCoordinate, correlationSecondCoordinate]
  rw [hpreimage]
  exact sheppardsFormula ρ hρclosed

/-- O'Donnell, Exercise 5.33(c): Bentkus's theorem controls each of the four
quadrants for the pair of regular homogeneous linear forms. -/
theorem exists_exercise5_33c_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {ρ ε : ℝ} (hρ : ρ ∈ Ioo (-1 : ℝ) 1)
        (a : Fin n → ℝ) (_hnorm : ∑ i, a i ^ 2 = 1)
        (_hregular : ∀ i, |a i| ≤ ε) (s t : Sign),
        |(((correlatedPairPMF ρ ⟨hρ.1.le, hρ.2.le⟩).toMeasure.map
              (regularThresholdPairSum a)) (signQuadrant s t)).toReal -
            (multivariateGaussian 0 (correlationMatrix ρ)
              (signQuadrant s t)).toReal| ≤
          C * ε / Real.sqrt (1 - ρ ^ 2) := by
  obtain ⟨C, hC, hBentkus⟩ :=
    ProbabilityTheory.exists_bentkus_convex_set_constant
  refine ⟨4 * C * (2 : ℝ) ^ (1 / 4 : ℝ), by positivity, ?_⟩
  intro n ρ ε hρ a hnorm hregular s t
  let hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  let μ : Measure ({−1,1}^[n] × {−1,1}^[n]) :=
    (correlatedPairPMF ρ hρclosed).toMeasure
  have hbound := hBentkus (d := 2) (n := n) (by norm_num) μ
    (regularThresholdPairSummand a) (correlationMatrix ρ)
    (regularThresholdPairSummand_memLp ρ hρclosed a)
    (regularThresholdPairSummand_iIndep ρ hρclosed a)
    (integral_regularThresholdPairSummand_eq_zero ρ hρclosed a)
    (correlationMatrix_posDef hρ)
    (covarianceBilin_regularThresholdPairSum ρ hρclosed a hnorm)
    (signQuadrant s t) (measurableSet_signQuadrant s t)
    (isConvexSet_signQuadrant s t)
  have hsum :
      (fun xy ↦ ∑ i, regularThresholdPairSummand a i xy) =
        regularThresholdPairSum a := rfl
  rw [hsum] at hbound
  have hmoment :=
    sum_integral_regularThresholdPairSummand_whitening_cube_le
      hρ a hnorm hregular
  calc
    |(((correlatedPairPMF ρ ⟨hρ.1.le, hρ.2.le⟩).toMeasure.map
          (regularThresholdPairSum a)) (signQuadrant s t)).toReal -
        (multivariateGaussian 0 (correlationMatrix ρ)
          (signQuadrant s t)).toReal| ≤
        C * (2 : ℝ) ^ (1 / 4 : ℝ) *
          ∑ i, ∫ xy,
            ‖(toEuclideanCLM (𝕜 := ℝ)
                (CFC.sqrt (correlationMatrix ρ))⁻¹)
              (regularThresholdPairSummand a i xy)‖ ^ 3
            ∂(correlatedPairPMF ρ
              ⟨hρ.1.le, hρ.2.le⟩).toMeasure := by
      dsimp only [μ] at hbound
      convert hbound using 1
      all_goals norm_num
    _ ≤ C * (2 : ℝ) ^ (1 / 4 : ℝ) *
          (4 * ε / Real.sqrt (1 - ρ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [hρclosed] using hmoment
      · positivity
    _ = (4 * C * (2 : ℝ) ^ (1 / 4 : ℝ)) * ε /
          Real.sqrt (1 - ρ ^ 2) := by ring

private theorem linearForm_neg_input_regularThreshold
    {n : ℕ} (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    linearForm a (-x) = -linearForm a x := by
  have hsign (i : Fin n) : signValue ((-x) i) = -signValue (x i) := by
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi, signValue]
  simp only [linearForm, hsign, mul_neg, Finset.sum_neg_distrib]

private theorem homogeneousThreshold_linearForm_ne_zero_of_balanced
    {n : ℕ} (f : BooleanFunction n) (a : Fin n → ℝ)
    (hbalanced : IsBalanced f.toReal)
    (hrep : ∀ x, f x = thresholdSign (linearForm a x)) :
    ∀ x, linearForm a x ≠ 0 := by
  have hpair (x : {−1,1}^[n]) :
      f.toReal x + f.toReal (-x) =
        if linearForm a x = 0 then 2 else 0 := by
    simp only [BooleanFunction.toReal, hrep,
      linearForm_neg_input_regularThreshold]
    by_cases hx : linearForm a x = 0
    · norm_num [hx]
    · rw [if_neg hx, thresholdSign_neg _ hx]
      rcases Int.units_eq_one_or (thresholdSign (linearForm a x)) with hs | hs <;>
        simp [hs]
  have hnegExpect :
      (𝔼 x : {−1,1}^[n], f.toReal (-x)) =
        𝔼 x : {−1,1}^[n], f.toReal x := by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    rfl
  have hmean :
      (𝔼 x : {−1,1}^[n],
        (fun y ↦ f.toReal y + f.toReal (-y)) x) = 0 := by
    change (𝔼 x : {−1,1}^[n], f.toReal x) = 0 at hbalanced
    rw [Finset.expect_add_distrib, hnegExpect, hbalanced, add_zero]
  have hnonneg :
      0 ≤ fun x : {−1,1}^[n] ↦ f.toReal x + f.toReal (-x) := by
    intro x
    change 0 ≤ f.toReal x + f.toReal (-x)
    rw [hpair]
    split <;> norm_num
  have hzero :
      (fun x : {−1,1}^[n] ↦ f.toReal x + f.toReal (-x)) = 0 :=
    (Fintype.expect_eq_zero_iff_of_nonneg hnonneg).1 hmean
  intro x hx
  have hxzero := congrFun hzero x
  rw [hpair, if_pos hx] at hxzero
  norm_num at hxzero

private theorem homogeneousThreshold_eq_neg_one_iff
    {n : ℕ} (f : BooleanFunction n) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (linearForm a x))
    (x : {−1,1}^[n]) :
    f x = -1 ↔ linearForm a x < 0 := by
  constructor
  · intro hx
    rw [hrep x] at hx
    by_contra hnonneg
    rw [thresholdSign_of_nonneg (le_of_not_gt hnonneg)] at hx
    norm_num at hx
  · intro hx
    rw [hrep x, thresholdSign_of_neg hx]

private theorem regularThresholdPairSum_mem_lowerLeft_iff
    {n : ℕ} (f : BooleanFunction n) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (linearForm a x))
    (hnozero : ∀ x, linearForm a x ≠ 0)
    (xy : {−1,1}^[n] × {−1,1}^[n]) :
    regularThresholdPairSum a xy ∈ signQuadrant (-1) (-1) ↔
      f xy.1 = -1 ∧ f xy.2 = -1 := by
  rw [homogeneousThreshold_eq_neg_one_iff f a hrep,
    homogeneousThreshold_eq_neg_one_iff f a hrep]
  simp only [signQuadrant, Set.mem_setOf_eq, signValue_neg_one,
    regularThresholdPairSum_apply_zero, regularThresholdPairSum_apply_one,
    neg_one_mul, neg_nonneg]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨lt_of_le_of_ne hx (hnozero xy.1),
      lt_of_le_of_ne hy (hnozero xy.2)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx.le, hy.le⟩

private theorem regularThresholdPair_lowerLeftProbability_eq
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (f : BooleanFunction n) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (linearForm a x))
    (hnozero : ∀ x, linearForm a x ≠ 0) :
    (((correlatedPairPMF ρ hρ).toMeasure.map
        (regularThresholdPairSum a)) (signQuadrant (-1) (-1))).toReal =
      pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ if f xy.1 = -1 ∧ f xy.2 = -1 then 1 else 0) := by
  rw [Measure.map_apply (measurable_of_finite _)
    (measurableSet_signQuadrant (-1) (-1))]
  let A :
      Set ({−1,1}^[n] × {−1,1}^[n]) :=
    regularThresholdPairSum a ⁻¹' signQuadrant (-1) (-1)
  have hA : MeasurableSet A :=
    (measurableSet_signQuadrant (-1) (-1)).preimage
      (measurable_of_finite _)
  change (correlatedPairPMF ρ hρ).toMeasure.real A = _
  rw [← integral_indicator_one hA,
    ← pmfExpectation_eq_integral]
  apply congrArg (pmfExpectation (correlatedPairPMF ρ hρ))
  funext xy
  have hevent :
      xy ∈ A ↔ f xy.1 = -1 ∧ f xy.2 = -1 :=
    regularThresholdPairSum_mem_lowerLeft_iff f a hrep hnozero xy
  by_cases hxy : xy ∈ A
  · rw [Set.indicator_of_mem hxy, if_pos (hevent.1 hxy)]
    rfl
  · rw [Set.indicator_of_notMem hxy, if_neg]
    exact fun h ↦ hxy (hevent.2 h)

private theorem noiseStability_eq_four_mul_lowerLeftProbability_sub_one
    {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1)
    (f : BooleanFunction n) (hbalanced : IsBalanced f.toReal) :
    noiseStability ρ hρ f.toReal =
      4 * pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ if f xy.1 = -1 ∧ f xy.2 = -1 then 1 else 0) - 1 := by
  have hmean : (𝔼 x : {−1,1}^[n], f.toReal x) = 0 := hbalanced
  have hfst :
      pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ f.toReal xy.1) = 0 := by
    rw [pmfExpectation_correlatedPairPMF_fst,
      pmfExpectation_uniformPMF_eq_expect, hmean]
  have hsnd :
      pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ f.toReal xy.2) = 0 := by
    rw [pmfExpectation_correlatedPairPMF_snd,
      pmfExpectation_uniformPMF_eq_expect, hmean]
  have hpointwise :
      (fun xy : {−1,1}^[n] × {−1,1}^[n] ↦
        f.toReal xy.1 * f.toReal xy.2) =
      fun xy ↦
        4 * (if f xy.1 = -1 ∧ f xy.2 = -1 then 1 else 0) +
          (-1) + f.toReal xy.1 + f.toReal xy.2 := by
    funext xy
    rcases Int.units_eq_one_or (f xy.1) with hx | hx <;>
      rcases Int.units_eq_one_or (f xy.2) with hy | hy <;>
      norm_num [BooleanFunction.toReal, hx, hy]
  unfold noiseStability
  rw [hpointwise, pmfExpectation_add, pmfExpectation_add,
    pmfExpectation_add, pmfExpectation_const_mul, pmfExpectation_const,
    hfst, hsnd]
  ring

/-- O'Donnell, Theorem 5.17: the noise stability of an unbiased regular
homogeneous linear threshold function is within the Berry--Esseen error of the
Gaussian arcsine law. -/
theorem exists_noiseStability_sub_arcsine_le_of_regular_homogeneous_threshold :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : BooleanFunction n) (a : Fin n → ℝ) {ε ρ : ℝ}
        (_hbalanced : IsBalanced f.toReal)
        (_hrep : ∀ x, f x = thresholdSign (linearForm a x))
        (_hnorm : ∑ i, a i ^ 2 = 1)
        (_hregular : ∀ i, |a i| ≤ ε)
        (hρ : ρ ∈ Ioo (-1 : ℝ) 1),
        |noiseStability ρ ⟨hρ.1.le, hρ.2.le⟩ f.toReal -
            2 / Real.pi * Real.arcsin ρ| ≤
          C * ε / Real.sqrt (1 - ρ ^ 2) := by
  obtain ⟨C, hC, hquadrants⟩ := exists_exercise5_33c_constant
  refine ⟨4 * C, by positivity, ?_⟩
  intro n f a ε ρ hbalanced hrep hnorm hregular hρ
  have hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  have hnozero :
      ∀ x, linearForm a x ≠ 0 :=
    homogeneousThreshold_linearForm_ne_zero_of_balanced
      f a hbalanced hrep
  have hlowerLeft :=
    hquadrants hρ a hnorm hregular (-1) (-1)
  have hprobability :=
    regularThresholdPair_lowerLeftProbability_eq
      ρ hρclosed f a hrep hnozero
  have hstability :=
    noiseStability_eq_four_mul_lowerLeftProbability_sub_one
      ρ hρclosed f hbalanced
  have hgaussian :=
    multivariateGaussian_lowerLeftQuadrant ρ hρ
  have harcsine :=
    two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos ρ
  calc
    |noiseStability ρ ⟨hρ.1.le, hρ.2.le⟩ f.toReal -
        2 / Real.pi * Real.arcsin ρ| =
      4 * |(((correlatedPairPMF ρ hρclosed).toMeasure.map
            (regularThresholdPairSum a)) (signQuadrant (-1) (-1))).toReal -
          (multivariateGaussian 0 (correlationMatrix ρ)
            (signQuadrant (-1) (-1))).toReal| := by
      rw [hstability, ← hprobability, hgaussian, harcsine]
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), ← abs_mul]
      congr 1
      ring
    _ ≤ 4 * (C * ε / Real.sqrt (1 - ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlowerLeft (by norm_num)
    _ = (4 * C) * ε / Real.sqrt (1 - ρ ^ 2) := by ring

end FABL
