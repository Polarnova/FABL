/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.CorrelationImmunityBounds
public import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations
public import FABL.Chapter06.Pseudorandomness.SmallBias

/-!
# Fourier one-norm bounds for small-bias distributions

Book items: Lemma 6.38, the Fourier one-norm product support lemma, Corollary 6.39.

Small-bias expectation bounds are obtained from the covariance characterization of Fourier
regularity. The product estimate uses the symmetric-difference convolution formula for Fourier
coefficients.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Lemma 6.38: an `ε`-biased density fools a real-valued function up to its
Fourier `1`-norm times `ε`. -/
theorem ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_mul
    (φ : ProbabilityDensity n) (f : {−1,1}^[n] → ℝ) {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 ≤ ε) :
    |φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) - mean f| ≤
      fourierOneNorm f * ε := by
  have hmixed :
      (𝔼 x : {−1,1}^[n], binaryFunctionOnSignCube φ x * f x) =
        φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) := by
    symm
    rw [ProbabilityDensity.expectation]
    apply Fintype.expect_equiv (binaryCubeSignEquiv n)
    intro x
    simp [binaryFunctionOnSignCube]
  have hmean : mean (binaryFunctionOnSignCube φ) = 1 := by
    rw [mean]
    calc
      (𝔼 x : {−1,1}^[n], binaryFunctionOnSignCube φ x) =
          𝔼 x : 𝔽₂^[n], φ x := by
        symm
        apply Fintype.expect_equiv (binaryCubeSignEquiv n)
        intro x
        simp [binaryFunctionOnSignCube]
      _ = 1 := φ.expect_eq_one
  have hcovariance :
      covariance (binaryFunctionOnSignCube φ) f =
        φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) - mean f := by
    rw [(covariance_eq_sum_fourierCoeff_mul
      (binaryFunctionOnSignCube φ) f).1, hmixed, hmean, one_mul]
  rw [← hcovariance]
  exact IsLowDegreeFourierRegular.abs_covariance_le_fourierOneNorm_mul
    (((φ.isBiased_iff_isFourierRegular ε).1 hφ).isLowDegreeFourierRegular n)
    (fourierDegree_le_dimension f) hε

/-- Exercise 6.32(a), refined Lemma 6.38: the constant Fourier coefficient contributes
no small-bias error. -/
theorem ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_sub
    (φ : ProbabilityDensity n) (f : {−1,1}^[n] → ℝ) {ε : ℝ}
    (hφ : φ.IsBiased ε) :
    |φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) - mean f| ≤
      (fourierOneNorm f - |fourierCoeff f ∅|) * ε := by
  classical
  let d := binaryFunctionOnSignCube φ
  have hmixed :
      (𝔼 x : {−1,1}^[n], d x * f x) =
        φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) := by
    symm
    rw [ProbabilityDensity.expectation]
    apply Fintype.expect_equiv (binaryCubeSignEquiv n)
    intro x
    simp [d, binaryFunctionOnSignCube]
  have hmean : mean d = 1 := by
    rw [mean]
    calc
      (𝔼 x : {−1,1}^[n], d x) = 𝔼 x : F₂Cube n, φ x := by
        symm
        apply Fintype.expect_equiv (binaryCubeSignEquiv n)
        intro x
        simp [d, binaryFunctionOnSignCube]
      _ = 1 := φ.expect_eq_one
  have hcovariance :
      covariance d f =
        φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x)) - mean f := by
    rw [(covariance_eq_sum_fourierCoeff_mul d f).1, hmixed, hmean, one_mul]
  have hregular : IsFourierRegular ε d :=
    (φ.isBiased_iff_isFourierRegular ε).1 hφ
  rw [← hcovariance, (covariance_eq_sum_fourierCoeff_mul d f).2]
  calc
    |∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
        fourierCoeff d S * fourierCoeff f S| ≤
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
          |fourierCoeff d S * fourierCoeff f S| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
        ε * |fourierCoeff f S| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hregular S
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_filter.mp hS).2))
        (abs_nonneg (fourierCoeff f S))
    _ = (fourierOneNorm f - |fourierCoeff f ∅|) * ε := by
      rw [← Finset.mul_sum]
      have hnonconstant :
          (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
            |fourierCoeff f S|) =
            fourierOneNorm f - |fourierCoeff f ∅| := by
        unfold fourierOneNorm
        rw [Finset.filter_ne']
        have hsum :=
          Finset.sum_erase_add
            (Finset.univ : Finset (Finset (Fin n)))
            (fun S ↦ |fourierCoeff f S|) (Finset.mem_univ ∅)
        linarith
      rw [hnonconstant]
      ring

/-- The Fourier `1`-norm is submultiplicative under pointwise multiplication. -/
theorem fourierOneNorm_pointwise_mul_le
    (f g : {−1,1}^[n] → ℝ) :
    fourierOneNorm (fun x ↦ f x * g x) ≤
      fourierOneNorm f * fourierOneNorm g := by
  classical
  have hsymmDiffSum (T : Finset (Fin n)) :
      (∑ S : Finset (Fin n), |fourierCoeff f (T ∆ S)|) =
        ∑ S : Finset (Fin n), |fourierCoeff f S| := by
    let e : Finset (Fin n) ≃ Finset (Fin n) :=
      { toFun := fun S ↦ T ∆ S
        invFun := fun S ↦ T ∆ S
        left_inv := by
          intro S
          ext i
          simp
        right_inv := by
          intro S
          ext i
          simp }
    apply Fintype.sum_equiv e
    intro S
    rfl
  unfold fourierOneNorm
  simp_rw [fourierCoeff_pointwise_mul]
  calc
    (∑ S : Finset (Fin n),
        |∑ T : Finset (Fin n),
          fourierCoeff f (T ∆ S) * fourierCoeff g T|) ≤
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          |fourierCoeff f (T ∆ S) * fourierCoeff g T| := by
      apply Finset.sum_le_sum
      intro S _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T : Finset (Fin n), ∑ S : Finset (Fin n),
          |fourierCoeff f (T ∆ S) * fourierCoeff g T| := by
      rw [Finset.sum_comm]
    _ = ∑ T : Finset (Fin n),
          (∑ S : Finset (Fin n), |fourierCoeff f S|) *
            |fourierCoeff g T| := by
      apply Finset.sum_congr rfl
      intro T _
      simp_rw [abs_mul]
      rw [← Finset.sum_mul, hsymmDiffSum]
    _ = (∑ S : Finset (Fin n), |fourierCoeff f S|) *
          ∑ T : Finset (Fin n), |fourierCoeff g T| := by
      rw [Finset.mul_sum]

/-- The Fourier `1`-norm of a pointwise square is at most the square of the original
Fourier `1`-norm. -/
theorem fourierOneNorm_sq_le (f : {−1,1}^[n] → ℝ) :
    fourierOneNorm (fun x ↦ f x ^ 2) ≤ fourierOneNorm f ^ 2 := by
  simpa [pow_two] using fourierOneNorm_pointwise_mul_le f f

/-- O'Donnell, Corollary 6.39: an `ε`-biased density estimates the second moment of a
real-valued function up to `‖f̂‖₁² ε`. -/
theorem ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le
    (φ : ProbabilityDensity n) (f : {−1,1}^[n] → ℝ) {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 ≤ ε) :
    |φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x) ^ 2) -
        mean (fun x ↦ f x ^ 2)| ≤
      fourierOneNorm f ^ 2 * ε := by
  calc
    |φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x) ^ 2) -
        mean (fun x ↦ f x ^ 2)| ≤
        fourierOneNorm (fun x ↦ f x ^ 2) * ε := by
      simpa only using
        φ.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_mul
          (fun x ↦ f x ^ 2) hφ hε
    _ ≤ fourierOneNorm f ^ 2 * ε :=
      mul_le_mul_of_nonneg_right (fourierOneNorm_sq_le f) hε

/-- Exercise 6.32(a), refined Corollary 6.39: the uniform second moment is the
constant coefficient of the pointwise square and therefore contributes no error. -/
theorem ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le_refined
    (φ : ProbabilityDensity n) (f : {−1,1}^[n] → ℝ) {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 ≤ ε) :
    |φ.expectation (fun x ↦ f (binaryCubeSignEquiv n x) ^ 2) -
        mean (fun x ↦ f x ^ 2)| ≤
      (fourierOneNorm f ^ 2 - uniformLpNorm 2 f ^ 2) * ε := by
  have hrefined :=
    φ.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_sub
      (fun x ↦ f x ^ 2) hφ
  have hmeanNonneg : 0 ≤ mean (fun x ↦ f x ^ 2) := by
    unfold mean
    exact Finset.expect_nonneg fun x _ ↦ sq_nonneg (f x)
  have hconstant :
      |fourierCoeff (fun x ↦ f x ^ 2) ∅| =
        uniformLpNorm 2 f ^ 2 := by
    rw [← mean_eq_fourierCoeff_empty, abs_of_nonneg hmeanNonneg,
      uniformLpNorm_two_sq_eq_expect_sq]
    rfl
  have hfactor :
      fourierOneNorm (fun x ↦ f x ^ 2) -
          |fourierCoeff (fun x ↦ f x ^ 2) ∅| ≤
        fourierOneNorm f ^ 2 - uniformLpNorm 2 f ^ 2 := by
    rw [hconstant]
    linarith [fourierOneNorm_sq_le f]
  exact hrefined.trans
    (mul_le_mul_of_nonneg_right hfactor hε)

end FABL
