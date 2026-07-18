/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.FKN
public import FABL.Chapter02.NoiseStability.GaussianDisagreement

/-!
# Correlated majority sums

Book item: Exercise 5.19.

The mean and covariance calculation for the normalized sum of a correlated pair of sign strings.
-/

open Finset WithLp
open scoped BigOperators BooleanCube RealInnerProductSpace

@[expose] public section

namespace FABL

variable {n : ℕ}

theorem pmfExpectation_correlatedPairPMF_fst
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) :
    pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ f xy.1) =
      pmfExpectation (uniformPMF {−1,1}^[n]) f := by
  rw [correlatedPairPMF, pmfExpectation_bind]
  simp_rw [pmfExpectation_map]
  apply congrArg (pmfExpectation (uniformPMF {−1,1}^[n]))
  funext x
  change pmfExpectation (noiseKernel ρ hρ x) (fun _ ↦ f x) = f x
  exact pmfExpectation_const (noiseKernel ρ hρ x) (f x)

theorem pmfExpectation_correlatedPairPMF_snd
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) :
    pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ f xy.2) =
      pmfExpectation (uniformPMF {−1,1}^[n]) f := by
  have hswap := congrArg
    (fun p : PMF ({−1,1}^[n] × {−1,1}^[n]) ↦
      pmfExpectation p (fun xy ↦ f xy.2))
    (correlatedPairPMF_map_swap (n := n) ρ hρ)
  rw [pmfExpectation_map] at hswap
  exact hswap.symm.trans (pmfExpectation_correlatedPairPMF_fst ρ hρ f)

private theorem pmfExpectation_noiseKernel_linearForm
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x : {−1,1}^[n]) (a : Fin n → ℝ) :
    pmfExpectation (noiseKernel ρ hρ x) (linearForm a) =
      ρ * linearForm a x := by
  classical
  unfold linearForm
  rw [show
      pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ ∑ i, a i * signValue (y i)) =
        ∑ i, pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ a i * signValue (y i)) by
    unfold pmfExpectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]]
  calc
    ∑ i, pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ a i * signValue (y i)) =
        ∑ i, a i * pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ signValue (y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pmfExpectation_const_mul (noiseKernel ρ hρ x) (a i)
        (fun y ↦ signValue (y i))
    _ = ∑ i, a i * (ρ * signValue (x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (fun y : {−1,1}^[n] ↦ signValue (y i)) = monomial {i} by
        funext y
        simp [monomial]]
      rw [pmfExpectation_noiseKernel_monomial]
      simp [monomial]
    _ = ρ * ∑ i, a i * signValue (x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem pmfExpectation_correlatedPairPMF_linearForm_mul
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (a : Fin n → ℝ) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ linearForm a xy.1 * linearForm a xy.2) =
      ρ * ∑ i, a i ^ 2 := by
  rw [correlatedPairPMF, pmfExpectation_bind]
  have hconditional (x : {−1,1}^[n]) :
      pmfExpectation ((noiseKernel ρ hρ x).map fun y ↦ (x, y))
          (fun xy ↦ linearForm a xy.1 * linearForm a xy.2) =
        ρ * linearForm a x ^ 2 := by
    rw [pmfExpectation_map]
    change pmfExpectation (noiseKernel ρ hρ x)
      (fun y ↦ linearForm a x * linearForm a y) = _
    rw [pmfExpectation_const_mul, pmfExpectation_noiseKernel_linearForm]
    ring
  simp_rw [hconditional]
  rw [pmfExpectation_const_mul, pmfExpectation_uniformPMF_eq_expect,
    expect_linearForm_sq]

private theorem normalizedMargin_eq_linearForm
    (n : ℕ) (x : {−1,1}^[n]) :
    (Real.sqrt n)⁻¹ * ∑ i, signValue (x i) =
      linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) x := by
  rw [linearForm, Finset.mul_sum]

private theorem sum_normalizedCoefficient_sq {n : ℕ} (hn : 0 < n) :
    ∑ _ : Fin n, (Real.sqrt n)⁻¹ ^ 2 = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_ne_zero').2 (by exact_mod_cast hn)
  rw [inv_pow]
  field_simp
  exact (Real.sq_sqrt (Nat.cast_nonneg n)).symm

private theorem normalizedCorrelatedPairSum_first_mean
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy)) = 0 := by
  simp_rw [correlationFirstCoordinate_normalizedCorrelatedPairSum,
    normalizedMargin_eq_linearForm]
  rw [pmfExpectation_correlatedPairPMF_fst,
    pmfExpectation_uniformPMF_eq_expect]
  classical
  unfold linearForm
  rw [Finset.expect_sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.mul_expect]
  simp [show (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} by
    funext x
    simp [monomial], expect_monomial]

private theorem normalizedCorrelatedPairSum_second_mean
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ correlationSecondCoordinate (normalizedCorrelatedPairSum n xy)) = 0 := by
  simp_rw [correlationSecondCoordinate_normalizedCorrelatedPairSum,
    normalizedMargin_eq_linearForm]
  rw [pmfExpectation_correlatedPairPMF_snd,
    pmfExpectation_uniformPMF_eq_expect]
  classical
  unfold linearForm
  rw [Finset.expect_sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.mul_expect]
  simp [show (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} by
    funext x
    simp [monomial], expect_monomial]

private theorem normalizedCorrelatedPairSum_first_secondMoment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) ^ 2) = 1 := by
  simp_rw [correlationFirstCoordinate_normalizedCorrelatedPairSum,
    normalizedMargin_eq_linearForm]
  calc
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) xy.1 ^ 2) =
        pmfExpectation (uniformPMF {−1,1}^[n])
          (fun x ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) x ^ 2) :=
      pmfExpectation_correlatedPairPMF_fst (n := n) ρ hρ
        (fun x ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) x ^ 2)
    _ = 1 := by
      rw [pmfExpectation_uniformPMF_eq_expect, expect_linearForm_sq,
        sum_normalizedCoefficient_sq hn]

private theorem normalizedCorrelatedPairSum_second_secondMoment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) ^ 2) = 1 := by
  simp_rw [correlationSecondCoordinate_normalizedCorrelatedPairSum,
    normalizedMargin_eq_linearForm]
  calc
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) xy.2 ^ 2) =
        pmfExpectation (uniformPMF {−1,1}^[n])
          (fun x ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) x ^ 2) :=
      pmfExpectation_correlatedPairPMF_snd (n := n) ρ hρ
        (fun x ↦ linearForm (fun _ : Fin n ↦ (Real.sqrt n)⁻¹) x ^ 2)
    _ = 1 := by
      rw [pmfExpectation_uniformPMF_eq_expect, expect_linearForm_sq,
        sum_normalizedCoefficient_sq hn]

private theorem normalizedCorrelatedPairSum_crossMoment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) *
          correlationSecondCoordinate (normalizedCorrelatedPairSum n xy)) = ρ := by
  simp_rw [correlationFirstCoordinate_normalizedCorrelatedPairSum,
    correlationSecondCoordinate_normalizedCorrelatedPairSum,
    normalizedMargin_eq_linearForm]
  rw [pmfExpectation_correlatedPairPMF_linearForm_mul,
    sum_normalizedCoefficient_sq hn, mul_one]

/-- Exercise 5.19: the two normalized correlated vote margins are centered, have unit second
moments, and have cross moment `ρ`. -/
theorem exercise5_19
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy)) = 0 ∧
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ correlationSecondCoordinate (normalizedCorrelatedPairSum n xy)) = 0 ∧
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) ^ 2) = 1 ∧
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) ^ 2) = 1 ∧
      pmfExpectation (correlatedPairPMF ρ hρ)
          (fun xy ↦ correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) *
            correlationSecondCoordinate (normalizedCorrelatedPairSum n xy)) = ρ := by
  exact ⟨normalizedCorrelatedPairSum_first_mean ρ hρ,
    normalizedCorrelatedPairSum_second_mean ρ hρ,
    normalizedCorrelatedPairSum_first_secondMoment ρ hρ hn,
    normalizedCorrelatedPairSum_second_secondMoment ρ hρ hn,
    normalizedCorrelatedPairSum_crossMoment ρ hρ hn⟩

/-- The mean vector in Exercise 5.19 is zero, expressed by testing every linear functional. -/
theorem normalizedCorrelatedPairSum_projection_mean
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ}
    (t : CorrelationPlane) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ inner ℝ (normalizedCorrelatedPairSum n xy) t) = 0 := by
  have hfirst := normalizedCorrelatedPairSum_first_mean (n := n) ρ hρ
  have hsecond := normalizedCorrelatedPairSum_second_mean (n := n) ρ hρ
  rw [show (fun xy ↦ inner ℝ (normalizedCorrelatedPairSum n xy) t) =
      fun xy ↦
        correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) * (ofLp t).1 +
        correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) * (ofLp t).2 by
    funext xy
    simp only [correlationFirstCoordinate, correlationSecondCoordinate,
      prod_inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring]
  rw [pmfExpectation_add, pmfExpectation_mul_const, pmfExpectation_mul_const,
    hfirst, hsecond]
  ring

/-- The covariance matrix in Exercise 5.19 is `[[1, ρ], [ρ, 1]]`, expressed by its quadratic
form on every direction. -/
theorem normalizedCorrelatedPairSum_projection_secondMoment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : 0 < n)
    (t : CorrelationPlane) :
    pmfExpectation (correlatedPairPMF ρ hρ)
        (fun xy ↦ inner ℝ (normalizedCorrelatedPairSum n xy) t ^ 2) =
      correlationQuadraticForm ρ t := by
  have hfirst := normalizedCorrelatedPairSum_first_secondMoment ρ hρ hn
  have hsecond := normalizedCorrelatedPairSum_second_secondMoment ρ hρ hn
  have hcross := normalizedCorrelatedPairSum_crossMoment ρ hρ hn
  rw [show (fun xy ↦ inner ℝ (normalizedCorrelatedPairSum n xy) t ^ 2) =
      fun xy ↦
        correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) ^ 2 * (ofLp t).1 ^ 2 +
        2 * ((ofLp t).1 * (ofLp t).2) *
          (correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) *
            correlationSecondCoordinate (normalizedCorrelatedPairSum n xy)) +
        correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) ^ 2 * (ofLp t).2 ^ 2 by
    funext xy
    simp [correlationFirstCoordinate, correlationSecondCoordinate,
      prod_inner_apply, RCLike.inner_apply]
    ring]
  rw [pmfExpectation_add, pmfExpectation_add]
  rw [pmfExpectation_mul_const, pmfExpectation_const_mul, pmfExpectation_mul_const]
  rw [hfirst, hcross, hsecond]
  unfold correlationQuadraticForm
  ring

end FABL
