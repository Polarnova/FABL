/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.LaplacianAndPoincare

/-!
# Khintchine--Kahane inequality

Book item: Exercise 2.55, recalled in Section 5.1.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The norm of a signed sum of vectors. -/
noncomputable def rademacherNorm (w : Fin n → V) (x : {−1,1}^[n]) : ℝ :=
  ‖∑ i, signValue (x i) • w i‖

private theorem signedSum_flipCoordinate (w : Fin n → V) (x : {−1,1}^[n])
    (i : Fin n) :
    (∑ j, signValue (flipCoordinate x i j) • w j) =
      (∑ j, signValue (x j) • w j) - 2 • (signValue (x i) • w i) := by
  classical
  rw [show (∑ j, signValue (flipCoordinate x i j) • w j) =
      signValue (flipCoordinate x i i) • w i +
        ∑ j ∈ (Finset.univ.erase i), signValue (flipCoordinate x i j) • w j by
    calc
      (∑ j, signValue (flipCoordinate x i j) • w j) =
          (∑ j ∈ (Finset.univ.erase i), signValue (flipCoordinate x i j) • w j) +
            signValue (flipCoordinate x i i) • w i :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
      _ = _ := add_comm _ _]
  rw [show (∑ j, signValue (x j) • w j) =
      signValue (x i) • w i +
        ∑ j ∈ (Finset.univ.erase i), signValue (x j) • w j by
    calc
      (∑ j, signValue (x j) • w j) =
          (∑ j ∈ (Finset.univ.erase i), signValue (x j) • w j) +
            signValue (x i) • w i :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
      _ = _ := add_comm _ _]
  have hflip : signValue (flipCoordinate x i i) = -signValue (x i) := by
    rcases Int.units_eq_one_or (x i) with hi | hi <;>
      simp [flipCoordinate, setCoordinate, hi, signValue]
  have hsame : ∀ j ∈ Finset.univ.erase i,
      signValue (flipCoordinate x i j) • w j = signValue (x j) • w j := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [flipCoordinate, setCoordinate, hji]
  rw [hflip, Finset.sum_congr rfl hsame]
  module

private theorem sum_signedSum_flipCoordinate (w : Fin n → V) (x : {−1,1}^[n]) :
    (∑ i, ∑ j, signValue (flipCoordinate x i j) • w j) =
      (n : ℝ) • (∑ j, signValue (x j) • w j) -
        2 • (∑ j, signValue (x j) • w j) := by
  simp_rw [signedSum_flipCoordinate]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.smul_sum]
  simp only [Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℝ]

private theorem monomial_neg_input (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    monomial S (-x) = (-1 : ℝ) ^ S.card * monomial S x := by
  simp [monomial, signValue, Finset.prod_neg]

private theorem fourierCoeff_eq_zero_of_even_of_odd_card
    {f : {−1,1}^[n] → ℝ} (hf : Function.Even f)
    (S : Finset (Fin n)) (hS : Odd S.card) :
    fourierCoeff f S = 0 := by
  have hodd : Function.Odd (fun x ↦ f x * monomial S x) := by
    intro x
    change f (-x) * monomial S (-x) = -(f x * monomial S x)
    rw [hf x, monomial_neg_input, hS.neg_one_pow]
    ring
  unfold fourierCoeff
  rw [Fintype.expect_eq_sum_div_card, hodd.sum_eq_zero, zero_div]

/-- Exercise 2.28: the Poincaré inequality improves by a factor of two for even functions. -/
theorem two_mul_variance_le_totalInfluence_of_even
    (f : {−1,1}^[n] → ℝ) (hf : Function.Even f) :
    2 * variance f ≤ totalInfluence f := by
  classical
  rw [(variance_eq_sum_sq_fourierCoeff f).2,
    totalInfluence_eq_sum_card_mul_sq_fourierCoeff, Finset.mul_sum,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  rw [if_pos hS]
  by_cases hEven : Even S.card
  · obtain ⟨k, hk⟩ := hEven
    have hcard : (2 : ℝ) ≤ S.card := by
      have hcardNat : 2 ≤ S.card := by
        have hpositive := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
        omega
      exact_mod_cast hcardNat
    nlinarith [sq_nonneg (fourierCoeff f S)]
  · have hOdd : Odd S.card := Nat.not_even_iff_odd.mp hEven
    rw [fourierCoeff_eq_zero_of_even_of_odd_card hf S hOdd]
    simp

/-- The norm of a signed vector sum is unchanged when all signs are negated. -/
theorem rademacherNorm_even (w : Fin n → V) : Function.Even (rademacherNorm w) := by
  intro x
  change ‖∑ i, signValue ((-x) i) • w i‖ = ‖∑ i, signValue (x i) • w i‖
  have hsign (i : Fin n) : signValue ((-x) i) = -signValue (x i) := by
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi, signValue]
  simp_rw [hsign, neg_smul]
  rw [Finset.sum_neg_distrib, norm_neg]

/-- Exercise 2.55(a): the Boolean-cube Laplacian of the signed-sum norm is bounded pointwise
by the norm itself. -/
theorem laplacian_rademacherNorm_le (w : Fin n → V) (x : {−1,1}^[n]) :
    laplacian (rademacherNorm w) x ≤ rademacherNorm w x := by
  let v : V := ∑ j, signValue (x j) • w j
  have hneighbors :
      ((n : ℝ) - 2) * ‖v‖ ≤
        ∑ i, ‖∑ j, signValue (flipCoordinate x i j) • w j‖ := by
    calc
      ((n : ℝ) - 2) * ‖v‖ ≤ |(n : ℝ) - 2| * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ = ‖((n : ℝ) - 2) • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖(n : ℝ) • v - 2 • v‖ := by
        congr 1
        module
      _ = ‖∑ i, ∑ j, signValue (flipCoordinate x i j) • w j‖ := by
        rw [sum_signedSum_flipCoordinate]
      _ ≤ ∑ i, ‖∑ j, signValue (flipCoordinate x i j) • w j‖ :=
        norm_sum_le _ _
  rw [laplacian_eq_sum_sub_flip_div_two]
  change (∑ i, (‖v‖ - ‖∑ j, signValue (flipCoordinate x i j) • w j‖) / 2) ≤ ‖v‖
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- Exercise 2.55(b): twice the variance of the signed-sum norm is bounded by its second
moment. -/
theorem two_mul_variance_rademacherNorm_le_secondMoment (w : Fin n → V) :
    2 * variance (rademacherNorm w) ≤ 𝔼 x, rademacherNorm w x ^ 2 := by
  have hPoincare :=
    two_mul_variance_le_totalInfluence_of_even (rademacherNorm w) (rademacherNorm_even w)
  apply hPoincare.trans
  rw [← uniformInner_laplacian_eq_totalInfluence, uniformInner,
    RCLike.wInner_cWeight_eq_expect]
  apply Finset.expect_le_expect
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  calc
    laplacian (rademacherNorm w) x * rademacherNorm w x ≤
        rademacherNorm w x * rademacherNorm w x :=
      mul_le_mul_of_nonneg_right (laplacian_rademacherNorm_le w x) (norm_nonneg _)
    _ = rademacherNorm w x ^ 2 := by ring

/-- Exercise 2.55(b), the Khintchine--Kahane inequality with its sharp universal
`1 / √2` constant. -/
theorem khintchineKahane (w : Fin n → V) :
    (1 / Real.sqrt 2) * Real.sqrt (𝔼 x, rademacherNorm w x ^ 2) ≤
      𝔼 x, rademacherNorm w x := by
  let q : ℝ := 𝔼 x, rademacherNorm w x ^ 2
  let m : ℝ := 𝔼 x, rademacherNorm w x
  have hvariance := two_mul_variance_rademacherNorm_le_secondMoment w
  rw [(variance_eq_sum_sq_fourierCoeff (rademacherNorm w)).1] at hvariance
  change 2 * (q - m ^ 2) ≤ q at hvariance
  have hq : 0 ≤ q := Finset.expect_nonneg fun x _ ↦ sq_nonneg (rademacherNorm w x)
  have hm : 0 ≤ m := Finset.expect_nonneg fun x _ ↦ norm_nonneg _
  have hq_le : q ≤ 2 * m ^ 2 := by linarith
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare :
      ((1 / Real.sqrt 2) * Real.sqrt q) ^ 2 ≤ m ^ 2 := by
    have hsqrtq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
    have hsqrtTwoSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [ne_of_gt hsqrtTwo]
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg (by positivity) (Real.sqrt_nonneg q)) hm).mp hsquare

private theorem rademacherNorm_two_equal_weights (x : {−1,1}^[2]) :
    rademacherNorm (fun _ : Fin 2 ↦ (1 : ℝ)) x = 1 + monomial {0, 1} x := by
  rcases Int.units_eq_one_or (x 0) with h0 | h0 <;>
    rcases Int.units_eq_one_or (x 1) with h1 | h1 <;>
    norm_num [rademacherNorm, monomial, h0, h1, signValue, Fin.sum_univ_two]

/-- Exercise 2.55(c): two equal real weights have first absolute moment one and second
moment two. -/
theorem rademacherNorm_two_equal_weights_moments :
    (𝔼 x, rademacherNorm (fun _ : Fin 2 ↦ (1 : ℝ)) x) = 1 ∧
      (𝔼 x, rademacherNorm (fun _ : Fin 2 ↦ (1 : ℝ)) x ^ 2) = 2 := by
  constructor
  · simp_rw [rademacherNorm_two_equal_weights]
    rw [Finset.expect_add_distrib, Fintype.expect_const, expect_monomial]
    norm_num
  · simp_rw [rademacherNorm_two_equal_weights]
    calc
      (𝔼 x : {−1,1}^[2], (1 + monomial {0, 1} x) ^ 2) =
          𝔼 x : {−1,1}^[2], (2 + 2 * monomial {0, 1} x) := by
        apply Finset.expect_congr rfl
        intro x _
        nlinarith [monomial_sq ({0, 1} : Finset (Fin 2)) x]
      _ = 2 := by
        rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
          expect_monomial]
        norm_num

/-- Exercise 2.55(c): the two-equal-weight example forces every universal
Khintchine--Kahane constant to be at most `1 / √2`. -/
theorem khintchineKahane_constant_le_inv_sqrt_two (c : ℝ)
    (h : c * Real.sqrt
        (𝔼 x, rademacherNorm (fun _ : Fin 2 ↦ (1 : ℝ)) x ^ 2) ≤
      𝔼 x, rademacherNorm (fun _ : Fin 2 ↦ (1 : ℝ)) x) :
    c ≤ 1 / Real.sqrt 2 := by
  rw [rademacherNorm_two_equal_weights_moments.1,
    rademacherNorm_two_equal_weights_moments.2] at h
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  apply (le_div_iff₀ hsqrtTwo).2
  simpa [mul_comm] using h

end FABL
