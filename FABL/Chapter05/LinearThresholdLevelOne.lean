/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.IntegralThresholdRepresentations
public import FABL.Chapter05.KhintchineKahane
public import FABL.Chapter02.FKN
public import FABL.Chapter02.TotalInfluence.MajorityOptimality

/-!
# Level-one weight of linear threshold functions

Book items: Exercise 5.5 and Theorem 5.2.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- An affine linear form on the sign cube. -/
def affineLinearForm (a₀ : ℝ) (a : Fin n → ℝ) (x : {−1,1}^[n]) : ℝ :=
  a₀ + linearForm a x

/-- An affine linear form has Fourier degree at most one. -/
theorem fourierDegree_affineLinearForm_le_one (a₀ : ℝ) (a : Fin n → ℝ) :
    fourierDegree (affineLinearForm a₀ a) ≤ 1 := by
  change fourierDegree (fun x : {−1,1}^[n] ↦
    a₀ + ∑ i, a i * signValue (x i)) ≤ 1
  exact fourierDegree_affineSignLinearForm_le_one a₀ a

/-- The homogeneous form obtained by adjoining the affine constant as a new signed
coordinate. -/
def homogenizedAffineLinearForm (a₀ : ℝ) (a : Fin n → ℝ) : {−1,1}^[n + 1] → ℝ :=
  linearForm (Fin.cons a₀ a)

@[simp] theorem homogenizedAffineLinearForm_fin_cons
    (a₀ : ℝ) (a : Fin n → ℝ) (b : Sign) (x : {−1,1}^[n]) :
    homogenizedAffineLinearForm a₀ a (Fin.cons b x) =
      a₀ * signValue b + linearForm a x := by
  exact linearForm_fin_cons (Fin.cons a₀ a) b x

private theorem linearForm_neg_input (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    linearForm a (-x) = -linearForm a x := by
  have hsign (i : Fin n) : signValue ((-x) i) = -signValue (x i) := by
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi, signValue]
  simp only [linearForm, hsign, mul_neg, Finset.sum_neg_distrib]

private theorem expect_abs_neg_affineLinearForm (a₀ : ℝ) (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], |-a₀ + linearForm a x|) =
      𝔼 x : {−1,1}^[n], |affineLinearForm a₀ a x| := by
  apply Fintype.expect_equiv (Equiv.neg _)
  intro x
  rw [Equiv.neg_apply, affineLinearForm, linearForm_neg_input]
  rw [show a₀ + -linearForm a x = -(-a₀ + linearForm a x) by ring, abs_neg]

private theorem expect_sq_neg_affineLinearForm (a₀ : ℝ) (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], (-a₀ + linearForm a x) ^ 2) =
      𝔼 x : {−1,1}^[n], affineLinearForm a₀ a x ^ 2 := by
  apply Fintype.expect_equiv (Equiv.neg _)
  intro x
  rw [Equiv.neg_apply, affineLinearForm, linearForm_neg_input]
  ring

private theorem expect_sq_homogenizedAffineLinearForm
    (a₀ : ℝ) (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n + 1], homogenizedAffineLinearForm a₀ a x ^ 2) =
      𝔼 x : {−1,1}^[n], affineLinearForm a₀ a x ^ 2 := by
  rw [expect_fin_cons]
  simp only [homogenizedAffineLinearForm_fin_cons, signValue_one, mul_one,
    signValue_neg_one, mul_neg_one]
  rw [expect_sq_neg_affineLinearForm]
  change ((𝔼 x : {−1,1}^[n], affineLinearForm a₀ a x ^ 2) +
      (𝔼 x : {−1,1}^[n], affineLinearForm a₀ a x ^ 2)) / 2 =
    𝔼 x : {−1,1}^[n], affineLinearForm a₀ a x ^ 2
  ring

/-- Exercise 5.5(a): homogenization preserves the uniform `L¹` norm. -/
theorem uniformLpNorm_one_homogenizedAffineLinearForm
    (a₀ : ℝ) (a : Fin n → ℝ) :
    uniformLpNorm 1 (homogenizedAffineLinearForm a₀ a) =
      uniformLpNorm 1 (affineLinearForm a₀ a) := by
  simp only [show uniformLpNorm 1 (homogenizedAffineLinearForm a₀ a) =
      (𝔼 x : {−1,1}^[n + 1], |homogenizedAffineLinearForm a₀ a x|) by
        simp [uniformLpNorm],
    show uniformLpNorm 1 (affineLinearForm a₀ a) =
      (𝔼 x : {−1,1}^[n], |affineLinearForm a₀ a x|) by
        simp [uniformLpNorm]]
  rw [expect_fin_cons]
  simp only [homogenizedAffineLinearForm_fin_cons, signValue_one, mul_one,
    signValue_neg_one, mul_neg_one]
  rw [expect_abs_neg_affineLinearForm]
  change ((𝔼 x : {−1,1}^[n], |affineLinearForm a₀ a x|) +
      (𝔼 x : {−1,1}^[n], |affineLinearForm a₀ a x|)) / 2 =
    𝔼 x : {−1,1}^[n], |affineLinearForm a₀ a x|
  ring

/-- Exercise 5.5(a): homogenization preserves the square of the uniform `L²` norm. -/
theorem uniformLpNorm_two_sq_homogenizedAffineLinearForm
    (a₀ : ℝ) (a : Fin n → ℝ) :
    uniformLpNorm 2 (homogenizedAffineLinearForm a₀ a) ^ 2 =
      uniformLpNorm 2 (affineLinearForm a₀ a) ^ 2 := by
  simp_rw [uniformLpNorm_two_sq_eq_expect_sq]
  exact expect_sq_homogenizedAffineLinearForm a₀ a

/-- Exercise 5.5(a): homogenization preserves the uniform `L²` norm. -/
theorem uniformLpNorm_two_homogenizedAffineLinearForm
    (a₀ : ℝ) (a : Fin n → ℝ) :
    uniformLpNorm 2 (homogenizedAffineLinearForm a₀ a) =
      uniformLpNorm 2 (affineLinearForm a₀ a) := by
  rw [uniformLpNorm_two_eq_sqrt_expect_sq,
    uniformLpNorm_two_eq_sqrt_expect_sq,
    expect_sq_homogenizedAffineLinearForm]

private theorem rademacherNorm_real_eq_abs_linearForm
    (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    rademacherNorm a x = |linearForm a x| := by
  simp [rademacherNorm, linearForm, Real.norm_eq_abs, mul_comm]

/-- Exercise 5.5(b): the Khintchine--Kahane lower bound extends from homogeneous
linear forms to affine linear forms by homogenization. -/
theorem affineKhintchineKahane (a₀ : ℝ) (a : Fin n → ℝ) :
    (1 / Real.sqrt 2) * uniformLpNorm 2 (affineLinearForm a₀ a) ≤
      uniformLpNorm 1 (affineLinearForm a₀ a) := by
  have h := khintchineKahane (V := ℝ) (Fin.cons a₀ a)
  simp_rw [rademacherNorm_real_eq_abs_linearForm] at h
  simp_rw [sq_abs] at h
  change (1 / Real.sqrt 2) *
      Real.sqrt (𝔼 x, homogenizedAffineLinearForm a₀ a x ^ 2) ≤
    𝔼 x, |homogenizedAffineLinearForm a₀ a x| at h
  have hone :
      (𝔼 x, |homogenizedAffineLinearForm a₀ a x|) =
        uniformLpNorm 1 (homogenizedAffineLinearForm a₀ a) := by
    simp [uniformLpNorm]
  rw [← uniformLpNorm_two_eq_sqrt_expect_sq, hone,
    uniformLpNorm_two_homogenizedAffineLinearForm] at h
  rw [uniformLpNorm_one_homogenizedAffineLinearForm] at h
  exact h

/-- O'Donnell, Theorem 5.2: a Boolean linear threshold function has at least one
half of its Fourier weight on degrees zero and one. -/
theorem one_half_le_fourierWeightAtMost_one_of_isLinearThreshold
    (f : BooleanFunction n) (hf : IsLinearThreshold f) :
    1 / 2 ≤ fourierWeightAtMost 1 f.toReal := by
  classical
  obtain ⟨a₀, a, hrep, hp⟩ := exists_integer_linearThresholdRepresentation f hf
  let p : {−1,1}^[n] → ℝ :=
    affineLinearForm (a₀ : ℝ) (fun i ↦ (a i : ℝ))
  have hrep' : IsPolynomialThresholdRepresentation f p := by
    intro x
    simpa [p, affineLinearForm, linearForm] using hrep x
  have hp' (x : {−1,1}^[n]) : p x ≠ 0 := by
    simpa [p, affineLinearForm, linearForm] using hp x
  have hdegree : fourierDegree p ≤ 1 := by
    simpa [p] using
      fourierDegree_affineLinearForm_le_one (a₀ : ℝ) (fun i ↦ (a i : ℝ))
  have hpointwise (x : {−1,1}^[n]) : f.toReal x * p x = |p x| := by
    by_cases hx : 0 ≤ p x
    · simp [BooleanFunction.toReal, hrep' x, thresholdSign_of_nonneg hx,
        abs_of_nonneg hx]
    · have hx' : p x < 0 := lt_of_not_ge hx
      simp [BooleanFunction.toReal, hrep' x, thresholdSign_of_neg hx', abs_of_neg hx']
  have hnormInner : uniformLpNorm 1 p = ⟪f.toReal, p⟫ᵤ := by
    rw [uniformLpNorm, uniformInner, RCLike.wInner_cWeight_eq_expect]
    simp only [Real.rpow_eq_pow, inv_one, Real.rpow_one, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_comm, hpointwise]
  let low : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S ↦ S.card ≤ 1
  have hrestrict :
      (∑ S : Finset (Fin n), fourierCoeff f.toReal S * fourierCoeff p S) =
        ∑ S ∈ low, fourierCoeff f.toReal S * fourierCoeff p S := by
    symm
    apply Finset.sum_subset (Finset.subset_univ low)
    intro S _ hS
    have hcard : 1 < S.card := by
      simpa [low] using hS
    have hpzero := (fourierDegree_le_iff p 1).1 hdegree S hcard
    simp [hpzero]
  have hnormSum :
      uniformLpNorm 1 p =
        ∑ S ∈ low, fourierCoeff f.toReal S * fourierCoeff p S := by
    calc
      uniformLpNorm 1 p = ⟪f.toReal, p⟫ᵤ := hnormInner
      _ = ∑ S : Finset (Fin n),
          fourierCoeff f.toReal S * fourierCoeff p S := plancherel f.toReal p
      _ = ∑ S ∈ low,
          fourierCoeff f.toReal S * fourierCoeff p S := hrestrict
  have hpEnergy :
      (∑ S ∈ low, fourierCoeff p S ^ 2) = uniformLpNorm 2 p ^ 2 := by
    rw [uniformLpNorm_two_sq_eq_uniformInner, parseval]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hcard : 1 < S.card := by
      simpa [low] using hS
    have hpzero := (fourierDegree_le_iff p 1).1 hdegree S hcard
    simp [hpzero]
  have hcauchy :
      uniformLpNorm 1 p ^ 2 ≤
        (∑ S ∈ low, fourierCoeff f.toReal S ^ 2) *
          ∑ S ∈ low, fourierCoeff p S ^ 2 := by
    rw [hnormSum]
    exact Finset.sum_mul_sq_le_sq_mul_sq low
      (fun S ↦ fourierCoeff f.toReal S) (fun S ↦ fourierCoeff p S)
  have hnormBound :
      uniformLpNorm 1 p ^ 2 ≤
        fourierWeightAtMost 1 f.toReal * uniformLpNorm 2 p ^ 2 := by
    calc
      uniformLpNorm 1 p ^ 2 ≤
          (∑ S ∈ low, fourierCoeff f.toReal S ^ 2) *
            ∑ S ∈ low, fourierCoeff p S ^ 2 := hcauchy
      _ = fourierWeightAtMost 1 f.toReal * uniformLpNorm 2 p ^ 2 := by
        rw [hpEnergy]
        simp [low, fourierWeightAtMost, fourierWeight]
  have hkhintchine :
      (1 / Real.sqrt 2) * uniformLpNorm 2 p ≤ uniformLpNorm 1 p := by
    simpa [p] using
      affineKhintchineKahane (a₀ : ℝ) (fun i ↦ (a i : ℝ))
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwoNonneg : 0 ≤ uniformLpNorm 2 p := by
    rw [uniformLpNorm_two_eq_sqrt_expect_sq]
    positivity
  have honeNonneg : 0 ≤ uniformLpNorm 1 p := by
    rw [show uniformLpNorm 1 p = 𝔼 x, |p x| by simp [uniformLpNorm]]
    exact Finset.expect_nonneg fun x _ ↦ abs_nonneg (p x)
  have hkhintchineSq :
      ((1 / Real.sqrt 2) * uniformLpNorm 2 p) ^ 2 ≤
        uniformLpNorm 1 p ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (one_div_pos.mpr hsqrt2pos).le htwoNonneg)
      honeNonneg).2 hkhintchine
  have hnormTwoSqPos : 0 < uniformLpNorm 2 p ^ 2 := by
    rw [uniformLpNorm_two_sq_eq_expect_sq]
    apply Finset.expect_pos'
    · intro x _
      exact sq_nonneg (p x)
    · let x : {−1,1}^[n] := fun _ ↦ 1
      exact ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero (hp' x)⟩
  have hcancel :
      (1 / Real.sqrt 2) ^ 2 * uniformLpNorm 2 p ^ 2 ≤
        fourierWeightAtMost 1 f.toReal * uniformLpNorm 2 p ^ 2 := by
    calc
      (1 / Real.sqrt 2) ^ 2 * uniformLpNorm 2 p ^ 2 =
          ((1 / Real.sqrt 2) * uniformLpNorm 2 p) ^ 2 := by ring
      _ ≤ uniformLpNorm 1 p ^ 2 := hkhintchineSq
      _ ≤ fourierWeightAtMost 1 f.toReal * uniformLpNorm 2 p ^ 2 := hnormBound
  have hcoefficient :
      (1 / Real.sqrt 2) ^ 2 ≤ fourierWeightAtMost 1 f.toReal :=
    le_of_mul_le_mul_right hcancel hnormTwoSqPos
  calc
    1 / 2 = (1 / Real.sqrt 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ fourierWeightAtMost 1 f.toReal := hcoefficient

end FABL
