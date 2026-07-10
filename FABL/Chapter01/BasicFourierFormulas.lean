/-
Copyright (c) 2026 FABL contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FABL contributors
-/
module

public import FABL.Chapter01.ParityBasis

/-!
# Basic Fourier formulas

Formalization of Section 1.4 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A sign-valued Boolean function on the sign cube. -/
abbrev BooleanFunction (n : ℕ) := {−1,1}^[n] → Sign

/-- Regard a sign-valued function as real-valued. -/
def BooleanFunction.toReal (f : BooleanFunction n) : {−1,1}^[n] → ℝ :=
  fun x ↦ signValue (f x)

/-- Uniform probability of a decidable event on a finite nonempty type. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  𝔼 x, if P x then (1 : ℝ) else 0

/-- O'Donnell, Definition 1.10: relative Hamming distance, obtained by normalizing Mathlib's
`hammingDist`. -/
noncomputable def relativeHammingDist {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (f g : Ω → β) : ℝ :=
  (hammingDist f g : ℝ) / Fintype.card Ω

/-- Relative Hamming distance is the uniform probability that two functions disagree. -/
theorem uniformProbability_ne_eq_relativeHammingDist {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq β] (f g : Ω → β) :
    uniformProbability (fun x ↦ f x ≠ g x) = relativeHammingDist f g := by
  classical
  rw [uniformProbability, Fintype.expect_eq_sum_div_card, relativeHammingDist, hammingDist]
  congr 1
  simp only [Finset.sum_boole]

/-- O'Donnell, Definition 1.11: the uniform mean of a real-valued function. -/
noncomputable def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  𝔼 x, f x

/-- A function is balanced (unbiased) when its uniform mean is zero. -/
def IsBalanced {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : Prop :=
  mean f = 0

/-- The variance of a real-valued function under the uniform distribution. -/
noncomputable def variance {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  𝔼 x, (f x - mean f) ^ 2

/-- The covariance of two real-valued functions under the uniform distribution. -/
noncomputable def covariance {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) : ℝ :=
  𝔼 x, (f x - mean f) * (g x - mean g)

/-- O'Donnell, Proposition 1.8: a Fourier coefficient is an inner product with a parity. -/
theorem fourierCoeff_eq_uniformInner (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff f S = ⟪f, monomial S⟫ᵤ := by
  simp [fourierCoeff, uniformInner, RCLike.wInner_cWeight_eq_expect,
    RCLike.inner_apply, mul_comm]

/-- Parseval's identity on `{-1,1}ⁿ`. -/
theorem parseval (f : {−1,1}^[n] → ℝ) :
    ⟪f, f⟫ᵤ = ∑ S, fourierCoeff f S ^ 2 := by
  classical
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  calc
    (𝔼 x, f x * f x) =
        𝔼 x, ((∑ S, fourierCoeff f S * monomial S x) * f x) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← fourier_expansion f x]
    _ = 𝔼 x, ∑ S, (fourierCoeff f S * monomial S x) * f x := by
      congr 1
      funext x
      rw [Finset.sum_mul]
    _ = ∑ S, 𝔼 x, (fourierCoeff f S * monomial S x) * f x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S, fourierCoeff f S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _
      simp_rw [mul_assoc]
      rw [← Finset.mul_expect]
      simp [fourierCoeff, pow_two, mul_comm]

/-- The Boolean-valued specialization following Parseval's identity. -/
theorem sum_sq_fourierCoeff_eq_one (f : BooleanFunction n) :
    ∑ S, fourierCoeff f.toReal S ^ 2 = 1 := by
  rw [← parseval, uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp only [RCLike.inner_apply, BooleanFunction.toReal, starRingEnd_apply, star_trivial]
  calc
    (𝔼 x, signValue (f x) * signValue (f x)) = 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      rcases Int.units_eq_one_or (f x) with h | h <;> simp [h]
    _ = 1 := Fintype.expect_const 1

/-- The square of the normalized `L²` quantity is the normalized self-inner product. -/
theorem uniformLpNorm_two_sq_eq_uniformInner (f : {−1,1}^[n] → ℝ) :
    uniformLpNorm 2 f ^ 2 = ⟪f, f⟫ᵤ := by
  rw [uniformLpNorm, uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  have hmoment : (𝔼 x, |f x|.rpow 2) = 𝔼 x, f x ^ 2 := by
    apply Finset.expect_congr rfl
    intro x _
    change |f x| ^ (2 : ℝ) = f x ^ 2
    rw [Real.rpow_two, sq_abs]
  rw [hmoment]
  have hnonneg : 0 ≤ (𝔼 x, f x ^ 2) := by
    rw [Fintype.expect_eq_sum_div_card]
    positivity
  have hsquare : ((𝔼 x, f x ^ 2).rpow ((2 : ℝ)⁻¹)) ^ 2 = 𝔼 x, f x ^ 2 := by
    simpa using Real.rpow_inv_natCast_pow hnonneg (by norm_num : (2 : ℕ) ≠ 0)
  rw [hsquare]
  apply Finset.expect_congr rfl
  intro x _
  ring

/-- O'Donnell, Definition 1.3: the normalized `L²` quantity is the square root of the normalized
self-inner product. -/
theorem uniformLpNorm_two_eq_sqrt_uniformInner (f : {−1,1}^[n] → ℝ) :
    uniformLpNorm 2 f = Real.sqrt ⟪f, f⟫ᵤ := by
  have hnonneg : 0 ≤ uniformLpNorm 2 f := by
    unfold uniformLpNorm
    apply Real.rpow_nonneg
    rw [Fintype.expect_eq_sum_div_card]
    apply div_nonneg
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
    · positivity
  calc
    uniformLpNorm 2 f = |uniformLpNorm 2 f| := (abs_of_nonneg hnonneg).symm
    _ = Real.sqrt (uniformLpNorm 2 f ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ⟪f, f⟫ᵤ := by rw [uniformLpNorm_two_sq_eq_uniformInner]

/-- Plancherel's identity on `{-1,1}ⁿ`. -/
theorem plancherel (f g : {−1,1}^[n] → ℝ) :
    ⟪f, g⟫ᵤ = ∑ S, fourierCoeff f S * fourierCoeff g S := by
  classical
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  calc
    (𝔼 x, g x * f x) =
        𝔼 x, ((∑ S, fourierCoeff g S * monomial S x) * f x) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← fourier_expansion g x]
    _ = 𝔼 x, ∑ S, (fourierCoeff g S * monomial S x) * f x := by
      congr 1
      funext x
      rw [Finset.sum_mul]
    _ = ∑ S, 𝔼 x, (fourierCoeff g S * monomial S x) * f x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S, fourierCoeff f S * fourierCoeff g S := by
      apply Finset.sum_congr rfl
      intro S _
      simp_rw [mul_assoc]
      rw [← Finset.mul_expect]
      simp [fourierCoeff, mul_comm]

/-- O'Donnell, Proposition 1.9: correlation of sign-valued functions is one minus twice their
relative Hamming distance. -/
theorem uniformInner_eq_one_sub_two_mul_relativeHammingDist (f g : BooleanFunction n) :
    ⟪f.toReal, g.toReal⟫ᵤ = 1 - 2 * relativeHammingDist f g := by
  classical
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect,
    ← uniformProbability_ne_eq_relativeHammingDist f g, uniformProbability]
  simp only [RCLike.inner_apply, BooleanFunction.toReal, starRingEnd_apply, star_trivial]
  calc
    (𝔼 x, signValue (g x) * signValue (f x)) =
        (𝔼 x, (1 - 2 * (if f x ≠ g x then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro x _
      rcases Int.units_eq_one_or (f x) with hf | hf <;>
        rcases Int.units_eq_one_or (g x) with hg | hg <;>
        simp [hf, hg] <;> norm_num
    _ = 1 - 2 * (𝔼 x, if f x ≠ g x then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect]
      simp

/-- The first equality in O'Donnell, Proposition 1.9: correlation is agreement probability minus
disagreement probability. -/
theorem uniformInner_eq_uniformProbability_eq_sub_ne (f g : BooleanFunction n) :
    ⟪f.toReal, g.toReal⟫ᵤ = uniformProbability (fun x ↦ f x = g x) -
      uniformProbability (fun x ↦ f x ≠ g x) := by
  classical
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect, uniformProbability, uniformProbability,
    ← Finset.expect_sub_distrib]
  simp only [RCLike.inner_apply, BooleanFunction.toReal, starRingEnd_apply, star_trivial]
  apply Finset.expect_congr rfl
  intro x _
  rcases Int.units_eq_one_or (f x) with hf | hf <;>
    rcases Int.units_eq_one_or (g x) with hg | hg <;>
    simp [hf, hg]

/-- The probability formula for the mean of a sign-valued Boolean function from Definition 1.11. -/
theorem mean_eq_probability_one_sub_probability_neg_one (f : BooleanFunction n) :
    mean f.toReal = uniformProbability (fun x ↦ f x = 1) -
      uniformProbability (fun x ↦ f x = -1) := by
  classical
  rw [mean, uniformProbability, uniformProbability, ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro x _
  rcases Int.units_eq_one_or (f x) with h | h <;>
    simp [BooleanFunction.toReal, h]

/-- The probabilities of the two possible values of a sign-valued function sum to one. -/
theorem uniformProbability_one_add_neg_one_eq_one (f : BooleanFunction n) :
    uniformProbability (fun x ↦ f x = 1) +
      uniformProbability (fun x ↦ f x = -1) = 1 := by
  classical
  rw [uniformProbability, uniformProbability, ← Finset.expect_add_distrib]
  calc
    (𝔼 x, ((if f x = 1 then (1 : ℝ) else 0) +
        (if f x = -1 then (1 : ℝ) else 0))) =
        𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      rcases Int.units_eq_one_or (f x) with h | h <;> simp [h]
    _ = 1 := Fintype.expect_const 1

/-- The Boolean specialization in O'Donnell, Definition 1.11: balanced means that `+1` occurs
with probability one half. -/
theorem isBalanced_iff_uniformProbability_one_eq_half (f : BooleanFunction n) :
    IsBalanced f.toReal ↔ uniformProbability (fun x ↦ f x = 1) = (2 : ℝ)⁻¹ := by
  rw [IsBalanced, mean_eq_probability_one_sub_probability_neg_one]
  have htotal := uniformProbability_one_add_neg_one_eq_one f
  constructor <;> intro h <;> linarith

/-- O'Donnell, Fact 1.12: the mean is the constant Fourier coefficient. -/
theorem mean_eq_fourierCoeff_empty (f : {−1,1}^[n] → ℝ) :
    mean f = fourierCoeff f ∅ := by
  simp [mean, fourierCoeff, monomial]

/-- The consequence following O'Donnell, Fact 1.12: balanced functions are exactly those whose
constant Fourier coefficient vanishes. -/
theorem isBalanced_iff_fourierCoeff_empty_eq_zero (f : {−1,1}^[n] → ℝ) :
    IsBalanced f ↔ fourierCoeff f ∅ = 0 := by
  rw [IsBalanced, mean_eq_fourierCoeff_empty]

/-- The centered-inner-product expression in O'Donnell, Proposition 1.13. -/
theorem variance_eq_uniformInner_centered (f : {−1,1}^[n] → ℝ) :
    variance f = ⟪fun x ↦ f x - mean f, fun x ↦ f x - mean f⟫ᵤ := by
  rw [variance, uniformInner, RCLike.wInner_cWeight_eq_expect]
  apply Finset.expect_congr rfl
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- O'Donnell, Proposition 1.13: the variance identities and nonconstant Fourier mass formula. -/
theorem variance_eq_sum_sq_fourierCoeff (f : {−1,1}^[n] → ℝ) :
    variance f = (𝔼 x, f x ^ 2) - mean f ^ 2 ∧
      variance f = ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
        fourierCoeff f S ^ 2 := by
  classical
  have hvariance : variance f = (𝔼 x, f x ^ 2) - mean f ^ 2 := by
    rw [variance]
    calc
      (𝔼 x, (f x - mean f) ^ 2) =
          𝔼 x, (f x ^ 2 - (2 * mean f) * f x + mean f ^ 2) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = (𝔼 x, f x ^ 2) - (2 * mean f) * (𝔼 x, f x) + mean f ^ 2 := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, Fintype.expect_const]
      _ = (𝔼 x, f x ^ 2) - mean f ^ 2 := by
        simp [mean]
        ring
  refine ⟨hvariance, ?_⟩
  have hsecondMoment : (𝔼 x, f x ^ 2) = ∑ S, fourierCoeff f S ^ 2 := by
    calc
      (𝔼 x, f x ^ 2) = ⟪f, f⟫ᵤ := by
        simp [uniformInner, RCLike.wInner_cWeight_eq_expect, pow_two]
      _ = ∑ S, fourierCoeff f S ^ 2 := parseval f
  rw [hvariance, hsecondMoment, mean_eq_fourierCoeff_empty, Finset.filter_ne']
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S ↦ fourierCoeff f S ^ 2) (Finset.mem_univ ∅)
  linarith

/-- O'Donnell, Fact 1.14: the variance of a sign-valued Boolean function. -/
theorem variance_eq_four_mul_probabilities (f : BooleanFunction n) :
    variance f.toReal = 1 - mean f.toReal ^ 2 ∧
      variance f.toReal = 4 * uniformProbability (fun x ↦ f x = 1) *
        uniformProbability (fun x ↦ f x = -1) ∧
      variance f.toReal ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let p := uniformProbability (fun x ↦ f x = 1)
  let q := uniformProbability (fun x ↦ f x = -1)
  have hpq : p + q = 1 := by
    simpa [p, q] using uniformProbability_one_add_neg_one_eq_one f
  have hp : 0 ≤ p := by
    simp only [p]
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    positivity
  have hq : 0 ≤ q := by
    simp only [q]
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    positivity
  have hsecondMoment : (𝔼 x, f.toReal x ^ 2) = 1 := by
    calc
      (𝔼 x, f.toReal x ^ 2) = 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        rcases Int.units_eq_one_or (f x) with h | h <;>
          simp [BooleanFunction.toReal, h]
      _ = 1 := Fintype.expect_const 1
  have hvariance : variance f.toReal = 1 - mean f.toReal ^ 2 := by
    rw [(variance_eq_sum_sq_fourierCoeff f.toReal).1, hsecondMoment]
  have hmean : mean f.toReal = p - q := by
    simpa [p, q] using mean_eq_probability_one_sub_probability_neg_one f
  have hproduct : variance f.toReal = 4 * p * q := by
    rw [hvariance, hmean]
    nlinarith
  refine ⟨hvariance, ?_, ?_⟩
  · simpa [p, q] using hproduct
  · constructor
    · rw [hproduct]
      positivity
    · rw [hvariance]
      nlinarith [sq_nonneg (mean f.toReal)]

/-- Distance from a sign-valued function to the constant `+1` is the probability of output
`-1`. -/
theorem relativeHammingDist_one_eq_uniformProbability_neg_one (f : BooleanFunction n) :
    relativeHammingDist f (fun _ ↦ 1) = uniformProbability (fun x ↦ f x = -1) := by
  classical
  rw [← uniformProbability_ne_eq_relativeHammingDist, uniformProbability, uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  rcases Int.units_eq_one_or (f x) with h | h <;> simp [h]

/-- Distance from a sign-valued function to the constant `-1` is the probability of output
`+1`. -/
theorem relativeHammingDist_neg_one_eq_uniformProbability_one (f : BooleanFunction n) :
    relativeHammingDist f (fun _ ↦ -1) = uniformProbability (fun x ↦ f x = 1) := by
  classical
  rw [← uniformProbability_ne_eq_relativeHammingDist, uniformProbability, uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  rcases Int.units_eq_one_or (f x) with h | h <;> simp [h]

/-- O'Donnell, Exercise 1.16: Boolean variance is four times the product of the distances to the
two constant functions. -/
theorem variance_eq_four_mul_relativeHammingDist_one_mul_neg_one (f : BooleanFunction n) :
    variance f.toReal = 4 * relativeHammingDist f (fun _ ↦ 1) *
      relativeHammingDist f (fun _ ↦ -1) := by
  rw [(variance_eq_four_mul_probabilities f).2.1,
    relativeHammingDist_one_eq_uniformProbability_neg_one,
    relativeHammingDist_neg_one_eq_uniformProbability_one]
  ring

/-- The distance from `f` to the nearer constant sign function. -/
noncomputable def distanceToNearestConstant (f : BooleanFunction n) : ℝ :=
  min (relativeHammingDist f (fun _ ↦ 1)) (relativeHammingDist f (fun _ ↦ -1))

/-- O'Donnell, Proposition 1.15: variance is controlled by distance to the nearer constant. -/
theorem variance_bounds_distanceToNearestConstant (f : BooleanFunction n) :
    2 * distanceToNearestConstant f ≤ variance f.toReal ∧
      variance f.toReal ≤ 4 * distanceToNearestConstant f := by
  classical
  let p := uniformProbability (fun x ↦ f x = 1)
  let q := uniformProbability (fun x ↦ f x = -1)
  have hpq : p + q = 1 := by
    simpa [p, q] using uniformProbability_one_add_neg_one_eq_one f
  have hp : 0 ≤ p := by
    simp only [p]
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    positivity
  have hq : 0 ≤ q := by
    simp only [q]
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    positivity
  have hdistOne : relativeHammingDist f (fun _ ↦ 1) = q := by
    simpa [q] using relativeHammingDist_one_eq_uniformProbability_neg_one f
  have hdistNegOne : relativeHammingDist f (fun _ ↦ -1) = p := by
    simpa [p] using relativeHammingDist_neg_one_eq_uniformProbability_one f
  have hdistance : distanceToNearestConstant f = min q p := by
    simp [distanceToNearestConstant, hdistOne, hdistNegOne]
  have hvariance : variance f.toReal = 4 * p * q := by
    rw [variance_eq_four_mul_relativeHammingDist_one_mul_neg_one, hdistOne, hdistNegOne]
    ring
  rw [hdistance, hvariance]
  by_cases hpqOrder : p ≤ q
  · rw [min_eq_right hpqOrder]
    constructor <;> nlinarith
  · have hqp : q ≤ p := le_of_not_ge hpqOrder
    rw [min_eq_left hqp]
    constructor <;> nlinarith

/-- The centered-inner-product expression in O'Donnell, Proposition 1.16. -/
theorem covariance_eq_uniformInner_centered (f g : {−1,1}^[n] → ℝ) :
    covariance f g = ⟪fun x ↦ f x - mean f, fun x ↦ g x - mean g⟫ᵤ := by
  rw [covariance, uniformInner, RCLike.wInner_cWeight_eq_expect]
  apply Finset.expect_congr rfl
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- O'Donnell, Proposition 1.16: the covariance identities and Fourier formula. -/
theorem covariance_eq_sum_fourierCoeff_mul (f g : {−1,1}^[n] → ℝ) :
    covariance f g = (𝔼 x, f x * g x) - mean f * mean g ∧
      covariance f g = ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅),
        fourierCoeff f S * fourierCoeff g S := by
  classical
  have hcovariance : covariance f g = (𝔼 x, f x * g x) - mean f * mean g := by
    rw [covariance]
    calc
      (𝔼 x, (f x - mean f) * (g x - mean g)) =
          𝔼 x, (f x * g x - mean g * f x - mean f * g x + mean f * mean g) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = (𝔼 x, f x * g x) - mean g * (𝔼 x, f x) -
          mean f * (𝔼 x, g x) + mean f * mean g := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          Finset.expect_sub_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
          Fintype.expect_const]
      _ = (𝔼 x, f x * g x) - mean f * mean g := by
        simp [mean]
        ring
  refine ⟨hcovariance, ?_⟩
  have hmixedMoment : (𝔼 x, f x * g x) =
      ∑ S, fourierCoeff f S * fourierCoeff g S := by
    calc
      (𝔼 x, f x * g x) = ⟪f, g⟫ᵤ := by
        simp [uniformInner, RCLike.wInner_cWeight_eq_expect, mul_comm]
      _ = ∑ S, fourierCoeff f S * fourierCoeff g S := plancherel f g
  rw [hcovariance, hmixedMoment, mean_eq_fourierCoeff_empty,
    mean_eq_fourierCoeff_empty, Finset.filter_ne']
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S ↦ fourierCoeff f S * fourierCoeff g S) (Finset.mem_univ ∅)
  linarith

/-- O'Donnell, Definition 1.17: Fourier weight on `S`. -/
noncomputable def fourierWeight (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) : ℝ :=
  fourierCoeff f S ^ 2

/-- O'Donnell, Definition 1.18: the spectral sample of a Boolean function. -/
noncomputable def spectralSample (f : BooleanFunction n) : PMF (Finset (Fin n)) := by
  classical
  refine PMF.ofFintype (fun S ↦ ENNReal.ofReal (fourierWeight f.toReal S)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · simp [fourierWeight, sum_sq_fourierCoeff_eq_one]
  · intro S _
    exact sq_nonneg _

/-- The spectral sample has point mass `f̂(S)²`. -/
theorem spectralSample_apply_toReal (f : BooleanFunction n) (S : Finset (Fin n)) :
    (spectralSample f S).toReal = fourierWeight f.toReal S := by
  classical
  simp [spectralSample, fourierWeight, sq_nonneg]

/-- O'Donnell, Definition 1.19: level-`k` Fourier weight `𝐖ᵏ[f]`. -/
noncomputable def fourierWeightAtLevel (k : ℕ) (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k), fourierWeight f S

/-- The homogeneous degree-`k` part `f⁼ᵏ`. -/
noncomputable def degreePart (k : ℕ) (f : {−1,1}^[n] → ℝ) : {−1,1}^[n] → ℝ :=
  fun x ↦ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
    fourierCoeff f S * monomial S x

/-- The degree-`k` part retains exactly the Fourier coefficients at level `k`. -/
theorem fourierCoeff_degreePart (k : ℕ) (f : {−1,1}^[n] → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (degreePart k f) T =
      if T.card = k then fourierCoeff f T else 0 := by
  classical
  unfold fourierCoeff degreePart
  calc
    (𝔼 x, (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
        fourierCoeff f S * monomial S x) * monomial T x) =
        𝔼 x, ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
          (fourierCoeff f S * monomial S x) * monomial T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
        𝔼 x, (fourierCoeff f S * monomial S x) * monomial T x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
        fourierCoeff f S * (if S = T then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← expect_monomial_mul S T, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = if T.card = k then fourierCoeff f T else 0 := by
      by_cases hT : T.card = k <;> simp [hT]

/-- The norm identity in O'Donnell, Definition 1.19: level-`k` Fourier weight is the squared
normalized `L²` quantity of the degree-`k` part. -/
theorem fourierWeightAtLevel_eq_uniformLpNorm_degreePart_sq (k : ℕ)
    (f : {−1,1}^[n] → ℝ) :
    fourierWeightAtLevel k f = uniformLpNorm 2 (degreePart k f) ^ 2 := by
  rw [uniformLpNorm_two_sq_eq_uniformInner, parseval]
  unfold fourierWeightAtLevel fourierWeight
  simp_rw [fourierCoeff_degreePart]
  simp only [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Finset.sum_filter]

/-- The Fourier weight above degree `k`. -/
noncomputable def fourierWeightAbove (k : ℕ) (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ k < S.card), fourierWeight f S

/-- The degree-at-most-`k` part `f≤ᵏ`. -/
noncomputable def lowDegreePart (k : ℕ) (f : {−1,1}^[n] → ℝ) : {−1,1}^[n] → ℝ :=
  fun x ↦ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
    fourierCoeff f S * monomial S x

/-- The probability interpretation included in O'Donnell, Definition 1.19. -/
theorem spectralSample_card_eq (f : BooleanFunction n) (k : ℕ) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k),
      (spectralSample f S).toReal) = fourierWeightAtLevel k f.toReal := by
  simp [spectralSample_apply_toReal, fourierWeightAtLevel]

end FABL
