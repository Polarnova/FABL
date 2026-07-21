/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.Regularity
public import FABL.Chapter03.SubspacesAndDecisionTrees.VectorFourier

/-!
# The fourth spectral moment

Book item: Proposition 6.7.

The fourth spectral moment is the fourth-power sum of the normalized vector-indexed Fourier
coefficients. Its regularity bounds follow from vector Parseval, and its additive-energy formula
uses normalized convolution on the binary cube.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The fourth power of the vector-indexed Fourier `4`-norm. -/
noncomputable def vectorFourierFourthMoment (f : F₂Cube n → ℝ) : ℝ :=
  ∑ γ, vectorFourierCoeff f γ ^ 4

/-- The Fourier coefficient at the zero frequency is the uniform mean. -/
theorem vectorFourierCoeff_zero_eq_mean (f : F₂Cube n → ℝ) :
    vectorFourierCoeff f 0 = mean f := by
  rw [vectorFourierCoeff_eq_expect, mean]
  simp

/-- Vector-indexed Parseval identifies variance with the square mass at nonzero
frequencies. -/
theorem variance_eq_sum_sq_vectorFourierCoeff_ne_zero (f : F₂Cube n → ℝ) :
    variance f =
      ∑ γ ∈ (Finset.univ.filter fun γ : F₂Cube n ↦ γ ≠ 0),
        vectorFourierCoeff f γ ^ 2 := by
  classical
  have hvariance :
      variance f = (𝔼 x, f x ^ 2) - mean f ^ 2 := by
    rw [variance]
    calc
      (𝔼 x, (f x - mean f) ^ 2) =
          (𝔼 x, (f x ^ 2 - (2 * mean f) * f x + mean f ^ 2)) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = (𝔼 x, f x ^ 2) -
          (2 * mean f) * (𝔼 x, f x) + mean f ^ 2 := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, Fintype.expect_const]
      _ = (𝔼 x, f x ^ 2) - mean f ^ 2 := by
        simp [mean]
        ring
  have hsecondMoment :
      (𝔼 x, f x ^ 2) = ∑ γ, vectorFourierCoeff f γ ^ 2 := by
    calc
      (𝔼 x, f x ^ 2) = 𝔼 x, f x * f x := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = ∑ γ, vectorFourierCoeff f γ * vectorFourierCoeff f γ :=
        vector_plancherel f f
      _ = ∑ γ, vectorFourierCoeff f γ ^ 2 := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [pow_two]
  rw [hvariance, hsecondMoment, ← vectorFourierCoeff_zero_eq_mean,
    Finset.filter_ne']
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (F₂Cube n))
    (fun γ ↦ vectorFourierCoeff f γ ^ 2) (Finset.mem_univ 0)
  linarith

/-- Removing the constant coefficient from the fourth spectral moment leaves exactly the
fourth-power mass at nonzero frequencies. -/
theorem vectorFourierFourthMoment_sub_mean_pow_four (f : F₂Cube n → ℝ) :
    vectorFourierFourthMoment f - mean f ^ 4 =
      ∑ γ ∈ (Finset.univ.filter fun γ : F₂Cube n ↦ γ ≠ 0),
        vectorFourierCoeff f γ ^ 4 := by
  classical
  rw [vectorFourierFourthMoment, ← vectorFourierCoeff_zero_eq_mean,
    Finset.filter_ne']
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (F₂Cube n))
    (fun γ ↦ vectorFourierCoeff f γ ^ 4) (Finset.mem_univ 0)
  linarith

/-- Fourier regularity gives the corresponding bound on every nonzero vector-indexed
coefficient. -/
theorem IsFourierRegular.abs_vectorFourierCoeff_le
    {f : F₂Cube n → ℝ} {ε : ℝ}
    (hregular : IsFourierRegular ε (binaryFunctionOnSignCube f))
    {γ : F₂Cube n} (hγ : γ ≠ 0) :
    |vectorFourierCoeff f γ| ≤ ε := by
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
  apply hregular (f₂Support γ)
  rw [Finset.nonempty_iff_ne_empty]
  intro hsupport
  apply hγ
  apply (f₂CubeEquivFinset n).injective
  calc
    f₂Support γ = ∅ := hsupport
    _ = f₂Support (0 : F₂Cube n) := by ext i; simp [f₂Support]

/-- O'Donnell, Proposition 6.7(1): regularity bounds the nonconstant fourth spectral
moment by `ε²` times the variance. -/
theorem vectorFourierFourthMoment_sub_mean_pow_four_le
    (f : F₂Cube n → ℝ) {ε : ℝ}
    (hregular : IsFourierRegular ε (binaryFunctionOnSignCube f)) :
    vectorFourierFourthMoment f - mean f ^ 4 ≤ ε ^ 2 * variance f := by
  rw [vectorFourierFourthMoment_sub_mean_pow_four,
    variance_eq_sum_sq_vectorFourierCoeff_ne_zero, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro γ hγ
  have hγ_ne : γ ≠ 0 := (Finset.mem_filter.mp hγ).2
  have hsquare :
      |vectorFourierCoeff f γ| ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _)
      (hregular.abs_vectorFourierCoeff_le hγ_ne) 2
  calc
    vectorFourierCoeff f γ ^ 4 =
        |vectorFourierCoeff f γ| ^ 2 *
          vectorFourierCoeff f γ ^ 2 := by rw [sq_abs]; ring
    _ ≤ ε ^ 2 * vectorFourierCoeff f γ ^ 2 :=
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)

/-- Failure of regularity supplies a nonzero vector-indexed coefficient exceeding the
regularity threshold. -/
theorem exists_abs_vectorFourierCoeff_gt_of_not_isFourierRegular
    (f : F₂Cube n → ℝ) {ε : ℝ}
    (hregular : ¬ IsFourierRegular ε (binaryFunctionOnSignCube f)) :
    ∃ γ : F₂Cube n, γ ≠ 0 ∧ ε < |vectorFourierCoeff f γ| := by
  classical
  rw [IsFourierRegular] at hregular
  push Not at hregular
  obtain ⟨S, hS, hcoeff⟩ := hregular
  let γ : F₂Cube n := (f₂CubeEquivFinset n).symm S
  have hsupport : f₂Support γ = S := (f₂CubeEquivFinset n).apply_symm_apply S
  have hγ_ne : γ ≠ 0 := by
    intro hγ
    apply Finset.nonempty_iff_ne_empty.mp hS
    calc
      S = f₂Support γ := hsupport.symm
      _ = f₂Support (0 : F₂Cube n) := congrArg f₂Support hγ
      _ = ∅ := by ext i; simp [f₂Support]
  refine ⟨γ, hγ_ne, ?_⟩
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube, hsupport]
  exact hcoeff

/-- O'Donnell, Proposition 6.7(2): failure of `ε`-regularity forces at least `ε⁴`
nonconstant fourth spectral mass. -/
theorem epsilon_pow_four_le_vectorFourierFourthMoment_sub_mean_pow_four
    (f : F₂Cube n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hregular : ¬ IsFourierRegular ε (binaryFunctionOnSignCube f)) :
    ε ^ 4 ≤ vectorFourierFourthMoment f - mean f ^ 4 := by
  rw [vectorFourierFourthMoment_sub_mean_pow_four]
  obtain ⟨γ, hγ_ne, hγ⟩ :=
    exists_abs_vectorFourierCoeff_gt_of_not_isFourierRegular f hregular
  have hpow : ε ^ 4 < |vectorFourierCoeff f γ| ^ 4 :=
    pow_lt_pow_left₀ hγ hε (by norm_num)
  have habspow :
      |vectorFourierCoeff f γ| ^ 4 = vectorFourierCoeff f γ ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  rw [habspow] at hpow
  refine hpow.le.trans ?_
  exact Finset.single_le_sum
    (s := Finset.univ.filter fun δ : F₂Cube n ↦ δ ≠ 0)
    (f := fun δ ↦ vectorFourierCoeff f δ ^ 4)
    (fun δ _ ↦ by positivity)
    (by simp [hγ_ne])

/-- Normalized convolution multiplies vector-indexed Fourier coefficients. -/
theorem vectorFourierCoeff_convolution
    (f g : F₂Cube n → ℝ) (γ : F₂Cube n) :
    vectorFourierCoeff (convolution f g) γ =
      vectorFourierCoeff f γ * vectorFourierCoeff g γ := by
  exact binaryFourierCoeff_convolution f g (f₂Support γ)

/-- The fourth spectral moment is the second moment of the self-convolution. -/
theorem vectorFourierFourthMoment_eq_expect_convolution_mul_self
    (f : F₂Cube n → ℝ) :
    vectorFourierFourthMoment f =
      𝔼 t, convolution f f t * convolution f f t := by
  rw [vectorFourierFourthMoment]
  calc
    (∑ γ, vectorFourierCoeff f γ ^ 4) =
        ∑ γ, vectorFourierCoeff (convolution f f) γ *
          vectorFourierCoeff (convolution f f) γ := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [vectorFourierCoeff_convolution]
      ring
    _ = 𝔼 t, convolution f f t * convolution f f t :=
      (vector_plancherel (convolution f f) (convolution f f)).symm

/-- The second moment of the self-convolution is the normalized additive energy of `f`. -/
theorem expect_convolution_mul_self_eq_additiveEnergy
    (f : F₂Cube n → ℝ) :
    (𝔼 t, convolution f f t * convolution f f t) =
      𝔼 x, 𝔼 y, 𝔼 z, f x * f y * f z * f (x + y + z) := by
  calc
    (𝔼 t, convolution f f t * convolution f f t) =
        𝔼 t, (𝔼 a, f a * f (t + a)) *
          (𝔼 b, f b * f (t + b)) := by
      apply Finset.expect_congr rfl
      intro t _
      rw [convolution_apply_add]
    _ = 𝔼 t, 𝔼 a, 𝔼 b,
          (f a * f (t + a)) * (f b * f (t + b)) := by
      apply Finset.expect_congr rfl
      intro t _
      rw [Fintype.expect_mul_expect]
    _ = 𝔼 t, 𝔼 a, 𝔼 b,
          f a * f (t + a) * f b * f (t + b) := by
      apply Finset.expect_congr rfl
      intro t _
      apply Finset.expect_congr rfl
      intro a _
      apply Finset.expect_congr rfl
      intro b _
      ring
    _ = 𝔼 a, 𝔼 t, 𝔼 b,
          f a * f (t + a) * f b * f (t + b) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 a, 𝔼 y, 𝔼 b,
          f a * f y * f b * f (a + y + b) := by
      apply Finset.expect_congr rfl
      intro a _
      apply Fintype.expect_equiv (Equiv.addRight a)
      intro t
      have hdouble : a + a = 0 := ZModModule.add_self a
      have hcycle : a + (t + a) = t := by
        calc
          a + (t + a) = (a + a) + t := by ac_rfl
          _ = t := by rw [hdouble, zero_add]
      apply Finset.expect_congr rfl
      intro b _
      change f a * f (t + a) * f b * f (t + b) =
        f a * f ((Equiv.addRight a) t) * f b *
          f (a + (Equiv.addRight a) t + b)
      rw [show (Equiv.addRight a) t = t + a by rfl, hcycle]
    _ = 𝔼 x, 𝔼 y, 𝔼 z,
          f x * f y * f z * f (x + y + z) := rfl

/-- O'Donnell, Proposition 6.7: the exact additive-energy formula for the fourth
spectral moment. -/
theorem vectorFourierFourthMoment_eq_additiveEnergy
    (f : F₂Cube n → ℝ) :
    vectorFourierFourthMoment f =
      𝔼 x, 𝔼 y, 𝔼 z, f x * f y * f z * f (x + y + z) := by
  rw [vectorFourierFourthMoment_eq_expect_convolution_mul_self,
    expect_convolution_mul_self_eq_additiveEnergy]

end FABL
