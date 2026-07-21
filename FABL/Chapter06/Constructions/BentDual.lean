/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.BentFunctions

/-!
# Fourier duals of bent functions

Book item: Exercise 6.17.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Applying the normalized Fourier transform twice on the binary cube scales the
original function by the reciprocal of the cube cardinality. -/
theorem vectorFourierCoeff_vectorFourierCoeff
    (f : F₂Cube n → ℝ) (x : F₂Cube n) :
    vectorFourierCoeff (fun γ ↦ vectorFourierCoeff f γ) x =
      ((2 : ℝ) ^ n)⁻¹ * f x := by
  rw [vectorFourierCoeff_eq_expect, Fintype.expect_eq_sum_div_card]
  have hsum :
      (∑ γ : F₂Cube n,
          vectorFourierCoeff f γ * vectorWalshCharacter x γ) = f x := by
    rw [vector_fourier_expansion f x]
    apply Finset.sum_congr rfl
    intro γ _
    congr 1
    rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply]
    exact congrArg binarySign (dotProduct_comm x γ)
  rw [hsum]
  have hcard : Fintype.card (F₂Cube n) = 2 ^ n :=
    Fintype.card_pi_const 𝔽₂ n
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The normalized Fourier dual of a bent function. -/
noncomputable def bentDual (f : F₂Cube n → ℝ) :
    F₂Cube n → ℝ :=
  fun γ ↦ (2 : ℝ) ^ (n / 2) * vectorFourierCoeff f γ

/-- The Fourier dual of a bent function is sign-valued. -/
theorem IsBent.isSignValued_bentDual
    {f : F₂Cube n → ℝ} (hf : IsBent f) :
    IsSignValued (bentDual f) := by
  intro γ
  rw [bentDual, abs_mul, abs_pow, abs_two, hf γ]
  field_simp

/-- Fourier coefficients of the bent dual recover the original function with the
expected even-dimensional normalization. -/
theorem vectorFourierCoeff_bentDual
    {f : F₂Cube n → ℝ} (hn : Even n) (x : F₂Cube n) :
    vectorFourierCoeff (bentDual f) x =
      ((2 : ℝ) ^ (n / 2))⁻¹ * f x := by
  change
    vectorFourierCoeff
        (fun γ ↦ (2 : ℝ) ^ (n / 2) * vectorFourierCoeff f γ) x =
      _
  rw [vectorFourierCoeff_const_mul,
    vectorFourierCoeff_vectorFourierCoeff]
  rcases hn with ⟨k, rfl⟩
  have hhalf : (k + k) / 2 = k := by omega
  rw [hhalf, pow_add]
  field_simp

/-- The scaled Fourier transform of an even-dimensional sign-valued function is bent. -/
theorem IsSignValued.isBent_bentDual
    {f : F₂Cube n → ℝ} (hn : Even n) (hsign : IsSignValued f) :
    IsBent (bentDual f) := by
  intro x
  rw [vectorFourierCoeff_bentDual hn, abs_mul, hsign x, mul_one,
    abs_inv, abs_pow, abs_two]

/-- O'Donnell, Exercise 6.17: the scaled Fourier transform of a bent sign-valued
function is again a bent sign-valued function. -/
theorem IsBent.bentDual
    {f : F₂Cube n → ℝ} (hn : Even n) (hf : IsBent f)
    (hsign : IsSignValued f) :
    IsSignValued (bentDual f) ∧ IsBent (bentDual f) :=
  ⟨hf.isSignValued_bentDual, hsign.isBent_bentDual hn⟩

end FABL
