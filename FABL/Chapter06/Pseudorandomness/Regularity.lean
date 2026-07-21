/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions

/-!
# Fourier regularity

Book items: Definition 6.2, Remark 6.3, Definition 6.11.

Regularity is stated directly through the canonical finite-subset Fourier coefficients.  The
low-degree variant records the same bound only through a prescribed Fourier level.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A real-valued function is `ε`-regular when every nonconstant Fourier coefficient has
absolute value at most `ε`. -/
def IsFourierRegular (ε : ℝ) (f : {−1,1}^[n] → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → |fourierCoeff f S| ≤ ε

/-- Low-degree Fourier regularity through level `k`. -/
def IsLowDegreeFourierRegular (ε : ℝ) (k : ℕ) (f : {−1,1}^[n] → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k → |fourierCoeff f S| ≤ ε

/-- Ordinary Fourier regularity implies every low-degree version with the same parameter. -/
theorem IsFourierRegular.isLowDegreeFourierRegular
    {ε : ℝ} {f : {−1,1}^[n] → ℝ}
    (h : IsFourierRegular ε f) (k : ℕ) :
    IsLowDegreeFourierRegular ε k f :=
  fun S hS _ ↦ h S hS

/-- In dimension `n`, regularity through level `n` is ordinary regularity. -/
theorem isLowDegreeFourierRegular_dimension_iff
    (ε : ℝ) (f : {−1,1}^[n] → ℝ) :
    IsLowDegreeFourierRegular ε n f ↔ IsFourierRegular ε f := by
  constructor
  · intro h S hS
    exact h S hS (by simpa using Finset.card_le_univ S)
  · exact fun h ↦ h.isLowDegreeFourierRegular n

/-- Every function is regular with parameter its uniform `L¹` norm. -/
theorem isFourierRegular_uniformLpNorm_one (f : {−1,1}^[n] → ℝ) :
    IsFourierRegular (uniformLpNorm 1 f) f :=
  fun S _ ↦ abs_fourierCoeff_le_uniformLpNorm_one f S

/-- A function is zero-regular exactly when it is constant. -/
theorem isFourierRegular_zero_iff_exists_const (f : {−1,1}^[n] → ℝ) :
    IsFourierRegular 0 f ↔ ∃ c : ℝ, f = fun _ ↦ c := by
  classical
  constructor
  · intro h
    refine ⟨fourierCoeff f ∅, funext fun x ↦ ?_⟩
    rw [fourier_expansion f x]
    calc
      ∑ S, fourierCoeff f S * monomial S x =
          fourierCoeff f ∅ * monomial ∅ x := by
        apply Finset.sum_eq_single
        · intro S _ hS
          have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
          have habs : |fourierCoeff f S| = 0 :=
            le_antisymm (h S hnonempty) (abs_nonneg _)
          rw [abs_eq_zero.mp habs, zero_mul]
        · simp
      _ = fourierCoeff f ∅ := by simp [monomial]
  · rintro ⟨c, rfl⟩ S hS
    rw [fourierCoeff]
    calc
      |𝔼 _x : {−1,1}^[n], c * monomial S _x| =
          |c * (𝔼 x : {−1,1}^[n], monomial S x)| := by
        rw [Finset.mul_expect]
      _ = 0 := by
        rw [expect_monomial, if_neg (Finset.nonempty_iff_ne_empty.mp hS)]
        simp
      _ ≤ 0 := le_rfl

end FABL
