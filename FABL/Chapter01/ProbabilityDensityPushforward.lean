/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.ProbabilityDensitiesAndConvolution

/-!
# Pushforwards of finite probability densities

This infrastructure has no independent book-facing declaration. It converts a pushed finite
probability law back to a density relative to uniform measure and supplies the corresponding
expectation change-of-variables formula.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

namespace ProbabilityDensity

variable {m n : ℕ}

/-- The density of the pushforward of `φ` through a map between finite binary cubes. -/
noncomputable def pushforward (φ : ProbabilityDensity m)
    (L : 𝔽₂^[m] → 𝔽₂^[n]) : ProbabilityDensity n where
  toFun z :=
    (Fintype.card 𝔽₂^[n] : ℝ) *
      (𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0)
  nonneg' := by
    intro z
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.expect_nonneg fun y _ ↦ by
      split_ifs
      · exact φ.nonneg y
      · exact le_rfl)
  expect_eq_one' := by
    classical
    calc
      (𝔼 z : 𝔽₂^[n],
          (Fintype.card 𝔽₂^[n] : ℝ) *
            (𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0)) =
          ∑ z : 𝔽₂^[n], 𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0 := by
        rw [← Finset.mul_expect, Fintype.card_mul_expect]
      _ = 𝔼 y : 𝔽₂^[m], ∑ z : 𝔽₂^[n], if z = L y then φ y else 0 := by
        rw [Finset.expect_sum_comm]
      _ = 𝔼 y : 𝔽₂^[m], φ y := by
        apply Finset.expect_congr rfl
        intro y _
        simp
      _ = 1 := φ.expect_eq_one

@[simp] theorem pushforward_apply (φ : ProbabilityDensity m)
    (L : 𝔽₂^[m] → 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    φ.pushforward L z =
      (Fintype.card 𝔽₂^[n] : ℝ) *
        (𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0) :=
  rfl

/-- Integration against a finite-density pushforward is integration after composition. -/
theorem pushforward_expectation (φ : ProbabilityDensity m)
    (L : 𝔽₂^[m] → 𝔽₂^[n]) (g : 𝔽₂^[n] → ℝ) :
    (φ.pushforward L).expectation g =
      φ.expectation fun y ↦ g (L y) := by
  classical
  calc
    (φ.pushforward L).expectation g =
        𝔼 z : 𝔽₂^[n],
          ((Fintype.card 𝔽₂^[n] : ℝ) *
            (𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0)) * g z := by
      rfl
    _ = 𝔼 z : 𝔽₂^[n],
          (Fintype.card 𝔽₂^[n] : ℝ) *
            ((𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0) * g z) := by
      apply Finset.expect_congr rfl
      intro z _
      ring
    _ = ∑ z : 𝔽₂^[n],
          (𝔼 y : 𝔽₂^[m], if z = L y then φ y else 0) * g z := by
      rw [← Finset.mul_expect, Fintype.card_mul_expect]
    _ = ∑ z : 𝔽₂^[n],
          𝔼 y : 𝔽₂^[m], (if z = L y then φ y else 0) * g z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.expect_mul]
    _ = 𝔼 y : 𝔽₂^[m],
          ∑ z : 𝔽₂^[n], (if z = L y then φ y else 0) * g z := by
      rw [Finset.expect_sum_comm]
    _ = 𝔼 y : 𝔽₂^[m], φ y * g (L y) := by
      apply Finset.expect_congr rfl
      intro y _
      simp
    _ = φ.expectation (fun y ↦ g (L y)) := rfl

/-- Cauchy--Schwarz for expectation under a finite probability density. -/
theorem sq_expectation_le_expectation_sq
    (φ : ProbabilityDensity n) (f : 𝔽₂^[n] → ℝ) :
    φ.expectation f ^ 2 ≤ φ.expectation (fun x ↦ f x ^ 2) := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset 𝔽₂^[n])
    (fun x ↦ Real.sqrt (φ x))
    (fun x ↦ Real.sqrt (φ x) * f x)
  unfold ProbabilityDensity.expectation
  have hleft :
      (𝔼 x, Real.sqrt (φ x) *
        (Real.sqrt (φ x) * f x)) =
        𝔼 x, φ x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [← mul_assoc, Real.mul_self_sqrt (φ.nonneg x)]
  have hfirst :
      (𝔼 x, Real.sqrt (φ x) ^ 2) = 1 := by
    calc
      (𝔼 x, Real.sqrt (φ x) ^ 2) = 𝔼 x, φ x := by
        apply Finset.expect_congr rfl
        intro x _
        exact Real.sq_sqrt (φ.nonneg x)
      _ = 1 := φ.expect_eq_one
  have hsecond :
      (𝔼 x, (Real.sqrt (φ x) * f x) ^ 2) =
        𝔼 x, φ x * f x ^ 2 := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, Real.sq_sqrt (φ.nonneg x)]
  rw [hleft, hfirst, hsecond, one_mul] at hcs
  exact hcs

end ProbabilityDensity

end FABL
