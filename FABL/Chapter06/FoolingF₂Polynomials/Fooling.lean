/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.ProbabilityDensitiesAndConvolution

/-!
# Fooling translation-closed function classes

Book items: Definition 6.46, Exercise 6.29.

Fooling compares expectation under a probability density with uniform expectation.  For a
translation-closed class, convolving a fooling density with any other density preserves the same
error bound.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A class of real-valued binary-cube functions is closed under every additive translation. -/
def IsTranslationClosed (C : Set (𝔽₂^[n] → ℝ)) : Prop :=
  ∀ ⦃f : 𝔽₂^[n] → ℝ⦄, f ∈ C → ∀ z, (fun x ↦ f (x + z)) ∈ C

namespace ProbabilityDensity

/-- O'Donnell, Definition 6.46: a density `ε`-fools a function class when each
density-weighted expectation is within `ε` of the corresponding uniform expectation. -/
def Fools (φ : ProbabilityDensity n) (C : Set (𝔽₂^[n] → ℝ)) (ε : ℝ) : Prop :=
  ∀ ⦃f : 𝔽₂^[n] → ℝ⦄, f ∈ C →
    |φ.expectation f - 𝔼 x, f x| ≤ ε

/-- Expectation against a convolution is the iterated expectation of the translated test
function. -/
theorem expectation_convolution (ψ φ : ProbabilityDensity n) (f : 𝔽₂^[n] → ℝ) :
    (ψ.convolution φ).expectation f =
      𝔼 z, φ z * ψ.expectation (fun y ↦ f (y + z)) := by
  unfold ProbabilityDensity.expectation
  simp_rw [ProbabilityDensity.convolution, FABL.convolution_apply, Finset.expect_mul]
  calc
    (𝔼 x, 𝔼 y, ψ y * φ (x - y) * f x) =
        𝔼 y, 𝔼 x, ψ y * φ (x - y) * f x := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y, 𝔼 z, ψ y * φ z * f (y + z) := by
      apply Finset.expect_congr rfl
      intro y _
      exact Fintype.expect_equiv (Equiv.addRight y)
        (fun x ↦ ψ y * φ (x - y) * f x)
        (fun z ↦ ψ y * φ z * f (y + z)) (by
          intro z
          rw [sub_eq_add_neg]
          have hneg : -y = y := by
            funext i
            exact ZMod.neg_eq_self_mod_two (y i)
          have hdouble : y + y = 0 := by
            calc
              y + y = -y + y := congrArg (· + y) hneg.symm
              _ = 0 := neg_add_cancel y
          have hcycle : y + (y + z) = z := by
            rw [← add_assoc, hdouble, zero_add]
          have he : (Equiv.addRight y) z = z + y := rfl
          rw [hneg, he, add_comm z y, hcycle])
    _ = 𝔼 z, 𝔼 y, ψ y * φ z * f (y + z) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 z, φ z * (𝔼 y, ψ y * f (y + z)) := by
      apply Finset.expect_congr rfl
      intro z _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro y _
      ring

/-- Uniform expectation is invariant under additive translation. -/
private theorem expect_translate_add (f : 𝔽₂^[n] → ℝ) (z : 𝔽₂^[n]) :
    (𝔼 x, f (x + z)) = 𝔼 x, f x :=
  Fintype.expect_equiv (Equiv.addRight z) (fun x ↦ f (x + z)) f (fun _ ↦ rfl)

/-- O'Donnell, Exercise 6.29: right convolution by an arbitrary density preserves fooling
of a translation-closed class. -/
theorem Fools.convolution_right
    {C : Set (𝔽₂^[n] → ℝ)} {ε : ℝ} {ψ : ProbabilityDensity n}
    (hψ : ψ.Fools C ε) (hC : IsTranslationClosed C) (φ : ProbabilityDensity n) :
    (ψ.convolution φ).Fools C ε := by
  intro f hf
  have huniform :
      (𝔼 x, f x) = 𝔼 z, φ z * (𝔼 x, f x) := by
    calc
      (𝔼 x, f x) = 1 * (𝔼 x, f x) := (one_mul _).symm
      _ = (𝔼 z, φ z) * (𝔼 x, f x) := by rw [φ.expect_eq_one]
      _ = 𝔼 z, φ z * (𝔼 x, f x) := by rw [Finset.expect_mul]
  rw [expectation_convolution, huniform]
  calc
    |(𝔼 z, φ z * ψ.expectation (fun y ↦ f (y + z))) -
        (𝔼 z, φ z * (𝔼 x, f x))| =
        |𝔼 z, φ z * (ψ.expectation (fun y ↦ f (y + z)) - 𝔼 x, f x)| := by
      congr 1
      rw [← Finset.expect_sub_distrib]
      apply Finset.expect_congr rfl
      intro z _
      ring
    _ ≤ 𝔼 z, |φ z * (ψ.expectation (fun y ↦ f (y + z)) - 𝔼 x, f x)| :=
      Finset.abs_expect_le _ _
    _ = 𝔼 z, φ z * |ψ.expectation (fun y ↦ f (y + z)) - 𝔼 x, f x| := by
      apply Finset.expect_congr rfl
      intro z _
      rw [abs_mul, abs_of_nonneg (φ.nonneg z)]
    _ ≤ 𝔼 z, φ z * ε := by
      apply Finset.expect_le_expect
      intro z _
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg z)
      have hz := hψ (hC hf z)
      rw [expect_translate_add] at hz
      exact hz
    _ = ε := by
      rw [← Finset.expect_mul, φ.expect_eq_one, one_mul]

end ProbabilityDensity

end FABL
