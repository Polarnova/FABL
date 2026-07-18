/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.MajorityLimits

/-!
# Limiting majority Fourier weights

This file formalizes the limiting majority Fourier weights in O'Donnell,
Equation (5.10), and their convergent upper tails.
-/

@[expose] public section

namespace FABL

open Set
open scoped Topology

/-- O'Donnell, Equation (5.10): the degree-`k` coefficient of
`(2 / π) * arcsin ρ`. -/
noncomputable def limitingMajorityFourierWeight (k : ℕ) : ℝ :=
  (2 / Real.pi) * arcsinOddPowerCoefficient k

/-- The explicit odd/even formula in O'Donnell, Equation (5.10). -/
theorem limitingMajorityFourierWeight_eq (k : ℕ) :
    limitingMajorityFourierWeight k =
      if Odd k then
        4 / (Real.pi * (k : ℝ) * (2 : ℝ) ^ k) *
          (Nat.choose (k - 1) ((k - 1) / 2) : ℝ)
      else
        0 := by
  rw [limitingMajorityFourierWeight, arcsinOddPowerCoefficient]
  split_ifs with hk
  · have hk0 : (k : ℝ) ≠ 0 := by
      norm_cast
      intro hkzero
      subst k
      simp at hk
    field_simp [Real.pi_ne_zero, hk0]
    all_goals ring
  · simp

/-- The limiting majority Fourier weights sum to `1`. -/
theorem limitingMajorityFourierWeight_hasSum_one :
    HasSum limitingMajorityFourierWeight 1 := by
  have h :=
    (exercise5_18_arcsinSeries 1 (by norm_num)).2.mul_left (2 / Real.pi)
  have h' :
      HasSum limitingMajorityFourierWeight
        ((2 / Real.pi) * Real.arcsin 1) := by
    simpa only [one_pow, mul_one, limitingMajorityFourierWeight] using! h
  have hvalue : (2 / Real.pi) * Real.arcsin 1 = 1 := by
    rw [Real.arcsin_one]
    field_simp [Real.pi_ne_zero]
  rwa [hvalue] at h'

/-- O'Donnell's `𝐖^{>k}(Maj)`, expressed as the convergent sum over degrees
strictly greater than `k`. -/
noncomputable def limitingMajorityFourierWeightAbove (k : ℕ) : ℝ :=
  ∑' j : {j : ℕ // k < j}, limitingMajorityFourierWeight j

/-- The series defining `limitingMajorityFourierWeightAbove` is summable. -/
theorem limitingMajorityFourierWeightAbove_summable (k : ℕ) :
    Summable (fun j : {j : ℕ // k < j} ↦ limitingMajorityFourierWeight j) := by
  change Summable
    (limitingMajorityFourierWeight ∘ ((↑) : {j : ℕ // k < j} → ℕ))
  exact limitingMajorityFourierWeight_hasSum_one.summable.subtype {j : ℕ | k < j}

end FABL
