/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations

/-!
# Variance of restricted means

Book item: Exercise 6.6.

The variance of the mean of a uniformly random restriction is exactly the nonconstant
Fourier mass supported on the fixed coordinates.  The resulting second-moment argument
gives the probabilistic-method proof of Proposition 6.12(2).
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem variance_eq_sum_sq_indexedFourierCoeff_ne_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : IndexedSignCube ι → ℝ) :
    variance g =
      ∑ S ∈ (Finset.univ.filter fun S : Finset ι ↦ S ≠ ∅),
        indexedFourierCoeff g S ^ 2 := by
  classical
  have hvariance :
      variance g = (𝔼 x, g x ^ 2) - mean g ^ 2 := by
    rw [variance]
    calc
      (𝔼 x, (g x - mean g) ^ 2) =
          𝔼 x, (g x ^ 2 - (2 * mean g) * g x + mean g ^ 2) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = (𝔼 x, g x ^ 2) -
            (2 * mean g) * (𝔼 x, g x) + mean g ^ 2 := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, Fintype.expect_const]
      _ = (𝔼 x, g x ^ 2) - mean g ^ 2 := by
        simp [mean]
        ring
  have hsecondMoment :
      (𝔼 x, g x ^ 2) =
        ∑ S : Finset ι, indexedFourierCoeff g S ^ 2 := by
    simpa [pow_two] using indexed_parseval g
  rw [hvariance, hsecondMoment, mean, expect_eq_indexedFourierCoeff_empty,
    Finset.filter_ne']
  have hsum :=
    Finset.sum_erase_add
      (Finset.univ : Finset (Finset ι))
      (fun S ↦ indexedFourierCoeff g S ^ 2)
      (Finset.mem_univ ∅)
  linarith

/-- The mean of a sign restriction is its empty restricted Fourier coefficient. -/
theorem mean_signRestriction_eq_restrictionFourierCoeff_empty
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    mean (signRestriction f J z) =
      restrictionFourierCoeff f J ∅ z := by
  change (𝔼 y, signRestriction f J z y) =
    indexedFourierCoeff (signRestriction f J z) ∅
  exact expect_eq_indexedFourierCoeff_empty _

/-- O'Donnell, Exercise 6.6(a): the variance of the mean of a uniformly random
restriction equals the nonconstant Fourier mass on the fixed coordinates. -/
theorem variance_mean_signRestriction_eq_sum_sq_fixed
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) :
    variance (fun z : FixedSignCube J ↦ mean (signRestriction f J z)) =
      ∑ T ∈
          (Finset.univ.filter
            fun T : Finset (FixedIndex J) ↦ T ≠ ∅),
        fourierCoeff f (liftFixedFrequency T) ^ 2 := by
  classical
  have hfunctions :
      (fun z : FixedSignCube J ↦ mean (signRestriction f J z)) =
        restrictionFourierCoeff f J ∅ := by
    funext z
    exact mean_signRestriction_eq_restrictionFourierCoeff_empty f J z
  rw [hfunctions,
    variance_eq_sum_sq_indexedFourierCoeff_ne_empty]
  apply Finset.sum_congr rfl
  intro T _
  rw [indexedFourierCoeff_restrictionFourierCoeff]
  simp [liftFreeFrequency]

/-- O'Donnell, Exercise 6.6(b): the restriction witness in Proposition 6.12(2),
proved from the variance identity and the probabilistic method. -/
theorem exists_signRestriction_mean_change_gt_via_variance
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} {k : ℕ}
    (hregular : ¬ IsLowDegreeFourierRegular ε k f) :
    ∃ J : Finset (Fin n), Fintype.card (FixedIndex J) ≤ k ∧
      ∃ z : FixedSignCube J,
        ε < |mean (signRestriction f J z) - mean f| := by
  classical
  rw [IsLowDegreeFourierRegular] at hregular
  push Not at hregular
  obtain ⟨S, hSnonempty, hScard, hScoeff⟩ := hregular
  let J : Finset (Fin n) := Sᶜ
  let T : Finset (FixedIndex J) := fixedFrequencyPart J S
  have hfree : freeFrequencyPart J S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiS : (i : Fin n) ∈ S :=
      (mem_freeFrequencyPart J S i).1 hi
    exact (Finset.mem_compl.mp i.property) hiS
  have hlift : liftFixedFrequency T = S := by
    have hsplit :=
      liftFreeFrequencyPart_union_liftFixedFrequencyPart J S
    rw [hfree] at hsplit
    simpa [T, liftFreeFrequency] using hsplit
  have hTnonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    have : S = ∅ := by
      rw [← hlift, hT]
      simp [liftFixedFrequency]
    exact (Finset.nonempty_iff_ne_empty.mp hSnonempty) this
  have hfixedCard : Fintype.card (FixedIndex J) = S.card := by
    simp [J, FixedIndex]
  refine ⟨J, hfixedCard.trans_le hScard, ?_⟩
  by_cases hε : 0 ≤ ε
  · have hvarianceLower :
        ε ^ 2 <
          variance
            (fun z : FixedSignCube J ↦
              mean (signRestriction f J z)) := by
      rw [variance_mean_signRestriction_eq_sum_sq_fixed]
      calc
        ε ^ 2 < |fourierCoeff f S| ^ 2 :=
          (sq_lt_sq₀ hε (abs_nonneg _)).2 hScoeff
        _ = fourierCoeff f S ^ 2 := sq_abs _
        _ = fourierCoeff f (liftFixedFrequency T) ^ 2 := by
          rw [hlift]
        _ ≤
            ∑ U ∈
                (Finset.univ.filter
                  fun U : Finset (FixedIndex J) ↦ U ≠ ∅),
              fourierCoeff f (liftFixedFrequency U) ^ 2 := by
          exact Finset.single_le_sum
            (fun U _ ↦ sq_nonneg
              (fourierCoeff f (liftFixedFrequency U)))
            (by simp [Finset.nonempty_iff_ne_empty.mp hTnonempty])
    by_contra hexists
    push Not at hexists
    have hmean :
        mean
            (fun z : FixedSignCube J ↦
              mean (signRestriction f J z)) =
          mean f := by
      rw [mean]
      calc
        (𝔼 z : FixedSignCube J, mean (signRestriction f J z)) =
            𝔼 z : FixedSignCube J,
              restrictionFourierCoeff f J ∅ z := by
          apply Finset.expect_congr rfl
          intro z _
          exact
            mean_signRestriction_eq_restrictionFourierCoeff_empty
              f J z
        _ = fourierCoeff f (liftFreeFrequency (∅ : Finset J)) :=
          expect_restrictionFourierCoeff f J ∅
        _ = mean f := by
          simp [liftFreeFrequency, mean_eq_fourierCoeff_empty]
    have hvarianceUpper :
        variance
            (fun z : FixedSignCube J ↦
              mean (signRestriction f J z)) ≤
          ε ^ 2 := by
      rw [variance, hmean]
      calc
        (𝔼 z : FixedSignCube J,
            (mean (signRestriction f J z) - mean f) ^ 2) ≤
            𝔼 _z : FixedSignCube J, ε ^ 2 := by
          apply Finset.expect_le_expect
          intro z _
          exact
            (by
              rw [← sq_abs]
              exact
                (sq_le_sq₀
                  (abs_nonneg
                    (mean (signRestriction f J z) - mean f))
                  hε).2 (hexists z))
        _ = ε ^ 2 := Fintype.expect_const _
    exact (not_le_of_gt hvarianceLower) hvarianceUpper
  · refine ⟨(fun _ ↦ 1), ?_⟩
    exact (lt_of_not_ge hε).trans_le (abs_nonneg _)

end FABL
