/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.GoldreichLevin.PrefixBuckets
public import FABL.Chapter06.LearningAndTesting.FourierNorms

/-!
# Restricted Fourier weights under small-bias distributions

Book items: Equation (6.6), Exercise 3.7 on Fourier `1`-norms under restriction,
Equation (6.7).

The restricted-weight identity and its associated function reuse the Chapter 3 restriction
and Goldreich--Levin APIs. A single explicit coordinate equivalence reindexes the complementary
subtype cube onto a standard finite cube before applying Corollary 6.39.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem abs_indexedMonomial_eq_one
    {ι : Type*} (S : Finset ι) (x : IndexedSignCube ι) :
    |indexedMonomial S x| = 1 := by
  rcases sq_eq_one_iff.mp (indexedMonomial_sq S x) with h | h <;>
    simp [h]

private theorem sum_abs_split_fourierCoeff_eq_fourierOneNorm
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) :
    (∑ S : Finset J, ∑ T : Finset (FixedIndex J),
        |fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T)|) =
      fourierOneNorm f := by
  rw [show
      (∑ S : Finset J, ∑ T : Finset (FixedIndex J),
          |fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T)|) =
        ∑ ST : Finset J × Finset (FixedIndex J),
          |fourierCoeff f
            (liftFreeFrequency ST.1 ∪ liftFixedFrequency ST.2)| by
      rw [Fintype.sum_prod_type]]
  unfold fourierOneNorm
  apply Fintype.sum_equiv (frequencySplitEquiv J)
  intro ST
  rw [frequencySplitEquiv_apply]

/-- O'Donnell, Equation (6.6): the restricted Fourier weight is both the sum of
the squared coefficients in its frequency bucket and the uniform second moment of
the associated restricted-coefficient function. -/
theorem restrictedFourierWeight_equation6_6
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    (restrictedFourierWeight f J S =
      ∑ T : Finset (FixedIndex J),
        fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) ^ 2) ∧
    ((∑ T : Finset (FixedIndex J),
        fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) ^ 2) =
      mean fun z : FixedSignCube J ↦ restrictionFourierCoeff f J S z ^ 2) := by
  constructor
  · rfl
  · simpa [mean] using
      (expect_sq_restrictionFourierCoeff f J S).symm

/-- O'Donnell, Exercise 3.7: restriction cannot increase the Fourier `1`-norm.
The left side is the subtype-indexed Fourier `1`-norm of the restricted function. -/
theorem sum_abs_indexedFourierCoeff_signRestriction_le_fourierOneNorm
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    (∑ S : Finset J,
        |indexedFourierCoeff (signRestriction f J z) S|) ≤
      fourierOneNorm f := by
  classical
  calc
    (∑ S : Finset J,
        |indexedFourierCoeff (signRestriction f J z) S|) ≤
        ∑ S : Finset J, ∑ T : Finset (FixedIndex J),
          |fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T)| := by
      apply Finset.sum_le_sum
      intro S _
      change |restrictionFourierCoeff f J S z| ≤ _
      rw [restrictionFourierCoeff_eq_sum]
      simpa [abs_mul, abs_indexedMonomial_eq_one] using
        (Finset.abs_sum_le_sum_abs
          (fun T : Finset (FixedIndex J) ↦
            fourierCoeff f
                (liftFreeFrequency S ∪ liftFixedFrequency T) *
              indexedMonomial T z)
          (Finset.univ : Finset (Finset (FixedIndex J))))
    _ = fourierOneNorm f :=
      sum_abs_split_fourierCoeff_eq_fourierOneNorm f J

/-- O'Donnell, Exercise 3.7: the associated restricted-coefficient function has
Fourier `1`-norm at most that of the ambient function. -/
theorem sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    (∑ T : Finset (FixedIndex J),
        |indexedFourierCoeff (restrictionFourierCoeff f J S) T|) ≤
      fourierOneNorm f := by
  classical
  calc
    (∑ T : Finset (FixedIndex J),
        |indexedFourierCoeff (restrictionFourierCoeff f J S) T|) =
        ∑ T : Finset (FixedIndex J),
          |fourierCoeff f
            (liftFreeFrequency S ∪ liftFixedFrequency T)| := by
      apply Finset.sum_congr rfl
      intro T _
      rw [indexedFourierCoeff_restrictionFourierCoeff]
    _ ≤ ∑ S' : Finset J, ∑ T : Finset (FixedIndex J),
          |fourierCoeff f
            (liftFreeFrequency S' ∪ liftFixedFrequency T)| := by
      exact Finset.single_le_sum
        (fun S' _ ↦ Finset.sum_nonneg fun T _ ↦
          abs_nonneg
            (fourierCoeff f
              (liftFreeFrequency S' ∪ liftFixedFrequency T)))
        (Finset.mem_univ S)
    _ = fourierOneNorm f :=
      sum_abs_split_fourierCoeff_eq_fourierOneNorm f J

/-- Reindex assignments on the complementary coordinate subtype by a standard finite cube. -/
noncomputable def fixedSignCubeEquiv (J : Finset (Fin n)) :
    {−1,1}^[Fintype.card (FixedIndex J)] ≃ FixedSignCube J where
  toFun z i := z (Fintype.equivFin (FixedIndex J) i)
  invFun z q := z ((Fintype.equivFin (FixedIndex J)).symm q)
  left_inv z := by
    funext q
    simp
  right_inv z := by
    funext i
    simp

private theorem fourierCoeff_restrictionFourierCoeff_comp_fixedSignCubeEquiv
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (T : Finset (Fin (Fintype.card (FixedIndex J)))) :
    fourierCoeff
        (fun z ↦ restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) T =
      indexedFourierCoeff (restrictionFourierCoeff f J S)
        (T.map (Fintype.equivFin (FixedIndex J)).symm.toEmbedding) := by
  classical
  unfold fourierCoeff indexedFourierCoeff
  apply Fintype.expect_equiv (fixedSignCubeEquiv J)
  intro z
  congr 1
  rw [indexedMonomial, Finset.prod_map]
  simp [monomial, fixedSignCubeEquiv]

private theorem fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_eq
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    fourierOneNorm
        (fun z ↦ restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) =
      ∑ T : Finset (FixedIndex J),
        |indexedFourierCoeff (restrictionFourierCoeff f J S) T| := by
  classical
  unfold fourierOneNorm
  let e : Fin (Fintype.card (FixedIndex J)) ≃ FixedIndex J :=
    (Fintype.equivFin (FixedIndex J)).symm
  apply Fintype.sum_equiv e.finsetCongr
  intro T
  rw [Equiv.finsetCongr_apply]
  exact congrArg abs
    (fourierCoeff_restrictionFourierCoeff_comp_fixedSignCubeEquiv
      f J S T)

/-- The standard-cube reindexing of the associated restricted-coefficient function
also has Fourier `1`-norm at most that of the ambient function. -/
theorem fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    fourierOneNorm
        (fun z ↦ restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) ≤
      fourierOneNorm f := by
  rw [fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_eq]
  exact
    sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm
      f J S

/-- O'Donnell, Equation (6.7): a density with nonnegative bias parameter
`ε / (4s²)` estimates the restricted Fourier weight to within `ε / 4`.
The first conjunct records the Corollary 6.39 bound and the second its
specialization using the Fourier `1`-norm hypothesis. -/
theorem restrictionFourierWeight_equation6_7
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (φ : ProbabilityDensity (Fintype.card (FixedIndex J)))
    {ε s : ℝ}
    (hφ : φ.IsBiased (ε / (4 * s ^ 2)))
    (hε : 0 ≤ ε) (hs : 1 ≤ s)
    (hf : fourierOneNorm f ≤ s) :
    let F : {−1,1}^[Fintype.card (FixedIndex J)] → ℝ :=
      fun z ↦ restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)
    (|φ.expectation (fun x ↦
          F (binaryCubeSignEquiv (Fintype.card (FixedIndex J)) x) ^ 2) -
        mean (fun z ↦ F z ^ 2)| ≤
      fourierOneNorm F ^ 2 * (ε / (4 * s ^ 2))) ∧
    (fourierOneNorm F ^ 2 * (ε / (4 * s ^ 2)) ≤ ε / 4) := by
  dsimp only
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsnonneg : 0 ≤ s := hspos.le
  have hdenom : 0 ≤ 4 * s ^ 2 := by positivity
  have hbias : 0 ≤ ε / (4 * s ^ 2) := div_nonneg hε hdenom
  constructor
  · exact
      φ.abs_expectation_signFunction_sq_sub_mean_sq_le
        (fun z ↦ restrictionFourierCoeff f J S (fixedSignCubeEquiv J z))
        hφ hbias
  · have hnorm :
        fourierOneNorm
            (fun z ↦
              restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) ≤
          s :=
      (fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le
        f J S).trans hf
    have hnormNonneg :
        0 ≤ fourierOneNorm
          (fun z ↦
            restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) :=
      fourierOneNorm_nonneg _
    have hsquare :
        fourierOneNorm
            (fun z ↦
              restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) ^ 2 ≤
          s ^ 2 :=
      (sq_le_sq₀ hnormNonneg hsnonneg).2 hnorm
    calc
      fourierOneNorm
            (fun z ↦
              restrictionFourierCoeff f J S (fixedSignCubeEquiv J z)) ^ 2 *
          (ε / (4 * s ^ 2)) ≤
          s ^ 2 * (ε / (4 * s ^ 2)) :=
        mul_le_mul_of_nonneg_right hsquare hbias
      _ = ε / 4 := by
        field_simp [ne_of_gt hspos]

end FABL
