/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.FKN
public import FABL.Chapter05.UnateFunctions

/-!
# Robust edge isoperimetry at volume one half

Book item: Exercise 5.35.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem two_sub_totalInfluence_le_fourierWeightAtLevel_one_of_isBalanced
    (f : BooleanFunction n) (hbalanced : IsBalanced f.toReal) :
    2 - totalInfluence f.toReal ≤ fourierWeightAtLevel 1 f.toReal := by
  classical
  have hzero : fourierCoeff f.toReal ∅ = 0 :=
    (isBalanced_iff_fourierCoeff_empty_eq_zero f.toReal).mp hbalanced
  rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  unfold fourierWeightAtLevel fourierWeight
  calc
    2 - ∑ S, (S.card : ℝ) * fourierCoeff f.toReal S ^ 2 =
        2 * (∑ S, fourierCoeff f.toReal S ^ 2) -
          ∑ S, (S.card : ℝ) * fourierCoeff f.toReal S ^ 2 := by
      rw [sum_sq_fourierCoeff_eq_one f]
      ring
    _ = ∑ S, (2 * fourierCoeff f.toReal S ^ 2 -
        (S.card : ℝ) * fourierCoeff f.toReal S ^ 2) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ =
        ∑ S, ((2 : ℝ) - S.card) * fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = 1),
        fourierCoeff f.toReal S ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = ∅
      · subst S
        simp [hzero]
      by_cases hcard : S.card = 1
      · norm_num [hcard]
      · have hcardTwo : 2 ≤ S.card := by
          have hcardPos : 1 ≤ S.card :=
            Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
          omega
        have hfactor : (2 : ℝ) - S.card ≤ 0 := by
          have hcardReal : (2 : ℝ) ≤ S.card := by
            exact_mod_cast hcardTwo
          linarith
        rw [if_neg hcard]
        exact mul_nonpos_of_nonpos_of_nonneg hfactor (sq_nonneg _)

private theorem positive_dimension_of_isBalanced
    (f : BooleanFunction n) (hbalanced : IsBalanced f.toReal) :
    0 < n := by
  by_contra hn
  have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let x₀ : {−1,1}^[0] := fun i ↦ Fin.elim0 i
  have hconstant :
      f.toReal = fun _ ↦ signValue (f x₀) := by
    funext x
    rw [BooleanFunction.toReal]
    exact congrArg signValue (congrArg f (Subsingleton.elim x x₀))
  rw [hconstant] at hbalanced
  unfold IsBalanced mean at hbalanced
  rw [Fintype.expect_const] at hbalanced
  rcases Int.units_eq_one_or (f x₀) with h | h <;>
    simp [h, signValue] at hbalanced

/-- Exercise 5.35: a balanced Boolean function of total influence at most
`1 + δ` is `δ`-close to a dictator or negated dictator. -/
theorem exists_signedDictator_relativeHammingDist_le_of_isBalanced_totalInfluence_le
    (f : BooleanFunction n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbalanced : IsBalanced f.toReal)
    (hinfluence : totalInfluence f.toReal ≤ 1 + δ) :
    ∃ i : Fin n, ∃ negated : Bool,
      relativeHammingDist f (signedDictator i negated) ≤ δ := by
  classical
  have hn := positive_dimension_of_isBalanced f hbalanced
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j ↦ |fourierCoeff f.toReal {j}|)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let c : ℝ := fourierCoeff f.toReal {i}
  have hweightLower :
      1 - δ ≤ fourierWeightAtLevel 1 f.toReal := by
    calc
      1 - δ ≤ 2 - totalInfluence f.toReal := by linarith
      _ ≤ fourierWeightAtLevel 1 f.toReal :=
        two_sub_totalInfluence_le_fourierWeightAtLevel_one_of_isBalanced
          f hbalanced
  have hweightUpper :
      fourierWeightAtLevel 1 f.toReal ≤
        |c| * totalInfluence f.toReal := by
    rw [fourierWeightAtLevel_one_eq_sum_singleton, totalInfluence,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hmax :
        |fourierCoeff f.toReal {j}| ≤ |c| := by
      exact hi j (Finset.mem_univ j)
    have hcoefficient :=
      abs_fourierCoeff_singleton_le_influence f j
    calc
      fourierCoeff f.toReal {j} ^ 2 =
          |fourierCoeff f.toReal {j}| *
            |fourierCoeff f.toReal {j}| := by
        rw [← sq_abs, pow_two]
      _ ≤ |c| * influence f.toReal j :=
        mul_le_mul hmax hcoefficient
          (abs_nonneg _) (abs_nonneg _)
  have hproduct :
      1 - δ ≤ |c| * (1 + δ) := by
    exact hweightLower.trans
      (hweightUpper.trans
        (mul_le_mul_of_nonneg_left hinfluence (abs_nonneg c)))
  have hcSqLeWeight :
      c ^ 2 ≤ fourierWeightAtLevel 1 f.toReal := by
    rw [fourierWeightAtLevel_one_eq_sum_singleton]
    exact Finset.single_le_sum
      (fun j _ ↦ sq_nonneg (fourierCoeff f.toReal {j}))
      (Finset.mem_univ i)
  have hcSqLeOne :
      c ^ 2 ≤ 1 :=
    hcSqLeWeight.trans (fourierWeightAtLevel_one_mem_Icc f).2
  have hcAbsLeOne : |c| ≤ 1 := by
    exact (sq_le_sq₀ (abs_nonneg c) (by norm_num)).mp
      (by simpa [sq_abs] using hcSqLeOne)
  have hproductUpper : |c| * (1 + δ) ≤ |c| + δ := by
    calc
      |c| * (1 + δ) = |c| + |c| * δ := by ring
      _ ≤ |c| + 1 * δ :=
        add_le_add_right
          (mul_le_mul_of_nonneg_right hcAbsLeOne hδ) _
      _ = |c| + δ := by ring
  have hcLarge : 1 - 2 * δ ≤ |c| := by
    linarith
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  have hcorr : c = ⟪f.toReal, (dictator i).toReal⟫ᵤ := by
    rw [hdictator]
    exact fourierCoeff_eq_uniformInner f.toReal {i}
  by_cases hc : 0 ≤ c
  · refine ⟨i, false, ?_⟩
    simp only [signedDictator, Bool.false_eq_true, if_false]
    have hcLower : 1 - 2 * δ ≤ c := by
      simpa [abs_of_nonneg hc] using hcLarge
    rw [uniformInner_eq_one_sub_two_mul_relativeHammingDist] at hcorr
    linarith
  · refine ⟨i, true, ?_⟩
    simp only [signedDictator, if_true]
    have hcneg : -c = |c| := by
      rw [abs_of_neg (lt_of_not_ge hc)]
    have hcorrNeg :
        -c = ⟪f.toReal, (-dictator i : BooleanFunction n).toReal⟫ᵤ := by
      rw [BooleanFunction.toReal_neg, uniformInner, RCLike.wInner_neg_right]
      exact congrArg Neg.neg hcorr
    have hcLower : 1 - 2 * δ ≤ -c := by
      simpa [hcneg] using hcLarge
    rw [uniformInner_eq_one_sub_two_mul_relativeHammingDist] at hcorrNeg
    linarith

end FABL
