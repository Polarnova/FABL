/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdLevelOne
public import FABL.Chapter05.UnateFunctions

/-!
# Coordinate influences of linear threshold functions

Book item: Exercise 5.6.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem thresholdSign_add_ne_sub_iff
    (r a : ℝ) :
    thresholdSign (r + a) ≠ thresholdSign (r - a) ↔
      -|a| ≤ r ∧ r < |a| := by
  constructor
  · intro hne
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha]
      constructor
      · by_contra hlower
        have hp : r + a < 0 := by linarith
        have hm : r - a < 0 := by linarith
        rw [thresholdSign_of_neg hp, thresholdSign_of_neg hm] at hne
        exact hne rfl
      · by_contra hupper
        have hp : 0 ≤ r + a := by linarith
        have hm : 0 ≤ r - a := by linarith
        rw [thresholdSign_of_nonneg hp, thresholdSign_of_nonneg hm] at hne
        exact hne rfl
    · have ha' : a < 0 := lt_of_not_ge ha
      rw [abs_of_neg ha']
      constructor
      · by_contra hlower
        have hp : r + a < 0 := by linarith
        have hm : r - a < 0 := by linarith
        rw [thresholdSign_of_neg hp, thresholdSign_of_neg hm] at hne
        exact hne rfl
      · by_contra hupper
        have hp : 0 ≤ r + a := by linarith
        have hm : 0 ≤ r - a := by linarith
        rw [thresholdSign_of_nonneg hp, thresholdSign_of_nonneg hm] at hne
        exact hne rfl
  · intro hinterval
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha] at hinterval
      have hp : 0 ≤ r + a := by linarith
      have hm : r - a < 0 := by linarith
      rw [thresholdSign_of_nonneg hp, thresholdSign_of_neg hm]
      decide
    · have ha' : a < 0 := lt_of_not_ge ha
      rw [abs_of_neg ha'] at hinterval
      have hp : r + a < 0 := by linarith
      have hm : 0 ≤ r - a := by linarith
      rw [thresholdSign_of_neg hp, thresholdSign_of_nonneg hm]
      decide

private noncomputable def affineLinearRemainder
    (a₀ : ℝ) (a : Fin n → ℝ) (i : Fin n)
    (x : {−1,1}^[n]) : ℝ :=
  a₀ + ∑ k ∈ (Finset.univ.erase i), a k * signValue (x k)

private noncomputable def affineLinearRemainderTwo
    (a₀ : ℝ) (a : Fin n → ℝ) (i j : Fin n)
    (x : {−1,1}^[n]) : ℝ :=
  a₀ + ∑ k ∈ ((Finset.univ.erase i).erase j),
    a k * signValue (x k)

private theorem affineLinearForm_setCoordinate
    (a₀ : ℝ) (a : Fin n → ℝ) (i : Fin n)
    (x : {−1,1}^[n]) (s : Sign) :
    affineLinearForm a₀ a (setCoordinate x i s) =
      affineLinearRemainder a₀ a i x + a i * signValue s := by
  classical
  unfold affineLinearForm linearForm affineLinearRemainder
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset (Fin n))
    (fun k ↦ a k * signValue (setCoordinate x i s k))
    (Finset.mem_univ i)
  rw [← hsplit]
  have hrest :
      (∑ k ∈ Finset.univ.erase i,
          a k * signValue (setCoordinate x i s k)) =
        ∑ k ∈ Finset.univ.erase i, a k * signValue (x k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [setCoordinate_apply_of_ne x (Finset.ne_of_mem_erase hk)]
  rw [hrest, setCoordinate_apply_self]
  ring

private theorem affineLinearRemainder_eq_two_add
    (a₀ : ℝ) (a : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (x : {−1,1}^[n]) :
    affineLinearRemainder a₀ a j x =
      affineLinearRemainderTwo a₀ a i j x +
        a i * signValue (x i) := by
  classical
  unfold affineLinearRemainder affineLinearRemainderTwo
  have hi : i ∈ (Finset.univ.erase j : Finset (Fin n)) := by
    simp [hij]
  have hsplit := Finset.sum_erase_add
    (Finset.univ.erase j)
    (fun k ↦ a k * signValue (x k)) hi
  rw [← hsplit, Finset.erase_right_comm]
  ring

private theorem affineLinearRemainder_permute_swap_eq
    (a₀ : ℝ) (a : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (x : {−1,1}^[n]) :
    affineLinearRemainder a₀ a i
        (permuteInput (Equiv.swap i j) x) =
      affineLinearRemainderTwo a₀ a i j x +
        a j * signValue (x i) := by
  classical
  unfold affineLinearRemainder affineLinearRemainderTwo
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hsplit := Finset.sum_erase_add
    (Finset.univ.erase i)
    (fun k ↦ a k * signValue (permuteInput (Equiv.swap i j) x k)) hj
  rw [← hsplit]
  have hrest :
      (∑ k ∈ (Finset.univ.erase i).erase j,
          a k * signValue (permuteInput (Equiv.swap i j) x k)) =
        ∑ k ∈ (Finset.univ.erase i).erase j,
          a k * signValue (x k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [permuteInput, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, permuteInput, Equiv.swap_apply_right]
  ring

private theorem mul_signValue_thresholdSign_mul
    (a : ℝ) (s : Sign) :
    a * signValue (thresholdSign a * s) =
      |a| * signValue s := by
  by_cases ha : 0 ≤ a
  · rw [thresholdSign_of_nonneg ha, abs_of_nonneg ha]
    simp
  · have ha' : a < 0 := lt_of_not_ge ha
    rw [thresholdSign_of_neg ha', abs_of_neg ha']
    rcases Int.units_eq_one_or s with hs | hs <;>
      simp [hs, signValue]

private theorem isPivotal_linearThreshold_iff
    (f : BooleanFunction n) (a₀ : ℝ) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm a₀ a x))
    (i : Fin n) (x : {−1,1}^[n]) :
    IsPivotal f i x ↔
      -|a i| ≤ affineLinearRemainder a₀ a i x ∧
        affineLinearRemainder a₀ a i x < |a i| := by
  rw [isPivotal_iff_setCoordinate_ne, hrep, hrep,
    affineLinearForm_setCoordinate, affineLinearForm_setCoordinate]
  simpa [sub_eq_add_neg] using
    thresholdSign_add_ne_sub_iff
      (affineLinearRemainder a₀ a i x) (a i)

private theorem booleanInfluence_le_of_nonnegative_weight_le
    (f : BooleanFunction n) (a₀ : ℝ) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm a₀ a x))
    {i j : Fin n} (hi : 0 ≤ a i) (hj : 0 ≤ a j)
    (hweight : a i ≤ a j) :
    booleanInfluence f i ≤ booleanInfluence f j := by
  classical
  by_cases hij : i = j
  · subst j
    exact le_rfl
  unfold booleanInfluence uniformProbability
  calc
    (𝔼 x, if IsPivotal f i x then (1 : ℝ) else 0) ≤
        𝔼 x,
          if IsPivotal f j (permuteInput (Equiv.swap j i) x)
          then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hpivotal : IsPivotal f i x
      · have hinterval :=
          (isPivotal_linearThreshold_iff f a₀ a hrep i x).mp hpivotal
        have htarget :
            IsPivotal f j (permuteInput (Equiv.swap j i) x) := by
          apply
            (isPivotal_linearThreshold_iff f a₀ a hrep j
              (permuteInput (Equiv.swap j i) x)).mpr
          rw [affineLinearRemainder_permute_swap_eq a₀ a (Ne.symm hij),
            abs_of_nonneg hj]
          rw [affineLinearRemainder_eq_two_add a₀ a (Ne.symm hij),
            abs_of_nonneg hi] at hinterval
          rcases Int.units_eq_one_or (x j) with hx | hx
          · have hu : signValue (x j) = 1 := by
              simp [hx, signValue]
            rw [hu] at hinterval ⊢
            norm_num only [mul_one] at hinterval ⊢
            constructor <;> linarith
          · have hu : signValue (x j) = -1 := by
              simp [hx, signValue]
            rw [hu] at hinterval ⊢
            norm_num only [mul_neg, mul_one] at hinterval ⊢
            constructor <;> linarith
        simp [hpivotal, htarget]
      · simp only [hpivotal, ↓reduceIte]
        split <;> norm_num
    _ = 𝔼 x, if IsPivotal f j x then (1 : ℝ) else 0 := by
      apply Fintype.expect_equiv (permuteInputEquiv (Equiv.swap j i))
      intro x
      rfl

/-- O'Donnell, Exercise 5.3, in pairwise form: among the coefficients of a
fixed affine threshold representation, a coordinate with no larger absolute
weight has no larger influence. -/
theorem influence_le_of_abs_linearThresholdWeight_le
    (f : BooleanFunction n) (a₀ : ℝ) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm a₀ a x))
    {i j : Fin n} (hweight : |a i| ≤ |a j|) :
    influence f.toReal i ≤ influence f.toReal j := by
  let σ : {−1,1}^[n] := fun k ↦ thresholdSign (a k)
  let g : BooleanFunction n := fun x ↦ f (reorientInput σ x)
  have hrepReoriented :
      ∀ x, g x =
        thresholdSign (affineLinearForm a₀ (fun k ↦ |a k|) x) := by
    intro x
    rw [show g x = f (reorientInput σ x) by rfl, hrep]
    congr 1
    unfold affineLinearForm linearForm
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_signValue_thresholdSign_mul (a k) (x k)
  have hcomparison :
      booleanInfluence g i ≤ booleanInfluence g j :=
    booleanInfluence_le_of_nonnegative_weight_le
      g a₀ (fun k ↦ |a k|) hrepReoriented
      (abs_nonneg _) (abs_nonneg _) hweight
  rw [show g = fun x ↦ f (reorientInput σ x) by rfl,
    booleanInfluence_comp_reorientInput,
    booleanInfluence_comp_reorientInput,
    booleanInfluence_eq_influence_toReal,
    booleanInfluence_eq_influence_toReal] at hcomparison
  exact hcomparison

/-- O'Donnell, Exercise 5.6: an unbiased linear threshold function on a nonempty
cube has a coordinate of influence at least `1 / √(2n)`. -/
theorem exists_one_div_sqrt_two_mul_dimension_le_influence_of_balanced_linearThreshold
    (f : BooleanFunction n) (hn : 1 ≤ n)
    (hbalanced : IsBalanced f.toReal) (hthreshold : IsLinearThreshold f) :
    ∃ i : Fin n,
      1 / Real.sqrt (2 * (n : ℝ)) ≤ influence f.toReal i := by
  have hweightAtMost :=
    one_half_le_fourierWeightAtMost_one_of_isLinearThreshold f hthreshold
  have hconstant :
      fourierCoeff f.toReal ∅ = 0 :=
    (isBalanced_iff_fourierCoeff_empty_eq_zero f.toReal).mp hbalanced
  have hweight :
      (1 : ℝ) / 2 ≤ ∑ i, fourierCoeff f.toReal {i} ^ 2 := by
    rw [fourierWeightAtMost_one_eq_empty_add_sum_singleton,
      hconstant, zero_pow (by norm_num), zero_add] at hweightAtMost
    exact hweightAtMost
  have hunate : IsUnate f := isUnate_of_isLinearThreshold f hthreshold
  have hcoefficient (i : Fin n) :
      fourierCoeff f.toReal {i} ^ 2 = influence f.toReal i ^ 2 := by
    rw [← sq_abs,
      (abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate f i).2
        (hunate i)]
  have hinfluenceWeight :
      (1 : ℝ) / 2 ≤ ∑ i, influence f.toReal i ^ 2 := by
    calc
      (1 : ℝ) / 2 ≤ ∑ i, fourierCoeff f.toReal {i} ^ 2 := hweight
      _ = ∑ i, influence f.toReal i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcoefficient i
  let c : ℝ := 1 / Real.sqrt (2 * (n : ℝ))
  have hnpos : 0 < n := by omega
  have hdimension : 0 < 2 * (n : ℝ) := by positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  by_contra hexists
  push Not at hexists
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hsum :
      (∑ i, influence f.toReal i ^ 2) <
        ∑ _i : Fin n, c ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    exact (sq_lt_sq₀ (influence_nonneg f.toReal i) hc.le).2
      (hexists i)
  have hconstantSum :
      (∑ _i : Fin n, c ^ 2) = (1 : ℝ) / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [c]
    have hsqrt : 0 < Real.sqrt (2 * (n : ℝ)) :=
      Real.sqrt_pos.2 hdimension
    rw [div_pow, one_pow, Real.sq_sqrt hdimension.le]
    field_simp [ne_of_gt hdimension]
  rw [hconstantSum] at hsum
  exact (not_lt_of_ge hinfluenceWeight) hsum

end FABL
