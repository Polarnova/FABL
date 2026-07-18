/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.ArrowLevelOneBound

/-!
# Unate Boolean functions

Book items: Exercise 2.5, Exercise 2.6.

The coordinatewise notion of unateness and the influence bounds used by Section 5.5 of
O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Reorient each coordinate of a sign-cube input by a fixed sign pattern. -/
def reorientInput (σ x : {−1,1}^[n]) : {−1,1}^[n] :=
  fun i ↦ σ i * x i

/-- Coordinatewise sign reorientation is an involutive equivalence of the sign cube. -/
def reorientInputEquiv (σ : {−1,1}^[n]) :
    {−1,1}^[n] ≃ {−1,1}^[n] where
  toFun := reorientInput σ
  invFun := reorientInput σ
  left_inv x := by
    funext i
    rcases Int.units_eq_one_or (σ i) with hσ | hσ <;>
      simp [reorientInput, hσ]
  right_inv x := by
    funext i
    rcases Int.units_eq_one_or (σ i) with hσ | hσ <;>
      simp [reorientInput, hσ]

@[simp] theorem reorientInputEquiv_apply
    (σ x : {−1,1}^[n]) :
    reorientInputEquiv σ x = reorientInput σ x :=
  rfl

/-- Reorienting coordinates commutes with flipping any one coordinate. -/
theorem reorientInput_flipCoordinate
    (σ x : {−1,1}^[n]) (i : Fin n) :
    reorientInput σ (flipCoordinate x i) =
      flipCoordinate (reorientInput σ x) i := by
  funext j
  by_cases hji : j = i
  · subst j
    rcases Int.units_eq_one_or (σ i) with hσ | hσ <;>
      rcases Int.units_eq_one_or (x i) with hx | hx <;>
      simp [reorientInput, flipCoordinate, setCoordinate, hσ, hx]
  · simp [reorientInput, flipCoordinate, setCoordinate, hji]

/-- Reorienting the inputs of a Boolean function does not change any coordinate influence. -/
theorem booleanInfluence_comp_reorientInput
    (f : BooleanFunction n) (σ : {−1,1}^[n]) (i : Fin n) :
    booleanInfluence (fun x ↦ f (reorientInput σ x)) i =
      booleanInfluence f i := by
  classical
  unfold booleanInfluence uniformProbability
  apply Fintype.expect_equiv (reorientInputEquiv σ)
  intro x
  have hpivotal :
      IsPivotal (fun y ↦ f (reorientInput σ y)) i x ↔
        IsPivotal f i (reorientInputEquiv σ x) := by
    unfold IsPivotal
    change
      f (reorientInput σ x) ≠
          f (reorientInput σ (flipCoordinate x i)) ↔
        f (reorientInput σ x) ≠
          f (flipCoordinate (reorientInput σ x) i)
    rw [reorientInput_flipCoordinate]
  simp only [hpivotal]

/-- A Boolean function is monotone in coordinate `i` when changing that coordinate from `-1`
to `1` cannot decrease its value. -/
def IsMonotoneInCoordinate (f : BooleanFunction n) (i : Fin n) : Prop :=
  ∀ x, f (setCoordinate x i (-1)) ≤ f (setCoordinate x i 1)

/-- A Boolean function is antimonotone in coordinate `i` when changing that coordinate from `-1`
to `1` cannot increase its value. -/
def IsAntimonotoneInCoordinate (f : BooleanFunction n) (i : Fin n) : Prop :=
  ∀ x, f (setCoordinate x i 1) ≤ f (setCoordinate x i (-1))

/-- O'Donnell, Exercise 2.5: a Boolean function is unate in a coordinate when it is monotone or
antimonotone in that coordinate. -/
def IsUnateInCoordinate (f : BooleanFunction n) (i : Fin n) : Prop :=
  IsMonotoneInCoordinate f i ∨ IsAntimonotoneInCoordinate f i

/-- O'Donnell, Exercise 2.5: a Boolean function is unate when it is unate in every coordinate. -/
def IsUnate (f : BooleanFunction n) : Prop :=
  ∀ i, IsUnateInCoordinate f i

private theorem abs_discreteDerivative_toReal_eq_sq
    (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) :
    |discreteDerivative i f.toReal x| = discreteDerivative i f.toReal x ^ 2 := by
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

/-- O'Donnell, Exercise 2.5(a): a singleton Fourier coefficient is bounded in absolute value by
the corresponding coordinate influence. -/
theorem abs_fourierCoeff_singleton_le_influence
    (f : BooleanFunction n) (i : Fin n) :
    |fourierCoeff f.toReal {i}| ≤ influence f.toReal i := by
  rw [← mean_discreteDerivative_eq_fourierCoeff_singleton, influence, mean]
  calc
    |𝔼 x, discreteDerivative i f.toReal x| ≤
        𝔼 x, |discreteDerivative i f.toReal x| :=
      Finset.abs_expect_le _ _
    _ = 𝔼 x, discreteDerivative i f.toReal x ^ 2 := by
      apply Finset.expect_congr rfl
      intro x _
      exact abs_discreteDerivative_toReal_eq_sq f i x

private theorem derivative_sq_sub_self_nonneg
    (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) :
    0 ≤ discreteDerivative i f.toReal x ^ 2 - discreteDerivative i f.toReal x := by
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

private theorem derivative_sq_add_self_nonneg
    (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) :
    0 ≤ discreteDerivative i f.toReal x ^ 2 + discreteDerivative i f.toReal x := by
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

/-- Equality in the singleton-coefficient influence bound holds exactly in the unate
directions. -/
theorem abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate
    (f : BooleanFunction n) (i : Fin n) :
    |fourierCoeff f.toReal {i}| = influence f.toReal i ↔
      IsUnateInCoordinate f i := by
  rw [← mean_discreteDerivative_eq_fourierCoeff_singleton, influence]
  constructor
  · intro heq
    by_cases hmean : 0 ≤ mean (discreteDerivative i f.toReal)
    · left
      intro x
      have hzero :
          (𝔼 y, (discreteDerivative i f.toReal y ^ 2 -
            discreteDerivative i f.toReal y)) = 0 := by
        rw [Finset.expect_sub_distrib]
        change (𝔼 y, discreteDerivative i f.toReal y ^ 2) -
          mean (discreteDerivative i f.toReal) = 0
        rw [← heq, abs_of_nonneg hmean]
        ring
      have hxzero :
          discreteDerivative i f.toReal x ^ 2 -
            discreteDerivative i f.toReal x = 0 :=
        (Finset.expect_eq_zero_iff_of_nonneg
          fun y _ ↦ derivative_sq_sub_self_nonneg f i y).mp hzero x (Finset.mem_univ x)
      rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp
      · rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · rw [hp, hm]
        · rw [hp, hm]
          decide
      · rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm] at hxzero
        · rw [hp, hm]
    · right
      intro x
      have hmean' : mean (discreteDerivative i f.toReal) ≤ 0 := le_of_not_ge hmean
      have hzero :
          (𝔼 y, (discreteDerivative i f.toReal y ^ 2 +
            discreteDerivative i f.toReal y)) = 0 := by
        rw [Finset.expect_add_distrib]
        change (𝔼 y, discreteDerivative i f.toReal y ^ 2) +
          mean (discreteDerivative i f.toReal) = 0
        rw [← heq, abs_of_nonpos hmean']
        ring
      have hxzero :
          discreteDerivative i f.toReal x ^ 2 +
            discreteDerivative i f.toReal x = 0 :=
        (Finset.expect_eq_zero_iff_of_nonneg
          fun y _ ↦ derivative_sq_add_self_nonneg f i y).mp hzero x (Finset.mem_univ x)
      rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp
      · rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · rw [hp, hm]
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm] at hxzero
      · rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · rw [hp, hm]
          decide
        · rw [hp, hm]
  · rintro (hmono | hanti)
    · have hderivative (x : {−1,1}^[n]) :
          discreteDerivative i f.toReal x ^ 2 =
            discreteDerivative i f.toReal x := by
        have hle := hmono x
        rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
          rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
        · rw [hp, hm] at hle
          exact False.elim ((by decide : ¬ ((1 : Sign) ≤ -1)) hle)
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
      have hmeanNonneg : 0 ≤ mean (discreteDerivative i f.toReal) := by
        rw [mean]
        apply Finset.expect_nonneg
        intro x _
        rw [← hderivative x]
        positivity
      rw [abs_of_nonneg hmeanNonneg]
      change mean (discreteDerivative i f.toReal) =
        𝔼 x, discreteDerivative i f.toReal x ^ 2
      rw [mean]
      apply Finset.expect_congr rfl
      intro x _
      exact (hderivative x).symm
    · have hderivative (x : {−1,1}^[n]) :
          discreteDerivative i f.toReal x ^ 2 =
            -discreteDerivative i f.toReal x := by
        have hle := hanti x
        rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
          rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
        · rw [hp, hm] at hle
          exact False.elim ((by decide : ¬ ((1 : Sign) ≤ -1)) hle)
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
        · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
      have hmeanNonpos : mean (discreteDerivative i f.toReal) ≤ 0 := by
        rw [mean]
        apply neg_nonneg.mp
        rw [← Finset.expect_neg_distrib]
        apply Finset.expect_nonneg
        intro x _
        rw [← hderivative x]
        positivity
      rw [abs_of_nonpos hmeanNonpos]
      change -mean (discreteDerivative i f.toReal) =
        𝔼 x, discreteDerivative i f.toReal x ^ 2
      rw [mean, ← Finset.expect_neg_distrib]
      apply Finset.expect_congr rfl
      intro x _
      exact (hderivative x).symm

private theorem sum_abs_fourierCoeff_singleton_le_totalInfluence_majority
    (f : BooleanFunction n) :
    (∑ i, |fourierCoeff f.toReal {i}|) ≤
      totalInfluence (majority n).toReal := by
  classical
  let σ : Fin n → Sign := fun i ↦ thresholdSign (fourierCoeff f.toReal {i})
  let reorient : {−1,1}^[n] ≃ {−1,1}^[n] :=
    reorientInputEquiv σ
  let g : BooleanFunction n := fun x ↦ f (reorient x)
  have hσ (i : Fin n) :
      signValue (σ i) * fourierCoeff f.toReal {i} =
        |fourierCoeff f.toReal {i}| := by
    simp only [σ, signValue_thresholdSign]
    by_cases hcoeff : 0 ≤ fourierCoeff f.toReal {i}
    · rw [if_pos hcoeff, abs_of_nonneg hcoeff]
      ring
    · have hcoeff' : fourierCoeff f.toReal {i} < 0 := lt_of_not_ge hcoeff
      rw [if_neg hcoeff, abs_of_neg hcoeff']
      ring
  have hcoeff (i : Fin n) :
      fourierCoeff g.toReal {i} =
        signValue (σ i) * fourierCoeff f.toReal {i} := by
    rw [fourierCoeff, fourierCoeff, Finset.mul_expect]
    apply Fintype.expect_equiv reorient
    intro x
    change signValue (f (reorient x)) * monomial {i} x =
      signValue (σ i) * (signValue (f (reorient x)) * monomial {i} (reorient x))
    simp only [monomial, Finset.prod_singleton]
    change signValue (f (reorient x)) * signValue (x i) =
      signValue (σ i) *
        (signValue (f (reorient x)) * signValue (σ i * x i))
    rcases Int.units_eq_one_or (σ i) with hσi | hσi <;>
      rcases Int.units_eq_one_or (x i) with hxi | hxi <;>
      simp [signValue, hσi, hxi]
  calc
    (∑ i, |fourierCoeff f.toReal {i}|) =
        ∑ i, fourierCoeff g.toReal {i} := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff, hσ]
    _ ≤ ∑ i, fourierCoeff (majority n).toReal {i} :=
      sum_fourierCoeff_singleton_le_majority g
    _ = totalInfluence (majority n).toReal :=
      (totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone
        (majority n) (majority_monotone n)).symm

/-- O'Donnell, Exercise 2.5(b): every unate Boolean function has total influence at most
majority's total influence. -/
theorem totalInfluence_toReal_le_majority_of_unate
    (f : BooleanFunction n) (hf : IsUnate f) :
    totalInfluence f.toReal ≤ totalInfluence (majority n).toReal := by
  rw [totalInfluence]
  calc
    (∑ i, influence f.toReal i) =
        ∑ i, |fourierCoeff f.toReal {i}| := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        (abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate f i).2
          (hf i) |>.symm
    _ ≤ totalInfluence (majority n).toReal :=
      sum_abs_fourierCoeff_singleton_le_totalInfluence_majority f

/-- O'Donnell, Exercise 2.23: every unate Boolean function on `n` variables has total influence
at most `√n`. -/
theorem totalInfluence_toReal_le_sqrt_card_of_unate
    (f : BooleanFunction n) (hf : IsUnate f) :
    totalInfluence f.toReal ≤ Real.sqrt n := by
  classical
  have hlevel : fourierWeightAtLevel 1 f.toReal ≤ 1 := by
    unfold fourierWeightAtLevel fourierWeight
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = 1),
          fourierCoeff f.toReal S ^ 2) ≤
          ∑ S : Finset (Fin n), fourierCoeff f.toReal S ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ ↦ sq_nonneg (fourierCoeff f.toReal S))
      _ = 1 := sum_sq_fourierCoeff_eq_one f
  have hsingletonSq :
      (∑ i, |fourierCoeff f.toReal {i}| ^ 2) ≤ 1 := by
    rw [show (∑ i, |fourierCoeff f.toReal {i}| ^ 2) =
        fourierWeightAtLevel 1 f.toReal by
      rw [fourierWeightAtLevel_one_eq_sum_singleton]
      apply Finset.sum_congr rfl
      intro i _
      exact sq_abs (fourierCoeff f.toReal {i})]
    exact hlevel
  have hcauchy :
      (∑ i, |fourierCoeff f.toReal {i}|) ≤
        Real.sqrt (∑ i, |fourierCoeff f.toReal {i}| ^ 2) *
          Real.sqrt n := by
    simpa using
      (Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset (Fin n))
        (fun i ↦ |fourierCoeff f.toReal {i}|)
        (fun _ ↦ (1 : ℝ)))
  rw [totalInfluence]
  calc
    (∑ i, influence f.toReal i) =
        ∑ i, |fourierCoeff f.toReal {i}| := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        (abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate f i).2
          (hf i) |>.symm
    _ ≤ Real.sqrt (∑ i, |fourierCoeff f.toReal {i}| ^ 2) *
          Real.sqrt n := hcauchy
    _ ≤ Real.sqrt 1 * Real.sqrt n := by
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsingletonSq)
        (Real.sqrt_nonneg n)
    _ = Real.sqrt n := by simp

/-- O'Donnell, Exercise 2.6: every Boolean linear threshold function is unate. -/
theorem isUnate_of_isLinearThreshold
    (f : BooleanFunction n) (hf : IsLinearThreshold f) :
    IsUnate f := by
  classical
  rcases hf with ⟨a₀, a, hrep⟩
  intro i
  rcases le_total 0 (a i) with hai | hai
  · left
    intro x
    rw [hrep, hrep]
    apply monotone_thresholdSign
    have hsum :
        (∑ j, a j * signValue (setCoordinate x i (-1) j)) ≤
          ∑ j, a j * signValue (setCoordinate x i 1 j) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [setCoordinate_apply_self, signValue_neg_one, signValue_one]
        linarith
      · rw [setCoordinate_apply_of_ne x hji, setCoordinate_apply_of_ne x hji]
    linarith
  · right
    intro x
    rw [hrep, hrep]
    apply monotone_thresholdSign
    have hsum :
        (∑ j, a j * signValue (setCoordinate x i 1 j)) ≤
          ∑ j, a j * signValue (setCoordinate x i (-1) j) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [setCoordinate_apply_self, signValue_neg_one, signValue_one]
        linarith
      · rw [setCoordinate_apply_of_ne x hji, setCoordinate_apply_of_ne x hji]
    linarith

end FABL
