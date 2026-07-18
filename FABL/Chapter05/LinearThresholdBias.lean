/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdLevelOne

/-!
# Bias and homogeneous representations of linear threshold functions

Book item: Exercise 5.2.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem affineLinearForm_neg_input
    (a₀ : ℝ) (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    affineLinearForm a₀ a (-x) = a₀ - linearForm a x := by
  simp only [affineLinearForm, linearForm, Pi.neg_apply, signValue_neg, mul_neg,
    Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

private theorem thresholdPair_nonneg_of_bias_nonneg
    (a₀ t : ℝ) (ha₀ : 0 ≤ a₀) :
    0 ≤ signValue (thresholdSign (a₀ + t)) +
      signValue (thresholdSign (a₀ - t)) := by
  rw [signValue_thresholdSign, signValue_thresholdSign]
  by_cases hplus : 0 ≤ a₀ + t
  · by_cases hminus : 0 ≤ a₀ - t <;> simp [hplus, hminus]
  · have hminus : 0 ≤ a₀ - t := by linarith
    simp [hplus, hminus]

private theorem thresholdPair_nonpos_of_bias_neg
    (a₀ t : ℝ) (ha₀ : a₀ < 0) :
    signValue (thresholdSign (a₀ + t)) +
      signValue (thresholdSign (a₀ - t)) ≤ 0 := by
  rw [signValue_thresholdSign, signValue_thresholdSign]
  by_cases hplus : 0 ≤ a₀ + t
  · have hminus : ¬0 ≤ a₀ - t := by linarith
    simp [hplus, hminus]
  · by_cases hminus : 0 ≤ a₀ - t <;> simp [hplus, hminus]

private theorem expect_neg_input
    (u : {−1,1}^[n] → ℝ) :
    (𝔼 x : {−1,1}^[n], u (-x)) = 𝔼 x : {−1,1}^[n], u x := by
  apply Fintype.expect_equiv (Equiv.neg _)
  intro x
  rfl

private theorem odd_toReal (f : BooleanFunction n) (hf : Function.Odd f) :
    Function.Odd f.toReal := by
  intro x
  rw [BooleanFunction.toReal, BooleanFunction.toReal, hf x, signValue_neg]

private theorem odd_of_balanced_affineLinearThresholdRepresentation
    (f : BooleanFunction n) (a₀ : ℝ) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm a₀ a x))
    (hbalanced : IsBalanced f.toReal) :
    Function.Odd f := by
  have hpairExpectation :
      (𝔼 x : {−1,1}^[n], (f.toReal x + f.toReal (-x))) = 0 := by
    rw [Finset.expect_add_distrib, expect_neg_input]
    change mean f.toReal + mean f.toReal = 0
    rw [hbalanced]
    ring
  have hpairZero :
      ∀ x : {−1,1}^[n], f.toReal x + f.toReal (-x) = 0 := by
    by_cases ha₀ : 0 ≤ a₀
    · have hpairNonneg :
          ∀ x : {−1,1}^[n], 0 ≤ f.toReal x + f.toReal (-x) := by
        intro x
        rw [BooleanFunction.toReal, BooleanFunction.toReal, hrep x, hrep (-x),
          affineLinearForm_neg_input]
        simpa [affineLinearForm] using
          thresholdPair_nonneg_of_bias_nonneg a₀ (linearForm a x) ha₀
      intro x
      exact
        (Finset.expect_eq_zero_iff_of_nonneg
          fun y _ ↦ hpairNonneg y).mp hpairExpectation x (Finset.mem_univ x)
    · have ha₀neg : a₀ < 0 := lt_of_not_ge ha₀
      have hpairNonpos :
          ∀ x : {−1,1}^[n], f.toReal x + f.toReal (-x) ≤ 0 := by
        intro x
        rw [BooleanFunction.toReal, BooleanFunction.toReal, hrep x, hrep (-x),
          affineLinearForm_neg_input]
        simpa [affineLinearForm] using
          thresholdPair_nonpos_of_bias_neg a₀ (linearForm a x) ha₀neg
      intro x
      exact
        (Finset.expect_eq_zero_iff_of_nonpos
          fun y _ ↦ hpairNonpos y).mp hpairExpectation x (Finset.mem_univ x)
  intro x
  apply signValue_injective
  rw [signValue_neg]
  change f.toReal (-x) = -f.toReal x
  linarith [hpairZero x]

/-- Exercise 5.2(a), corrected for the book's convention `sgn(0) = 1`: a homogeneous
linear threshold representation with no cube point on its zero set is odd and balanced. -/
theorem homogeneousLinearThreshold_isOdd_and_isBalanced
    (f : BooleanFunction n) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm 0 a x))
    (hmargin : ∀ x : {−1,1}^[n], affineLinearForm 0 a x ≠ 0) :
    Function.Odd f ∧ IsBalanced f.toReal := by
  have hodd : Function.Odd f := by
    intro x
    rw [hrep (-x), hrep x, affineLinearForm_neg_input]
    have hmargin' : linearForm a x ≠ 0 := by
      simpa [affineLinearForm] using hmargin x
    simpa [affineLinearForm] using
      thresholdSign_neg (linearForm a x) hmargin'
  refine ⟨hodd, ?_⟩
  rw [IsBalanced, mean, Fintype.expect_eq_sum_div_card,
    (odd_toReal f hodd).sum_eq_zero]
  simp

/-- The smallest positive-dimensional counterexample to the unqualified wording of
Exercise 5.2(a): the all-zero homogeneous form represents the constant `+1` function,
which is neither odd nor balanced. -/
theorem zero_homogeneousLinearThreshold_counterexample :
    let f : BooleanFunction 1 := fun _ ↦ 1
    let a : Fin 1 → ℝ := fun _ ↦ 0
    (∀ x, f x = thresholdSign (affineLinearForm 0 a x)) ∧
      ¬Function.Odd f ∧ mean f.toReal = 1 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [affineLinearForm, linearForm]
  · intro hodd
    have h := hodd (fun _ : Fin 1 ↦ 1)
    norm_num at h
  · rw [mean]
    simp [BooleanFunction.toReal]

/-- Exercise 5.2(b): a nonnegative affine bias forces a nonnegative mean. -/
theorem mean_nonneg_of_nonnegative_linearThresholdBias
    (f : BooleanFunction n) (a₀ : ℝ) (a : Fin n → ℝ)
    (hrep : ∀ x, f x = thresholdSign (affineLinearForm a₀ a x))
    (ha₀ : 0 ≤ a₀) :
    0 ≤ mean f.toReal := by
  have hpairNonneg :
      ∀ x : {−1,1}^[n], 0 ≤ f.toReal x + f.toReal (-x) := by
    intro x
    rw [BooleanFunction.toReal, BooleanFunction.toReal, hrep x, hrep (-x),
      affineLinearForm_neg_input]
    simpa [affineLinearForm] using
      thresholdPair_nonneg_of_bias_nonneg a₀ (linearForm a x) ha₀
  have hmeanPair :
      0 ≤ 𝔼 x : {−1,1}^[n], (f.toReal x + f.toReal (-x)) :=
    Finset.expect_nonneg fun x _ ↦ hpairNonneg x
  rw [Finset.expect_add_distrib, expect_neg_input] at hmeanPair
  change 0 ≤ mean f.toReal
  change 0 ≤ (𝔼 x : {−1,1}^[n], f.toReal x)
  linarith

/-- Exercise 5.2(b), converse counterexample: the one-variable dictator has mean zero while
the displayed valid representation has strictly negative affine bias. -/
theorem nonnegative_mean_negative_bias_counterexample :
    ∃ (f : BooleanFunction 1) (a₀ : ℝ) (a : Fin 1 → ℝ),
      a₀ < 0 ∧
      (∀ x, f x = thresholdSign (affineLinearForm a₀ a x)) ∧
      0 ≤ mean f.toReal := by
  refine ⟨dictator 0, -(1 / 2 : ℝ), fun _ ↦ 1, by norm_num, ?_, ?_⟩
  · intro x
    rcases Int.units_eq_one_or (x 0) with hx | hx <;>
      simp [dictator, affineLinearForm, linearForm, hx,
        thresholdSign] <;>
      norm_num
  · have hreal :
        (dictator (0 : Fin 1)).toReal = monomial {(0 : Fin 1)} := by
      funext x
      exact dictator_toReal_eq_monomial_singleton 0 x
    rw [mean, hreal, expect_monomial]
    simp

/-- Exercise 5.2(c): every balanced linear threshold function admits an exact homogeneous
linear threshold representation. No no-tie hypothesis is required. -/
theorem exists_homogeneousLinearThresholdRepresentation_of_isBalanced
    (g : BooleanFunction n) (hg : IsLinearThreshold g)
    (hbalanced : IsBalanced g.toReal) :
    ∃ c : Fin n → ℝ,
      ∀ x, g x = thresholdSign (affineLinearForm 0 c x) := by
  rcases hg with ⟨a₀, a, hrep⟩
  have hrepAffine :
      ∀ x, g x = thresholdSign (affineLinearForm a₀ a x) := by
    simpa [affineLinearForm, linearForm] using hrep
  have hodd :=
    odd_of_balanced_affineLinearThresholdRepresentation g a₀ a
      hrepAffine hbalanced
  refine ⟨a, ?_⟩
  intro x
  rcases Int.units_eq_one_or (g x) with hx | hx
  · have hneg : g (-x) = -1 := by
      rw [hodd x, hx]
    have hpositive : 0 < linearForm a x := by
      have hplus : 0 ≤ affineLinearForm a₀ a x := by
        by_contra h
        have hlt : affineLinearForm a₀ a x < 0 := lt_of_not_ge h
        have := hrepAffine x
        rw [hx, thresholdSign_of_neg hlt] at this
        norm_num at this
      have hminus : affineLinearForm a₀ a (-x) < 0 := by
        by_contra h
        have hnonneg : 0 ≤ affineLinearForm a₀ a (-x) := le_of_not_gt h
        have := hrepAffine (-x)
        rw [hneg, thresholdSign_of_nonneg hnonneg] at this
        norm_num at this
      rw [affineLinearForm_neg_input] at hminus
      rw [affineLinearForm] at hplus
      by_cases ha₀ : 0 ≤ a₀
      · linarith
      · have ha₀neg : a₀ < 0 := lt_of_not_ge ha₀
        linarith
    rw [hx]
    simp [affineLinearForm, thresholdSign_of_nonneg hpositive.le]
  · have hpos : g (-x) = 1 := by
      rw [hodd x, hx]
      norm_num
    have hnegative : linearForm a x < 0 := by
      have hplus : affineLinearForm a₀ a x < 0 := by
        by_contra h
        have hnonneg : 0 ≤ affineLinearForm a₀ a x := le_of_not_gt h
        have := hrepAffine x
        rw [hx, thresholdSign_of_nonneg hnonneg] at this
        norm_num at this
      have hminus : 0 ≤ affineLinearForm a₀ a (-x) := by
        by_contra h
        have hlt : affineLinearForm a₀ a (-x) < 0 := lt_of_not_ge h
        have := hrepAffine (-x)
        rw [hpos, thresholdSign_of_neg hlt] at this
        norm_num at this
      rw [affineLinearForm_neg_input] at hminus
      rw [affineLinearForm] at hplus
      by_cases ha₀ : 0 ≤ a₀
      · linarith
      · have ha₀neg : a₀ < 0 := lt_of_not_ge ha₀
        linarith
    rw [hx]
    simp [affineLinearForm, thresholdSign_of_neg hnegative]

end FABL
