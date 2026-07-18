/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/

import FABL.Chapter02.FKN
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The sharp Level-1 inequality

Book item: Remark 5.28.

The printed signed generalization in Remark 5.28 is false. This module proves
the sharp statement for `[0,1]`-valued functions, including the zero-density
case, and records a two-dimensional counterexample to the printed
`[-1,1]`-valued statement.
-/

open Finset Set
open scoped BigOperators BooleanCube

namespace FABL

variable {n : ℕ}

private theorem expect_mul_linearForm_eq_singletonCoeffs
    (f : {−1,1}^[n] → ℝ) (a : Fin n → ℝ) :
    (𝔼 x, f x * linearForm a x) =
      ∑ i, a i * fourierCoeff f {i} := by
  rw [show
      (fun x : {−1,1}^[n] ↦ f x * linearForm a x) =
        fun x ↦ ∑ i, a i * (f x * monomial {i} x) by
    funext x
    rw [linearForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [monomial]
    ring]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_expect]
  rfl

private theorem gibbs_pointwise
    {q y Z : ℝ} (hq : 0 ≤ q) (hZ : 0 < Z) :
    q * y - q * Real.log Z - q * Real.log q ≤
      Real.exp y / Z - q := by
  by_cases hqzero : q = 0
  · simp only [hqzero, zero_mul, Real.log_zero, sub_zero]
    exact div_nonneg (Real.exp_pos y).le hZ.le
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
    let r : ℝ := Real.exp y / Z
    have hrpos : 0 < r := div_pos (Real.exp_pos y) hZ
    have hlog :
        Real.log (q / r) =
          Real.log q - (y - Real.log Z) := by
      dsimp only [r]
      rw [Real.log_div hqzero hrpos.ne', Real.log_div (Real.exp_ne_zero y) hZ.ne',
        Real.log_exp]
    have hbase :=
      Real.self_sub_one_le_mul_log (div_nonneg hq hrpos.le)
    have hscaled :
        q - r ≤ q * (Real.log q - (y - Real.log Z)) := by
      calc
        q - r = r * (q / r - 1) := by
          field_simp [hrpos.ne']
        _ ≤ r * ((q / r) * Real.log (q / r)) :=
          mul_le_mul_of_nonneg_left hbase hrpos.le
        _ = q * (Real.log q - (y - Real.log Z)) := by
          rw [hlog]
          field_simp [hrpos.ne']
    linarith

private theorem expect_mul_sub_log_expect_exp_le_entropy
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q y : ι → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hqmean : (𝔼 x, q x) = 1) :
    (𝔼 x, q x * y x) -
        Real.log (𝔼 x, Real.exp (y x)) ≤
      𝔼 x, q x * Real.log (q x) := by
  let Z : ℝ := 𝔼 x, Real.exp (y x)
  have hZ : 0 < Z := by
    dsimp only [Z]
    positivity
  have hpoint (x : ι) :
      q x * y x - q x * Real.log Z -
          q x * Real.log (q x) ≤
        Real.exp (y x) / Z - q x :=
    gibbs_pointwise (hq x) hZ
  have havg :
      (𝔼 x, (q x * y x - q x * Real.log Z -
          q x * Real.log (q x))) ≤
        𝔼 x, (Real.exp (y x) / Z - q x) :=
    Finset.expect_le_expect fun x _ ↦ hpoint x
  have hleft :
      (𝔼 x, (q x * y x - q x * Real.log Z -
          q x * Real.log (q x))) =
        (𝔼 x, q x * y x) - Real.log Z -
          𝔼 x, q x * Real.log (q x) := by
    rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib,
      ← Finset.expect_mul, hqmean, one_mul]
  have hright :
      (𝔼 x, (Real.exp (y x) / Z - q x)) = 0 := by
    rw [Finset.expect_sub_distrib, ← Finset.expect_div, hqmean]
    dsimp only [Z]
    rw [div_self hZ.ne', sub_self]
  rw [hleft, hright] at havg
  dsimp only [Z] at havg
  linarith

private theorem expect_mul_log_le_log_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℝ) {M : ℝ}
    (hq : ∀ x, 0 ≤ q x)
    (hqM : ∀ x, q x ≤ M)
    (hqmean : (𝔼 x, q x) = 1) :
    (𝔼 x, q x * Real.log (q x)) ≤ Real.log M := by
  have hpoint (x : ι) :
      q x * Real.log (q x) ≤ q x * Real.log M := by
    by_cases hqzero : q x = 0
    · simp [hqzero]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (lt_of_le_of_ne (hq x) (Ne.symm hqzero)) (hqM x))
        (hq x)
  calc
    (𝔼 x, q x * Real.log (q x)) ≤
        𝔼 x, q x * Real.log M :=
      Finset.expect_le_expect fun x _ ↦ hpoint x
    _ = (𝔼 x, q x) * Real.log M := by
      rw [Finset.expect_mul]
    _ = Real.log M := by rw [hqmean, one_mul]

private theorem expect_exp_linearForm_le
    (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], Real.exp (linearForm a x)) ≤
      Real.exp ((∑ i, a i ^ 2) / 2) := by
  classical
  have hexp (x : {−1,1}^[n]) :
      Real.exp (linearForm a x) =
        ∏ i, Real.exp (a i * signValue (x i)) := by
    rw [linearForm, Real.exp_sum]
  have hfactor :
      (𝔼 x : {−1,1}^[n],
          ∏ i, Real.exp (a i * signValue (x i))) =
        ∏ i, 𝔼 s : Sign, Real.exp (a i * signValue s) := by
    rw [Fintype.expect_eq_sum_div_card,
      ← Fintype.prod_sum
        (f := fun i (s : Sign) ↦ Real.exp (a i * signValue s)),
      Fintype.card_pi]
    simp_rw [Fintype.expect_eq_sum_div_card]
    rw [Finset.prod_div_distrib]
    norm_cast
  have hcoordinate (i : Fin n) :
      (𝔼 s : Sign, Real.exp (a i * signValue s)) =
        Real.cosh (a i) := by
    rw [expect_sign, Real.cosh_eq]
    simp
  calc
    (𝔼 x : {−1,1}^[n], Real.exp (linearForm a x)) =
        𝔼 x : {−1,1}^[n],
          ∏ i, Real.exp (a i * signValue (x i)) := by
      apply Finset.expect_congr rfl
      intro x _
      exact hexp x
    _ = ∏ i, Real.cosh (a i) := by
      rw [hfactor]
      apply Finset.prod_congr rfl
      intro i _
      exact hcoordinate i
    _ ≤ ∏ i, Real.exp (a i ^ 2 / 2) :=
      Finset.prod_le_prod
        (fun i _ ↦ (Real.cosh_pos (a i)).le)
        (fun i _ ↦ Real.cosh_le_exp_half_sq (a i))
    _ = Real.exp ((∑ i, a i ^ 2) / 2) := by
      rw [← Real.exp_sum, Finset.sum_div]

/-- The zero-density case of the sharp Level-1 inequality. -/
theorem sharpLevelOneInequality_eq_zero
    (f : {−1,1}^[n] → ℝ)
    (hvalues : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hmean : mean f = 0) :
    fourierWeightAtLevel 1 f = 0 := by
  have hfzero : f = 0 := by
    apply (Fintype.expect_eq_zero_iff_of_nonneg fun x ↦ (hvalues x).1).mp
    simpa only [mean] using hmean
  rw [hfzero, fourierWeightAtLevel_one_eq_sum_singleton]
  simp [fourierCoeff]

/-- The intended sharp form of Remark 5.28 for a `[0,1]`-valued function. -/
theorem sharpLevelOneInequality
    (f : {−1,1}^[n] → ℝ) {α : ℝ}
    (hvalues : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hmean : mean f = α)
    (hα : 0 < α)
    (_hαhalf : α ≤ 1 / 2) :
    fourierWeightAtLevel 1 f ≤
      2 * α ^ 2 * Real.log (1 / α) := by
  classical
  change (𝔼 x, f x) = α at hmean
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f {i}
  let b : Fin n → ℝ := fun i ↦ a i / α
  let q : {−1,1}^[n] → ℝ := fun x ↦ f x / α
  let W : ℝ := ∑ i, a i ^ 2
  have hqnonneg (x : {−1,1}^[n]) : 0 ≤ q x :=
    div_nonneg (hvalues x).1 hα.le
  have hqmean : (𝔼 x, q x) = 1 := by
    dsimp only [q]
    rw [← Finset.expect_div, hmean, div_self hα.ne']
  have hqbound (x : {−1,1}^[n]) : q x ≤ 1 / α :=
    div_le_div_of_nonneg_right (hvalues x).2 hα.le
  have hentropy :
      (𝔼 x, q x * Real.log (q x)) ≤ Real.log (1 / α) :=
    expect_mul_log_le_log_bound q hqnonneg hqbound hqmean
  have hcoeffq (i : Fin n) :
      fourierCoeff q {i} = a i / α := by
    dsimp only [q, a]
    unfold fourierCoeff
    rw [show
        (fun x : {−1,1}^[n] ↦
          f x / α * monomial {i} x) =
          fun x ↦ (f x * monomial {i} x) / α by
      funext x
      ring]
    rw [← Finset.expect_div]
  have hbSq : ∑ i, b i ^ 2 = W / α ^ 2 := by
    dsimp only [b, W]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
  have hweighted :
      (𝔼 x, q x * linearForm b x) = W / α ^ 2 := by
    rw [expect_mul_linearForm_eq_singletonCoeffs]
    simp_rw [hcoeffq]
    dsimp only [b]
    calc
      (∑ i, (a i / α) * (a i / α)) =
          ∑ i, a i ^ 2 / α ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← div_pow]
        ring_nf
      _ = W / α ^ 2 := by
        rw [Finset.sum_div]
  have hvariational :=
    expect_mul_sub_log_expect_exp_le_entropy q (linearForm b)
      hqnonneg hqmean
  have hmgf :
      (𝔼 x : {−1,1}^[n], Real.exp (linearForm b x)) ≤
        Real.exp (W / α ^ 2 / 2) := by
    simpa only [hbSq] using expect_exp_linearForm_le b
  have hmgfpos :
      0 < 𝔼 x : {−1,1}^[n], Real.exp (linearForm b x) := by
    positivity
  have hlogmgf :
      Real.log (𝔼 x : {−1,1}^[n], Real.exp (linearForm b x)) ≤
        W / α ^ 2 / 2 := by
    calc
      Real.log (𝔼 x : {−1,1}^[n], Real.exp (linearForm b x)) ≤
          Real.log (Real.exp (W / α ^ 2 / 2)) :=
        Real.log_le_log hmgfpos hmgf
      _ = W / α ^ 2 / 2 := Real.log_exp _
  rw [hweighted] at hvariational
  have hnormalized :
      W / α ^ 2 ≤ 2 * Real.log (1 / α) := by
    nlinarith
  have hαsq : 0 < α ^ 2 := sq_pos_of_pos hα
  have hW :
      W ≤ 2 * α ^ 2 * Real.log (1 / α) := by
    calc
      W = α ^ 2 * (W / α ^ 2) := by
        field_simp [hαsq.ne']
      _ ≤ α ^ 2 * (2 * Real.log (1 / α)) :=
        mul_le_mul_of_nonneg_left hnormalized hαsq.le
      _ = 2 * α ^ 2 * Real.log (1 / α) := by ring
  rw [fourierWeightAtLevel_one_eq_sum_singleton]
  exact hW

/-- The two-dimensional signed function witnessing the erratum in Remark 5.28. -/
noncomputable def sharpLevelOneSignedCounterexample :
    {−1,1}^[2] → ℝ :=
  linearForm fun _ ↦ 1 / 2

theorem sharpLevelOneSignedCounterexample_mem_Icc
    (x : {−1,1}^[2]) :
    sharpLevelOneSignedCounterexample x ∈ Icc (-1 : ℝ) 1 := by
  rcases signValue_eq_neg_one_or_one (x 0) with h0 | h0 <;>
    rcases signValue_eq_neg_one_or_one (x 1) with h1 | h1 <;>
      norm_num [sharpLevelOneSignedCounterexample, linearForm, h0, h1,
        Fin.sum_univ_two]

theorem mean_abs_sharpLevelOneSignedCounterexample :
    mean (fun x ↦ |sharpLevelOneSignedCounterexample x|) = 1 / 2 := by
  change (𝔼 x : {−1,1}^[2],
    |sharpLevelOneSignedCounterexample x|) = 1 / 2
  calc
    (𝔼 x : {−1,1}^[2],
        |sharpLevelOneSignedCounterexample x|) =
        𝔼 p : Sign × Sign,
          |(signValue p.1 + signValue p.2) / 2| := by
      apply Fintype.expect_equiv (finTwoArrowEquiv Sign)
      intro x
      simp [sharpLevelOneSignedCounterexample, linearForm, Fin.sum_univ_two]
      ring
    _ = 𝔼 s : Sign, 𝔼 t : Sign,
          |(signValue s + signValue t) / 2| := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 1 / 2 := by
      rw [expect_sign]
      simp_rw [expect_sign]
      norm_num

private theorem fourierCoeff_linearForm_singleton
    (a : Fin n → ℝ) (i : Fin n) :
    fourierCoeff (linearForm a) {i} = a i := by
  unfold fourierCoeff linearForm
  rw [show
      (fun x : {−1,1}^[n] ↦
        (∑ j, a j * signValue (x j)) * monomial {i} x) =
        fun x ↦ ∑ j, (a j * signValue (x j)) * monomial {i} x by
    funext x
    rw [Finset.sum_mul]]
  rw [Finset.expect_sum_comm]
  have hterm (j : Fin n) :
      (𝔼 x : {−1,1}^[n],
          (a j * signValue (x j)) * monomial {i} x) =
        a j * (if j = i then 1 else 0) := by
    rw [show
        (fun x : {−1,1}^[n] ↦
          (a j * signValue (x j)) * monomial {i} x) =
          fun x ↦ a j * (monomial {j} x * monomial {i} x) by
      funext x
      simp [monomial]
      ring]
    rw [← Finset.mul_expect, expect_monomial_mul]
    simp
  simp_rw [hterm]
  simp

theorem fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample :
    fourierWeightAtLevel 1 sharpLevelOneSignedCounterexample = 1 / 2 := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton]
  simp_rw [sharpLevelOneSignedCounterexample, fourierCoeff_linearForm_singleton]
  norm_num [Fin.sum_univ_two]

/-- The signed generalization printed in Remark 5.28 is false. -/
theorem not_sharpLevelOneInequality_signed :
    ¬ ∀ {n : ℕ} (f : {−1,1}^[n] → ℝ) {α : ℝ},
        (∀ x, |f x| ≤ 1) →
        mean (fun x ↦ |f x|) = α →
        0 < α →
        α ≤ 1 / 2 →
          fourierWeightAtLevel 1 f ≤
            2 * α ^ 2 * Real.log (1 / α) := by
  intro h
  have hfalse := h sharpLevelOneSignedCounterexample
    (α := (1 / 2 : ℝ))
    (fun x ↦ abs_le.mpr
      (sharpLevelOneSignedCounterexample_mem_Icc x))
    mean_abs_sharpLevelOneSignedCounterexample
    (by norm_num)
    (by norm_num)
  rw [fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample] at hfalse
  have hlog : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  norm_num at hfalse
  nlinarith

end FABL
