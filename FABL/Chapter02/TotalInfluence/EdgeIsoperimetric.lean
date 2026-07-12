/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.LaplacianAndPoincare
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Edge-isoperimetric inequality

Book items: Theorem 2.39.

The edge-isoperimetric inequality closing Section 2.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ### The edge-isoperimetric inequality -/

/-- The uniform probability that a Boolean function takes the value `1`. -/
noncomputable def positiveProbability (f : BooleanFunction n) : ℝ :=
  uniformProbability fun x ↦ f x = 1

/-- The positive-value probability is nonnegative. -/
theorem positiveProbability_nonneg (f : BooleanFunction n) :
    0 ≤ positiveProbability f := by
  unfold positiveProbability uniformProbability
  exact Finset.expect_nonneg fun x _ ↦ by positivity

/-- The positive-value probability is at most one. -/
theorem positiveProbability_le_one (f : BooleanFunction n) :
    positiveProbability f ≤ 1 := by
  unfold positiveProbability uniformProbability
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  split <;> norm_num

/-- Positive-value probability is the average of the probabilities on the two first-coordinate
slices. -/
theorem positiveProbability_cons (f : BooleanFunction (n + 1)) :
    positiveProbability f =
      (positiveProbability (firstCoordinateRestriction f 1) +
        positiveProbability (firstCoordinateRestriction f (-1))) / 2 := by
  unfold positiveProbability uniformProbability
  rw [expect_fin_cons]
  rfl

/-- The difference between the positive-value probabilities of two Boolean functions is bounded
by their disagreement probability. -/
theorem abs_positiveProbability_sub_le_uniformProbability_ne
    (f g : BooleanFunction n) :
    |positiveProbability f - positiveProbability g| ≤
      uniformProbability fun x ↦ f x ≠ g x := by
  classical
  have hsub : positiveProbability f - positiveProbability g =
      𝔼 x, ((if f x = 1 then (1 : ℝ) else 0) -
        (if g x = 1 then (1 : ℝ) else 0)) := by
    unfold positiveProbability uniformProbability
    rw [Finset.expect_sub_distrib]
  rw [hsub]
  calc
    |𝔼 x, ((if f x = 1 then (1 : ℝ) else 0) -
        (if g x = 1 then (1 : ℝ) else 0))| ≤
      𝔼 x, |(if f x = 1 then (1 : ℝ) else 0) -
        (if g x = 1 then (1 : ℝ) else 0)| := Finset.abs_expect_le _ _
    _ ≤ 𝔼 x, if f x ≠ g x then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hfg : f x = g x
      · simp [hfg]
      · rcases Int.units_eq_one_or (f x) with hf | hf <;>
          rcases Int.units_eq_one_or (g x) with hg | hg <;>
          norm_num [hf, hg, hfg]
    _ = uniformProbability (fun x ↦ f x ≠ g x) := rfl

/-- The chord from binary entropy at `0` to its maximum at `1/2`. -/
theorem two_mul_mul_log_two_le_binEntropy_of_le_half
    (p : ℝ) (hp0 : 0 ≤ p) (hphalf : p ≤ (1 / 2 : ℝ)) :
    2 * p * Real.log 2 ≤ Real.binEntropy p := by
  have hcoeff0 : 0 ≤ 1 - 2 * p := by linarith
  have hcoeff1 : 0 ≤ 2 * p := by linarith
  have hsum : (1 - 2 * p) + 2 * p = (1 : ℝ) := by ring
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    hcoeff0 hcoeff1 hsum
  have harg : 2 * p * (1 / 2 : ℝ) = p := by ring
  have hhalfEntropy : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  simp only [smul_eq_mul, Real.binEntropy_zero, mul_zero, zero_add] at hconc
  rw [harg, hhalfEntropy] at hconc
  simpa [mul_assoc] using hconc

/-- Binary entropy lies above the two chords joining its endpoint values to its maximum. -/
theorem two_mul_min_mul_log_two_le_binEntropy
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    2 * min p (1 - p) * Real.log 2 ≤ Real.binEntropy p := by
  by_cases hhalf : p ≤ (1 / 2 : ℝ)
  · have hmin : min p (1 - p) = p := by
      apply min_eq_left
      linarith
    rw [hmin]
    exact two_mul_mul_log_two_le_binEntropy_of_le_half p hp.1 hhalf
  · have hhalf' : 1 - p ≤ (1 / 2 : ℝ) := by linarith
    have hcomp0 : 0 ≤ 1 - p := by linarith [hp.2]
    have ih := two_mul_mul_log_two_le_binEntropy_of_le_half (1 - p) hcomp0 hhalf'
    rw [Real.binEntropy_one_sub] at ih
    have hmin : min p (1 - p) = 1 - p := by
      apply min_eq_right
      linarith
    simpa [hmin] using ih

/-- The binary-entropy estimate in the normalized form used by the edge-isoperimetric
induction. -/
theorem one_le_binEntropy_div_log_two_add_abs
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ Real.binEntropy p / Real.log 2 + |2 * p - 1| := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hent := two_mul_min_mul_log_two_le_binEntropy p hp
  rw [← sub_le_iff_le_add]
  apply (le_div_iff₀ hlog).2
  by_cases hhalf : p ≤ (1 / 2 : ℝ)
  · have hmin : min p (1 - p) = p := by
      apply min_eq_left
      linarith
    rw [hmin] at hent
    have habs : |2 * p - 1| = 1 - 2 * p := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [habs]
    nlinarith
  · have hmin : min p (1 - p) = 1 - p := by
      apply min_eq_right
      linarith
    rw [hmin] at hent
    have habs : |2 * p - 1| = 2 * p - 1 := by
      rw [abs_of_nonneg]
      linarith
    rw [habs]
    nlinarith

/-- The numerical midpoint inequality that drives the first-coordinate induction in
Theorem 2.39. -/
theorem two_mul_midpoint_mul_logb_inv_le
    (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    2 * ((a + b) / 2) * Real.logb 2 (((a + b) / 2)⁻¹) ≤
      a * Real.logb 2 a⁻¹ + b * Real.logb 2 b⁻¹ + |a - b| := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · simp [hb]
    · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
      have harg : (b / 2)⁻¹ = 2 * b⁻¹ := by field_simp
      rw [zero_add, zero_mul, zero_add, zero_sub, abs_neg, abs_of_pos hbpos, harg,
        Real.logb_mul (by norm_num) (inv_ne_zero hb)]
      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      nlinarith
  · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    by_cases hb : b = 0
    · subst b
      have harg : (a / 2)⁻¹ = 2 * a⁻¹ := by field_simp
      rw [add_zero, zero_mul, add_zero, sub_zero, abs_of_pos hapos, harg,
        Real.logb_mul (by norm_num) (inv_ne_zero ha)]
      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      nlinarith
    · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
      have hs : 0 < a + b := add_pos hapos hbpos
      let p := a / (a + b)
      have hp : p ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hapos.le hs.le
        · exact (div_le_one hs).2 (by linarith)
      have hbase := one_le_binEntropy_div_log_two_add_abs p hp
      have hbasePrime : Real.log 2 ≤ Real.binEntropy p + |2 * p - 1| * Real.log 2 := by
        calc
          Real.log 2 = Real.log 2 * 1 := by ring
          _ ≤ Real.log 2 * (Real.binEntropy p / Real.log 2 + |2 * p - 1|) :=
            mul_le_mul_of_nonneg_left hbase hlog.le
          _ = Real.binEntropy p + |2 * p - 1| * Real.log 2 := by
            field_simp
      have hscaled := mul_le_mul_of_nonneg_left hbasePrime hs.le
      have hsplit :
          (a + b) * Real.binEntropy (a / (a + b)) =
            a * Real.log a⁻¹ + b * Real.log b⁻¹ -
              (a + b) * Real.log (a + b)⁻¹ := by
        have hone : 1 - a / (a + b) = b / (a + b) := by
          field_simp
          ring
        rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hone,
          Real.negMulLog_eq_neg]
        simp only
        rw [Real.log_div hapos.ne' hs.ne', Real.log_div hbpos.ne' hs.ne']
        rw [Real.log_inv, Real.log_inv, Real.log_inv]
        field_simp
        ring
      have habs : (a + b) * |2 * (a / (a + b)) - 1| = |a - b| := by
        rw [show 2 * (a / (a + b)) - 1 = (a - b) / (a + b) by
          field_simp
          ring]
        rw [abs_div, abs_of_pos hs]
        field_simp
      have hmidlog : Real.log (((a + b) / 2)⁻¹) =
          Real.log 2 + Real.log (a + b)⁻¹ := by
        rw [show ((a + b) / 2)⁻¹ = 2 / (a + b) by field_simp]
        rw [Real.log_div (by norm_num) hs.ne', Real.log_inv]
        ring
      dsimp [p] at hscaled
      have hnatural :
          (a + b) * Real.log (((a + b) / 2)⁻¹) ≤
            a * Real.log a⁻¹ + b * Real.log b⁻¹ + |a - b| * Real.log 2 := by
        rw [hmidlog]
        nlinarith [hscaled, hsplit, habs]
      simp only [Real.logb]
      calc
        2 * ((a + b) / 2) * (Real.log (((a + b) / 2)⁻¹) / Real.log 2) =
            ((a + b) * Real.log (((a + b) / 2)⁻¹)) / Real.log 2 := by ring
        _ ≤ (a * Real.log a⁻¹ + b * Real.log b⁻¹ + |a - b| * Real.log 2) /
            Real.log 2 := (div_le_div_iff_of_pos_right hlog).2 hnatural
        _ = a * (Real.log a⁻¹ / Real.log 2) + b * (Real.log b⁻¹ / Real.log 2) +
            |a - b| := by field_simp

/-- The one-sided form of Theorem 2.39, proved by first-coordinate induction. -/
theorem two_mul_positiveProbability_mul_logb_inv_le_totalInfluence
    (f : BooleanFunction n) :
    2 * positiveProbability f * Real.logb 2 (positiveProbability f)⁻¹ ≤
      totalInfluence f.toReal := by
  induction n with
  | zero =>
      let x0 : {−1,1}^[0] := fun i ↦ Fin.elim0 i
      rcases Int.units_eq_one_or (f x0) with hf | hf
      · have hfun : f = fun _ ↦ 1 := by
          funext x
          rw [Subsingleton.elim x x0, hf]
        rw [hfun]
        simp [positiveProbability, uniformProbability, totalInfluence]
      · have hfun : f = fun _ ↦ -1 := by
          funext x
          rw [Subsingleton.elim x x0, hf]
        rw [hfun]
        simp [positiveProbability, uniformProbability, totalInfluence]
  | succ n ih =>
      let fp := firstCoordinateRestriction f 1
      let fm := firstCoordinateRestriction f (-1)
      let a := positiveProbability fp
      let b := positiveProbability fm
      have hpa : 0 ≤ a := positiveProbability_nonneg fp
      have hpb : 0 ≤ b := positiveProbability_nonneg fm
      have hiha := ih fp
      have hihb := ih fm
      have hihaHalf : a * Real.logb 2 a⁻¹ ≤ totalInfluence fp.toReal / 2 := by
        dsimp [a] at hiha ⊢
        nlinarith
      have hihbHalf : b * Real.logb 2 b⁻¹ ≤ totalInfluence fm.toReal / 2 := by
        dsimp [b] at hihb ⊢
        nlinarith
      have hdiff : |a - b| ≤ uniformProbability fun x ↦ fp x ≠ fm x :=
        abs_positiveProbability_sub_le_uniformProbability_ne fp fm
      rw [positiveProbability_cons]
      change
        2 * ((a + b) / 2) * Real.logb 2 (((a + b) / 2)⁻¹) ≤
          totalInfluence f.toReal
      calc
        2 * ((a + b) / 2) * Real.logb 2 (((a + b) / 2)⁻¹) ≤
            a * Real.logb 2 a⁻¹ + b * Real.logb 2 b⁻¹ + |a - b| :=
          two_mul_midpoint_mul_logb_inv_le a b hpa hpb
        _ ≤ totalInfluence fp.toReal / 2 + totalInfluence fm.toReal / 2 +
            uniformProbability (fun x ↦ fp x ≠ fm x) := by gcongr
        _ = totalInfluence f.toReal := by
          rw [totalInfluence_cons]
          dsimp [fp, fm]
          ring

/-- The uniform probability that a Boolean function takes the value `-1`. -/
noncomputable def negativeProbability (f : BooleanFunction n) : ℝ :=
  uniformProbability fun x ↦ f x = -1

/-- Negating a Boolean function exchanges its positive- and negative-value probabilities. -/
theorem positiveProbability_neg (f : BooleanFunction n) :
    positiveProbability (-f) = negativeProbability f := by
  classical
  unfold positiveProbability negativeProbability uniformProbability
  apply Finset.expect_congr rfl
  intro x _
  rcases Int.units_eq_one_or (f x) with hx | hx <;> simp [hx]

/-- Real encoding commutes with pointwise negation of Boolean functions. -/
theorem BooleanFunction.toReal_neg (f : BooleanFunction n) :
    (-f : BooleanFunction n).toReal = -f.toReal := by
  funext x
  change signValue (-f x) = -signValue (f x)
  rcases Int.units_eq_one_or (f x) with hx | hx <;> simp [hx]

/-- The smaller of the probabilities of the two Boolean output values. -/
noncomputable def minorityProbability (f : BooleanFunction n) : ℝ :=
  min (positiveProbability f) (negativeProbability f)

/-- O'Donnell, Theorem 2.39: if `α` is the smaller output probability of a Boolean function,
then `2 α log₂(1/α) ≤ I[f]`. -/
theorem two_mul_minorityProbability_mul_logb_inv_le_totalInfluence
    (f : BooleanFunction n) :
    2 * minorityProbability f * Real.logb 2 (minorityProbability f)⁻¹ ≤
      totalInfluence f.toReal := by
  have hpos := two_mul_positiveProbability_mul_logb_inv_le_totalInfluence f
  have hneg := two_mul_positiveProbability_mul_logb_inv_le_totalInfluence (-f)
  rw [positiveProbability_neg, BooleanFunction.toReal_neg, totalInfluence_neg] at hneg
  unfold minorityProbability
  by_cases h : positiveProbability f ≤ negativeProbability f
  · rw [min_eq_left h]
    exact hpos
  · rw [min_eq_right (le_of_not_ge h)]
    exact hneg


end FABL
