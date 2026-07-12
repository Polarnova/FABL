/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Influence of odd majority

Book items: Example 2.30, Exercise 2.22.

Exact formulas and asymptotic estimates for odd majority in Section 2.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The common influence of a coordinate of majority on `2m+1` voters. This is the central
binomial probability appearing in Exercise 2.22(a). -/
noncomputable def oddMajorityInfluence (m : ℕ) : ℝ :=
  (Nat.choose (2 * m) m : ℝ) / (2 ^ (2 * m) : ℝ)

/-- Exercise 2.22(a), restated using the central-binomial probability. -/
theorem booleanInfluence_majority_odd_eq_oddMajorityInfluence
    (m : ℕ) (i : Fin (2 * m + 1)) :
    booleanInfluence (majority (2 * m + 1)) i = oddMajorityInfluence m := by
  exact booleanInfluence_majority_odd m i

/-- The central-binomial probability is positive. -/
theorem oddMajorityInfluence_pos (m : ℕ) : 0 < oddMajorityInfluence m := by
  unfold oddMajorityInfluence
  exact div_pos (by exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)) (by positivity)

/-- The exact recurrence behind Exercise 2.22(b). -/
theorem oddMajorityInfluence_succ (m : ℕ) :
    oddMajorityInfluence (m + 1) =
      ((2 * m + 1 : ℕ) : ℝ) / (2 * m + 2) * oddMajorityInfluence m := by
  unfold oddMajorityInfluence
  have hcentral := Nat.succ_mul_centralBinom_succ m
  simp only [Nat.centralBinom_eq_two_mul_choose] at hcentral
  have hcentralR :
      ((m + 1 : ℕ) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) =
        2 * ((2 * m + 1 : ℕ) : ℝ) * (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast hcentral
  have hpow : (2 : ℝ) ^ (2 * (m + 1)) = 4 * 2 ^ (2 * m) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
    ring
  rw [hpow]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_mul] at hcentralR ⊢
  linear_combination 2 * hcentralR

/-- O'Donnell, Exercise 2.22(b): coordinate influence of odd majority strictly decreases with
the odd arity. -/
theorem oddMajorityInfluence_strictAnti : StrictAnti oddMajorityInfluence := by
  apply strictAnti_nat_of_succ_lt
  intro m
  rw [oddMajorityInfluence_succ]
  have hratio : ((2 * m + 1 : ℕ) : ℝ) / (2 * m + 2) < 1 := by
    rw [div_lt_one]
    · norm_num
    · positivity
  nlinarith [oddMajorityInfluence_pos m]

/-- The leading term in Exercise 2.22(c), written for odd arity `2m+1`. -/
noncomputable def oddMajorityInfluenceMain (m : ℕ) : ℝ :=
  Real.sqrt (2 / (Real.pi * (2 * m + 1 : ℕ)))

/-- The exact factorial identity relating the central-binomial probability to Mathlib's Wallis
product. This is the arithmetic core of the sharp Exercise 2.22 estimates. -/
theorem oddMajorityInfluence_sq_mul_wallis (m : ℕ) :
    oddMajorityInfluence m ^ 2 * ((2 * m + 1 : ℕ) : ℝ) * Real.Wallis.W m = 1 := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold oddMajorityInfluence
  rw [Nat.cast_choose ℝ (by omega : m ≤ 2 * m)]
  rw [show 2 * m - m = m by omega]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hmfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have htwomfac : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  have hpow : (2 ^ (2 * m) : ℝ) ≠ 0 := by positivity
  have hodd : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpowers : (2 : ℝ) ^ (4 * m) = (2 ^ (2 * m)) ^ 2 := by
    rw [show 4 * m = 2 * m + 2 * m by omega, pow_add, pow_two]
  rw [hpowers]
  field_simp
  ring

/-- The square of the main term in Exercise 2.22(c). -/
theorem oddMajorityInfluenceMain_sq (m : ℕ) :
    oddMajorityInfluenceMain m ^ 2 = 2 / (Real.pi * (2 * m + 1 : ℕ)) := by
  unfold oddMajorityInfluenceMain
  rw [Real.sq_sqrt]
  positivity

/-- The Wallis upper bound yields the nonnegative-error half of Exercise 2.22(c). -/
theorem oddMajorityInfluenceMain_le (m : ℕ) :
    oddMajorityInfluenceMain m ≤ oddMajorityInfluence m := by
  have hwallis := Real.Wallis.W_le m
  have hid := oddMajorityInfluence_sq_mul_wallis m
  have hmainNonneg : 0 ≤ oddMajorityInfluenceMain m := by
    exact Real.sqrt_nonneg _
  have hinfNonneg : 0 ≤ oddMajorityInfluence m := (oddMajorityInfluence_pos m).le
  apply (sq_le_sq₀ hmainNonneg hinfNonneg).mp
  rw [oddMajorityInfluenceMain_sq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hodd : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hW : 0 < Real.Wallis.W m := Real.Wallis.W_pos m
  have hsquare : oddMajorityInfluence m ^ 2 =
      1 / (((2 * m + 1 : ℕ) : ℝ) * Real.Wallis.W m) := by
    apply (eq_div_iff (mul_ne_zero hodd.ne' hW.ne')).2
    nlinarith [hid]
  rw [hsquare]
  rw [div_le_div_iff₀ (mul_pos hpi hodd) (mul_pos hodd hW)]
  nlinarith

/-- The Wallis lower bound gives a sharp enough squared upper bound to recover the
`O(n⁻³ᐟ²)` error in Exercise 2.22(c). -/
theorem oddMajorityInfluence_sq_le (m : ℕ) :
    oddMajorityInfluence m ^ 2 ≤
      2 * (((2 * m + 1 : ℕ) : ℝ) + 1) /
        (Real.pi * ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hW : 0 < Real.Wallis.W m := Real.Wallis.W_pos m
  have hpi : 0 < Real.pi := Real.pi_pos
  have hwallis : N / (N + 1) * (Real.pi / 2) ≤ Real.Wallis.W m := by
    dsimp [N]
    push_cast
    rw [show (2 : ℝ) * m + 1 + 1 = 2 * m + 2 by ring]
    exact Real.Wallis.le_W m
  have hcross : N * Real.pi ≤ 2 * (N + 1) * Real.Wallis.W m := by
    calc
      N * Real.pi = (N / (N + 1) * (Real.pi / 2)) * (2 * (N + 1)) := by
        field_simp
      _ ≤ Real.Wallis.W m * (2 * (N + 1)) :=
        mul_le_mul_of_nonneg_right hwallis (by positivity)
      _ = 2 * (N + 1) * Real.Wallis.W m := by ring
  have hsquare : oddMajorityInfluence m ^ 2 = 1 / (N * Real.Wallis.W m) := by
    apply (eq_div_iff (mul_ne_zero hN.ne' hW.ne')).2
    rw [← mul_assoc]
    change oddMajorityInfluence m ^ 2 * ((2 * m + 1 : ℕ) : ℝ) * Real.Wallis.W m = 1
    exact oddMajorityInfluence_sq_mul_wallis m
  rw [hsquare]
  change 1 / (N * Real.Wallis.W m) ≤ 2 * (N + 1) / (Real.pi * N ^ 2)
  rw [div_le_div_iff₀ (mul_pos hN hW) (mul_pos hpi (sq_pos_of_pos hN))]
  calc
    1 * (Real.pi * N ^ 2) = N * (N * Real.pi) := by ring
    _ ≤ N * (2 * (N + 1) * Real.Wallis.W m) :=
      mul_le_mul_of_nonneg_left hcross hN.le
    _ = 2 * (N + 1) * (N * Real.Wallis.W m) := by ring

/-- An explicit one-sided remainder bound for Exercise 2.22(c). -/
theorem oddMajorityInfluence_le_main_add (m : ℕ) :
    oddMajorityInfluence m ≤ oddMajorityInfluenceMain m +
      oddMajorityInfluenceMain m / ((2 * m + 1 : ℕ) : ℝ) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hmain : 0 ≤ oddMajorityInfluenceMain m := Real.sqrt_nonneg _
  have hinf : 0 ≤ oddMajorityInfluence m := (oddMajorityInfluence_pos m).le
  have hright : 0 ≤ oddMajorityInfluenceMain m + oddMajorityInfluenceMain m / N :=
    add_nonneg hmain (div_nonneg hmain hN.le)
  apply (sq_le_sq₀ hinf hright).mp
  calc
    oddMajorityInfluence m ^ 2 ≤ 2 * (N + 1) / (Real.pi * N ^ 2) := by
      exact oddMajorityInfluence_sq_le m
    _ ≤ (oddMajorityInfluenceMain m + oddMajorityInfluenceMain m / N) ^ 2 := by
      rw [show (oddMajorityInfluenceMain m + oddMajorityInfluenceMain m / N) ^ 2 =
          oddMajorityInfluenceMain m ^ 2 * (1 + 1 / N) ^ 2 by ring]
      rw [oddMajorityInfluenceMain_sq]
      change 2 * (N + 1) / (Real.pi * N ^ 2) ≤
        (2 / (Real.pi * N)) * (1 + 1 / N) ^ 2
      field_simp
      nlinarith

/-- The nonnegative remainder in the majority-influence estimate of Exercise 2.22(c). -/
noncomputable def oddMajorityInfluenceError (m : ℕ) : ℝ :=
  oddMajorityInfluence m - oddMajorityInfluenceMain m

/-- Exercise 2.22(c), with an explicit nonnegative error bound. -/
theorem oddMajorityInfluenceError_mem_Icc (m : ℕ) :
    oddMajorityInfluenceError m ∈ Set.Icc 0
      (oddMajorityInfluenceMain m / ((2 * m + 1 : ℕ) : ℝ)) := by
  constructor
  · exact sub_nonneg.mpr (oddMajorityInfluenceMain_le m)
  · exact sub_le_iff_le_add.mpr (by
      simpa [add_comm] using oddMajorityInfluence_le_main_add m)

/-- The book's `n⁻³ᐟ²` scale for odd arity `n = 2m+1`. -/
theorem oddArity_rpow_neg_three_halves (m : ℕ) :
    (((2 * m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) =
      1 / (((2 * m + 1 : ℕ) : ℝ) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) := by
  have hN : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [show -(3 / 2 : ℝ) = -(1 + 1 / 2) by ring]
  rw [Real.rpow_neg hN.le, Real.rpow_add hN, Real.rpow_one, ← Real.sqrt_eq_rpow]
  simp [one_div]

/-- The leading majority-influence term is at most `n⁻¹ᐟ²`. -/
theorem oddMajorityInfluenceMain_le_inv_sqrt (m : ℕ) :
    oddMajorityInfluenceMain m ≤
      1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  change oddMajorityInfluenceMain m ≤ 1 / Real.sqrt N
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (div_nonneg zero_le_one hsqrt.le)).mp
  change Real.sqrt (2 / (Real.pi * N)) ^ 2 ≤ (1 / Real.sqrt N) ^ 2
  rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt hN.le]
  field_simp
  nlinarith [Real.pi_gt_three]

/-- Exercise 2.22(c): the nonnegative error is globally bounded by the exact `n⁻³ᐟ²`
scale. -/
theorem oddMajorityInfluenceError_le_rpow (m : ℕ) :
    oddMajorityInfluenceError m ≤
      (((2 * m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  calc
    oddMajorityInfluenceError m ≤ oddMajorityInfluenceMain m / N :=
      (oddMajorityInfluenceError_mem_Icc m).2
    _ ≤ (1 / Real.sqrt N) / N :=
      div_le_div_of_nonneg_right (oddMajorityInfluenceMain_le_inv_sqrt m) hN.le
    _ = 1 / (N * Real.sqrt N) := by field_simp
    _ = N ^ (-(3 / 2 : ℝ)) := by
      exact (oddArity_rpow_neg_three_halves m).symm

/-- O'Donnell, Exercise 2.22(c), in literal asymptotic notation, including the book's
nonnegative remainder convention. -/
theorem oddMajorityInfluenceError_isBigO :
    oddMajorityInfluenceError =O[atTop]
      fun m : ℕ ↦ (((2 * m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  apply Asymptotics.isBigO_of_le atTop
  intro m
  rw [Real.norm_eq_abs, abs_of_nonneg (oddMajorityInfluenceError_mem_Icc m).1]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  exact oddMajorityInfluenceError_le_rpow m

/-- Exercise 2.22(d): the level-one Fourier weight of odd majority is `n` times the square of
its common coordinate influence. -/
theorem fourierWeightAtLevel_one_majority_odd (m : ℕ) :
    fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal =
      ((2 * m + 1 : ℕ) : ℝ) * oddMajorityInfluence m ^ 2 := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton]
  simp_rw [← influence_eq_fourierCoeff_singleton_of_monotone
    (majority (2 * m + 1)) (majority_monotone _)]
  simp_rw [← booleanInfluence_eq_influence_toReal,
    booleanInfluence_majority_odd_eq_oddMajorityInfluence]
  simp

/-- Exercise 2.22(d), lower bound: `2/π ≤ W¹[Majₙ]` for odd `n`. -/
theorem two_div_pi_le_fourierWeightAtLevel_one_majority_odd (m : ℕ) :
    (2 : ℝ) / Real.pi ≤
      fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal := by
  rw [fourierWeightAtLevel_one_majority_odd]
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  change (2 : ℝ) / Real.pi ≤ N * oddMajorityInfluence m ^ 2
  have hsq : oddMajorityInfluenceMain m ^ 2 ≤ oddMajorityInfluence m ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (oddMajorityInfluence_pos m).le).2
      (oddMajorityInfluenceMain_le m)
  calc
    (2 : ℝ) / Real.pi = N * oddMajorityInfluenceMain m ^ 2 := by
      rw [oddMajorityInfluenceMain_sq]
      change (2 : ℝ) / Real.pi = N * (2 / (Real.pi * N))
      field_simp
    _ ≤ N * oddMajorityInfluence m ^ 2 := mul_le_mul_of_nonneg_left hsq hN.le

/-- Exercise 2.22(d), explicit upper bound with an `O(n⁻¹)` remainder. -/
theorem fourierWeightAtLevel_one_majority_odd_le (m : ℕ) :
    fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal ≤
      (2 : ℝ) / Real.pi +
        2 / (Real.pi * ((2 * m + 1 : ℕ) : ℝ)) := by
  rw [fourierWeightAtLevel_one_majority_odd]
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  change N * oddMajorityInfluence m ^ 2 ≤ 2 / Real.pi + 2 / (Real.pi * N)
  calc
    N * oddMajorityInfluence m ^ 2 ≤
        N * (2 * (N + 1) / (Real.pi * N ^ 2)) :=
      mul_le_mul_of_nonneg_left (oddMajorityInfluence_sq_le m) hN.le
    _ = 2 / Real.pi + 2 / (Real.pi * N) := by field_simp

/-- The nonnegative `O(n⁻¹)` remainder in Exercise 2.22(d). -/
noncomputable def oddMajorityLevelOneWeightError (m : ℕ) : ℝ :=
  fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal - 2 / Real.pi

/-- Exercise 2.22(d), with a global explicit error interval. -/
theorem oddMajorityLevelOneWeightError_mem_Icc (m : ℕ) :
    oddMajorityLevelOneWeightError m ∈ Set.Icc 0
      (2 / (Real.pi * ((2 * m + 1 : ℕ) : ℝ))) := by
  constructor
  · exact sub_nonneg.mpr (two_div_pi_le_fourierWeightAtLevel_one_majority_odd m)
  · exact sub_le_iff_le_add.mpr (by
      simpa [add_comm] using fourierWeightAtLevel_one_majority_odd_le m)

/-- The book's `n⁻¹` scale for odd arity. -/
theorem oddArity_rpow_neg_one (m : ℕ) :
    (((2 * m + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) =
      1 / ((2 * m + 1 : ℕ) : ℝ) := by
  rw [Real.rpow_neg_one]
  simp [one_div]

/-- Exercise 2.22(d), in literal asymptotic notation. -/
theorem oddMajorityLevelOneWeightError_isBigO :
    oddMajorityLevelOneWeightError =O[atTop]
      fun m : ℕ ↦ (((2 * m + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (2 / Real.pi)
  filter_upwards [] with m
  rw [Real.norm_eq_abs, abs_of_nonneg (oddMajorityLevelOneWeightError_mem_Icc m).1]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  calc
    oddMajorityLevelOneWeightError m ≤
        2 / (Real.pi * ((2 * m + 1 : ℕ) : ℝ)) :=
      (oddMajorityLevelOneWeightError_mem_Icc m).2
    _ = (2 / Real.pi) * (((2 * m + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      rw [oddArity_rpow_neg_one]
      field_simp

/-- Exercise 2.22(e): total influence of odd majority is `n` times its common coordinate
influence. -/
theorem totalInfluence_majority_odd_eq_mul_oddMajorityInfluence (m : ℕ) :
    totalInfluence (majority (2 * m + 1)).toReal =
      ((2 * m + 1 : ℕ) : ℝ) * oddMajorityInfluence m := by
  rw [totalInfluence_majority_odd]
  unfold oddMajorityInfluence
  ring

/-- Multiplying the influence main term by the odd arity gives the book's
`sqrt(2/π) sqrt(n)` main term. -/
theorem oddArity_mul_oddMajorityInfluenceMain (m : ℕ) :
    ((2 * m + 1 : ℕ) : ℝ) * oddMajorityInfluenceMain m =
      Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  change N * oddMajorityInfluenceMain m = Real.sqrt (2 / Real.pi) * Real.sqrt N
  apply (sq_eq_sq₀ (mul_nonneg hN (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  change (N * Real.sqrt (2 / (Real.pi * N))) ^ 2 =
    (Real.sqrt (2 / Real.pi) * Real.sqrt N) ^ 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt hN]
  field_simp

/-- The nonnegative remainder in the total-influence estimate of Exercise 2.22(e) and
Example 2.30. -/
noncomputable def oddMajorityTotalInfluenceError (m : ℕ) : ℝ :=
  totalInfluence (majority (2 * m + 1)).toReal -
    Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ)

/-- Exercise 2.22(e), with the explicit global `n⁻¹ᐟ²` error bound. -/
theorem oddMajorityTotalInfluenceError_mem_Icc (m : ℕ) :
    oddMajorityTotalInfluenceError m ∈ Set.Icc 0
      (1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  rw [oddMajorityTotalInfluenceError,
    totalInfluence_majority_odd_eq_mul_oddMajorityInfluence,
    ← oddArity_mul_oddMajorityInfluenceMain]
  change N * oddMajorityInfluence m - N * oddMajorityInfluenceMain m ∈
    Set.Icc 0 (1 / Real.sqrt N)
  constructor
  · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (oddMajorityInfluenceMain_le m) hN.le)
  · calc
      N * oddMajorityInfluence m - N * oddMajorityInfluenceMain m =
          N * oddMajorityInfluenceError m := by
        simp [oddMajorityInfluenceError]
        ring
      _ ≤ N * (oddMajorityInfluenceMain m / N) :=
        mul_le_mul_of_nonneg_left (oddMajorityInfluenceError_mem_Icc m).2 hN.le
      _ = oddMajorityInfluenceMain m := by field_simp
      _ ≤ 1 / Real.sqrt N := oddMajorityInfluenceMain_le_inv_sqrt m

/-- The book's `n⁻¹ᐟ²` scale for odd arity. -/
theorem oddArity_rpow_neg_one_half (m : ℕ) :
    (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
  have hN : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  rw [Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
  simp [one_div]

/-- O'Donnell, Exercise 2.22(e) and Example 2.30, in literal asymptotic notation. -/
theorem oddMajorityTotalInfluenceError_isBigO :
    oddMajorityTotalInfluenceError =O[atTop]
      fun m : ℕ ↦ (((2 * m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  apply Asymptotics.isBigO_of_le atTop
  intro m
  rw [Real.norm_eq_abs, abs_of_nonneg (oddMajorityTotalInfluenceError_mem_Icc m).1]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  rw [oddArity_rpow_neg_one_half]
  exact (oddMajorityTotalInfluenceError_mem_Icc m).2

/-- Example 2.30's complete odd-majority estimate, with its exact nonnegative remainder. -/
theorem totalInfluence_majority_odd_eq_main_add_error (m : ℕ) :
    totalInfluence (majority (2 * m + 1)).toReal =
      Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ) +
        oddMajorityTotalInfluenceError m := by
  simp [oddMajorityTotalInfluenceError]


end FABL
