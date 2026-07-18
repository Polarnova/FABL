/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.MajorityOptimality

/-!
# Even majority

Book items: Theorem 2.33, Exercise 2.22.

Exact and asymptotic total-influence formulas for even majority from Section 2.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Exercise 2.22(f): every majority function on `2m+2` voters has the same total
influence as odd majority on `2m+1` voters. This includes arbitrary tie-breaking. -/
theorem totalInfluence_evenMajority_eq_oddMajority
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) (hf : IsMajorityFunction f) :
    totalInfluence f.toReal = totalInfluence (majority (2 * m + 1)).toReal := by
  calc
    totalInfluence f.toReal = totalInfluence (majority (2 * m + 2)).toReal :=
      totalInfluence_eq_majority_of_isMajorityFunction f hf
    _ = totalInfluence (liftedOddMajority m).toReal :=
      (totalInfluence_eq_majority_of_isMajorityFunction
        (liftedOddMajority m) (liftedOddMajority_isMajorityFunction m)).symm
    _ = totalInfluence (majority (2 * m + 1)).toReal :=
      totalInfluence_liftedOddMajority m

/-- Exercise 2.22(f), expanded using the exact odd-majority central-binomial formula. -/
theorem totalInfluence_evenMajority_exact
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) (hf : IsMajorityFunction f) :
    totalInfluence f.toReal =
      ((2 * m + 1 : ℕ) : ℝ) * (Nat.choose (2 * m) m : ℝ) /
        (2 ^ (2 * m) : ℝ) := by
  rw [totalInfluence_evenMajority_eq_oddMajority m f hf,
    totalInfluence_majority_odd]

/-- Exercise 2.22(f), in the complete odd-main-term plus error form. -/
theorem totalInfluence_evenMajority_eq_odd_main_add_error
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) (hf : IsMajorityFunction f) :
    totalInfluence f.toReal =
      Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ) +
        oddMajorityTotalInfluenceError m := by
  rw [totalInfluence_evenMajority_eq_oddMajority m f hf,
    totalInfluence_majority_odd_eq_main_add_error]

/-- Exercise 2.22(f), stated for an arbitrary positive even arity `n`. -/
theorem totalInfluence_evenMajority_eq_predecessor
    {n : ℕ} (hn : Even n) (hnpos : 0 < n)
    (f : BooleanFunction n) (hf : IsMajorityFunction f) :
    totalInfluence f.toReal = totalInfluence (majority (n - 1)).toReal := by
  rcases even_iff_exists_two_mul.mp hn with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  convert totalInfluence_evenMajority_eq_oddMajority m f hf using 1
  congr 3

/-- The signed remainder when an even-arity majority function is expanded using `sqrt(n)` rather
than `sqrt(n-1)`. -/
noncomputable def evenMajorityTotalInfluenceError
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) : ℝ :=
  totalInfluence f.toReal -
    Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 2 : ℕ) : ℝ)

/-- Exercise 2.22(f): the signed even-arity remainder is bounded by `4 n⁻¹ᐟ²`. -/
theorem abs_evenMajorityTotalInfluenceError_le
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) (hf : IsMajorityFunction f) :
    |evenMajorityTotalInfluenceError m f| ≤
      4 / Real.sqrt ((2 * m + 2 : ℕ) : ℝ) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  let M : ℝ := ((2 * m + 2 : ℕ) : ℝ)
  let c : ℝ := Real.sqrt (2 / Real.pi)
  let e : ℝ := oddMajorityTotalInfluenceError m
  have hN : 0 < N := by dsimp [N]; positivity
  have hNone : 1 ≤ N := by dsimp [N]; norm_num
  have hM : 0 < M := by dsimp [M]; positivity
  have hMN : M = N + 1 := by
    dsimp [M, N]
    norm_num
    ring
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [Real.sqrt_le_one, div_le_one Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have he0 : 0 ≤ e := (oddMajorityTotalInfluenceError_mem_Icc m).1
  have he : e ≤ 1 / Real.sqrt N := (oddMajorityTotalInfluenceError_mem_Icc m).2
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hsqrt : Real.sqrt N ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (by rw [hMN]; linarith)
  let d := Real.sqrt M - Real.sqrt N
  have hd0 : 0 ≤ d := sub_nonneg.mpr hsqrt
  have hd : d ≤ 1 / Real.sqrt N := by
    have hid : d = 1 / (Real.sqrt M + Real.sqrt N) := by
      apply (eq_div_iff (by positivity : Real.sqrt M + Real.sqrt N ≠ 0)).2
      calc
        d * (Real.sqrt M + Real.sqrt N) = Real.sqrt M ^ 2 - Real.sqrt N ^ 2 := by
          dsimp [d]
          ring
        _ = M - N := by rw [Real.sq_sqrt hM.le, Real.sq_sqrt hN.le]
        _ = 1 := by rw [hMN]; ring
    rw [hid]
    exact one_div_le_one_div_of_le hsN (by linarith [Real.sqrt_nonneg M])
  have hcd : c * d ≤ 1 / Real.sqrt N :=
    (mul_le_of_le_one_left hd0 hc1).trans hd
  rw [evenMajorityTotalInfluenceError,
    totalInfluence_evenMajority_eq_odd_main_add_error m f hf]
  change |c * Real.sqrt N + e - c * Real.sqrt M| ≤ 4 / Real.sqrt M
  have herr : |c * Real.sqrt N + e - c * Real.sqrt M| ≤ 2 / Real.sqrt N := by
    have heq : c * Real.sqrt N + e - c * Real.sqrt M = e - c * d := by
      dsimp [d]
      ring
    rw [heq]
    calc
      |e - c * d| ≤ |e| + |c * d| := abs_sub _ _
      _ = e + c * d := by
        rw [abs_of_nonneg he0, abs_of_nonneg (mul_nonneg hc0 hd0)]
      _ ≤ 1 / Real.sqrt N + 1 / Real.sqrt N := add_le_add he hcd
      _ = 2 / Real.sqrt N := by ring
  apply herr.trans
  have hsqrtBound : Real.sqrt M ≤ 2 * Real.sqrt N := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt hM.le, mul_pow, Real.sq_sqrt hN.le]
    rw [hMN]
    nlinarith
  rw [div_le_div_iff₀ hsN hsM]
  nlinarith

/-- Exercise 2.22(f), with the even-arity signed remainder displayed explicitly. -/
theorem totalInfluence_evenMajority_eq_main_add_error
    (m : ℕ) (f : BooleanFunction (2 * m + 2)) :
    totalInfluence f.toReal =
      Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 2 : ℕ) : ℝ) +
        evenMajorityTotalInfluenceError m f := by
  simp [evenMajorityTotalInfluenceError]

/-- The book's `n⁻¹ᐟ²` scale for even arity `n = 2m+2`. -/
theorem evenArity_rpow_neg_one_half (m : ℕ) :
    (((2 * m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
      1 / Real.sqrt ((2 * m + 2 : ℕ) : ℝ) := by
  have hN : 0 < ((2 * m + 2 : ℕ) : ℝ) := by positivity
  rw [Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
  simp [one_div]

/-- O'Donnell, Exercise 2.22(f), in literal `O(n⁻¹ᐟ²)` notation for any family of
even-arity majority functions. -/
theorem evenMajorityTotalInfluenceError_isBigO
    (f : ∀ m : ℕ, BooleanFunction (2 * m + 2))
    (hf : ∀ m, IsMajorityFunction (f m)) :
    (fun m ↦ evenMajorityTotalInfluenceError m (f m)) =O[atTop]
      fun m : ℕ ↦ (((2 * m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [] with m
  rw [Real.norm_eq_abs]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  rw [evenArity_rpow_neg_one_half]
  simpa [div_eq_mul_inv] using abs_evenMajorityTotalInfluenceError_le m (f m) (hf m)

/-- Theorem 2.33 with the complete Exercise 2.22(e) asymptotic bound substituted. -/
theorem totalInfluence_toReal_le_majority_main_add_error_of_monotone
    (m : ℕ) (f : BooleanFunction (2 * m + 1)) (hf : Monotone f) :
    totalInfluence f.toReal ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt ((2 * m + 1 : ℕ) : ℝ) +
        oddMajorityTotalInfluenceError m := by
  rw [← totalInfluence_majority_odd_eq_main_add_error]
  exact totalInfluence_toReal_le_majority_of_monotone f hf


end FABL
