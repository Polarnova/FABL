/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence

/-!
# Equal singleton coefficients

Book items: Proposition 2.58, Exercise 2.24.

The sharp level-one estimate used in Section 2.5 of O'Donnell's
*Analysis of Boolean Functions*.  The proof combines Theorem 2.33 with the explicit majority
estimates from Exercise 2.22.
-/

open Finset Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- All singleton Fourier coefficients of a Boolean function are equal. -/
def HasEqualSingletonFourierCoefficients (f : BooleanFunction n) : Prop :=
  ∀ i j : Fin n, fourierCoeff f.toReal {i} = fourierCoeff f.toReal {j}

/-- Negating a Boolean function negates the sum of its singleton Fourier coefficients. -/
theorem sum_fourierCoeff_singleton_neg (f : BooleanFunction n) :
    (∑ i, fourierCoeff (-f : BooleanFunction n).toReal {i}) =
      -(∑ i, fourierCoeff f.toReal {i}) := by
  rw [sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue,
    sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue,
    BooleanFunction.toReal_neg]
  rw [show (fun x : {−1,1}^[n] ↦
      (-f.toReal) x * ∑ i, signValue (x i)) =
      -(fun x ↦ f.toReal x * ∑ i, signValue (x i)) by
    funext x
    simp]
  exact Finset.expect_neg_distrib
    (Finset.univ : Finset ({−1,1}^[n]))
    (fun x ↦ f.toReal x * ∑ i, signValue (x i))

/-- The absolute singleton-coefficient sum of any Boolean function is at most majority's
singleton-coefficient sum. -/
theorem abs_sum_fourierCoeff_singleton_le_majority (f : BooleanFunction n) :
    |∑ i, fourierCoeff f.toReal {i}| ≤
      ∑ i, fourierCoeff (majority n).toReal {i} := by
  have hupper := sum_fourierCoeff_singleton_le_majority f
  have hlower := sum_fourierCoeff_singleton_le_majority (-f)
  rw [sum_fourierCoeff_singleton_neg] at hlower
  rw [abs_le]
  constructor
  · linarith
  · exact hupper

/-- If all singleton coefficients are equal, level-one weight is bounded by majority's squared
total influence divided by the arity. -/
theorem fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div
    (f : BooleanFunction n) (hf : HasEqualSingletonFourierCoefficients f)
    (hn : 0 < n) :
    fourierWeightAtLevel 1 f.toReal ≤
      totalInfluence (majority n).toReal ^ 2 / (n : ℝ) := by
  let i : Fin n := ⟨0, hn⟩
  let a := fourierCoeff f.toReal {i}
  let M := totalInfluence (majority n).toReal
  have hcast : 0 < (n : ℝ) := by exact_mod_cast hn
  have hweight : fourierWeightAtLevel 1 f.toReal = (n : ℝ) * a ^ 2 := by
    rw [fourierWeightAtLevel_one_eq_sum_singleton]
    simp_rw [hf _ i]
    simp [a]
  have hsum : (∑ j, fourierCoeff f.toReal {j}) = (n : ℝ) * a := by
    simp_rw [hf _ i]
    simp [a]
  have hmajoritySum :
      (∑ j, fourierCoeff (majority n).toReal {j}) = M := by
    exact (totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone
      (majority n) (majority_monotone n)).symm
  have habs : |(n : ℝ) * a| ≤ M := by
    rw [← hsum, ← hmajoritySum]
    exact abs_sum_fourierCoeff_singleton_le_majority f
  have hM : 0 ≤ M := by
    dsimp [M]
    exact totalInfluence_nonneg _
  have hsquare : ((n : ℝ) * a) ^ 2 ≤ M ^ 2 := by
    calc
      ((n : ℝ) * a) ^ 2 = |(n : ℝ) * a| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := (sq_le_sq₀ (abs_nonneg ((n : ℝ) * a)) hM).2 habs
  rw [hweight]
  apply (le_div_iff₀ hcast).2
  calc
    ((n : ℝ) * a ^ 2) * (n : ℝ) = ((n : ℝ) * a) ^ 2 := by ring
    _ ≤ M ^ 2 := hsquare

/-- The squared total influence of odd majority, divided by its arity, is its level-one Fourier
weight. -/
theorem totalInfluence_majority_odd_sq_div_card (m : ℕ) :
    totalInfluence (majority (2 * m + 1)).toReal ^ 2 /
        ((2 * m + 1 : ℕ) : ℝ) =
      fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal := by
  rw [totalInfluence_majority_odd_eq_mul_oddMajorityInfluence,
    fourierWeightAtLevel_one_majority_odd]
  have hcard : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-- The majority quotient needed for Exercise 2.24 has the uniform explicit `O(1/n)` bound
`2/π + 3/n`. -/
theorem totalInfluence_majority_sq_div_card_le
    (n : ℕ) (hn : 0 < n) :
    totalInfluence (majority n).toReal ^ 2 / (n : ℝ) ≤
      2 / Real.pi + 3 / (n : ℝ) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases even_iff_exists_two_mul.mp heven with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    let M : ℝ := ((2 * m + 1 : ℕ) : ℝ)
    let N : ℝ := ((2 * m + 2 : ℕ) : ℝ)
    let c : ℝ := Real.sqrt (2 / Real.pi)
    let e : ℝ := oddMajorityTotalInfluenceError m
    have hM : 0 < M := by dsimp [M]; positivity
    have hMone : 1 ≤ M := by dsimp [M]; norm_num
    have hN : 0 < N := by dsimp [N]; positivity
    have hMN : N = M + 1 := by
      dsimp [M, N]
      norm_num
      ring
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hc1 : c ≤ 1 := by
      dsimp [c]
      rw [Real.sqrt_le_one, div_le_one Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have hcsq : c ^ 2 = 2 / Real.pi := by
      dsimp [c]
      rw [Real.sq_sqrt]
      positivity
    have he0 : 0 ≤ e := (oddMajorityTotalInfluenceError_mem_Icc m).1
    have he : e ≤ 1 / Real.sqrt M := by
      simpa [e, M] using (oddMajorityTotalInfluenceError_mem_Icc m).2
    have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
    have hsqrtOne : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hMone
    have hsqrtSq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM.le
    have hsqrtMulError : Real.sqrt M * e ≤ 1 := by
      calc
        Real.sqrt M * e ≤ Real.sqrt M * (1 / Real.sqrt M) :=
          mul_le_mul_of_nonneg_left he hsqrt.le
        _ = 1 := by field_simp
    have he1 : e ≤ 1 := by
      exact he.trans ((div_le_one hsqrt).2 hsqrtOne)
    have heSq : e ^ 2 ≤ 1 := by nlinarith [sq_nonneg e, sq_nonneg (1 - e)]
    have hcross : c * Real.sqrt M * e ≤ 1 := by
      calc
        c * Real.sqrt M * e = c * (Real.sqrt M * e) := by ring
        _ ≤ 1 * (Real.sqrt M * e) :=
          mul_le_mul_of_nonneg_right hc1 (mul_nonneg hsqrt.le he0)
        _ ≤ 1 := by simpa using hsqrtMulError
    change totalInfluence (majority (2 * m + 2)).toReal ^ 2 / N ≤
      2 / Real.pi + 3 / N
    rw [totalInfluence_evenMajority_eq_odd_main_add_error
      m (majority (2 * m + 2)) (majority_isMajorityFunction _)]
    change (c * Real.sqrt M + e) ^ 2 / N ≤ 2 / Real.pi + 3 / N
    rw [← hcsq]
    apply (div_le_iff₀ hN).2
    have hright : (c ^ 2 + 3 / N) * N = c ^ 2 * N + 3 := by
      field_simp
    rw [hright]
    nlinarith [sq_nonneg c]
  · obtain ⟨m, rfl⟩ := hodd.exists_bit1
    rw [totalInfluence_majority_odd_sq_div_card]
    calc
      fourierWeightAtLevel 1 (majority (2 * m + 1)).toReal ≤
          2 / Real.pi + 2 / (Real.pi * ((2 * m + 1 : ℕ) : ℝ)) :=
        fourierWeightAtLevel_one_majority_odd_le m
      _ ≤ 2 / Real.pi + 3 / ((2 * m + 1 : ℕ) : ℝ) := by
        have hpi : 0 < Real.pi := Real.pi_pos
        have hcard : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
        rw [add_le_add_iff_left]
        rw [div_le_div_iff₀ (mul_pos hpi hcard) hcard]
        nlinarith [Real.pi_gt_three]

/-- O'Donnell, Exercise 2.24: equal singleton coefficients imply the explicit strengthened
bound `W¹[f] ≤ 2/π + 3/n`. -/
theorem fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card
    (f : BooleanFunction n) (hf : HasEqualSingletonFourierCoefficients f)
    (hn : 0 < n) :
    fourierWeightAtLevel 1 f.toReal ≤ 2 / Real.pi + 3 / (n : ℝ) :=
  (fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div f hf hn).trans
    (totalInfluence_majority_sq_div_card_le n hn)

/-- The explicit `3/n` remainder in Exercise 2.24 is little-oh of one. -/
theorem three_div_nat_isLittleO_one :
    (fun n : ℕ ↦ (3 : ℝ) / n) =o[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff ℝ]
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using hinv.const_mul 3

/-- O'Donnell, Proposition 2.58 in literal `2/π + o_n(1)` form for a family of Boolean
functions with equal singleton coefficients. -/
theorem exists_levelOneWeight_upperError_isLittleO
    (f : (n : ℕ) → BooleanFunction n)
    (hf : ∀ n, HasEqualSingletonFourierCoefficients (f n)) :
    ∃ r : ℕ → ℝ,
      r =o[atTop] (fun _n : ℕ ↦ (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          fourierWeightAtLevel 1 (f n).toReal ≤ 2 / Real.pi + r n := by
  refine ⟨fun n ↦ 3 / (n : ℝ), three_div_nat_isLittleO_one, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card
    (f n) (hf n) hn

/-- The epsilon-eventual formulation of Proposition 2.58. -/
theorem fourierWeightAtLevel_one_eventually_le_two_div_pi_add
    (f : (n : ℕ) → BooleanFunction n)
    (hf : ∀ n, HasEqualSingletonFourierCoefficients (f n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      fourierWeightAtLevel 1 (f n).toReal ≤ 2 / Real.pi + ε := by
  have htendsto : Tendsto (fun n : ℕ ↦ (3 : ℝ) / n) atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp three_div_nat_isLittleO_one
  filter_upwards [eventually_ge_atTop 1, htendsto.eventually (Iio_mem_nhds hε)] with n hn herr
  have hbound := fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card
    (f n) (hf n) hn
  linarith

end FABL
