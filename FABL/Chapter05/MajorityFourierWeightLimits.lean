/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LimitingMajorityWeights
public import FABL.Chapter05.MajorityWeightMonotonicity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Topology.Order.Basic

/-!
# Limits of fixed-level majority Fourier weights

Book item: Theorem 5.22.
-/

open Filter
open scoped BooleanCube Topology

@[expose] public section

namespace FABL

/-- The factorial identity in the proof of Theorem 5.22. -/
private theorem majority_binomial_factorization
    (m j : ℕ) (hj : j ≤ m) :
    ((Nat.choose m j : ℝ) ^ 2 * (Nat.choose (2 * m) m : ℝ)) /
        (Nat.choose (2 * m) (2 * j) : ℝ) =
      (Nat.choose (2 * j) j : ℝ) *
        (Nat.choose (2 * (m - j)) (m - j) : ℝ) := by
  rw [Nat.cast_choose ℝ hj,
    Nat.cast_choose ℝ (by omega : m ≤ 2 * m),
    Nat.cast_choose ℝ (by omega : 2 * j ≤ 2 * m),
    Nat.cast_choose ℝ (by omega : j ≤ 2 * j),
    Nat.cast_choose ℝ (by omega : m - j ≤ 2 * (m - j))]
  rw [show 2 * m - m = m by omega,
    show 2 * m - 2 * j = 2 * (m - j) by omega,
    show 2 * j - j = j by omega,
    show 2 * (m - j) - (m - j) = m - j by omega]
  have hmfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hsubfac : ((m - j).factorial : ℝ) ≠ 0 := by positivity
  have htwomfac : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  have htwojfac : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have htwosubfac : ((2 * (m - j)).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hmfac, hjfac, hsubfac, htwomfac, htwojfac, htwosubfac]

/-- Every positive odd limiting majority weight is strictly positive. -/
theorem limitingMajorityFourierWeight_pos_of_odd
    {k : ℕ} (hk : Odd k) :
    0 < limitingMajorityFourierWeight k := by
  rcases hk with ⟨j, rfl⟩
  rw [limitingMajorityFourierWeight_eq, if_pos ⟨j, rfl⟩]
  have hkPred : 2 * j + 1 - 1 = 2 * j := by omega
  have hkHalf : 2 * j / 2 = j := by omega
  rw [hkPred, hkHalf]
  have hchoose : 0 < (Nat.choose (2 * j) j : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  positivity

/-- The exact central-binomial factorization used in Theorem 5.22. -/
theorem fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul
    (m j : ℕ) (hj : j ≤ m) :
    fourierWeightAtLevel (2 * j + 1) (majority (2 * m + 1)).toReal =
      limitingMajorityFourierWeight (2 * j + 1) *
        ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) := by
  classical
  have hlevel : 2 * j + 1 ≤ 2 * m + 1 := by omega
  obtain ⟨S, _, hS⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (n := 2 * j + 1)
        (by simpa using hlevel)
  rw [fourierWeightAtLevel_majority_eq_choose_mul
    (2 * m + 1) (2 * j + 1) S hS]
  unfold fourierWeight
  rw [fourierCoeff_majority_two_mul_add_one m j S hS]
  have hinfluence :
      (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) =
        oddMajorityInfluence m := by
    unfold oddMajorityInfluence
    ring
  have hcoeffScale :
      (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) /
          (Nat.choose (2 * m) (2 * j) : ℝ) *
          (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) =
        (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) /
          (Nat.choose (2 * m) (2 * j) : ℝ) *
          oddMajorityInfluence m := by
    rw [mul_assoc, hinfluence]
  rw [hcoeffScale]
  have hchooseEvenPos : 0 < (Nat.choose (2 * m) (2 * j) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hchooseEvenNe : (Nat.choose (2 * m) (2 * j) : ℝ) ≠ 0 :=
    ne_of_gt hchooseEvenPos
  have hkPos : 0 < (((2 * j + 1 : ℕ) : ℝ)) := by positivity
  have hkNe : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hkPos
  have hsign : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  have hchooseSuccNat :=
    Nat.add_one_mul_choose_eq (2 * m) (2 * j)
  have hchooseSucc :
      (((2 * m + 1 : ℕ) : ℝ)) *
          (Nat.choose (2 * m) (2 * j) : ℝ) =
        (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) *
          (((2 * j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hchooseSuccNat
  have hchooseRatio :
      (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) /
          (Nat.choose (2 * m) (2 * j) : ℝ) =
        (((2 * m + 1 : ℕ) : ℝ)) / (((2 * j + 1 : ℕ) : ℝ)) := by
    apply (div_eq_div_iff hchooseEvenNe hkNe).2
    simpa [mul_comm] using hchooseSucc.symm
  have hbinomial := majority_binomial_factorization m j hj
  have hpow :
      (2 : ℝ) ^ (2 * j) * (2 : ℝ) ^ (2 * (m - j)) =
        (2 : ℝ) ^ (2 * m) := by
    rw [← pow_add]
    congr 1
    omega
  have hcentralFactor :
      (((Nat.choose m j : ℝ) ^ 2 /
          (Nat.choose (2 * m) (2 * j) : ℝ)) *
        oddMajorityInfluence m) =
      ((Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j)) *
        oddMajorityInfluence (m - j) := by
    unfold oddMajorityInfluence
    calc
      ((Nat.choose m j : ℝ) ^ 2 /
            (Nat.choose (2 * m) (2 * j) : ℝ)) *
          ((Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m)) =
          (((Nat.choose m j : ℝ) ^ 2 *
              (Nat.choose (2 * m) m : ℝ)) /
            (Nat.choose (2 * m) (2 * j) : ℝ)) /
              (2 : ℝ) ^ (2 * m) := by ring
      _ = ((Nat.choose (2 * j) j : ℝ) *
            (Nat.choose (2 * (m - j)) (m - j) : ℝ)) /
              (2 : ℝ) ^ (2 * m) := by rw [hbinomial]
      _ = ((Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j)) *
          ((Nat.choose (2 * (m - j)) (m - j) : ℝ) /
            (2 : ℝ) ^ (2 * (m - j))) := by
        rw [← hpow]
        field_simp
  calc
    (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) *
        (((-1 : ℝ) ^ j * (Nat.choose m j : ℝ) /
          (Nat.choose (2 * m) (2 * j) : ℝ) *
          oddMajorityInfluence m) ^ 2) =
      ((Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) /
          (Nat.choose (2 * m) (2 * j) : ℝ)) *
        (((Nat.choose m j : ℝ) ^ 2 /
          (Nat.choose (2 * m) (2 * j) : ℝ)) *
          oddMajorityInfluence m) * oddMajorityInfluence m := by
      field_simp [hchooseEvenNe]
      rw [hsign]
      ring
    _ = ((((2 * m + 1 : ℕ) : ℝ)) / (((2 * j + 1 : ℕ) : ℝ))) *
        (((Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j)) *
          oddMajorityInfluence (m - j)) * oddMajorityInfluence m := by
      rw [hchooseRatio, hcentralFactor]
    _ = limitingMajorityFourierWeight (2 * j + 1) *
        ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) := by
      rw [limitingMajorityFourierWeight_eq, if_pos ⟨j, rfl⟩]
      have hkPred : 2 * j + 1 - 1 = 2 * j := by omega
      have hkHalf : 2 * j / 2 = j := by omega
      rw [hkPred, hkHalf, pow_succ]
      field_simp [Real.pi_ne_zero, hkNe]
      ring

/-- The lower Wallis estimate makes the finite-dimensional correction factor at least one. -/
private theorem one_le_majorityFourierWeightLimitFactor
    (m j : ℕ) (hj : j ≤ m) :
    1 ≤ (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
      oddMajorityInfluence (m - j) * oddMajorityInfluence m := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  let M : ℝ := ((2 * (m - j) + 1 : ℕ) : ℝ)
  let G : ℝ := (Real.pi / 2) * N *
    oddMajorityInfluenceMain (m - j) * oddMajorityInfluenceMain m
  have hNPos : 0 < N := by dsimp [N]; positivity
  have hMPos : 0 < M := by dsimp [M]; positivity
  have hMLeN : M ≤ N := by
    dsimp [M, N]
    exact_mod_cast (by omega : 2 * (m - j) + 1 ≤ 2 * m + 1)
  have hGNonneg : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) hNPos.le)
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hGSq : G ^ 2 = N / M := by
    calc
      G ^ 2 = (Real.pi / 2) ^ 2 * N ^ 2 *
          oddMajorityInfluenceMain (m - j) ^ 2 *
          oddMajorityInfluenceMain m ^ 2 := by
        dsimp [G]
        ring
      _ = N / M := by
        rw [oddMajorityInfluenceMain_sq, oddMajorityInfluenceMain_sq]
        dsimp [M, N]
        field_simp [Real.pi_ne_zero]
  have hOneLeG : 1 ≤ G := by
    apply (sq_le_sq₀ zero_le_one hGNonneg).mp
    rw [one_pow, hGSq]
    exact (le_div_iff₀ hMPos).2 (by simpa using hMLeN)
  have hMainProduct :
      oddMajorityInfluenceMain (m - j) * oddMajorityInfluenceMain m ≤
        oddMajorityInfluence (m - j) * oddMajorityInfluence m :=
    mul_le_mul (oddMajorityInfluenceMain_le (m - j))
      (oddMajorityInfluenceMain_le m)
      (Real.sqrt_nonneg _) (oddMajorityInfluence_pos (m - j)).le
  calc
    1 ≤ G := hOneLeG
    _ ≤ (Real.pi / 2) * N *
        oddMajorityInfluence (m - j) * oddMajorityInfluence m := by
      dsimp [G]
      calc
        (Real.pi / 2) * N *
            oddMajorityInfluenceMain (m - j) * oddMajorityInfluenceMain m =
          ((Real.pi / 2) * N) *
            (oddMajorityInfluenceMain (m - j) *
              oddMajorityInfluenceMain m) := by ring
        _ ≤ ((Real.pi / 2) * N) *
            (oddMajorityInfluence (m - j) * oddMajorityInfluence m) :=
          mul_le_mul_of_nonneg_left hMainProduct (by positivity)
        _ = (Real.pi / 2) * N *
            oddMajorityInfluence (m - j) * oddMajorityInfluence m := by ring
    _ = (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
        oddMajorityInfluence (m - j) * oddMajorityInfluence m := by
      rfl

/-- The upper Wallis estimate at an even central-binomial scale. -/
private theorem oddMajorityInfluence_sq_le_even
    (m : ℕ) (hm : 0 < m) :
    oddMajorityInfluence m ^ 2 ≤
      2 / (Real.pi * ((2 * m : ℕ) : ℝ)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have heven : 0 < (((2 * m : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 2 * m)
  calc
    oddMajorityInfluence m ^ 2 ≤
        2 * (((2 * m + 1 : ℕ) : ℝ) + 1) /
          (Real.pi * ((2 * m + 1 : ℕ) : ℝ) ^ 2) :=
      oddMajorityInfluence_sq_le m
    _ ≤ 2 / (Real.pi * ((2 * m : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (mul_pos hpi heven)]
      push_cast
      nlinarith

/-- The central-binomial correction factor is bounded by the square-root expression in the
proof of Theorem 5.22. -/
private theorem majorityFourierWeightLimitFactor_le_rpow
    (m j : ℕ) (hj : j < m) :
    (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
        oddMajorityInfluence (m - j) * oddMajorityInfluence m ≤
      ((1 : ℝ) - (((2 * j + 1 + 1 : ℕ) : ℝ)) /
          (((2 * m + 1 : ℕ) : ℝ)) +
        (((2 * j + 1 : ℕ) : ℝ)) /
          (((2 * m + 1 : ℕ) : ℝ)) ^ 2) ^ (-(1 / 2 : ℝ)) := by
  let N : ℝ := ((2 * m + 1 : ℕ) : ℝ)
  let A : ℝ :=
    1 - (((2 * j + 1 + 1 : ℕ) : ℝ)) / N +
      (((2 * j + 1 : ℕ) : ℝ)) / N ^ 2
  have hjle : j ≤ m := hj.le
  have hsubPos : 0 < m - j := Nat.sub_pos_of_lt hj
  have hmPos : 0 < m := lt_of_le_of_lt (Nat.zero_le j) hj
  have hAForm :
      A = (((2 * (m - j) : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ)) / N ^ 2 := by
    dsimp [A, N]
    push_cast [Nat.cast_sub hjle]
    field_simp
    ring
  have hAPos : 0 < A := by
    rw [hAForm]
    positivity
  have hSubSq :=
    oddMajorityInfluence_sq_le_even (m - j) hsubPos
  have hMSq := oddMajorityInfluence_sq_le_even m hmPos
  have hProductSq :
      oddMajorityInfluence (m - j) ^ 2 * oddMajorityInfluence m ^ 2 ≤
        (2 / (Real.pi * ((2 * (m - j) : ℕ) : ℝ))) *
          (2 / (Real.pi * ((2 * m : ℕ) : ℝ))) :=
    mul_le_mul hSubSq hMSq (sq_nonneg _) (by positivity)
  have hFactorNonneg :
      0 ≤ (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
        oddMajorityInfluence (m - j) * oddMajorityInfluence m := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (by positivity))
        (oddMajorityInfluence_pos (m - j)).le)
      (oddMajorityInfluence_pos m).le
  have hFactorSq :
      ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) ^ 2 ≤
        1 / A := by
    calc
      ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) ^ 2 =
        ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ)) ^ 2 *
          (oddMajorityInfluence (m - j) ^ 2 *
            oddMajorityInfluence m ^ 2) := by ring
      _ ≤ ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ)) ^ 2 *
          ((2 / (Real.pi * ((2 * (m - j) : ℕ) : ℝ))) *
            (2 / (Real.pi * ((2 * m : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hProductSq (sq_nonneg _)
      _ = 1 / A := by
        rw [hAForm]
        dsimp [N]
        field_simp [Real.pi_ne_zero]
  have hRpowSq :
      (A ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / A := by
    have hRpow :
        A ^ (-(1 / 2 : ℝ)) = (Real.sqrt A)⁻¹ := by
      rw [Real.rpow_neg hAPos.le, ← Real.sqrt_eq_rpow]
    rw [hRpow, inv_pow, Real.sq_sqrt hAPos.le]
    simp [one_div]
  change
    (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
        oddMajorityInfluence (m - j) * oddMajorityInfluence m ≤
      A ^ (-(1 / 2 : ℝ))
  apply (sq_le_sq₀ hFactorNonneg (Real.rpow_nonneg hAPos.le _)).mp
  rw [hRpowSq]
  exact hFactorSq

/-- Theorem 5.22, lower half of (5.15). -/
theorem limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hkn : k ≤ n) :
    limitingMajorityFourierWeight k ≤
      fourierWeightAtLevel k (majority n).toReal := by
  rcases hn with ⟨m, rfl⟩
  rcases hk with ⟨j, rfl⟩
  have hjm : j ≤ m := by omega
  rw [fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul m j hjm]
  have hlimitNonneg :
      0 ≤ limitingMajorityFourierWeight (2 * j + 1) :=
    (limitingMajorityFourierWeight_pos_of_odd ⟨j, rfl⟩).le
  calc
    limitingMajorityFourierWeight (2 * j + 1) =
        limitingMajorityFourierWeight (2 * j + 1) * 1 := by ring
    _ ≤ limitingMajorityFourierWeight (2 * j + 1) *
        ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) :=
      mul_le_mul_of_nonneg_left
        (one_le_majorityFourierWeightLimitFactor m j hjm) hlimitNonneg

/-- Theorem 5.22, upper half of (5.15). -/
theorem fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hkn : 2 * k < n) :
    fourierWeightAtLevel k (majority n).toReal ≤
      (1 + 2 * (k : ℝ) / (n : ℝ)) *
        limitingMajorityFourierWeight k := by
  rcases hn with ⟨m, rfl⟩
  rcases hk with ⟨j, rfl⟩
  have hjm : j < m := by omega
  have hhalf : 2 * (2 * j + 1) ≤ 2 * m + 1 := by omega
  rw [fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul m j hjm.le]
  have hlimitNonneg :
      0 ≤ limitingMajorityFourierWeight (2 * j + 1) :=
    (limitingMajorityFourierWeight_pos_of_odd ⟨j, rfl⟩).le
  have hfactor :
      (Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m ≤
        1 + 2 * (((2 * j + 1 : ℕ) : ℝ)) /
          (((2 * m + 1 : ℕ) : ℝ)) := by
    exact (majorityFourierWeightLimitFactor_le_rpow m j hjm).trans
      (exercise5_24 (2 * j + 1) (2 * m + 1) (by omega) hhalf)
  calc
    limitingMajorityFourierWeight (2 * j + 1) *
        ((Real.pi / 2) * ((2 * m + 1 : ℕ) : ℝ) *
          oddMajorityInfluence (m - j) * oddMajorityInfluence m) ≤
      limitingMajorityFourierWeight (2 * j + 1) *
        (1 + 2 * (((2 * j + 1 : ℕ) : ℝ)) /
          (((2 * m + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hfactor hlimitNonneg
    _ = (1 + 2 * (((2 * j + 1 : ℕ) : ℝ)) /
          (((2 * m + 1 : ℕ) : ℝ))) *
        limitingMajorityFourierWeight (2 * j + 1) := by ring

/-- Theorem 5.22, the complete two-sided estimate (5.15). -/
theorem majorityFourierWeight_bounds
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hkn : 2 * k < n) :
    limitingMajorityFourierWeight k ≤
        fourierWeightAtLevel k (majority n).toReal ∧
      fourierWeightAtLevel k (majority n).toReal ≤
        (1 + 2 * (k : ℝ) / (n : ℝ)) *
          limitingMajorityFourierWeight k := by
  exact ⟨
    limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority
      hn hk (by omega),
    fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight hn hk hkn⟩

/-- Theorem 5.22: for fixed positive odd level `k`, the Fourier weight tends to its
arcsine-series coefficient as `n` ranges over all odd arities `n ≥ k`. -/
theorem fourierWeightAtLevel_majority_odd_tendsto
    {k : ℕ} (hk : Odd k) :
    Tendsto
      (fun r : ℕ ↦
        fourierWeightAtLevel k (majority (k + 2 * r)).toReal)
      atTop (𝓝 (limitingMajorityFourierWeight k)) := by
  rcases hk with ⟨j, rfl⟩
  have harity :
      Tendsto (fun r : ℕ ↦ 2 * j + 1 + 2 * r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with r hr
    omega
  have hinv :
      Tendsto
        (fun r : ℕ ↦
          (1 : ℝ) / (((2 * j + 1 + 2 * r : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp harity
  have herror :
      Tendsto
        (fun r : ℕ ↦
          2 * (((2 * j + 1 : ℕ) : ℝ)) /
            (((2 * j + 1 + 2 * r : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Tendsto
          (fun r : ℕ ↦
            (2 * (((2 * j + 1 : ℕ) : ℝ))) *
              (1 / (((2 * j + 1 + 2 * r : ℕ) : ℝ))))
          atTop (𝓝 (2 * (((2 * j + 1 : ℕ) : ℝ)) * 0)))
  have hupper :
      Tendsto
        (fun r : ℕ ↦
          (1 + 2 * (((2 * j + 1 : ℕ) : ℝ)) /
            (((2 * j + 1 + 2 * r : ℕ) : ℝ))) *
              limitingMajorityFourierWeight (2 * j + 1))
        atTop (𝓝 (limitingMajorityFourierWeight (2 * j + 1))) := by
    simpa using
      ((tendsto_const_nhds.add herror).mul tendsto_const_nhds :
        Tendsto
          (fun r : ℕ ↦
            (1 + 2 * (((2 * j + 1 : ℕ) : ℝ)) /
              (((2 * j + 1 + 2 * r : ℕ) : ℝ))) *
                limitingMajorityFourierWeight (2 * j + 1))
          atTop
          (𝓝 ((1 + 0) * limitingMajorityFourierWeight (2 * j + 1))))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [] with r
    exact limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority
      ⟨j + r, by omega⟩ ⟨j, rfl⟩ (by omega)
  · filter_upwards [eventually_ge_atTop (2 * j + 1)] with r hr
    exact fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight
      ⟨j + r, by omega⟩ ⟨j, rfl⟩ (by omega)

/-- Theorem 5.22 in the book's `searrow` form. The parameter `r` enumerates exactly all odd
arities `n ≥ k`, via `n = k + 2r`. -/
theorem fourierWeightAtLevel_majority_odd_strictAnti_and_tendsto
    {k : ℕ} (hk : Odd k) :
    StrictAnti
        (fun r : ℕ ↦
          fourierWeightAtLevel k (majority (k + 2 * r)).toReal) ∧
      Tendsto
        (fun r : ℕ ↦
          fourierWeightAtLevel k (majority (k + 2 * r)).toReal)
        atTop (𝓝 (limitingMajorityFourierWeight k)) := by
  constructor
  · rcases hk with ⟨j, rfl⟩
    have hseq :
        (fun r : ℕ ↦
          fourierWeightAtLevel (2 * j + 1)
            (majority (2 * (j + r) + 1)).toReal) =
          fun r : ℕ ↦
            fourierWeightAtLevel (2 * j + 1)
              (majority (2 * j + 1 + 2 * r)).toReal := by
      funext r
      rw [show 2 * (j + r) + 1 = 2 * j + 1 + 2 * r by omega]
    rw [← hseq]
    exact fourierWeightAtLevel_majority_odd_sequence_strictAnti j
  · exact fourierWeightAtLevel_majority_odd_tendsto hk

end FABL
