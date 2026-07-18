/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.MajorityComplementaryWeights
import Mathlib.Data.Nat.Choose.Central

/-!
# Monotonicity of fixed-level majority Fourier weights

Book items: Exercise 5.22 and Corollary 5.21.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A symmetric level of majority consists of `n.choose k` equal Fourier weights. -/
theorem fourierWeightAtLevel_majority_eq_choose_mul
    (n k : ℕ) (S : Finset (Fin n)) (hS : S.card = k) :
    fourierWeightAtLevel k (majority n).toReal =
      (Nat.choose n k : ℝ) * fourierWeight (majority n).toReal S := by
  classical
  have hsym : IsSymmetric (majority n).toReal := by
    intro π x
    change signValue (majority n (permuteInput π x)) =
      signValue (majority n x)
    rw [majority_symmetric]
  unfold fourierWeightAtLevel
  calc
    (∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card = k),
        fourierWeight (majority n).toReal U) =
        ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          fourierWeight (majority n).toReal S := by
      apply Finset.sum_congr
      · ext U
        simp
      · intro U hU
        have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
        unfold fourierWeight
        rw [fourierCoeff_eq_of_card_eq_of_isSymmetric
          hsym (hUcard.trans hS.symm)]
    _ = (Nat.choose n k : ℝ) * fourierWeight (majority n).toReal S := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [nsmul_eq_mul]

/-- Theorem 5.19 implies an exact ratio between corresponding fixed-level
coefficients in two consecutive odd dimensions. -/
theorem fourierCoeff_majority_next_odd_eq
    (m j : ℕ) (hj : j ≤ m)
    (S : Finset (Fin (2 * m + 1))) (hS : S.card = 2 * j + 1)
    (T : Finset (Fin (2 * (m + 1) + 1))) (hT : T.card = 2 * j + 1) :
    fourierCoeff (majority (2 * (m + 1) + 1)).toReal T =
      (((2 * (m - j) + 1 : ℕ) : ℝ) / ((2 * (m + 1) : ℕ) : ℝ)) *
        fourierCoeff (majority (2 * m + 1)).toReal S := by
  have hsmall :=
    fourierCoeff_majority_two_mul_add_one m j S hS
  have hbig :=
    fourierCoeff_majority_two_mul_add_one (m + 1) j T hT
  have hAjPos : 0 < m + 1 - j := by omega
  have hAjNe : ((m + 1 - j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hAjPos.ne'
  have hA :
      (Nat.choose (m + 1) j : ℝ) =
        (Nat.choose m j : ℝ) * (m + 1 : ℕ) / (m + 1 - j : ℕ) := by
    apply (eq_div_iff hAjNe).2
    exact_mod_cast (Nat.choose_mul_succ_eq m j).symm
  have hd₁Nat : 2 * m + 1 - 2 * j = 2 * (m - j) + 1 := by omega
  have hd₂Nat : 2 * (m + 1) - 2 * j = 2 * (m - j) + 2 := by omega
  have hd₁Pos : 0 < 2 * (m - j) + 1 := by omega
  have hd₂Pos : 0 < 2 * (m - j) + 2 := by omega
  have hd₁Ne : (((2 * (m - j) + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hd₁Pos.ne'
  have hd₂Ne : (((2 * (m - j) + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hd₂Pos.ne'
  have hBmidNat :
      Nat.choose (2 * m) (2 * j) * (2 * m + 1) =
        Nat.choose (2 * m + 1) (2 * j) * (2 * (m - j) + 1) := by
    simpa only [hd₁Nat] using Nat.choose_mul_succ_eq (2 * m) (2 * j)
  have hBmid :
      (Nat.choose (2 * m + 1) (2 * j) : ℝ) =
        (Nat.choose (2 * m) (2 * j) : ℝ) * (2 * m + 1 : ℕ) /
          (2 * (m - j) + 1 : ℕ) := by
    apply (eq_div_iff hd₁Ne).2
    exact_mod_cast hBmidNat.symm
  have hstep : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  have hBbigNat :
      Nat.choose (2 * m + 1) (2 * j) * (2 * (m + 1)) =
        Nat.choose (2 * (m + 1)) (2 * j) * (2 * (m - j) + 2) := by
    simpa only [hstep, hd₂Nat] using
      Nat.choose_mul_succ_eq (2 * m + 1) (2 * j)
  have hBbig :
      (Nat.choose (2 * (m + 1)) (2 * j) : ℝ) =
        (Nat.choose (2 * m + 1) (2 * j) : ℝ) * (2 * (m + 1) : ℕ) /
          (2 * (m - j) + 2 : ℕ) := by
    apply (eq_div_iff hd₂Ne).2
    exact_mod_cast hBbigNat.symm
  have hmSuccNe : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcentral :
      (Nat.centralBinom (m + 1) : ℝ) =
        (2 * (2 * m + 1) : ℕ) * (Nat.centralBinom m : ℝ) /
          (m + 1 : ℕ) := by
    apply (eq_div_iff hmSuccNe).2
    have hcentralNat :
        Nat.centralBinom (m + 1) * (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
      simpa [mul_comm] using Nat.succ_mul_centralBinom_succ m
    exact_mod_cast hcentralNat
  have hchooseSmall : (Nat.choose (2 * m) (2 * j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hpow :
      (2 : ℝ) ^ (2 * (m + 1)) =
        4 * (2 : ℝ) ^ (2 * m) := by
    calc
      (2 : ℝ) ^ (2 * (m + 1)) = (2 : ℝ) ^ (2 * m + 2) := by
        rfl
      _ = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ 2 := by rw [pow_add]
      _ = 4 * (2 : ℝ) ^ (2 * m) := by ring
  rw [← Nat.centralBinom_eq_two_mul_choose] at hbig
  rw [← Nat.centralBinom_eq_two_mul_choose] at hsmall
  rw [hA, hBbig, hBmid, hcentral, hpow] at hbig
  rw [hbig, hsmall]
  field_simp [hAjNe, hd₁Ne, hd₂Ne, hmSuccNe, hchooseSmall]
  push_cast [Nat.cast_sub hj, Nat.cast_sub (show j ≤ m + 1 by omega)]
  ring

/-- Exercise 5.22, exact adjacent-step identity for a fixed positive odd level. -/
theorem fourierWeightAtLevel_majority_next_odd_eq
    (m j : ℕ) (hj : j ≤ m) :
    fourierWeightAtLevel (2 * j + 1)
        (majority (2 * (m + 1) + 1)).toReal =
      ((((2 * m + 3 : ℕ) : ℝ) * ((2 * (m - j) + 1 : ℕ) : ℝ)) /
          (((2 * m + 2 : ℕ) : ℝ) * ((2 * (m - j) + 2 : ℕ) : ℝ))) *
        fourierWeightAtLevel (2 * j + 1) (majority (2 * m + 1)).toReal := by
  classical
  have hlevelSmall : 2 * j + 1 ≤ 2 * m + 1 := by omega
  have hlevelBig : 2 * j + 1 ≤ 2 * (m + 1) + 1 := by omega
  obtain ⟨S, _, hS⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (n := 2 * j + 1)
        (by simpa using hlevelSmall)
  obtain ⟨T, _, hT⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 * (m + 1) + 1)))) (n := 2 * j + 1)
        (by simpa using hlevelBig)
  have hcoeff :=
    fourierCoeff_majority_next_odd_eq m j hj S hS T hT
  have hsmall :=
    fourierWeightAtLevel_majority_eq_choose_mul (2 * m + 1) (2 * j + 1) S hS
  have hbig :=
    fourierWeightAtLevel_majority_eq_choose_mul
      (2 * (m + 1) + 1) (2 * j + 1) T hT
  have hd₁Nat : 2 * m + 2 - (2 * j + 1) = 2 * (m - j) + 1 := by omega
  have hd₂Nat : 2 * m + 3 - (2 * j + 1) = 2 * (m - j) + 2 := by omega
  have hd₁Pos : 0 < 2 * (m - j) + 1 := by omega
  have hd₂Pos : 0 < 2 * (m - j) + 2 := by omega
  have hd₁Ne : (((2 * (m - j) + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hd₁Pos.ne'
  have hd₂Ne : (((2 * (m - j) + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hd₂Pos.ne'
  have hNmidNat :
      Nat.choose (2 * m + 1) (2 * j + 1) * (2 * m + 2) =
        Nat.choose (2 * m + 2) (2 * j + 1) * (2 * (m - j) + 1) := by
    simpa only [hd₁Nat] using
      Nat.choose_mul_succ_eq (2 * m + 1) (2 * j + 1)
  have hNmid :
      (Nat.choose (2 * m + 2) (2 * j + 1) : ℝ) =
        (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) * (2 * m + 2 : ℕ) /
          (2 * (m - j) + 1 : ℕ) := by
    apply (eq_div_iff hd₁Ne).2
    exact_mod_cast hNmidNat.symm
  have hNbigNat :
      Nat.choose (2 * m + 2) (2 * j + 1) * (2 * m + 3) =
        Nat.choose (2 * m + 3) (2 * j + 1) * (2 * (m - j) + 2) := by
    simpa only [hd₂Nat] using
      Nat.choose_mul_succ_eq (2 * m + 2) (2 * j + 1)
  have hNbig :
      (Nat.choose (2 * m + 3) (2 * j + 1) : ℝ) =
        (Nat.choose (2 * m + 2) (2 * j + 1) : ℝ) * (2 * m + 3 : ℕ) /
          (2 * (m - j) + 2 : ℕ) := by
    apply (eq_div_iff hd₂Ne).2
    exact_mod_cast hNbigNat.symm
  rw [hbig, hsmall]
  unfold fourierWeight
  rw [hcoeff]
  have hdimBig : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
  rw [hdimBig, hNbig, hNmid]
  field_simp [hd₁Ne, hd₂Ne]
  push_cast [Nat.cast_sub hj]
  ring

/-- Exercise 5.22: increasing odd arity by two strictly decreases every
available fixed positive odd Fourier level. -/
theorem fourierWeightAtLevel_majority_next_odd_lt
    (m j : ℕ) (hj : j ≤ m) :
    fourierWeightAtLevel (2 * j + 1)
        (majority (2 * (m + 1) + 1)).toReal <
      fourierWeightAtLevel (2 * j + 1) (majority (2 * m + 1)).toReal := by
  rw [fourierWeightAtLevel_majority_next_odd_eq m j hj]
  have hratio :
      ((((2 * m + 3 : ℕ) : ℝ) * ((2 * (m - j) + 1 : ℕ) : ℝ)) /
          (((2 * m + 2 : ℕ) : ℝ) * ((2 * (m - j) + 2 : ℕ) : ℝ))) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast
    rw [Nat.cast_sub hj]
    have hjNonneg : (0 : ℝ) ≤ j := by positivity
    nlinarith
  have hlevel : 2 * j + 1 ≤ 2 * m + 1 := by omega
  obtain ⟨S, _, hS⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (n := 2 * j + 1)
        (by simpa using hlevel)
  have hcoeffNe :
      fourierCoeff (majority (2 * m + 1)).toReal S ≠ 0 := by
    rw [fourierCoeff_majority_two_mul_add_one m j S hS]
    have htop : 0 < (Nat.choose m j : ℝ) := by
      exact_mod_cast Nat.choose_pos hj
    have hbottom : 0 < (Nat.choose (2 * m) (2 * j) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hcentral : 0 < (Nat.choose (2 * m) m : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have hweightPos :
      0 < fourierWeightAtLevel (2 * j + 1)
        (majority (2 * m + 1)).toReal := by
    rw [fourierWeightAtLevel_majority_eq_choose_mul
      (2 * m + 1) (2 * j + 1) S hS]
    unfold fourierWeight
    have hchoose : 0 < (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos hlevel
    exact mul_pos hchoose (sq_pos_of_ne_zero hcoeffNe)
  exact mul_lt_of_lt_one_left hweightPos hratio

/-- Corollary 5.21 in its canonical sequence form: for fixed level `2j+1`,
the Fourier weight is strictly decreasing along all odd arities at least `2j+1`. -/
theorem fourierWeightAtLevel_majority_odd_sequence_strictAnti (j : ℕ) :
    StrictAnti (fun r : ℕ ↦
      fourierWeightAtLevel (2 * j + 1)
        (majority (2 * (j + r) + 1)).toReal) := by
  apply strictAnti_nat_of_succ_lt
  intro r
  have hdim :
      2 * (j + (r + 1)) + 1 = 2 * ((j + r) + 1) + 1 := by omega
  rw [hdim]
  exact fourierWeightAtLevel_majority_next_odd_lt (j + r) j (by omega)

/-- Corollary 5.21 in the book's `k,n` notation. -/
theorem fourierWeightAtLevel_majority_strict_decreasing
    {k n₁ n₂ : ℕ} (hkPos : 0 < k) (hkOdd : Odd k)
    (hn₁Odd : Odd n₁) (hn₂Odd : Odd n₂)
    (hkn₁ : k ≤ n₁) (hn₁n₂ : n₁ < n₂) :
    fourierWeightAtLevel k (majority n₂).toReal <
      fourierWeightAtLevel k (majority n₁).toReal := by
  rcases hkOdd with ⟨j, rfl⟩
  rcases hn₁Odd with ⟨m₁, rfl⟩
  rcases hn₂Odd with ⟨m₂, rfl⟩
  have hjm₁ : j ≤ m₁ := by omega
  have hm₁m₂ : m₁ < m₂ := by omega
  have hsteps : m₁ - j < m₂ - j := by omega
  have hstrict :=
    fourierWeightAtLevel_majority_odd_sequence_strictAnti j hsteps
  have hdim₁ : 2 * (j + (m₁ - j)) + 1 = 2 * m₁ + 1 := by omega
  have hdim₂ : 2 * (j + (m₂ - j)) + 1 = 2 * m₂ + 1 := by omega
  dsimp only at hstrict
  rw [hdim₁, hdim₂] at hstrict
  exact hstrict

end FABL
