/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.FourierCoefficientsOfMajority

/-!
# Complementary Fourier levels of majority

Book items: Exercise 5.20 and Corollary 5.20.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Exercise 5.20 and Corollary 5.20: Fourier coefficients of odd-arity majority
at complementary cardinalities agree up to the middle-level sign. -/
theorem fourierCoeff_majority_complementary
    (hn : Odd n) (S T : Finset (Fin n))
    (hcard : S.card + T.card = n + 1) :
    fourierCoeff (majority n).toReal S =
      (-1 : ℝ) ^ ((n - 1) / 2) *
        fourierCoeff (majority n).toReal T := by
  rcases hn with ⟨m, rfl⟩
  have hnOdd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hnHalf : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hnHalf]
  rcases Nat.even_or_odd S.card with hSeven | hSodd
  · rcases hSeven with ⟨j, hSj⟩
    have hj : j ≤ m + 1 := by omega
    have hTcard : T.card = 2 * (m + 1 - j) := by omega
    have hTeven : Even T.card := by
      use m + 1 - j
      omega
    rw [fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      hnOdd S ⟨j, hSj⟩]
    rw [fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      hnOdd T hTeven]
    simp
  · rcases hSodd with ⟨j, hSj⟩
    have hj : j ≤ m := by omega
    have hTcard : T.card = 2 * (m - j) + 1 := by omega
    have hScoeff :=
      fourierCoeff_majority_two_mul_add_one m j S hSj
    have hTcoeff :=
      fourierCoeff_majority_two_mul_add_one m (m - j) T hTcard
    have hchooseTop :
        Nat.choose m (m - j) = Nat.choose m j :=
      Nat.choose_symm hj
    have htwice : 2 * (m - j) = 2 * m - 2 * j := by omega
    have hchooseBottom :
        Nat.choose (2 * m) (2 * (m - j)) =
          Nat.choose (2 * m) (2 * j) := by
      rw [htwice]
      exact Nat.choose_symm (by omega)
    have hTcoeff' :
        fourierCoeff (majority (2 * m + 1)).toReal T =
          (-1 : ℝ) ^ (m - j) *
            (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
            (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) := by
      simpa only [hchooseTop, hchooseBottom] using hTcoeff
    have hsign :
        (-1 : ℝ) ^ j =
          (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m - j) := by
      symm
      calc
        (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m - j) =
            (-1 : ℝ) ^ (m + (m - j)) := by rw [pow_add]
        _ = (-1 : ℝ) ^ (j + 2 * (m - j)) := by
          congr 1
          omega
        _ = (-1 : ℝ) ^ j := by
          rw [pow_add, pow_mul]
          norm_num
    calc
      fourierCoeff (majority (2 * m + 1)).toReal S =
          (-1 : ℝ) ^ j *
            (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
            (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) :=
        hScoeff
      _ = (-1 : ℝ) ^ m *
          fourierCoeff (majority (2 * m + 1)).toReal T := by
        rw [hTcoeff', hsign]
        ring

private theorem fourierWeightAtLevel_eq_choose_mul_of_isSymmetric
    {f : {−1,1}^[n] → ℝ} (hf : IsSymmetric f)
    (k : ℕ) (S : Finset (Fin n)) (hS : S.card = k) :
    fourierWeightAtLevel k f =
      (Nat.choose n k : ℝ) * fourierWeight f S := by
  classical
  unfold fourierWeightAtLevel
  calc
    (∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card = k),
        fourierWeight f U) =
        ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          fourierWeight f S := by
      apply Finset.sum_congr
      · ext U
        simp
      · intro U hU
        have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
        unfold fourierWeight
        rw [fourierCoeff_eq_of_card_eq_of_isSymmetric
          hf (hUcard.trans hS.symm)]
    _ = (Nat.choose n k : ℝ) * fourierWeight f S := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [nsmul_eq_mul]

/-- Exercise 5.20 and Corollary 5.20: complementary Fourier levels of odd-arity
majority differ by the ratio of their cardinalities. -/
theorem fourierWeightAtLevel_majority_complementary
    (hn : Odd n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    fourierWeightAtLevel (n - k + 1) (majority n).toReal =
      (k : ℝ) / (n - k + 1 : ℕ) *
        fourierWeightAtLevel k (majority n).toReal := by
  classical
  let ell := n - k + 1
  change fourierWeightAtLevel ell (majority n).toReal =
    (k : ℝ) / (ell : ℕ) * fourierWeightAtLevel k (majority n).toReal
  have hellPos : 0 < ell := by
    dsimp [ell]
    omega
  have hellLe : ell ≤ n := by
    dsimp [ell]
    omega
  obtain ⟨S, _, hS⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := k) (by simpa using hkn)
  obtain ⟨T, _, hT⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := ell) (by simpa using hellLe)
  have hST : S.card + T.card = n + 1 := by
    rw [hS, hT]
    dsimp [ell]
    omega
  have hcoeff :=
    fourierCoeff_majority_complementary hn S T hST
  have hweight :
      fourierWeight (majority n).toReal S =
        fourierWeight (majority n).toReal T := by
    unfold fourierWeight
    rw [hcoeff, mul_pow]
    have hsign :
        ((-1 : ℝ) ^ ((n - 1) / 2)) ^ 2 = 1 := by
      calc
        ((-1 : ℝ) ^ ((n - 1) / 2)) ^ 2 =
            (-1 : ℝ) ^ (((n - 1) / 2) * 2) := by
          rw [pow_mul]
        _ = (-1 : ℝ) ^ (2 * ((n - 1) / 2)) := by
          rw [Nat.mul_comm]
        _ = ((-1 : ℝ) ^ 2) ^ ((n - 1) / 2) := by
          rw [pow_mul]
        _ = 1 := by norm_num
    rw [hsign, one_mul]
  have hsym : IsSymmetric (majority n).toReal := by
    intro π x
    change signValue (majority n (permuteInput π x)) =
      signValue (majority n x)
    rw [majority_symmetric]
  have hlevelS :=
    fourierWeightAtLevel_eq_choose_mul_of_isSymmetric hsym k S hS
  have hlevelT :=
    fourierWeightAtLevel_eq_choose_mul_of_isSymmetric hsym ell T hT
  have hkPred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hnPred : n - (k - 1) = ell := by
    dsimp [ell]
    omega
  have hchooseNat :
      Nat.choose n k * k = Nat.choose n (k - 1) * ell := by
    simpa only [hkPred, hnPred] using Nat.choose_succ_right_eq n (k - 1)
  have hnEll : n - ell = k - 1 := by
    dsimp [ell]
    omega
  have hchooseComplement :
      Nat.choose n ell = Nat.choose n (k - 1) := by
    calc
      Nat.choose n ell = Nat.choose n (n - ell) :=
        (Nat.choose_symm hellLe).symm
      _ = Nat.choose n (k - 1) := by rw [hnEll]
  have hellNe : (ell : ℝ) ≠ 0 := by
    exact_mod_cast hellPos.ne'
  have hchooseCast :
      (Nat.choose n (k - 1) : ℝ) * (ell : ℝ) =
        (k : ℝ) * (Nat.choose n k : ℝ) := by
    exact_mod_cast hchooseNat.symm.trans (mul_comm _ _)
  have hchooseRatio :
      (Nat.choose n ell : ℝ) =
        (k : ℝ) / (ell : ℝ) * (Nat.choose n k : ℝ) := by
    rw [hchooseComplement]
    calc
      (Nat.choose n (k - 1) : ℝ) =
          ((Nat.choose n (k - 1) : ℝ) * (ell : ℝ)) / (ell : ℝ) := by
        field_simp [hellNe]
      _ = ((k : ℝ) * (Nat.choose n k : ℝ)) / (ell : ℝ) := by
        rw [hchooseCast]
      _ = (k : ℝ) / (ell : ℝ) * (Nat.choose n k : ℝ) := by
        ring
  rw [hlevelT, hlevelS, hchooseRatio, ← hweight]
  ring

end FABL
