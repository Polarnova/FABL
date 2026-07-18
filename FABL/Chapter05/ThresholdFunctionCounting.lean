/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.LowDegree
public import FABL.Chapter05.ChowTheorem

/-!
# Counting threshold functions

Book item: Exercise 5.4.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

/-- The finite type of degree-at-most-`k` polynomial threshold functions on `n` variables. -/
abbrev PolynomialThresholdFunction (n k : ℕ) :=
  {f : BooleanFunction n // IsPolynomialThreshold f k}

/-- The finite type of linear threshold functions on `n` variables. -/
abbrev LinearThresholdFunction (n : ℕ) :=
  {f : BooleanFunction n // IsLinearThreshold f}

private noncomputable def fourierAgreementCount
    {n : ℕ} (f : BooleanFunction n) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun x ↦ f x = parityFunction S x).card

private theorem fourierCoeff_eq_agreementCount
    {n : ℕ} (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff f.toReal S =
      (2 * (fourierAgreementCount f S : ℝ) - (2 : ℝ) ^ n) /
        (2 : ℝ) ^ n := by
  classical
  have hcard :
      Fintype.card ({−1,1}^[n]) = 2 ^ n := by
    simp [Fintype.card_units_int]
  have hcardReal :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hcard
  have hpoint (x : {−1,1}^[n]) :
      f.toReal x * monomial S x =
        if f x = parityFunction S x then (1 : ℝ) else -1 := by
    rw [← congrFun (parityFunction_toReal S) x]
    rcases Int.units_eq_one_or (f x) with hf | hf <;>
      rcases Int.units_eq_one_or (parityFunction S x) with hp | hp <;>
      simp [BooleanFunction.toReal, hf, hp]
  have hsum :
      (∑ x : {−1,1}^[n],
          if f x = parityFunction S x then (1 : ℝ) else -1) =
        2 * (fourierAgreementCount f S : ℝ) - (2 : ℝ) ^ n := by
    calc
      (∑ x : {−1,1}^[n],
          if f x = parityFunction S x then (1 : ℝ) else -1) =
          ∑ x : {−1,1}^[n],
            (2 * (if f x = parityFunction S x then (1 : ℝ) else 0) - 1) := by
        apply Finset.sum_congr rfl
        intro x _
        split <;> norm_num
      _ = 2 * ∑ x : {−1,1}^[n],
              (if f x = parityFunction S x then (1 : ℝ) else 0) -
            ∑ _x : {−1,1}^[n], (1 : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 2 * (fourierAgreementCount f S : ℝ) - (2 : ℝ) ^ n := by
        simp [fourierAgreementCount, hcard]
  rw [fourierCoeff, Fintype.expect_eq_sum_div_card, hcardReal]
  congr 1
  calc
    (∑ x : {−1,1}^[n], f.toReal x * monomial S x) =
        ∑ x : {−1,1}^[n],
          if f x = parityFunction S x then (1 : ℝ) else -1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    _ = 2 * (fourierAgreementCount f S : ℝ) - (2 : ℝ) ^ n := hsum

private noncomputable def lowDegreeAgreementProfile
    (n k : ℕ) (f : BooleanFunction n) :
    (↥(lowDegreeFourierFamily n k) →
      Fin (2 ^ n + 1)) :=
  fun S ↦
    ⟨fourierAgreementCount f S.1, by
      apply Nat.lt_succ_of_le
      calc
        fourierAgreementCount f S.1 ≤
            Fintype.card ({−1,1}^[n]) := by
          exact Finset.card_filter_le Finset.univ _
        _ = 2 ^ n := by
          simp [Fintype.card_units_int]⟩

private theorem lowDegreeAgreementProfile_injective_on_polynomialThreshold
    (n k : ℕ) :
    Function.Injective
      (fun f : PolynomialThresholdFunction n k ↦
        lowDegreeAgreementProfile n k f.1) := by
  intro f g hprofile
  apply Subtype.ext
  have hgf : g.1 = f.1 := by
    apply eq_of_isPolynomialThreshold_of_fourierCoeff_eq
      f.1 g.1 k f.2
    intro S hSk
    rw [fourierCoeff_eq_agreementCount, fourierCoeff_eq_agreementCount]
    have hvalue :=
      congrArg Fin.val
        (congrFun hprofile
          (⟨S, mem_lowDegreeFourierFamily S k |>.2 hSk⟩ :
            ↥(lowDegreeFourierFamily n k)))
    have hcount :
        fourierAgreementCount g.1 S =
          fourierAgreementCount f.1 S := by
      simpa [lowDegreeAgreementProfile] using hvalue.symm
    rw [hcount]
  exact hgf.symm

private theorem lowDegreeAgreementProfile_injective_on_linearThreshold
    (n : ℕ) :
    Function.Injective
      (fun f : LinearThresholdFunction n ↦
        lowDegreeAgreementProfile n 1 f.1) := by
  intro f g hprofile
  apply Subtype.ext
  have hgf : g.1 = f.1 := by
    apply eq_of_isLinearThreshold_of_fourierCoeff_eq f.1 g.1 f.2
    intro S hS
    rw [fourierCoeff_eq_agreementCount, fourierCoeff_eq_agreementCount]
    have hvalue :=
      congrArg Fin.val
        (congrFun hprofile
          (⟨S, mem_lowDegreeFourierFamily S 1 |>.2 hS⟩ :
            ↥(lowDegreeFourierFamily n 1)))
    have hcount :
        fourierAgreementCount g.1 S =
          fourierAgreementCount f.1 S := by
      simpa [lowDegreeAgreementProfile] using hvalue.symm
    rw [hcount]
  exact hgf.symm

/-- The exact finite-profile bound underlying Exercise 5.4(b). -/
theorem natCard_polynomialThresholdFunction_le_profileCount
    (n k : ℕ) :
    Nat.card (PolynomialThresholdFunction n k) ≤
      (2 ^ n + 1) ^ (lowDegreeFourierFamily n k).card := by
  let profile :=
    fun f : PolynomialThresholdFunction n k ↦
      lowDegreeAgreementProfile n k f.1
  calc
    Nat.card (PolynomialThresholdFunction n k) ≤
        Nat.card
          (↥(lowDegreeFourierFamily n k) → Fin (2 ^ n + 1)) :=
      Nat.card_le_card_of_injective profile
        (lowDegreeAgreementProfile_injective_on_polynomialThreshold n k)
    _ = (2 ^ n + 1) ^ (lowDegreeFourierFamily n k).card := by
      rw [Nat.card_fun, Nat.card_fin,
        Nat.card_eq_finsetCard]

/-- The exact finite-profile bound underlying Exercise 5.4(a). -/
theorem natCard_linearThresholdFunction_le_profileCount
    (n : ℕ) :
    Nat.card (LinearThresholdFunction n) ≤
      (2 ^ n + 1) ^ (lowDegreeFourierFamily n 1).card := by
  let profile :=
    fun f : LinearThresholdFunction n ↦
      lowDegreeAgreementProfile n 1 f.1
  calc
    Nat.card (LinearThresholdFunction n) ≤
        Nat.card
          (↥(lowDegreeFourierFamily n 1) → Fin (2 ^ n + 1)) :=
      Nat.card_le_card_of_injective profile
        (lowDegreeAgreementProfile_injective_on_linearThreshold n)
    _ = (2 ^ n + 1) ^ (lowDegreeFourierFamily n 1).card := by
      rw [Nat.card_fun, Nat.card_fin,
        Nat.card_eq_finsetCard]

private theorem two_pow_add_one_le_next_two_pow (n : ℕ) :
    2 ^ n + 1 ≤ 2 ^ (n + 1) := by
  rw [pow_succ]
  have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
  omega

/-- Exercise 5.4(a), with the `O(n)` term made explicit:
the number of linear threshold functions is at most
`2^((n+1)^2) = 2^(n^2+2n+1)`. -/
theorem natCard_linearThresholdFunction_le_two_pow_sq
    (n : ℕ) :
    Nat.card (LinearThresholdFunction n) ≤ 2 ^ (n + 1) ^ 2 := by
  have hfamily :
      (lowDegreeFourierFamily n 1).card = n + 1 := by
    rw [card_lowDegreeFourierFamily_eq_sum_choose]
    norm_num [Finset.sum_range_succ, Nat.choose_one_right]
    omega
  calc
    Nat.card (LinearThresholdFunction n) ≤
        (2 ^ n + 1) ^ (lowDegreeFourierFamily n 1).card :=
      natCard_linearThresholdFunction_le_profileCount n
    _ ≤ (2 ^ (n + 1)) ^ (lowDegreeFourierFamily n 1).card :=
      Nat.pow_le_pow_left (two_pow_add_one_le_next_two_pow n) _
    _ = 2 ^ (n + 1) ^ 2 := by
      rw [hfamily, ← pow_mul]
      congr 1
      ring

/-- A sharp-leading-term polynomial bound for the number of frequencies of degree at most
`k`: for positive `n`, the leading contribution is bounded by `n^k`, and the lower levels
contribute at most `k n^(k-1)`. -/
theorem card_lowDegreeFourierFamily_le_leadingTerm
    (n k : ℕ) (hn : 0 < n) :
    (lowDegreeFourierFamily n k).card ≤
      n ^ k + k * n ^ (k - 1) := by
  rw [card_lowDegreeFourierFamily_eq_sum_choose]
  cases k with
  | zero =>
      simp
  | succ k =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range (k + 1), Nat.choose n j) +
              Nat.choose n (k + 1) ≤
            (k + 1) * n ^ k + n ^ (k + 1) := by
          apply add_le_add
          · calc
              (∑ j ∈ Finset.range (k + 1), Nat.choose n j) ≤
                  ∑ _j ∈ Finset.range (k + 1), n ^ k := by
                apply Finset.sum_le_sum
                intro j hj
                have hjk : j ≤ k := by simpa using hj
                exact (Nat.choose_le_pow n j).trans
                  (Nat.pow_le_pow_right hn hjk)
              _ = (k + 1) * n ^ k := by simp
          · exact Nat.choose_le_pow n (k + 1)
        _ = n ^ (k + 1) + (k + 1) * n ^ k := by
          omega

private theorem natCard_polynomialThresholdFunction_le_two_pow_bookBound_of_pos
    (n k : ℕ) (hn : 0 < n) :
    Nat.card (PolynomialThresholdFunction n k) ≤
      2 ^ (n ^ (k + 1) + (2 * k + 1) * n ^ k) := by
  have hfamily :=
    card_lowDegreeFourierFamily_le_leadingTerm n k hn
  have hpower :
      n ^ (k - 1) ≤ n ^ k :=
    Nat.pow_le_pow_right hn (Nat.sub_le k 1)
  calc
    Nat.card (PolynomialThresholdFunction n k) ≤
        (2 ^ n + 1) ^ (lowDegreeFourierFamily n k).card :=
      natCard_polynomialThresholdFunction_le_profileCount n k
    _ ≤ (2 ^ (n + 1)) ^ (lowDegreeFourierFamily n k).card :=
      Nat.pow_le_pow_left (two_pow_add_one_le_next_two_pow n) _
    _ = 2 ^ ((n + 1) * (lowDegreeFourierFamily n k).card) := by
      rw [pow_mul]
    _ ≤ 2 ^ ((n + 1) * (n ^ k + k * n ^ (k - 1))) :=
      Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_left (n + 1) hfamily)
    _ ≤ 2 ^ (n ^ (k + 1) + (2 * k + 1) * n ^ k) := by
      apply Nat.pow_le_pow_right (by decide)
      calc
        (n + 1) * (n ^ k + k * n ^ (k - 1)) =
            n ^ (k + 1) + (k + 1) * n ^ k +
              k * n ^ (k - 1) := by
          cases k with
          | zero => simp
          | succ k =>
              simp only [Nat.succ_sub_one, pow_succ]
              ring
        _ ≤ n ^ (k + 1) + (k + 1) * n ^ k +
              k * n ^ k := by
          gcongr
        _ = n ^ (k + 1) + (2 * k + 1) * n ^ k := by
          ring

/-- Exercise 5.4(b), with the fixed-`k` error term made explicit:
the number of degree-at-most-`k` polynomial threshold functions is at most
`2^(n^(k+1) + (2k+1)n^k + 1)`, hence at most
`2^(n^(k+1) + O_k(n^k))`. -/
theorem natCard_polynomialThresholdFunction_le_two_pow_bookBound
    (n k : ℕ) :
    Nat.card (PolynomialThresholdFunction n k) ≤
      2 ^ (n ^ (k + 1) + (2 * k + 1) * n ^ k + 1) := by
  by_cases hn : n = 0
  · subst n
    calc
      Nat.card (PolynomialThresholdFunction 0 k) ≤
          Nat.card (BooleanFunction 0) :=
        Nat.card_le_card_of_injective
          (fun f : PolynomialThresholdFunction 0 k ↦ f.1)
          Subtype.val_injective
      _ = 2 := by
        rw [Nat.card_fun]
        simp [Sign]
      _ ≤ 2 ^ (0 ^ (k + 1) + (2 * k + 1) * 0 ^ k + 1) := by
        cases k <;> norm_num
  · exact
      (natCard_polynomialThresholdFunction_le_two_pow_bookBound_of_pos
        n k (Nat.pos_of_ne_zero hn)).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

end FABL
