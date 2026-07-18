/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.ParityThresholdDegree

/-!
# A polynomial threshold function with small low-degree Fourier weight

Book item: Exercise 5.11.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

/-- The all-one vertex of the sign cube. -/
def allOneSignCube (n : ℕ) : {−1,1}^[n] :=
  fun _ ↦ 1

/-- Full parity on `k+1` variables with its value at the all-one vertex reversed. -/
def onePointFlippedParity (k : ℕ) : BooleanFunction (k + 1) :=
  fun x ↦
    if x = allOneSignCube (k + 1) then
      -parityFunction (Finset.univ : Finset (Fin (k + 1))) x
    else
      parityFunction (Finset.univ : Finset (Fin (k + 1))) x

private theorem onePointFlippedParity_ne_fullParity (k : ℕ) :
    onePointFlippedParity k ≠
      parityFunction (Finset.univ : Finset (Fin (k + 1))) := by
  intro h
  have hvalue := congrFun h (allOneSignCube (k + 1))
  simp [onePointFlippedParity, allOneSignCube, parityFunction] at hvalue

private theorem onePointFlippedParity_ne_neg_fullParity (k : ℕ) :
    onePointFlippedParity k ≠
      -parityFunction (Finset.univ : Finset (Fin (k + 1))) := by
  let y : {−1,1}^[k + 1] :=
    fun i ↦ if i = (0 : Fin (k + 1)) then -1 else 1
  have hy :
      y ≠ allOneSignCube (k + 1) := by
    intro h
    have hzero := congrFun h (0 : Fin (k + 1))
    simp [y, allOneSignCube] at hzero
  intro h
  have hvalue := congrFun h y
  rw [onePointFlippedParity, if_neg hy] at hvalue
  change
    parityFunction (Finset.univ : Finset (Fin (k + 1))) y =
      -parityFunction (Finset.univ : Finset (Fin (k + 1))) y at hvalue
  rcases Int.units_eq_one_or
      (parityFunction (Finset.univ : Finset (Fin (k + 1))) y) with hp | hp <;>
    simp [hp] at hvalue

/-- The one-point perturbation of parity has polynomial threshold degree at most `k`. -/
theorem onePointFlippedParity_isPolynomialThreshold (k : ℕ) :
    IsPolynomialThreshold (onePointFlippedParity k) k := by
  simpa using
    isPolynomialThreshold_pred_of_ne_parityFunction_univ
      (onePointFlippedParity k) (Nat.succ_pos k)
      (onePointFlippedParity_ne_fullParity k)
      (onePointFlippedParity_ne_neg_fullParity k)

private theorem onePointFlippedParity_toReal (k : ℕ) :
    (onePointFlippedParity k).toReal =
      fun x ↦
        (parityFunction
          (Finset.univ : Finset (Fin (k + 1)))).toReal x -
          if x = allOneSignCube (k + 1) then 2 else 0 := by
  funext x
  by_cases hx : x = allOneSignCube (k + 1)
  · subst x
    simp [onePointFlippedParity, allOneSignCube, parityFunction,
      BooleanFunction.toReal]
    norm_num
  · change
      signValue (onePointFlippedParity k x) =
        signValue
            (parityFunction
              (Finset.univ : Finset (Fin (k + 1))) x) -
          (if x = allOneSignCube (k + 1) then 2 else 0)
    rw [onePointFlippedParity, if_neg hx, if_neg hx]
    ring

private theorem fourierCoeff_two_mul_allOnePointMass
    (k : ℕ) (S : Finset (Fin (k + 1))) :
    fourierCoeff
        (fun x : {−1,1}^[k + 1] ↦
          if x = allOneSignCube (k + 1) then (2 : ℝ) else 0)
        S =
      ((2 : ℝ)⁻¹) ^ k := by
  rw [fourierCoeff, Fintype.expect_eq_sum_div_card]
  have hcard :
      Fintype.card ({−1,1}^[k + 1]) = 2 ^ (k + 1) := by
    simp [Fintype.card_units_int]
  rw [hcard]
  simp [allOneSignCube, monomial]
  field_simp
  rw [pow_succ]
  ring

/-- Every Fourier coefficient of the one-point perturbation is the corresponding full-parity
coefficient shifted by `2⁻ᵏ`. -/
theorem fourierCoeff_onePointFlippedParity
    (k : ℕ) (S : Finset (Fin (k + 1))) :
    fourierCoeff (onePointFlippedParity k).toReal S =
      (if (Finset.univ : Finset (Fin (k + 1))) = S then 1 else 0) -
        ((2 : ℝ)⁻¹) ^ k := by
  rw [onePointFlippedParity_toReal, fourierCoeff_sub,
    parityFunction_toReal, fourierCoeff_monomial,
    fourierCoeff_two_mul_allOnePointMass]

private theorem lowDegreeFrequencies_eq_erase_univ (k : ℕ) :
    (Finset.univ : Finset (Finset (Fin (k + 1)))).filter
        (fun S ↦ S.card ≤ k) =
      Finset.univ.erase (Finset.univ : Finset (Fin (k + 1))) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  constructor
  · intro hcard
    refine ⟨?_, trivial⟩
    intro hS
    subst S
    simp at hcard
  · rintro ⟨hS, _⟩
    have hlt : S.card < k + 1 := by
      simpa using (Finset.card_lt_iff_ne_univ S).2 hS
    omega

/-- The exact low-degree Fourier weight of the one-point perturbation of parity. -/
theorem fourierWeightAtMost_onePointFlippedParity (k : ℕ) :
    fourierWeightAtMost k (onePointFlippedParity k).toReal =
      ((2 ^ (k + 1) - 1 : ℕ) : ℝ) * (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
  rw [fourierWeightAtMost, lowDegreeFrequencies_eq_erase_univ]
  calc
    (∑ S ∈
        (Finset.univ : Finset (Finset (Fin (k + 1)))).erase
          (Finset.univ : Finset (Fin (k + 1))),
        fourierWeight (onePointFlippedParity k).toReal S) =
        ∑ _S ∈
          (Finset.univ : Finset (Finset (Fin (k + 1)))).erase
            (Finset.univ : Finset (Fin (k + 1))),
          (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hne :
          (Finset.univ : Finset (Fin (k + 1))) ≠ S :=
        (Finset.mem_erase.mp hS).1.symm
      simp [fourierWeight, fourierCoeff_onePointFlippedParity, hne]
    _ = ((2 ^ (k + 1) - 1 : ℕ) : ℝ) *
        (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp [Fintype.card_finset]

/-- Exercise 5.11: for every `k`, a degree-at-most-`k` polynomial threshold function has
Fourier weight through level `k` strictly below `2^(1-k)`. The displayed right-hand side is
written as `2 · 2⁻ᵏ`, avoiding natural-number subtraction in the exponent. -/
theorem exists_polynomialThreshold_fourierWeightAtMost_lt_two_mul_invPow
    (k : ℕ) :
    ∃ f : BooleanFunction (k + 1),
      IsPolynomialThreshold f k ∧
        fourierWeightAtMost k f.toReal <
          2 * ((2 : ℝ)⁻¹) ^ k := by
  refine ⟨onePointFlippedParity k,
    onePointFlippedParity_isPolynomialThreshold k, ?_⟩
  rw [fourierWeightAtMost_onePointFlippedParity]
  have hpow : 0 < ((2 : ℝ)⁻¹) ^ k := by positivity
  have hidentity :
      ((2 ^ (k + 1) : ℕ) : ℝ) * (((2 : ℝ)⁻¹) ^ k) ^ 2 =
        2 * ((2 : ℝ)⁻¹) ^ k := by
    push_cast
    rw [pow_succ, inv_pow]
    field_simp
  calc
    ((2 ^ (k + 1) - 1 : ℕ) : ℝ) * (((2 : ℝ)⁻¹) ^ k) ^ 2 <
        ((2 ^ (k + 1) : ℕ) : ℝ) * (((2 : ℝ)⁻¹) ^ k) ^ 2 := by
      gcongr
      · exact_mod_cast Nat.sub_lt (by positivity : 0 < 2 ^ (k + 1))
          (by decide : 0 < 1)
    _ = 2 * ((2 : ℝ)⁻¹) ^ k := hidentity

end FABL
