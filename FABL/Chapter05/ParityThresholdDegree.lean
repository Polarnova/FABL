/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions

/-!
# Parity and polynomial threshold degree

Book item: Exercise 5.10.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Exercise 5.10(a): full parity on a nonempty cube is not a polynomial
threshold function of degree at most `n - 1`. -/
theorem not_isPolynomialThreshold_parityFunction_univ_pred
    (hn : 0 < n) :
    ¬IsPolynomialThreshold
      (parityFunction (Finset.univ : Finset (Fin n))) (n - 1) := by
  classical
  intro hthreshold
  obtain ⟨p, hrep, hdegree⟩ := hthreshold
  let lowFrequencies :=
    (Finset.univ : Finset (Finset (Fin n))).filter fun S ↦ S.card ≤ n - 1
  have hp : p ≠ 0 := by
    intro hpzero
    let i : Fin n := ⟨0, hn⟩
    let x : {−1,1}^[n] := fun j ↦ if j = i then -1 else 1
    have hparity :
        parityFunction (Finset.univ : Finset (Fin n)) x = -1 := by
      simp [parityFunction, x, Finset.prod_ite_eq']
    have hx := hrep x
    rw [hpzero, hparity] at hx
    norm_num at hx
  have hsupport : fourierSupport p ⊆ lowFrequencies := by
    intro S hS
    have hcard : S.card ≤ n - 1 := by
      by_contra hcard
      have hzero :=
        (fourierDegree_le_iff p (n - 1)).1 hdegree S (Nat.lt_of_not_ge hcard)
      exact (mem_fourierSupport p S).1 hS hzero
    simp [lowFrequencies, hcard]
  have hmass :
      1 ≤ ∑ S ∈ lowFrequencies,
        |fourierCoeff
          (parityFunction (Finset.univ : Finset (Fin n))).toReal S| :=
    one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation
      (parityFunction (Finset.univ : Finset (Fin n))) p lowFrequencies
        hrep hp hsupport
  have hzero :
      (∑ S ∈ lowFrequencies,
        |fourierCoeff
          (parityFunction (Finset.univ : Finset (Fin n))).toReal S|) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hcard : S.card ≤ n - 1 := by
      simpa [lowFrequencies] using hS
    have hne : (Finset.univ : Finset (Fin n)) ≠ S := by
      intro h
      rw [← h, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    rw [parityFunction_toReal, fourierCoeff_monomial]
    simp [hne]
  rw [hzero] at hmass
  norm_num at hmass

/-- O'Donnell, Exercise 5.10(b): every Boolean function other than full parity and its
negation is a polynomial threshold function of degree at most `n - 1`. -/
theorem isPolynomialThreshold_pred_of_ne_parityFunction_univ
    (f : BooleanFunction n) (hn : 0 < n)
    (hparity :
      f ≠ parityFunction (Finset.univ : Finset (Fin n)))
    (hnegParity :
      f ≠ -parityFunction (Finset.univ : Finset (Fin n))) :
    IsPolynomialThreshold f (n - 1) := by
  classical
  let parity := parityFunction (Finset.univ : Finset (Fin n))
  let a := fourierCoeff f.toReal (Finset.univ : Finset (Fin n))
  let p : {−1,1}^[n] → ℝ :=
    fun x ↦ f.toReal x - a * monomial (Finset.univ : Finset (Fin n)) x
  have hvalue (x : {−1,1}^[n]) :
      f.toReal x * monomial (Finset.univ : Finset (Fin n)) x =
        if f x = parity x then 1 else -1 := by
    rw [← congrFun (parityFunction_toReal
      (Finset.univ : Finset (Fin n))) x]
    rcases Int.units_eq_one_or (f x) with hfx | hfx <;>
      rcases Int.units_eq_one_or (parity x) with hpx | hpx <;>
      simp [BooleanFunction.toReal, parity, hfx, hpx]
  obtain ⟨xneg, hxneg⟩ := Function.ne_iff.mp hparity
  obtain ⟨xpos, hxpos⟩ := Function.ne_iff.mp hnegParity
  have hxpos' : f xpos = parity xpos := by
    rcases Int.units_eq_one_or (f xpos) with hfx | hfx <;>
      rcases Int.units_eq_one_or (parity xpos) with hpx | hpx <;>
      simp [parity, hfx, hpx] at hxpos ⊢
  have haUpper : a < 1 := by
    dsimp only [a]
    rw [fourierCoeff]
    apply Finset.expect_lt
    · intro x _
      rw [hvalue x]
      split_ifs <;> norm_num
    · refine ⟨xneg, Finset.mem_univ xneg, ?_⟩
      rw [hvalue xneg]
      simp [parity, hxneg]
  have haLower : -1 < a := by
    dsimp only [a]
    rw [fourierCoeff]
    apply Finset.lt_expect
    · intro x _
      rw [hvalue x]
      split_ifs <;> norm_num
    · refine ⟨xpos, Finset.mem_univ xpos, ?_⟩
      rw [hvalue xpos]
      simp [hxpos']
  have hdegree : fourierDegree p ≤ n - 1 := by
    rw [fourierDegree_le_iff]
    intro S hS
    have hcardLe : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    have hcard : S.card = n := by omega
    have hSuniv : S = (Finset.univ : Finset (Fin n)) := by
      apply Finset.eq_univ_of_card
      simpa [Fintype.card_fin] using hcard
    subst S
    have hscalar :
        fourierCoeff
            (fun x : {−1,1}^[n] ↦
              a * monomial (Finset.univ : Finset (Fin n)) x)
            (Finset.univ : Finset (Fin n)) =
          a * fourierCoeff
            (monomial (Finset.univ : Finset (Fin n)))
            (Finset.univ : Finset (Fin n)) := by
      rw [fourierCoeff, fourierCoeff]
      calc
        (𝔼 x : {−1,1}^[n],
            a * monomial (Finset.univ : Finset (Fin n)) x *
              monomial (Finset.univ : Finset (Fin n)) x) =
            𝔼 x : {−1,1}^[n],
              a * (monomial (Finset.univ : Finset (Fin n)) x *
                monomial (Finset.univ : Finset (Fin n)) x) := by
          apply Finset.expect_congr rfl
          intro x _
          ring
        _ = a * 𝔼 x : {−1,1}^[n],
              monomial (Finset.univ : Finset (Fin n)) x *
                monomial (Finset.univ : Finset (Fin n)) x :=
          (Finset.mul_expect
            (Finset.univ : Finset {−1,1}^[n])
            (fun x ↦ monomial (Finset.univ : Finset (Fin n)) x *
              monomial (Finset.univ : Finset (Fin n)) x) a).symm
    rw [show p = fun x ↦
        f.toReal x -
          a * monomial (Finset.univ : Finset (Fin n)) x by rfl,
      fourierCoeff_sub, hscalar, fourierCoeff_monomial]
    simp [a]
  refine ⟨p, ?_, hdegree⟩
  intro x
  rcases Int.units_eq_one_or (f x) with hfx | hfx
  · have hpnonneg : 0 ≤ p x := by
      simp only [p, BooleanFunction.toReal, hfx, signValue_one]
      rcases sq_eq_one_iff.mp
          (monomial_sq (Finset.univ : Finset (Fin n)) x) with hmonomial | hmonomial <;>
        rw [hmonomial] <;>
        linarith
    rw [hfx, thresholdSign_of_nonneg hpnonneg]
  · have hpneg : p x < 0 := by
      simp only [p, BooleanFunction.toReal, hfx, signValue_neg_one]
      rcases sq_eq_one_iff.mp
          (monomial_sq (Finset.univ : Finset (Fin n)) x) with hmonomial | hmonomial <;>
        rw [hmonomial] <;>
        linarith
    rw [hfx, thresholdSign_of_neg hpneg]

end FABL
