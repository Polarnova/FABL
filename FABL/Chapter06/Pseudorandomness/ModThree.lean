/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.RandomFunctions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The modulo-three function

Book item: Exercise 6.21.

The zero-one-valued modulo-three function is defined from the integer sum of its sign inputs.  Its
Fourier expansion is obtained from the cubic-root filter, with the integer, `ZMod 3`, complex, and
real representations connected by explicit lemmas.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The integer sum of the coordinates of a sign-cube input. -/
def signCoordinateIntegerSum (x : {−1,1}^[n]) : ℤ :=
  ∑ i, (x i : ℤ)

/-- Exercise 6.21: the zero-one-valued function detecting coordinate sums divisible by three. -/
def modThreeBoolean (n : ℕ) : ZeroOneFunction n :=
  fun x ↦ decide ((3 : ℤ) ∣ signCoordinateIntegerSum x)

/-- The real zero-one view of the modulo-three function. -/
def modThree (n : ℕ) : {−1,1}^[n] → ℝ :=
  (modThreeBoolean n).toReal

/-- The defining divisibility predicate is preserved by the real zero-one encoding. -/
theorem modThree_apply (x : {−1,1}^[n]) :
    modThree n x = if (3 : ℤ) ∣ signCoordinateIntegerSum x then 1 else 0 := by
  simp [modThree, modThreeBoolean, ZeroOneFunction.toReal, zeroOneValue]

/-- The coordinate sum reduced modulo three. -/
def modThreeResidue (x : {−1,1}^[n]) : ZMod 3 :=
  ∑ i, ((x i : ℤ) : ZMod 3)

/-- Explicit bridge from the book's integer divisibility predicate to `ZMod 3`. -/
theorem modThreeResidue_eq_zero_iff (x : {−1,1}^[n]) :
    modThreeResidue x = 0 ↔ (3 : ℤ) ∣ signCoordinateIntegerSum x := by
  have hcast :
      modThreeResidue x = (signCoordinateIntegerSum x : ZMod 3) := by
    simp [modThreeResidue, signCoordinateIntegerSum]
  rw [hcast]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd (signCoordinateIntegerSum x) 3

/-- The real function is the indicator of the zero residue. -/
theorem modThree_eq_residueIndicator (x : {−1,1}^[n]) :
    modThree n x = if modThreeResidue x = 0 then 1 else 0 := by
  rw [modThree_apply]
  by_cases hresidue : modThreeResidue x = 0
  · have hdvd : (3 : ℤ) ∣ signCoordinateIntegerSum x :=
      (modThreeResidue_eq_zero_iff x).mp hresidue
    simp [hresidue, hdvd]
  · have hdvd : ¬ ((3 : ℤ) ∣ signCoordinateIntegerSum x) :=
      fun h ↦ hresidue ((modThreeResidue_eq_zero_iff x).mpr h)
    simp [hresidue, hdvd]

private noncomputable def modThreeCubicRoot : ℂ :=
  Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)

private theorem modThreeCubicRoot_eq :
    modThreeCubicRoot =
      (-1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [modThreeCubicRoot, Complex.exp_ofReal_mul_I]
  have hangle : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [hangle, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

private theorem modThreeCubicRoot_sq :
    modThreeCubicRoot ^ 2 =
      (-1 / 2 : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [modThreeCubicRoot, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have hangle :
      (2 : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) =
        (((Real.pi + Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [congrArg Complex.exp hangle, Complex.exp_ofReal_mul_I,
    Real.cos_add, Real.sin_add]
  simp
  ring_nf

private theorem modThreeCubicRoot_cube : modThreeCubicRoot ^ 3 = 1 := by
  rw [modThreeCubicRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 1
  push_cast
  ring

private noncomputable def modThreeCubicCharacter : AddChar (ZMod 3) ℂ :=
  AddChar.zmodChar 3 modThreeCubicRoot_cube

private theorem modThreeCubicCharacter_zero :
    modThreeCubicCharacter 0 = 1 := by
  exact AddChar.map_zero_eq_one modThreeCubicCharacter

private theorem modThreeCubicCharacter_one :
    modThreeCubicCharacter 1 = modThreeCubicRoot := by
  rw [modThreeCubicCharacter, AddChar.zmodChar_apply,
    show ZMod.val (1 : ZMod 3) = 1 by decide, pow_one]

private theorem modThreeCubicCharacter_two :
    modThreeCubicCharacter 2 = modThreeCubicRoot ^ 2 := by
  rw [modThreeCubicCharacter, AddChar.zmodChar_apply,
    show ZMod.val (2 : ZMod 3) = 2 by decide]

private theorem modThreeCubicCharacter_neg_one :
    modThreeCubicCharacter (-1) = modThreeCubicRoot ^ 2 := by
  rw [modThreeCubicCharacter, AddChar.zmodChar_apply,
    show ZMod.val (-1 : ZMod 3) = 2 by decide]

private theorem modThreeCubicFilter (a : ZMod 3) :
    (if a = 0 then (1 : ℝ) else 0) =
      1 / 3 + 2 / 3 * (modThreeCubicCharacter a).re := by
  fin_cases a
  · change (if (0 : ZMod 3) = 0 then (1 : ℝ) else 0) =
      1 / 3 + 2 / 3 * (modThreeCubicCharacter (0 : ZMod 3)).re
    rw [modThreeCubicCharacter_zero]
    norm_num
  · change (if (1 : ZMod 3) = 0 then (1 : ℝ) else 0) =
      1 / 3 + 2 / 3 * (modThreeCubicCharacter (1 : ZMod 3)).re
    rw [modThreeCubicCharacter_one, modThreeCubicRoot_eq]
    norm_num
  · change (if (2 : ZMod 3) = 0 then (1 : ℝ) else 0) =
      1 / 3 + 2 / 3 * (modThreeCubicCharacter (2 : ZMod 3)).re
    rw [if_neg (by decide), modThreeCubicCharacter_two, modThreeCubicRoot_sq]
    norm_num

private noncomputable def modThreeCubicFactor (s : Sign) : ℂ :=
  (-1 / 2 : ℂ) +
    (((Real.sqrt 3 / 2) * signValue s : ℝ) : ℂ) * Complex.I

private theorem modThreeCubicCharacter_intCast_sign (s : Sign) :
    modThreeCubicCharacter ((s : ℤ) : ZMod 3) = modThreeCubicFactor s := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · change modThreeCubicCharacter (1 : ZMod 3) = modThreeCubicFactor 1
    rw [modThreeCubicCharacter_one, modThreeCubicRoot_eq]
    rw [modThreeCubicFactor, signValue_one]
    push_cast
    ring
  · change modThreeCubicCharacter (-1 : ZMod 3) = modThreeCubicFactor (-1)
    rw [modThreeCubicCharacter_neg_one, modThreeCubicRoot_sq]
    rw [modThreeCubicFactor, signValue_neg_one]
    push_cast
    ring

private theorem addChar_map_finset_sum_eq_prod
    {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (character : AddChar A M) (s : Finset ι) (f : ι → A) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, Finset.prod_insert hi, ih]

private theorem modThreeCubicCharacter_residue (x : {−1,1}^[n]) :
    modThreeCubicCharacter (modThreeResidue x) =
      ∏ i, modThreeCubicFactor (x i) := by
  rw [modThreeResidue]
  calc
    modThreeCubicCharacter (∑ i, ((x i : ℤ) : ZMod 3)) =
        ∏ i, modThreeCubicCharacter ((x i : ℤ) : ZMod 3) := by
      simpa using addChar_map_finset_sum_eq_prod modThreeCubicCharacter
        (Finset.univ : Finset (Fin n)) (fun i ↦ ((x i : ℤ) : ZMod 3))
    _ = ∏ i, modThreeCubicFactor (x i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact modThreeCubicCharacter_intCast_sign (x i)

private theorem modThree_eq_cubicRootFilter (x : {−1,1}^[n]) :
    modThree n x =
      1 / 3 + 2 / 3 * (∏ i, modThreeCubicFactor (x i)).re := by
  rw [modThree_eq_residueIndicator, modThreeCubicFilter,
    modThreeCubicCharacter_residue]

private noncomputable def modThreeComplexTerm
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℂ :=
  ((((-Real.sqrt 3) ^ S.card * monomial S x : ℝ) : ℂ) *
    Complex.I ^ S.card)

private theorem modThreeCubicVariableProduct
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    ∏ i ∈ S, (((-Real.sqrt 3 * signValue (x i) : ℝ) : ℂ) * Complex.I) =
      modThreeComplexTerm S x := by
  classical
  unfold modThreeComplexTerm
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih =>
      have hmonomial :
          monomial (insert i S) x = signValue (x i) * monomial S x := by
        simp only [monomial, Finset.prod_insert hi]
      rw [Finset.prod_insert hi, ih, Finset.card_insert_of_notMem hi,
        hmonomial, pow_succ]
      push_cast
      ring

private theorem modThreeCubicProduct_expansion (x : {−1,1}^[n]) :
    ∏ i, modThreeCubicFactor (x i) =
      (-1 / 2 : ℂ) ^ n * ∑ S : Finset (Fin n), modThreeComplexTerm S x := by
  classical
  calc
    ∏ i, modThreeCubicFactor (x i) =
        ∏ i, (-1 / 2 : ℂ) *
          ((((-Real.sqrt 3 * signValue (x i) : ℝ) : ℂ) * Complex.I) + 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [modThreeCubicFactor]
      push_cast
      ring
    _ = (-1 / 2 : ℂ) ^ n *
        ∏ i, ((((-Real.sqrt 3 * signValue (x i) : ℝ) : ℂ) * Complex.I) + 1) := by
      have hconst :
          (∏ _i : Fin n, (-1 / 2 : ℂ)) = (-1 / 2 : ℂ) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_mul_distrib, hconst]
    _ = (-1 / 2 : ℂ) ^ n *
        ∑ S : Finset (Fin n),
          ∏ i ∈ S, (((-Real.sqrt 3 * signValue (x i) : ℝ) : ℂ) * Complex.I) := by
      rw [Fintype.prod_add]
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      simp
    _ = (-1 / 2 : ℂ) ^ n * ∑ S : Finset (Fin n), modThreeComplexTerm S x := by
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      exact modThreeCubicVariableProduct S x

private theorem re_I_pow_eq_modFourPhase {k : ℕ} (hk : Even k) :
    (Complex.I ^ k).re = (-1 : ℝ) ^ ((k % 4) / 2) := by
  obtain ⟨m, rfl⟩ := hk
  have hmod : ((m + m) % 4) / 2 = m % 2 := by omega
  rw [hmod, ← neg_one_pow_eq_pow_mod_two]
  have hadd : m + m = 2 * m := by omega
  rw [hadd, pow_mul, Complex.I_sq]
  have hcast :
      (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    norm_cast
  rw [hcast]
  exact Complex.ofReal_re _

private theorem re_I_pow_eq_zero_of_odd {k : ℕ} (hk : Odd k) :
    (Complex.I ^ k).re = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, Complex.I_sq]
  have hcast :
      (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    norm_cast
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub]
  have him : ((-1 : ℂ) ^ m).im = 0 := by
    rw [hcast]
    exact Complex.ofReal_im _
  rw [him, neg_zero]

private theorem modThreeComplexTerm_re (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    (modThreeComplexTerm S x).re =
      if Even S.card then
        (-1 : ℝ) ^ ((S.card % 4) / 2) *
          (Real.sqrt 3) ^ S.card * monomial S x
      else 0 := by
  by_cases hS : Even S.card
  · rw [if_pos hS, modThreeComplexTerm]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [re_I_pow_eq_modFourPhase hS, hS.neg_pow]
    ring
  · have hSodd : Odd S.card := Nat.not_even_iff_odd.mp hS
    rw [if_neg hS, modThreeComplexTerm]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [re_I_pow_eq_zero_of_odd hSodd, mul_zero]

private theorem modThreeCubicProduct_re (x : {−1,1}^[n]) :
    (∏ i, modThreeCubicFactor (x i)).re =
      (-1 / 2 : ℝ) ^ n *
        ∑ S : Finset (Fin n) with Even S.card,
          (-1 : ℝ) ^ ((S.card % 4) / 2) *
            (Real.sqrt 3) ^ S.card * monomial S x := by
  rw [modThreeCubicProduct_expansion]
  have hreal :
      (-1 / 2 : ℂ) ^ n = (((-1 / 2 : ℝ) ^ n : ℝ) : ℂ) := by norm_cast
  rw [hreal]
  simp_rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum, modThreeComplexTerm_re]
  rw [Finset.sum_filter]

/-- Exercise 6.21: the complete pointwise Fourier expansion of the modulo-three function.

The theorem includes dimension zero: the empty-set summand contributes `2 / 3`, so the right-hand
side is `1`, as is the divisibility indicator of the empty coordinate sum. -/
theorem modThree_fourier_expansion (x : {−1,1}^[n]) :
    modThree n x =
      1 / 3 + 2 / 3 * (-1 / 2 : ℝ) ^ n *
        ∑ S : Finset (Fin n) with Even S.card,
          (-1 : ℝ) ^ ((S.card % 4) / 2) *
            (Real.sqrt 3) ^ S.card * monomial S x := by
  rw [modThree_eq_cubicRootFilter, modThreeCubicProduct_re]
  ring

/-- The coefficients displayed in Exercise 6.21, including the separate constant `1 / 3`. -/
noncomputable def modThreeFourierCoefficient (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (if S = ∅ then 1 / 3 else 0) +
    if Even S.card then
      2 / 3 * (-1 / 2 : ℝ) ^ n *
        (-1 : ℝ) ^ ((S.card % 4) / 2) * (Real.sqrt 3) ^ S.card
    else 0

private theorem modThree_eq_multilinearPolynomial (x : {−1,1}^[n]) :
    modThree n x = multilinearPolynomial (modThreeFourierCoefficient n) x := by
  classical
  rw [modThree_fourier_expansion, multilinearPolynomial]
  unfold modThreeFourierCoefficient
  simp only [add_mul, Finset.sum_add_distrib]
  have hempty :
      (∑ S : Finset (Fin n),
          (if S = ∅ then (1 / 3 : ℝ) else 0) * monomial S x) = 1 / 3 := by
    simp [monomial]
  have heven :
      (∑ S : Finset (Fin n),
          (if Even S.card then
              2 / 3 * (-1 / 2 : ℝ) ^ n *
                (-1 : ℝ) ^ ((S.card % 4) / 2) * (Real.sqrt 3) ^ S.card
            else 0) * monomial S x) =
        2 / 3 * (-1 / 2 : ℝ) ^ n *
          ∑ S : Finset (Fin n) with Even S.card,
            (-1 : ℝ) ^ ((S.card % 4) / 2) *
              (Real.sqrt 3) ^ S.card * monomial S x := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hEven : Even S.card
    · rw [if_pos hEven, if_pos hEven]
      ring
    · rw [if_neg hEven, if_neg hEven]
      ring
  rw [hempty, heven]

/-- The displayed coefficients are the canonical Fourier coefficients from Theorem 1.1. -/
theorem fourierCoeff_modThree (S : Finset (Fin n)) :
    fourierCoeff (modThree n) S = modThreeFourierCoefficient n S := by
  have hcoeff := (fourier_expansion_unique (modThree n)).2
    (modThreeFourierCoefficient n) modThree_eq_multilinearPolynomial
  exact (congrFun hcoeff S).symm

/-- Every nonconstant coefficient has exactly the even-cardinality value in the displayed sum. -/
theorem fourierCoeff_modThree_of_nonempty
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    fourierCoeff (modThree n) S =
      if Even S.card then
        2 / 3 * (-1 / 2 : ℝ) ^ n *
          (-1 : ℝ) ^ ((S.card % 4) / 2) * (Real.sqrt 3) ^ S.card
      else 0 := by
  rw [fourierCoeff_modThree, modThreeFourierCoefficient]
  simp [Finset.nonempty_iff_ne_empty.mp hS]

/-- Every nonconstant coefficient obeys the regularity bound claimed in Exercise 6.21. -/
theorem abs_fourierCoeff_modThree_le
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    |fourierCoeff (modThree n) S| ≤
      2 / 3 * (Real.sqrt 3 / 2) ^ n := by
  rw [fourierCoeff_modThree_of_nonempty S hS]
  by_cases hEven : Even S.card
  · rw [if_pos hEven]
    have hsqrtNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.one_le_sqrt]
      norm_num
    have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hpow : (Real.sqrt 3) ^ S.card ≤ (Real.sqrt 3) ^ n :=
      pow_le_pow_right₀ hsqrtOne hcard
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg hsqrtNonneg]
    norm_num
    calc
      2 / 3 * (1 / 2 : ℝ) ^ n * (Real.sqrt 3) ^ S.card ≤
          2 / 3 * (1 / 2 : ℝ) ^ n * (Real.sqrt 3) ^ n := by
        gcongr
      _ = 2 / 3 * (Real.sqrt 3 / 2) ^ n := by
        rw [one_div_pow, div_pow]
        ring
  · rw [if_neg hEven, abs_zero]
    positivity

/-- Exercise 6.21: `mod₃` is `(2/3)(√3/2)ⁿ`-regular. -/
theorem modThree_isFourierRegular :
    IsFourierRegular (2 / 3 * (Real.sqrt 3 / 2) ^ n) (modThree n) :=
  fun S hS ↦ abs_fourierCoeff_modThree_le S hS

end FABL
