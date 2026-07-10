/-
Copyright (c) 2026 FABL contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FABL contributors
-/
module

public import FABL.Mathlib

/-!
# Functions as multilinear polynomials

Formalization of Sections 1.1 and 1.2 of O'Donnell's *Analysis of Boolean Functions*.

The section-specific representation of the domain will be introduced with the first mathematical
definition. FABL does not impose a project-wide cube representation in advance.
-/

open scoped BigOperators

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The two-element field used for the additive Boolean cube. -/
abbrev 𝔽₂ := ZMod 2

/-- The additive Boolean cube `𝔽₂ⁿ`. -/
abbrev F₂Cube (n : ℕ) := Fin n → 𝔽₂

/-- The sign alphabet `{-1, 1}`, represented by the two units of `ℤ`. -/
abbrev Sign := ℤˣ

/-- The sign cube `{-1, 1}ⁿ`. -/
abbrev SignCube (n : ℕ) := Fin n → Sign

scoped[BooleanCube] notation "𝔽₂^[" n "]" => FABL.F₂Cube n
scoped[BooleanCube] notation "{−1,1}^[" n "]" => FABL.SignCube n

open scoped BooleanCube

/-- The real value of a sign. -/
def signValue (s : Sign) : ℝ := ((s : ℤ) : ℝ)

@[simp] theorem signValue_one : signValue 1 = 1 := by
  simp [signValue]

@[simp] theorem signValue_neg_one : signValue (-1) = -1 := by
  simp [signValue]

/-- Every element of `Sign` has real value `-1` or `1`. -/
theorem signValue_eq_neg_one_or_one (s : Sign) : signValue s = -1 ∨ signValue s = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [signValue]

/-- The indicator polynomial `𝟙_{a}(x) = ∏ᵢ (1 + aᵢxᵢ)/2` from Section 1.2. -/
noncomputable def indicatorPolynomial (a x : {−1,1}^[n]) : ℝ :=
  ∏ i, (1 + signValue (a i) * signValue (x i)) / 2

/-- The indicator polynomial is one exactly at its indexed point. -/
theorem indicatorPolynomial_eq_ite (a x : {−1,1}^[n]) :
    indicatorPolynomial a x = if x = a then 1 else 0 := by
  classical
  have hfactor (i : Fin n) :
      (1 + signValue (a i) * signValue (x i)) / 2 =
        if x i = a i then (1 : ℝ) else 0 := by
    rcases Int.units_eq_one_or (a i) with ha | ha <;>
      rcases Int.units_eq_one_or (x i) with hx | hx <;>
      simp [signValue, ha, hx]
  rw [indicatorPolynomial]
  simp_rw [hfactor]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

/-- The interpolation formula used for existence in O'Donnell, Theorem 1.1. -/
theorem sum_indicatorPolynomial (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    f x = ∑ a, f a * indicatorPolynomial a x := by
  classical
  simp [indicatorPolynomial_eq_ite]

/-- The monomial `xˢ = ∏ i ∈ S, xᵢ` on the sign cube. -/
def monomial (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℝ :=
  ∏ i ∈ S, signValue (x i)

/-- A sign-cube monomial bundled as a character of the additivized multiplicative cube. -/
noncomputable def signMonomialChar (S : Finset (Fin n)) :
    AddChar (Additive ({−1,1}^[n])) ℝ where
  toFun x := monomial S x.toMul
  map_zero_eq_one' := by simp [monomial, signValue]
  map_add_eq_mul' x y := by
    simp [monomial, signValue, Finset.prod_mul_distrib]

/-- The subset parameterization of sign-cube monomial characters is injective. -/
theorem signMonomialChar_injective : Function.Injective
    (signMonomialChar : Finset (Fin n) → AddChar (Additive ({−1,1}^[n])) ℝ) := by
  classical
  intro S T h
  ext i
  have hi := congrArg
    (fun ψ : AddChar (Additive ({−1,1}^[n])) ℝ ↦
      ψ (.ofMul (fun j ↦ if j = i then -1 else 1))) h
  have hv (j : Fin n) : signValue (if j = i then -1 else 1) =
      if j = i then (-1 : ℝ) else 1 := by
    split_ifs <;> simp
  have hi' : (if i ∈ S then (-1 : ℝ) else 1) = if i ∈ T then -1 else 1 := by
    simpa [signMonomialChar, monomial, hv, Finset.prod_ite_eq'] using hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT] at hi' ⊢ <;> norm_num at hi'

/-- Orthogonality of sign-cube monomials, delegated to Mathlib's finite-character theorem. -/
theorem expect_monomial_mul (S T : Finset (Fin n)) :
    (𝔼 x : {−1,1}^[n], monomial S x * monomial T x) = if S = T then 1 else 0 := by
  have hreindex : (𝔼 x : {−1,1}^[n], monomial S x * monomial T x) =
      RCLike.wInner RCLike.cWeight (signMonomialChar S) (signMonomialChar T) := by
    rw [RCLike.wInner_cWeight_eq_expect]
    symm
    apply Fintype.expect_equiv Additive.toMul
    intro x
    simp [RCLike.inner_apply, signMonomialChar, mul_comm]
  rw [hreindex]
  simpa [signMonomialChar_injective.eq_iff] using
    (AddChar.wInner_cWeight_eq_boole (signMonomialChar S) (signMonomialChar T))

/-- The `𝔽₂`-linear sum of the coordinates indexed by `S`. -/
def coordinateSum (S : Finset (Fin n)) : 𝔽₂^[n] →+ 𝔽₂ where
  toFun x := ∑ i ∈ S, x i
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

/-- The basic encoding `χ(0)=1`, `χ(1)=-1`. -/
noncomputable def binarySign : AddChar 𝔽₂ ℝ :=
  AddChar.zmodChar 2 (by norm_num : (-1 : ℝ) ^ 2 = 1)

/-- O'Donnell, Definition 1.2: the parity character `χₛ : 𝔽₂ⁿ → ℝ`. -/
noncomputable def χ (S : Finset (Fin n)) : AddChar 𝔽₂^[n] ℝ :=
  binarySign.compAddMonoidHom (coordinateSum S)

/-- O'Donnell, equation (1.5): parity characters turn addition into multiplication. -/
theorem χ_add (S : Finset (Fin n)) (x y : 𝔽₂^[n]) :
    χ S (x + y) = χ S x * χ S y := by
  exact AddChar.map_add_eq_mul (χ S) x y

/-- The uniform coefficient `f̂(S)` of a real-valued function on the sign cube. -/
noncomputable def fourierCoeff (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝔼 x, f x * monomial S x

/-- The indicator interpolation polynomial expanded in the squarefree monomial family. -/
theorem indicatorPolynomial_fourier_sum (a x : {−1,1}^[n]) :
    indicatorPolynomial a x =
      (Fintype.card ({−1,1}^[n]) : ℝ)⁻¹ * ∑ S, monomial S a * monomial S x := by
  classical
  rw [indicatorPolynomial]
  calc
    (∏ i, (1 + signValue (a i) * signValue (x i)) / 2) =
        ∏ i, (2 : ℝ)⁻¹ * (signValue (a i) * signValue (x i) + 1) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = (∏ _i : Fin n, (2 : ℝ)⁻¹) *
        ∏ i, (signValue (a i) * signValue (x i) + 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (Fintype.card ({−1,1}^[n]) : ℝ)⁻¹ *
        ∏ i, (signValue (a i) * signValue (x i) + 1) := by
      congr 1
      simp [Fintype.card_units_int]
    _ = (Fintype.card ({−1,1}^[n]) : ℝ)⁻¹ *
        ∑ S, monomial S a * monomial S x := by
      rw [Fintype.prod_add (fun i ↦ signValue (a i) * signValue (x i)) (fun _ ↦ 1)]
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      simp [monomial, Finset.prod_mul_distrib]

/-- The Fourier expansion obtained by inserting the monomial expansion of every point indicator. -/
theorem fourier_expansion_from_interpolation (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    f x = ∑ S, fourierCoeff f S * monomial S x := by
  classical
  let c : ℝ := (Fintype.card ({−1,1}^[n]) : ℝ)⁻¹
  calc
    f x = ∑ a, f a * indicatorPolynomial a x := sum_indicatorPolynomial f x
    _ = ∑ a, f a * (c * ∑ S, monomial S a * monomial S x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [indicatorPolynomial_fourier_sum]
    _ = ∑ a, ∑ S, (c * (f a * monomial S a)) * monomial S x := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ S, ∑ a, (c * (f a * monomial S a)) * monomial S x := by
      rw [Finset.sum_comm]
    _ = ∑ S, (c * ∑ a, f a * monomial S a) * monomial S x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ S, fourierCoeff f S * monomial S x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [fourierCoeff, Fintype.expect_eq_sum_div_card, div_eq_inv_mul]

/-- The multilinear polynomial with coefficient function `a`, evaluated at `x`. -/
def multilinearPolynomial (a : Finset (Fin n) → ℝ) (x : {−1,1}^[n]) : ℝ :=
  ∑ S, a S * monomial S x

/-- O'Donnell, Theorem 1.1: every real-valued function on `{-1,1}ⁿ` has a unique multilinear
expansion. -/
theorem fourier_expansion_unique (f : {−1,1}^[n] → ℝ) :
    (∀ x, f x = multilinearPolynomial (fourierCoeff f) x) ∧
      ∀ a : Finset (Fin n) → ℝ,
        (∀ x, f x = multilinearPolynomial a x) → a = fourierCoeff f := by
  classical
  constructor
  · intro x
    simpa [multilinearPolynomial] using fourier_expansion_from_interpolation f x
  · intro a ha
    funext T
    have hcoeff : fourierCoeff f T = a T := by
      rw [fourierCoeff]
      calc
        (𝔼 x, f x * monomial T x) =
            𝔼 x, (∑ S, a S * monomial S x) * monomial T x := by
          apply Finset.expect_congr rfl
          intro x _
          rw [ha x, multilinearPolynomial]
        _ = 𝔼 x, ∑ S, (a S * monomial S x) * monomial T x := by
          congr 1
          funext x
          rw [Finset.sum_mul]
        _ = ∑ S, 𝔼 x, (a S * monomial S x) * monomial T x := by
          rw [Finset.expect_sum_comm]
        _ = ∑ S, a S * (if S = T then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [← expect_monomial_mul S T, Finset.mul_expect]
          apply Finset.expect_congr rfl
          intro x _
          ring
        _ = a T := by simp
    exact hcoeff.symm

/-- The expansion identity from O'Donnell, Theorem 1.1. -/
theorem fourier_expansion (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    f x = ∑ S, fourierCoeff f S * monomial S x := by
  simpa [multilinearPolynomial] using (fourier_expansion_unique f).1 x

end FABL
