/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Mathlib

/-!
# Functions as multilinear polynomials

Book items: Definition 1.2, Theorem 1.1, Exercise 1.10, Exercise 1.11(b).

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

/-- Exercise 1.10: the finite support of the multilinear Fourier expansion. -/
noncomputable def fourierSupport (f : {−1,1}^[n] → ℝ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun S ↦ fourierCoeff f S ≠ 0

/-- Exercise 1.10: the real degree is the largest cardinality in the Fourier support.

The zero function has degree zero; this extends the book's definition, which is stated only for
functions that are not identically zero. -/
noncomputable def fourierDegree (f : {−1,1}^[n] → ℝ) : ℕ :=
  (fourierSupport f).sup Finset.card

/-- Membership in the Fourier support is nonvanishing of the corresponding coefficient. -/
@[simp] theorem mem_fourierSupport (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    S ∈ fourierSupport f ↔ fourierCoeff f S ≠ 0 := by
  classical
  simp [fourierSupport]

/-- A function has Fourier degree at most `k` exactly when every coefficient above `k`
vanishes. -/
theorem fourierDegree_le_iff (f : {−1,1}^[n] → ℝ) (k : ℕ) :
    fourierDegree f ≤ k ↔
      ∀ S : Finset (Fin n), k < S.card → fourierCoeff f S = 0 := by
  classical
  constructor
  · intro hdegree S hcard
    by_contra hcoeff
    have hmem : S ∈ fourierSupport f := (mem_fourierSupport f S).2 hcoeff
    have hle : S.card ≤ fourierDegree f := by
      exact Finset.le_sup hmem
    omega
  · intro hcoeff
    rw [fourierDegree]
    apply Finset.sup_le
    intro S hS
    by_contra hcard
    have hkS : k < S.card := by omega
    exact (mem_fourierSupport f S).1 hS (hcoeff S hkS)

/-- Every function on the `n`-dimensional sign cube has Fourier degree at most `n`. -/
theorem fourierDegree_le_dimension (f : {−1,1}^[n] → ℝ) :
    fourierDegree f ≤ n := by
  rw [fourierDegree_le_iff]
  intro S hS
  have : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

/-- Exercise 1.11(b): a Fourier transform is `ε`-granular when every coefficient is an integer
multiple of `ε`. -/
def IsFourierGranular (f : {−1,1}^[n] → ℝ) (ε : ℝ) : Prop :=
  ∀ S : Finset (Fin n), ∃ z : ℤ, fourierCoeff f S = (z : ℝ) * ε

/-! The private finite-index API below is used only for the proof of Exercise 1.11(b). -/

private def granularityIndexedMonomial {ι : Type*}
    (S : Finset ι) (x : ι → Sign) : ℝ :=
  ∏ i ∈ S, signValue (x i)

private noncomputable def granularitySignMonomialChar {ι : Type*} (S : Finset ι) :
    AddChar (Additive (ι → Sign)) ℝ where
  toFun x := granularityIndexedMonomial S x.toMul
  map_zero_eq_one' := by simp [granularityIndexedMonomial, signValue]
  map_add_eq_mul' x y := by
    simp [granularityIndexedMonomial, signValue, Finset.prod_mul_distrib]

private theorem granularitySignMonomialChar_injective {ι : Type*} : Function.Injective
    (granularitySignMonomialChar : Finset ι → AddChar (Additive (ι → Sign)) ℝ) := by
  classical
  intro S T h
  ext i
  have hi := congrArg
    (fun ψ : AddChar (Additive (ι → Sign)) ℝ ↦
      ψ (.ofMul (fun j ↦ if j = i then -1 else 1))) h
  have hv (j : ι) : signValue (if j = i then -1 else 1) =
      if j = i then (-1 : ℝ) else 1 := by
    split_ifs <;> simp
  have hi' : (if i ∈ S then (-1 : ℝ) else 1) = if i ∈ T then -1 else 1 := by
    simpa [granularitySignMonomialChar, granularityIndexedMonomial, hv,
      Finset.prod_ite_eq'] using hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT] at hi' ⊢ <;> norm_num at hi'

private theorem expect_granularityIndexedMonomial_mul {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S T : Finset ι) :
    (𝔼 x : ι → Sign,
      granularityIndexedMonomial S x * granularityIndexedMonomial T x) =
      if S = T then 1 else 0 := by
  have hreindex :
      (𝔼 x : ι → Sign,
        granularityIndexedMonomial S x * granularityIndexedMonomial T x) =
        RCLike.wInner RCLike.cWeight
          (granularitySignMonomialChar S) (granularitySignMonomialChar T) := by
    rw [RCLike.wInner_cWeight_eq_expect]
    symm
    apply Fintype.expect_equiv Additive.toMul
    intro x
    simp [RCLike.inner_apply, granularitySignMonomialChar, mul_comm]
  rw [hreindex]
  simpa [granularitySignMonomialChar_injective.eq_iff] using
    (AddChar.wInner_cWeight_eq_boole
      (granularitySignMonomialChar S) (granularitySignMonomialChar T))

private noncomputable def granularityExtendAtOne (J : Finset (Fin n))
    (y : J → Sign) : {−1,1}^[n] := by
  classical
  exact fun i ↦ if h : i ∈ J then y ⟨i, h⟩ else 1

private noncomputable def granularityFrequencyWithin
    (J U : Finset (Fin n)) : Finset J := by
  classical
  exact Finset.univ.filter fun i : J ↦ i.1 ∈ U

@[simp] private theorem mem_granularityFrequencyWithin
    (J U : Finset (Fin n)) (i : J) :
    i ∈ granularityFrequencyWithin J U ↔ i.1 ∈ U := by
  classical
  simp [granularityFrequencyWithin]

private theorem granularityFrequencyWithin_eq_univ_iff
    (J U : Finset (Fin n)) :
    granularityFrequencyWithin J U = Finset.univ ↔ J ⊆ U := by
  classical
  constructor
  · intro h i hi
    let j : J := ⟨i, hi⟩
    have hj : j ∈ granularityFrequencyWithin J U := by
      rw [h]
      exact Finset.mem_univ j
    exact (mem_granularityFrequencyWithin J U j).1 hj
  · intro h
    ext i
    simp [h i.property]

private theorem monomial_granularityExtendAtOne
    (J U : Finset (Fin n)) (y : J → Sign) :
    monomial U (granularityExtendAtOne J y) =
      granularityIndexedMonomial (granularityFrequencyWithin J U) y := by
  classical
  have hreduce :
      (∏ i ∈ U ∩ J, signValue (granularityExtendAtOne J y i)) =
        ∏ i ∈ U, signValue (granularityExtendAtOne J y i) := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro i hiU hiNot
    have hiJ : i ∉ J := by
      intro hiJ
      exact hiNot (Finset.mem_inter.mpr ⟨hiU, hiJ⟩)
    simp [granularityExtendAtOne, hiJ]
  have hreindex :
      (∏ i ∈ granularityFrequencyWithin J U, signValue (y i)) =
        ∏ i ∈ U ∩ J, signValue (granularityExtendAtOne J y i) := by
    apply Finset.prod_bij (fun i _ ↦ i.1)
    · intro i hi
      exact Finset.mem_inter.mpr
        ⟨(mem_granularityFrequencyWithin J U i).1 hi, i.property⟩
    · intro i₁ _ i₂ _ h
      exact Subtype.ext h
    · intro i hi
      refine ⟨⟨i, (Finset.mem_inter.mp hi).2⟩, ?_, rfl⟩
      exact (mem_granularityFrequencyWithin J U _).2 (Finset.mem_inter.mp hi).1
    · intro i _
      simp [granularityExtendAtOne, i.property]
  unfold monomial granularityIndexedMonomial
  exact hreduce.symm.trans hreindex.symm

private noncomputable def granularityRestrictionTopCoeff
    (f : {−1,1}^[n] → Sign) (J : Finset (Fin n)) : ℝ :=
  𝔼 y : J → Sign,
    signValue (f (granularityExtendAtOne J y)) *
      granularityIndexedMonomial Finset.univ y

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

private theorem granularityRestrictionTopCoeff_eq_sum_supersets
    (f : {−1,1}^[n] → Sign) (J : Finset (Fin n)) :
    granularityRestrictionTopCoeff f J =
      ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ J ⊆ U),
        fourierCoeff (fun x ↦ signValue (f x)) U := by
  classical
  unfold granularityRestrictionTopCoeff
  calc
    (𝔼 y : J → Sign,
        signValue (f (granularityExtendAtOne J y)) *
          granularityIndexedMonomial Finset.univ y) =
        𝔼 y : J → Sign,
          (∑ U, fourierCoeff (fun x ↦ signValue (f x)) U *
            monomial U (granularityExtendAtOne J y)) *
              granularityIndexedMonomial Finset.univ y := by
      apply Finset.expect_congr rfl
      intro y _
      rw [← fourier_expansion_from_interpolation
        (fun x ↦ signValue (f x)) (granularityExtendAtOne J y)]
    _ = 𝔼 y : J → Sign, ∑ U,
          (fourierCoeff (fun x ↦ signValue (f x)) U *
            granularityIndexedMonomial (granularityFrequencyWithin J U) y) *
              granularityIndexedMonomial Finset.univ y := by
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      rw [monomial_granularityExtendAtOne]
    _ = ∑ U, 𝔼 y : J → Sign,
          (fourierCoeff (fun x ↦ signValue (f x)) U *
            granularityIndexedMonomial (granularityFrequencyWithin J U) y) *
              granularityIndexedMonomial Finset.univ y := by
      rw [Finset.expect_sum_comm]
    _ = ∑ U, fourierCoeff (fun x ↦ signValue (f x)) U *
          (if granularityFrequencyWithin J U = Finset.univ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro U _
      simp_rw [mul_assoc]
      rw [← Finset.mul_expect,
        expect_granularityIndexedMonomial_mul]
    _ = ∑ U, if J ⊆ U then
          fourierCoeff (fun x ↦ signValue (f x)) U else 0 := by
      apply Finset.sum_congr rfl
      intro U _
      by_cases hJU : J ⊆ U
      · rw [if_pos ((granularityFrequencyWithin_eq_univ_iff J U).2 hJU), if_pos hJU]
        simp
      · have hfrequency : granularityFrequencyWithin J U ≠ Finset.univ :=
          fun h ↦ hJU ((granularityFrequencyWithin_eq_univ_iff J U).1 h)
        rw [if_neg hfrequency, if_neg hJU]
        simp
    _ = ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ J ⊆ U),
          fourierCoeff (fun x ↦ signValue (f x)) U := by
      rw [Finset.sum_filter]

private theorem expect_sign_values_eq_int_mul_two_inv_pow
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → ℝ) (hg : ∀ x, g x = -1 ∨ g x = 1)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card Ω = 2 ^ m) :
    ∃ z : ℤ, (𝔼 x, g x) = (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ m) := by
  classical
  let N : ℕ := (Finset.univ.filter fun x : Ω ↦ g x = -1).card
  have hpoint (x : Ω) :
      g x = 1 - 2 * (if g x = -1 then (1 : ℝ) else 0) := by
    rcases hg x with hx | hx <;> rw [hx] <;> norm_num
  have hsum : (∑ x, g x) = (Fintype.card Ω : ℝ) - 2 * (N : ℝ) := by
    calc
      (∑ x, g x) = ∑ x, (1 - 2 * (if g x = -1 then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = (∑ _x : Ω, (1 : ℝ)) -
          2 * ∑ x : Ω, (if g x = -1 then (1 : ℝ) else 0) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (Fintype.card Ω : ℝ) - 2 * (N : ℝ) := by
        simp [N]
  have hscale : 2 * ((2 : ℝ)⁻¹) ^ m = ((2 : ℝ) ^ (m - 1))⁻¹ := by
    rw [show m = m - 1 + 1 by omega, pow_succ, inv_pow]
    norm_num
    field_simp
  refine ⟨(2 ^ (m - 1) : ℤ) - (N : ℤ), ?_⟩
  rw [Fintype.expect_eq_sum_div_card, hsum, hcard, hscale]
  rw [show m = m - 1 + 1 by omega, pow_succ]
  push_cast
  field_simp

private theorem granularityRestrictionTopCoeff_eq_int_mul_two_inv_pow_of_nonempty
    (f : {−1,1}^[n] → Sign) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    ∃ z : ℤ, granularityRestrictionTopCoeff f J =
      (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ J.card) := by
  apply expect_sign_values_eq_int_mul_two_inv_pow
  · intro y
    have hvalue :
        signValue (f (granularityExtendAtOne J y)) *
            granularityIndexedMonomial Finset.univ y =
          signValue (f (granularityExtendAtOne J y) * ∏ i, y i) := by
      simp [granularityIndexedMonomial, signValue]
    rw [hvalue]
    exact signValue_eq_neg_one_or_one _
  · exact Finset.card_pos.mpr hJ
  · simp [Fintype.card_units_int]

private theorem granularityRestrictionTopCoeff_eq_int_mul_global_scale
    (f : {−1,1}^[n] → Sign) (J : Finset (Fin n)) {k : ℕ}
    (hk : 1 ≤ k) (hJk : J.card ≤ k) :
    ∃ z : ℤ, granularityRestrictionTopCoeff f J =
      (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) := by
  classical
  by_cases hJ : J = ∅
  · subst J
    have hext (y : (∅ : Finset (Fin n)) → Sign) :
        granularityExtendAtOne ∅ y = fun _ ↦ 1 := by
      funext i
      simp [granularityExtendAtOne]
    have htop : granularityRestrictionTopCoeff f ∅ =
        signValue (f (fun _ ↦ 1)) := by
      unfold granularityRestrictionTopCoeff
      simp [granularityIndexedMonomial, hext]
    have hunit : (((2 ^ (k - 1) : ℤ) : ℝ) *
        (2 * ((2 : ℝ)⁻¹) ^ k)) = 1 := by
      push_cast
      rw [show k = k - 1 + 1 by omega, pow_succ, inv_pow]
      norm_num
      field_simp
    rcases signValue_eq_neg_one_or_one (f (fun _ ↦ 1)) with hvalue | hvalue
    · refine ⟨-(2 ^ (k - 1) : ℤ), ?_⟩
      rw [htop, hvalue, Int.cast_neg]
      nlinarith
    · refine ⟨(2 ^ (k - 1) : ℤ), ?_⟩
      rw [htop, hvalue]
      exact hunit.symm
  · obtain ⟨z, hz⟩ :=
      granularityRestrictionTopCoeff_eq_int_mul_two_inv_pow_of_nonempty f J
        (Finset.nonempty_iff_ne_empty.mpr hJ)
    have hscale : 2 * ((2 : ℝ)⁻¹) ^ J.card =
        (((2 ^ (k - J.card) : ℤ) : ℝ) *
          (2 * ((2 : ℝ)⁻¹) ^ k)) := by
      push_cast
      rw [show k = J.card + (k - J.card) by omega, pow_add, inv_pow]
      field_simp
      rw [show J.card + (k - J.card) - J.card = k - J.card by omega,
        ← mul_pow]
      norm_num
    refine ⟨z * (2 ^ (k - J.card) : ℤ), ?_⟩
    rw [hz, hscale, Int.cast_mul]
    ring

private theorem fourierCoeff_eq_int_mul_global_scale_of_card_le
    (f : {−1,1}^[n] → Sign) {k : ℕ} (hk : 1 ≤ k)
    (hdegree : fourierDegree (fun x ↦ signValue (f x)) ≤ k)
    (S : Finset (Fin n)) (hSk : S.card ≤ k) :
    ∃ z : ℤ, fourierCoeff (fun x ↦ signValue (f x)) S =
      (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) := by
  generalize hd : k - S.card = d
  induction d using Nat.strong_induction_on generalizing S with
  | h d ih =>
      classical
      let A : Finset (Finset (Fin n)) :=
        Finset.univ.filter fun U : Finset (Fin n) ↦ S ⊆ U
      have hS : S ∈ A := by
        simp [A]
      have hid : granularityRestrictionTopCoeff f S =
          ∑ U ∈ A, fourierCoeff (fun x ↦ signValue (f x)) U := by
        simpa [A] using granularityRestrictionTopCoeff_eq_sum_supersets f S
      have hsplit :
          (∑ U ∈ A, fourierCoeff (fun x ↦ signValue (f x)) U) =
            fourierCoeff (fun x ↦ signValue (f x)) S +
              ∑ U ∈ A.erase S, fourierCoeff (fun x ↦ signValue (f x)) U := by
        calc
          (∑ U ∈ A, fourierCoeff (fun x ↦ signValue (f x)) U) =
              (∑ U ∈ A.erase S, fourierCoeff (fun x ↦ signValue (f x)) U) +
                fourierCoeff (fun x ↦ signValue (f x)) S := by
            exact (Finset.sum_erase_add A _ hS).symm
          _ = fourierCoeff (fun x ↦ signValue (f x)) S +
                ∑ U ∈ A.erase S, fourierCoeff (fun x ↦ signValue (f x)) U := by
            rw [add_comm]
      have hdecomp : granularityRestrictionTopCoeff f S =
          fourierCoeff (fun x ↦ signValue (f x)) S +
            ∑ U ∈ A.erase S, fourierCoeff (fun x ↦ signValue (f x)) U :=
        hid.trans hsplit
      obtain ⟨z₀, hz₀⟩ :=
        granularityRestrictionTopCoeff_eq_int_mul_global_scale f S hk hSk
      have hterm (U : Finset (Fin n)) (hU : U ∈ A.erase S) :
          ∃ z : ℤ, fourierCoeff (fun x ↦ signValue (f x)) U =
            (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) := by
        have hUS : U ≠ S := (Finset.mem_erase.mp hU).1
        have hsub : S ⊆ U := (Finset.mem_filter.mp (Finset.mem_erase.mp hU).2).2
        by_cases hUk : U.card ≤ k
        · have hstrict : S ⊂ U :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hUS⟩
          have hcard : S.card < U.card := Finset.card_lt_card hstrict
          have hdiff : k - U.card < d := by
            rw [← hd]
            omega
          exact ih (k - U.card) hdiff U hUk rfl
        · have hzero := (fourierDegree_le_iff (fun x ↦ signValue (f x)) k).1
              hdegree U (lt_of_not_ge hUk)
          exact ⟨0, by simp [hzero]⟩
      let z : Finset (Fin n) → ℤ := fun U ↦
        if hU : U ∈ A.erase S then Classical.choose (hterm U hU) else 0
      have hz (U : Finset (Fin n)) (hU : U ∈ A.erase S) :
          fourierCoeff (fun x ↦ signValue (f x)) U =
            (z U : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) := by
        simp only [z, dif_pos hU]
        exact Classical.choose_spec (hterm U hU)
      refine ⟨z₀ - ∑ U ∈ A.erase S, z U, ?_⟩
      calc
        fourierCoeff (fun x ↦ signValue (f x)) S =
            granularityRestrictionTopCoeff f S -
              ∑ U ∈ A.erase S, fourierCoeff (fun x ↦ signValue (f x)) U := by
          rw [hdecomp]
          ring
        _ = (z₀ : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) -
              ∑ U ∈ A.erase S, (z U : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ k) := by
          rw [hz₀]
          congr 1
          apply Finset.sum_congr rfl
          intro U hU
          exact hz U hU
        _ = ((z₀ - ∑ U ∈ A.erase S, z U : ℤ) : ℝ) *
              (2 * ((2 : ℝ)⁻¹) ^ k) := by
          rw [← Finset.sum_mul]
          push_cast
          ring

/-- O'Donnell, Exercise 1.11(b): if a sign-valued function has Fourier degree at most
`k ≥ 1`, every Fourier coefficient of its real encoding is an integer multiple of
`2^(1-k) = 2 * (2⁻¹)^k`.

This is stated directly for `SignCube n → Sign` to preserve the Chapter 1 import order;
`BooleanFunction.toReal` is definitionally the real encoding used here. -/
theorem isFourierGranular_signValue_of_fourierDegree_le
    (f : {−1,1}^[n] → Sign) {k : ℕ} (hk : 1 ≤ k)
    (hdegree : fourierDegree (fun x ↦ signValue (f x)) ≤ k) :
    IsFourierGranular (fun x ↦ signValue (f x)) (2 * ((2 : ℝ)⁻¹) ^ k) := by
  intro S
  by_cases hSk : S.card ≤ k
  · exact fourierCoeff_eq_int_mul_global_scale_of_card_le f hk hdegree S hSk
  · have hzero := (fourierDegree_le_iff (fun x ↦ signValue (f x)) k).1
        hdegree S (lt_of_not_ge hSk)
    exact ⟨0, by simp [hzero]⟩

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
