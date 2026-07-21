/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree
public import FABL.Chapter06.F₂Polynomials.Encoding

/-!
# The Fourier-to-`𝔽₂` polynomial bridge

Book support for Proposition 6.23: under the coordinate change `zᵢ = 1 - 2xᵢ`, the real Fourier
polynomial `p` becomes a real multilinear polynomial of the same degree on the binary cube.  For a
Boolean function, the affine output change `q = (1 - p) / 2` has integral coefficients, and their
reductions modulo two are the canonical algebraic-normal-form coefficients.

The numerical support and degree declarations in this module are general Chapter 6 infrastructure
for this bridge.  They are not specific to Carlet's spectral-support results.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The nonzero coefficient support of a numerical normal form. -/
noncomputable def numericalSupport (c : NumericalCoefficients n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ c S ≠ 0

/-- Membership in numerical support is nonvanishing of the corresponding coefficient. -/
@[simp] theorem mem_numericalSupport (c : NumericalCoefficients n)
    (S : Finset (Fin n)) :
    S ∈ numericalSupport c ↔ c S ≠ 0 := by
  classical
  simp [numericalSupport]

/-- The degree of a numerical normal form, with degree zero for the zero form. -/
noncomputable def numericalDegree (c : NumericalCoefficients n) : ℕ :=
  (numericalSupport c).sup Finset.card

/-- Numerical degree at most `D` is coefficientwise vanishing above `D`. -/
theorem numericalDegree_le_iff (c : NumericalCoefficients n) (D : ℕ) :
    numericalDegree c ≤ D ↔ ∀ S, c S ≠ 0 → S.card ≤ D := by
  classical
  rw [numericalDegree, Finset.sup_le_iff]
  constructor
  · intro h S hS
    exact h S (by simpa using hS)
  · intro h S hS
    exact h S (by simpa using hS)

/-- The numerical degree of a pseudo-Boolean function is the degree of its unique NNF. -/
noncomputable def functionNumericalDegree (φ : PseudoBooleanFunction n) : ℕ :=
  numericalDegree (numericalCoeff φ)

/-- The coefficient transform induced by substituting `zᵢ = 1 - 2xᵢ` into the Fourier
expansion of `p`. -/
noncomputable def fourierSubstitutionCoeff
    (p : {−1,1}^[n] → ℝ) : NumericalCoefficients n :=
  fun T ↦
    (-2 : ℝ) ^ T.card *
      ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ T ⊆ S), fourierCoeff p S

/-- The binary-cube function obtained by the coordinate substitution `zᵢ = 1 - 2xᵢ`. -/
def fourierSubstitution (p : {−1,1}^[n] → ℝ) : PseudoBooleanFunction n :=
  fun x ↦ p (binaryCubeSignEquiv n x)

/-- The polynomial `q(x) = 1/2 - p(1 - 2x)/2` on the binary cube. -/
noncomputable def fourierToF₂Polynomial
    (p : {−1,1}^[n] → ℝ) : PseudoBooleanFunction n :=
  fun x ↦ (1 - p (binaryCubeSignEquiv n x)) / 2

/-- The coefficient family obtained from the substituted Fourier polynomial by the affine output
change `q = (1 - p) / 2`. -/
noncomputable def fourierToF₂Coeff
    (p : {−1,1}^[n] → ℝ) : NumericalCoefficients n :=
  fun T ↦
    ((if T = ∅ then 1 else 0) - fourierSubstitutionCoeff p T) / 2

/-- A binary coordinate becomes `1 - 2xᵢ` under the standard sign encoding. -/
theorem signValue_binaryCubeSignEquiv_eq_one_sub_two
    (x : F₂Cube n) (i : Fin n) :
    signValue (binaryCubeSignEquiv n x i) =
      1 - 2 * numericalMonomial {i} x := by
  by_cases hxi : x i = 0
  · simp [binaryCubeSignEquiv_apply, numericalMonomial, hxi]
  · have hxi_one : x i = 1 := Fin.eq_one_of_ne_zero _ hxi
    simp [binaryCubeSignEquiv_apply, numericalMonomial, hxi_one]
    norm_num

/-- Expanding a sign monomial after `zᵢ = 1 - 2xᵢ` gives the corresponding Boolean-lattice
sum of numerical monomials. -/
theorem monomial_binaryCubeSignEquiv_eq_numerical_sum
    (S : Finset (Fin n)) (x : F₂Cube n) :
    monomial S (binaryCubeSignEquiv n x) =
      ∑ T ∈ S.powerset,
        (-2 : ℝ) ^ T.card * numericalMonomial T x := by
  classical
  rw [monomial]
  calc
    (∏ i ∈ S, signValue (binaryCubeSignEquiv n x i)) =
        ∏ i ∈ S,
          ((-2 : ℝ) * (if x i = 1 then 1 else 0) + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [signValue_binaryCubeSignEquiv_eq_one_sub_two]
      simp only [numericalMonomial, Finset.prod_singleton]
      ring
    _ = ∑ T ∈ S.powerset,
        (∏ i ∈ T, (-2 : ℝ) * (if x i = 1 then 1 else 0)) *
          ∏ _i ∈ S \ T, (1 : ℝ) := by
      rw [Finset.prod_add]
    _ = ∑ T ∈ S.powerset,
        (-2 : ℝ) ^ T.card * numericalMonomial T x := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.prod_const_one, mul_one]
      rw [Finset.prod_mul_distrib]
      simp [numericalMonomial]

/-- The transformed Fourier coefficients evaluate to the coordinate-substituted function. -/
theorem numericalEval_fourierSubstitutionCoeff
    (p : {−1,1}^[n] → ℝ) :
    numericalEval (fourierSubstitutionCoeff p) = fourierSubstitution p := by
  classical
  funext x
  rw [fourierSubstitution, fourier_expansion p (binaryCubeSignEquiv n x),
    numericalEval]
  symm
  simp_rw [monomial_binaryCubeSignEquiv_eq_numerical_sum]
  calc
    (∑ S : Finset (Fin n), fourierCoeff p S *
        ∑ T ∈ S.powerset,
          (-2 : ℝ) ^ T.card * numericalMonomial T x) =
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          if T ⊆ S then
            fourierCoeff p S *
              ((-2 : ℝ) ^ T.card * numericalMonomial T x)
          else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mul_sum]
      calc
        (∑ T ∈ S.powerset,
            fourierCoeff p S *
              ((-2 : ℝ) ^ T.card * numericalMonomial T x)) =
            ∑ T ∈ (Finset.univ.filter
              fun T : Finset (Fin n) ↦ T ⊆ S),
              fourierCoeff p S *
                ((-2 : ℝ) ^ T.card * numericalMonomial T x) := by
          apply Finset.sum_congr
          · ext T
            simp [Finset.mem_powerset]
          · intro T hT
            rfl
        _ = ∑ T : Finset (Fin n),
            if T ⊆ S then
              fourierCoeff p S *
                ((-2 : ℝ) ^ T.card * numericalMonomial T x)
            else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ T : Finset (Fin n), ∑ S : Finset (Fin n),
          if T ⊆ S then
            fourierCoeff p S *
              ((-2 : ℝ) ^ T.card * numericalMonomial T x)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ T : Finset (Fin n),
        fourierSubstitutionCoeff p T * numericalMonomial T x := by
      apply Finset.sum_congr rfl
      intro T hT
      calc
        (∑ S : Finset (Fin n),
            if T ⊆ S then
              fourierCoeff p S *
                ((-2 : ℝ) ^ T.card * numericalMonomial T x)
            else 0) =
            ∑ S ∈ (Finset.univ.filter
              fun S : Finset (Fin n) ↦ T ⊆ S),
              fourierCoeff p S *
                ((-2 : ℝ) ^ T.card * numericalMonomial T x) := by
          rw [Finset.sum_filter]
        _ = (∑ S ∈ (Finset.univ.filter
              fun S : Finset (Fin n) ↦ T ⊆ S),
              fourierCoeff p S) *
                ((-2 : ℝ) ^ T.card * numericalMonomial T x) := by
          rw [Finset.sum_mul]
        _ = fourierSubstitutionCoeff p T * numericalMonomial T x := by
          rw [fourierSubstitutionCoeff]
          ring

/-- The explicit substitution coefficients are the canonical numerical coefficients. -/
theorem numericalCoeff_fourierSubstitution
    (p : {−1,1}^[n] → ℝ) :
    numericalCoeff (fourierSubstitution p) = fourierSubstitutionCoeff p := by
  apply numericalEval_injective
  change numericalEval (numericalCoeff (fourierSubstitution p)) =
    numericalEval (fourierSubstitutionCoeff p)
  rw [numericalEval_numericalCoeff, numericalEval_fourierSubstitutionCoeff]

/-- The explicit `q` coefficients evaluate to `1/2 - p(1 - 2x)/2`. -/
theorem numericalEval_fourierToF₂Coeff
    (p : {−1,1}^[n] → ℝ) :
    numericalEval (fourierToF₂Coeff p) = fourierToF₂Polynomial p := by
  classical
  funext x
  rw [numericalEval, fourierToF₂Polynomial]
  calc
    (∑ T,
        fourierToF₂Coeff p T * numericalMonomial T x) =
        ∑ T,
          ((if T = ∅ then 1 else 0) * numericalMonomial T x / 2 -
            fourierSubstitutionCoeff p T * numericalMonomial T x / 2) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [fourierToF₂Coeff]
      ring
    _ = (∑ T, (if T = ∅ then 1 else 0) * numericalMonomial T x) / 2 -
        (∑ T, fourierSubstitutionCoeff p T * numericalMonomial T x) / 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    _ = (1 - numericalEval (fourierSubstitutionCoeff p) x) / 2 := by
      simp [numericalEval, numericalMonomial]
      ring
    _ = (1 - p (binaryCubeSignEquiv n x)) / 2 := by
      rw [numericalEval_fourierSubstitutionCoeff]
      rfl

/-- The explicit `q` coefficients are its canonical numerical-normal-form coefficients. -/
theorem numericalCoeff_fourierToF₂Polynomial
    (p : {−1,1}^[n] → ℝ) :
    numericalCoeff (fourierToF₂Polynomial p) = fourierToF₂Coeff p := by
  apply numericalEval_injective
  change numericalEval (numericalCoeff (fourierToF₂Polynomial p)) =
    numericalEval (fourierToF₂Coeff p)
  rw [numericalEval_numericalCoeff, numericalEval_fourierToF₂Coeff]

/-- Pointwise Fourier-expansion form of `q(x) = 1/2 - p(1 - 2x)/2`. -/
theorem fourierToF₂Polynomial_apply_fourierExpansion
    (p : {−1,1}^[n] → ℝ) (x : F₂Cube n) :
    fourierToF₂Polynomial p x =
      (1 -
        ∑ S, fourierCoeff p S *
          ∑ T ∈ S.powerset,
            (-2 : ℝ) ^ T.card * numericalMonomial T x) / 2 := by
  rw [fourierToF₂Polynomial, fourier_expansion p (binaryCubeSignEquiv n x)]
  simp_rw [monomial_binaryCubeSignEquiv_eq_numerical_sum]

private theorem exists_top_fourierCoeff
    (p : {−1,1}^[n] → ℝ) (hdegree : fourierDegree p ≠ 0) :
    ∃ S : Finset (Fin n),
      fourierCoeff p S ≠ 0 ∧ S.card = fourierDegree p := by
  classical
  have hsupport : (fourierSupport p).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hdegree
    simp [fourierDegree, h]
  obtain ⟨S, hS, hdegreeS⟩ :=
    Finset.exists_mem_eq_sup (fourierSupport p) hsupport Finset.card
  exact ⟨S, (mem_fourierSupport p S).mp hS, hdegreeS.symm⟩

private theorem sum_fourierCoeff_supersets_eq_self_of_card_eq_degree
    (p : {−1,1}^[n] → ℝ) (S : Finset (Fin n))
    (hcard : S.card = fourierDegree p) :
    (∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ S ⊆ U),
      fourierCoeff p U) = fourierCoeff p S := by
  classical
  rw [Finset.sum_eq_single S]
  · intro U hU hUS
    have hsubset : S ⊆ U := (Finset.mem_filter.mp hU).2
    have hlt : fourierDegree p < U.card := by
      rw [← hcard]
      exact Finset.card_lt_card (hsubset.ssubset_of_ne hUS.symm)
    exact (fourierDegree_le_iff p (fourierDegree p)).mp le_rfl U hlt
  · simp

/-- The invertible coordinate substitution `zᵢ = 1 - 2xᵢ` preserves real multilinear degree. -/
theorem numericalDegree_fourierSubstitutionCoeff
    (p : {−1,1}^[n] → ℝ) :
    numericalDegree (fourierSubstitutionCoeff p) = fourierDegree p := by
  apply Nat.le_antisymm
  · rw [numericalDegree_le_iff]
    intro T hcoeff
    by_contra hcard
    have hdegreeT : fourierDegree p < T.card := by omega
    apply hcoeff
    rw [fourierSubstitutionCoeff]
    have hsum : (∑ S ∈
        (Finset.univ.filter fun S : Finset (Fin n) ↦ T ⊆ S),
        fourierCoeff p S) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hsubset : T ⊆ S := (Finset.mem_filter.mp hS).2
      have hdegreeS : fourierDegree p < S.card :=
        hdegreeT.trans_le (Finset.card_le_card hsubset)
      exact (fourierDegree_le_iff p (fourierDegree p)).mp le_rfl S hdegreeS
    rw [hsum, mul_zero]
  · by_cases hdegree : fourierDegree p = 0
    · simp [hdegree]
    · obtain ⟨S, hcoeff, hcard⟩ := exists_top_fourierCoeff p hdegree
      have hsum :=
        sum_fourierCoeff_supersets_eq_self_of_card_eq_degree p S hcard
      have hsubstitution : fourierSubstitutionCoeff p S ≠ 0 := by
        rw [fourierSubstitutionCoeff, hsum]
        exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcoeff
      have hle :
          S.card ≤ numericalDegree (fourierSubstitutionCoeff p) :=
        (numericalDegree_le_iff
          (fourierSubstitutionCoeff p)
          (numericalDegree (fourierSubstitutionCoeff p))).mp
          le_rfl S hsubstitution
      simpa [hcard] using hle

/-- Function-level form of degree preservation for the coordinate substitution. -/
theorem functionNumericalDegree_fourierSubstitution
    (p : {−1,1}^[n] → ℝ) :
    functionNumericalDegree (fourierSubstitution p) = fourierDegree p := by
  rw [functionNumericalDegree, numericalCoeff_fourierSubstitution,
    numericalDegree_fourierSubstitutionCoeff]

/-- With the total natural-number convention assigning degree zero to the zero polynomial,
`q = (1 - p(1 - 2x))/2` has the same degree as `p`, including the exceptional case `p = 1`. -/
theorem numericalDegree_fourierToF₂Coeff
    (p : {−1,1}^[n] → ℝ) :
    numericalDegree (fourierToF₂Coeff p) = fourierDegree p := by
  apply Nat.le_antisymm
  · rw [numericalDegree_le_iff]
    intro T hcoeff
    by_contra hcard
    have hdegreeT : fourierDegree p < T.card := by omega
    have hsubstitution : fourierSubstitutionCoeff p T = 0 := by
      by_contra hne
      have hle :
          T.card ≤ numericalDegree (fourierSubstitutionCoeff p) :=
        (numericalDegree_le_iff
          (fourierSubstitutionCoeff p)
          (numericalDegree (fourierSubstitutionCoeff p))).mp le_rfl T hne
      rw [numericalDegree_fourierSubstitutionCoeff] at hle
      omega
    have hTnonempty : T ≠ ∅ := by
      intro h
      subst T
      simp at hdegreeT
    apply hcoeff
    simp [fourierToF₂Coeff, hTnonempty, hsubstitution]
  · by_cases hdegree : fourierDegree p = 0
    · simp [hdegree]
    · obtain ⟨S, hcoeff, hcard⟩ := exists_top_fourierCoeff p hdegree
      have hsum :=
        sum_fourierCoeff_supersets_eq_self_of_card_eq_degree p S hcard
      have hsubstitution : fourierSubstitutionCoeff p S ≠ 0 := by
        rw [fourierSubstitutionCoeff, hsum]
        exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcoeff
      have hS : S ≠ ∅ := by
        intro h
        subst S
        simp at hcard
        exact hdegree hcard.symm
      have hq : fourierToF₂Coeff p S ≠ 0 := by
        rw [fourierToF₂Coeff, if_neg hS]
        exact div_ne_zero (sub_ne_zero.mpr hsubstitution.symm) (by norm_num)
      have hle :
          S.card ≤ numericalDegree (fourierToF₂Coeff p) :=
        (numericalDegree_le_iff
          (fourierToF₂Coeff p)
          (numericalDegree (fourierToF₂Coeff p))).mp le_rfl S hq
      simpa [hcard] using hle

/-- Function-level degree preservation for the full affine Fourier-to-binary polynomial bridge. -/
theorem functionNumericalDegree_fourierToF₂Polynomial
    (p : {−1,1}^[n] → ℝ) :
    functionNumericalDegree (fourierToF₂Polynomial p) = fourierDegree p := by
  rw [functionNumericalDegree, numericalCoeff_fourierToF₂Polynomial,
    numericalDegree_fourierToF₂Coeff]

/-- The book's exceptional constant-one input becomes the zero polynomial. -/
@[simp] theorem fourierToF₂Polynomial_one :
    fourierToF₂Polynomial (fun _ : {−1,1}^[n] ↦ 1) = 0 := by
  funext x
  simp [fourierToF₂Polynomial]

/-- The integer Möbius coefficient of a `{0,1}`-valued Boolean embedding. -/
noncomputable def booleanNumericalCoeffInt
    (f : F₂BooleanFunction n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset,
    (-1 : ℤ) ^ (S.card - T.card) *
      if f (f₂CubeOfFinset T) = 1 then 1 else 0

/-- The numerical coefficients of a Boolean embedding are integers. -/
theorem numericalCoeff_booleanRealEmbedding_eq_intCast
    (f : F₂BooleanFunction n) (S : Finset (Fin n)) :
    numericalCoeff (booleanRealEmbedding f) S =
      (booleanNumericalCoeffInt f S : ℝ) := by
  classical
  rw [numericalCoeff_eq_mobius_sum, booleanNumericalCoeffInt, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Int.cast_mul, Int.cast_pow]
  by_cases h : f (f₂CubeOfFinset T) = 1
  · simp [booleanRealEmbedding, h]
  · simp [booleanRealEmbedding, h]

/-- Reducing the integral numerical coefficients modulo two gives the canonical ANF
coefficients. -/
theorem booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff
    (f : F₂BooleanFunction n) (S : Finset (Fin n)) :
    (booleanNumericalCoeffInt f S : 𝔽₂) = anfCoeff f S := by
  classical
  rw [booleanNumericalCoeffInt, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Int.cast_mul, Int.cast_pow]
  by_cases h : f (f₂CubeOfFinset T) = 1
  · simp [h]
  · have hzero : f (f₂CubeOfFinset T) = 0 := by
      by_contra hne
      exact h (Fin.eq_one_of_ne_zero _ hne)
    simp [hzero]

/-- For a sign-valued Boolean function, the Fourier-to-binary polynomial is its canonical real
`{0,1}` embedding. -/
theorem fourierToF₂Polynomial_booleanFunction
    (f : BooleanFunction n) :
    fourierToF₂Polynomial f.toReal =
      booleanRealEmbedding (booleanFunctionF₂Encoding f) := by
  funext x
  exact (booleanRealEmbedding_booleanFunctionF₂Encoding_apply f x).symm

/-- The explicit Fourier-to-`𝔽₂` coefficients of a Boolean function are integral. -/
theorem fourierToF₂Coeff_booleanFunction_eq_intCast
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierToF₂Coeff f.toReal S =
      (booleanNumericalCoeffInt (booleanFunctionF₂Encoding f) S : ℝ) := by
  calc
    fourierToF₂Coeff f.toReal S =
        numericalCoeff (fourierToF₂Polynomial f.toReal) S := by
      rw [numericalCoeff_fourierToF₂Polynomial]
    _ = numericalCoeff
        (booleanRealEmbedding (booleanFunctionF₂Encoding f)) S := by
      rw [fourierToF₂Polynomial_booleanFunction]
    _ = (booleanNumericalCoeffInt
        (booleanFunctionF₂Encoding f) S : ℝ) :=
      numericalCoeff_booleanRealEmbedding_eq_intCast
        (booleanFunctionF₂Encoding f) S

/-- Reducing an integral coefficient family modulo two cannot increase its degree. -/
theorem algebraicDegree_intCastModTwo_le_numericalDegree
    (z : Finset (Fin n) → ℤ) :
    algebraicDegree (fun S ↦ (z S : 𝔽₂)) ≤
      numericalDegree (fun S ↦ (z S : ℝ)) := by
  rw [algebraicDegree_le_iff]
  intro S hmod
  apply (numericalDegree_le_iff
    (fun S ↦ (z S : ℝ))
    (numericalDegree (fun S ↦ (z S : ℝ)))).mp le_rfl S
  intro hreal
  have hz : z S = 0 := by
    exact_mod_cast hreal
  apply hmod
  simp [hz]

/-- Coefficient reduction gives the algebraic-degree bound for a Boolean embedding. -/
theorem functionAlgebraicDegree_le_functionNumericalDegree_booleanRealEmbedding
    (f : F₂BooleanFunction n) :
    functionAlgebraicDegree f ≤
      functionNumericalDegree (booleanRealEmbedding f) := by
  rw [functionAlgebraicDegree, functionNumericalDegree]
  let z : Finset (Fin n) → ℤ := booleanNumericalCoeffInt f
  calc
    algebraicDegree (anfCoeff f) =
        algebraicDegree (fun S ↦ (z S : 𝔽₂)) := by
      congr 1
      funext S
      exact (booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff f S).symm
    _ ≤ numericalDegree (fun S ↦ (z S : ℝ)) :=
      algebraicDegree_intCastModTwo_le_numericalDegree z
    _ = numericalDegree (numericalCoeff (booleanRealEmbedding f)) := by
      congr 1
      funext S
      exact (numericalCoeff_booleanRealEmbedding_eq_intCast f S).symm

/-- The exact Fourier-to-`𝔽₂` polynomial bridge composes degree preservation with coefficient
reduction. -/
theorem functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree_viaPolynomial
    (f : BooleanFunction n) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding f) ≤ fourierDegree f.toReal := by
  calc
    functionAlgebraicDegree (booleanFunctionF₂Encoding f) ≤
        functionNumericalDegree
          (booleanRealEmbedding (booleanFunctionF₂Encoding f)) :=
      functionAlgebraicDegree_le_functionNumericalDegree_booleanRealEmbedding
        (booleanFunctionF₂Encoding f)
    _ = functionNumericalDegree (fourierToF₂Polynomial f.toReal) := by
      rw [fourierToF₂Polynomial_booleanFunction]
    _ = fourierDegree f.toReal :=
      functionNumericalDegree_fourierToF₂Polynomial f.toReal

end FABL
