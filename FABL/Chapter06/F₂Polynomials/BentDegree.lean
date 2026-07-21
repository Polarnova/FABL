/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.BentFunctions
public import FABL.Chapter06.F₂Polynomials.FourierDegreeBridge
public import FABL.Chapter06.F₂Polynomials.SpectralDegree

/-!
# Algebraic degree of bent functions

Book item: Exercise 6.13.

The ordinary granularity argument gives degree at most `n / 2 + 1`.  In the
equality case, a top ANF term gives an odd restricted Fourier numerator.
Bent flatness expresses the same coefficient as a sum of an even number of
signed flat-spectrum coefficients, giving the required parity contradiction
when `n > 2`.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The real sign encoding is the affine transform `1 - 2f` of the real
zero-one embedding. -/
theorem realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding
    (f : F₂BooleanFunction n) :
    realSignEncodedFunction f =
      fun x ↦ 1 - 2 * booleanRealEmbedding f x := by
  funext x
  by_cases hx : f x = 0
  · simp [realSignEncodedFunction, signEncodedFunction,
      booleanRealEmbedding, hx, signEncode]
  · have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hx
    simp [realSignEncodedFunction, signEncodedFunction,
      booleanRealEmbedding, hxOne, signEncode]
    norm_num

/-- At a nonempty free frequency, sign encoding multiplies the zero-one
restricted Fourier coefficient by `-2`. -/
theorem restrictionFourierCoeff_realSignEncodedFunction_eq_neg_two_mul
    (f : F₂BooleanFunction n) (J : Finset (Fin n))
    (A : Finset J) (hA : A.Nonempty) (z : FixedSignCube J) :
    restrictionFourierCoeff
        (binaryFunctionOnSignCube (realSignEncodedFunction f)) J A z =
      -2 * restrictionFourierCoeff
        (binaryFunctionOnSignCube (booleanRealEmbedding f)) J A z := by
  rw [restrictionFourierCoeff, restrictionFourierCoeff,
    indexedFourierCoeff, indexedFourierCoeff]
  simp_rw [signRestriction_apply, binaryFunctionOnSignCube,
    realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding]
  change
    (𝔼 y : FreeSignCube J,
        (1 - 2 *
          binaryFunctionOnSignCube (booleanRealEmbedding f)
            (combineSignCube J y z)) *
          indexedMonomial A y) =
      -2 * (𝔼 y : FreeSignCube J,
        binaryFunctionOnSignCube (booleanRealEmbedding f)
            (combineSignCube J y z) *
          indexedMonomial A y)
  calc
    (𝔼 y : FreeSignCube J,
        (1 - 2 *
          binaryFunctionOnSignCube (booleanRealEmbedding f)
            (combineSignCube J y z)) *
          indexedMonomial A y) =
        𝔼 y : FreeSignCube J,
          (indexedMonomial A y -
            2 *
              (binaryFunctionOnSignCube (booleanRealEmbedding f)
                  (combineSignCube J y z) *
                indexedMonomial A y)) := by
      apply Finset.expect_congr rfl
      intro y _
      ring
    _ =
        (𝔼 y : FreeSignCube J, indexedMonomial A y) -
          2 * (𝔼 y : FreeSignCube J,
            binaryFunctionOnSignCube (booleanRealEmbedding f)
                (combineSignCube J y z) *
              indexedMonomial A y) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect]
    _ = -2 * (𝔼 y : FreeSignCube J,
          binaryFunctionOnSignCube (booleanRealEmbedding f)
              (combineSignCube J y z) *
            indexedMonomial A y) := by
      have hAne : A ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp hA
      have hzero :
          (𝔼 y : FreeSignCube J, indexedMonomial A y) = 0 := by
        calc
          (𝔼 y : FreeSignCube J, indexedMonomial A y) =
              𝔼 y : FreeSignCube J,
                indexedMonomial A y *
                  indexedMonomial (∅ : Finset J) y := by
            apply Finset.expect_congr rfl
            intro y _
            simp [indexedMonomial]
          _ = 0 := by
            rw [expect_indexedMonomial_mul, if_neg hAne]
      rw [hzero]
      ring

private theorem even_scaled_restrictionFourierCoeff_of_isBent
    (f : F₂Cube n → ℝ) (hf : IsBent f)
    (J : Finset (Fin n))
    (hfixed : 0 < Fintype.card (FixedIndex J))
    (A : Finset J) (z : FixedSignCube J) :
    ∃ q : ℤ, Even q ∧
      restrictionFourierCoeff
          (binaryFunctionOnSignCube f) J A z =
        (q : ℝ) * ((2 : ℝ) ^ (n / 2))⁻¹ := by
  classical
  let scale : ℝ := ((2 : ℝ) ^ (n / 2))⁻¹
  let ambientFrequency :
      Finset (FixedIndex J) → Finset (Fin n) :=
    fun T ↦ liftFreeFrequency A ∪ liftFixedFrequency T
  let signedTerm : Finset (FixedIndex J) → ℤ := fun T ↦
    if fourierCoeff (binaryFunctionOnSignCube f) (ambientFrequency T) *
          indexedMonomial T z = scale
    then 1
    else -1
  have hterm (T : Finset (FixedIndex J)) :
      fourierCoeff (binaryFunctionOnSignCube f) (ambientFrequency T) *
          indexedMonomial T z =
        (signedTerm T : ℝ) * scale := by
    let γ : F₂Cube n :=
      (f₂CubeEquivFinset n).symm (ambientFrequency T)
    have hsupport : f₂Support γ = ambientFrequency T :=
      (f₂CubeEquivFinset n).apply_symm_apply _
    have hcoeff :
        |fourierCoeff (binaryFunctionOnSignCube f) (ambientFrequency T)| =
          scale := by
      rw [← hsupport,
        ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
      exact hf γ
    have hmonomial : |indexedMonomial T z| = 1 := by
      rcases sq_eq_one_iff.mp (indexedMonomial_sq T z) with h | h <;>
        simp [h]
    have habs :
        |fourierCoeff (binaryFunctionOnSignCube f) (ambientFrequency T) *
            indexedMonomial T z| = scale := by
      rw [abs_mul, hcoeff, hmonomial, mul_one]
    rcases eq_or_eq_neg_of_abs_eq habs with hpositive | hnegative
    · simp [signedTerm, hpositive]
    · have hne :
          fourierCoeff (binaryFunctionOnSignCube f) (ambientFrequency T) *
              indexedMonomial T z ≠ scale := by
        intro h
        rw [h] at hnegative
        have hscalePos : 0 < scale := by
          dsimp [scale]
          positivity
        linarith
      simp [signedTerm, hnegative]
  let q : ℤ := ∑ T : Finset (FixedIndex J), signedTerm T
  have hqCast : (q : 𝔽₂) = 0 := by
    dsimp [q]
    rw [Int.cast_sum]
    have hsignedCast (T : Finset (FixedIndex J)) :
        (signedTerm T : 𝔽₂) = 1 := by
      dsimp [signedTerm]
      split
      · norm_num
      · exact ZMod.neg_eq_self_mod_two 1
    simp_rw [hsignedCast]
    rw [Finset.sum_const, Finset.card_univ,
      Fintype.card_finset]
    have hcardNe :
        Fintype.card (FixedIndex J) ≠ 0 :=
      Nat.ne_of_gt hfixed
    rw [nsmul_eq_mul, mul_one, Nat.cast_pow,
      ZMod.natCast_self, zero_pow hcardNe]
  have hqEven : Even q := by
    by_contra hnot
    have hone : (q : 𝔽₂) = 1 := by
      rw [CharTwo.intCast_eq_ite, if_neg hnot]
    rw [hqCast] at hone
    norm_num at hone
  refine ⟨q, hqEven, ?_⟩
  rw [restrictionFourierCoeff_eq_sum]
  calc
    (∑ T : Finset (FixedIndex J),
        fourierCoeff (binaryFunctionOnSignCube f)
            (liftFreeFrequency A ∪ liftFixedFrequency T) *
          indexedMonomial T z) =
        ∑ T : Finset (FixedIndex J),
          (signedTerm T : ℝ) * scale := by
      apply Finset.sum_congr rfl
      intro T _
      exact hterm T
    _ = (q : ℝ) * scale := by
      dsimp [q]
      rw [Int.cast_sum, Finset.sum_mul]

private theorem isVectorFourierGranular_booleanRealEmbedding_of_isBent
    (f : F₂BooleanFunction n)
    (hf : IsBent (realSignEncodedFunction f)) :
    IsVectorFourierGranular
      (booleanRealEmbedding f)
      (((2 : ℝ) ^ (n / 2 + 1))⁻¹) := by
  rw [isVectorFourierGranular_iff]
  intro γ
  let S := f₂Support γ
  have hrelation :
      vectorFourierCoeff (booleanRealEmbedding f) γ =
        ((if S = ∅ then 1 else 0) -
          vectorFourierCoeff (realSignEncodedFunction f) γ) / 2 := by
    rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
      vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    rw [show
        binaryFunctionOnSignCube (booleanRealEmbedding f) =
          fun x ↦
            (1 -
              binaryFunctionOnSignCube
                (realSignEncodedFunction f) x) / 2 by
          funext x
          rw [binaryFunctionOnSignCube,
            binaryFunctionOnSignCube,
            realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding]
          ring]
    exact fourierCoeff_one_sub_div_two
      (binaryFunctionOnSignCube (realSignEncodedFunction f)) S
  have hflat := hf γ
  rcases eq_or_eq_neg_of_abs_eq hflat with hpositive | hnegative
  · by_cases hS : S = ∅
    · refine ⟨(2 ^ (n / 2) : ℤ) - 1, ?_⟩
      rw [hrelation, if_pos hS, hpositive]
      norm_num only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
      field_simp
      ring
    · refine ⟨-1, ?_⟩
      rw [hrelation, if_neg hS, hpositive]
      norm_num
      rw [pow_succ]
      field_simp
  · by_cases hS : S = ∅
    · refine ⟨(2 ^ (n / 2) : ℤ) + 1, ?_⟩
      rw [hrelation, if_pos hS, hnegative]
      norm_num only [Int.cast_add, Int.cast_pow, Int.cast_ofNat]
      field_simp
      ring
    · refine ⟨1, ?_⟩
      rw [hrelation, if_neg hS, hnegative]
      norm_num
      rw [pow_succ]
      field_simp

/-- O'Donnell, Exercise 6.13: in even dimension greater than two, a bent
binary Boolean function has algebraic degree at most half the dimension. -/
theorem functionAlgebraicDegree_le_half_of_isBent
    (f : F₂BooleanFunction n) (hn : Even n) (hnTwo : 2 < n)
    (hf : IsBent (realSignEncodedFunction f)) :
    functionAlgebraicDegree f ≤ n / 2 := by
  classical
  rcases hn with ⟨m, rfl⟩
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf]
  have hupper :
      functionAlgebraicDegree f ≤ m + 1 := by
    apply
      functionAlgebraicDegree_le_of_isVectorFourierGranular_booleanRealEmbedding
    simpa [hhalf] using
      isVectorFourierGranular_booleanRealEmbedding_of_isBent f hf
  by_contra hdegree
  have hdegreeEq : functionAlgebraicDegree f = m + 1 := by
    omega
  have hm : 1 < m := by omega
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero, functionAlgebraicDegree_zero] at hdegreeEq
    omega
  obtain ⟨S, hScoeff, hScard⟩ :=
    exists_top_anfCoeff f hfne
  have hScard' : S.card = m + 1 := hScard.trans hdegreeEq
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS
    rw [hS, Finset.card_empty] at hScard'
    omega
  obtain ⟨i, hiS⟩ := hSnonempty
  let A : Finset S := {⟨i, hiS⟩}
  have hAnonempty : A.Nonempty := by simp [A]
  obtain ⟨z, hzOdd, hz⟩ :=
    exists_odd_restrictionFourierCoeff f S hScoeff A
  have hfixed :
      0 < Fintype.card (FixedIndex S) := by
    simp [FixedIndex, hScard']
    omega
  obtain ⟨q, hqEven, hq⟩ :=
    even_scaled_restrictionFourierCoeff_of_isBent
      (realSignEncodedFunction f) hf S hfixed A (zeroFixedSign S)
  have hsign :=
    restrictionFourierCoeff_realSignEncodedFunction_eq_neg_two_mul
      f S A hAnonempty (zeroFixedSign S)
  rw [hz] at hsign
  have hscale :
      ((2 : ℝ) ^ ((m + m) / 2))⁻¹ =
        2 * ((2 : ℝ) ^ S.card)⁻¹ := by
    rw [hhalf, hScard', pow_succ]
    field_simp
  rw [hscale] at hq
  have hcast : (q : ℝ) = -(z : ℝ) := by
    have hpowPos : 0 < (2 : ℝ) ^ S.card := by positivity
    rw [hq] at hsign
    field_simp at hsign
    linarith
  have hqz : q = -z := by
    exact_mod_cast hcast
  have hzEven : Even z := by
    rw [hqz] at hqEven
    simpa using hqEven
  exact (Int.not_even_iff_odd.mpr hzOdd) hzEven

end FABL
