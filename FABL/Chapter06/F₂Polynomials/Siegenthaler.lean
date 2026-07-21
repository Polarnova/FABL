/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.FourierDegreeBridge
public import FABL.Chapter06.F₂Polynomials.SpectralDegree
public import FABL.Chapter06.Pseudorandomness.CorrelationImmunity
public import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations

/-!
# Siegenthaler's degree bounds

Book items: Proposition 6.24 and Siegenthaler's Theorem.

The canonical `𝔽₂` degree of a resilient Boolean function is at most `n - k - 1`.
For a correlation-immune Boolean function, the corresponding bound is `n - k`.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem restrictionFourierCoeff_encoding_empty
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictionFourierCoeff
        (binaryFunctionOnSignCube
          (booleanRealEmbedding (booleanFunctionF₂Encoding f)))
        J ∅ z =
      (1 - mean (signRestriction f.toReal J z)) / 2 := by
  rw [binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding]
  rw [restrictionFourierCoeff, indexedFourierCoeff]
  simp only [indexedMonomial, Finset.prod_empty, mul_one, signRestriction_apply]
  change (𝔼 y : FreeSignCube J,
      (1 - f.toReal (combineSignCube J y z)) / 2) =
    (1 - mean (signRestriction f.toReal J z)) / 2
  calc
    (𝔼 y : FreeSignCube J,
        (1 - f.toReal (combineSignCube J y z)) / 2) =
        ((𝔼 y : FreeSignCube J,
          ((1 : ℝ) - f.toReal (combineSignCube J y z))) : ℝ) / (2 : ℝ) := by
      exact (Finset.expect_div Finset.univ _ (2 : ℝ)).symm
    _ = (1 - mean (signRestriction f.toReal J z)) / 2 := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
      rfl

private theorem not_odd_scaled_eq_finer_scaled
    {d k : ℕ} {z w : ℤ} (hzOdd : Odd z) (hkd : k < d)
    (hscale :
      (z : ℝ) * ((2 : ℝ) ^ d)⁻¹ =
        (w : ℝ) * ((2 : ℝ) ^ k)⁻¹) :
    False := by
  have hcross :
      (z : ℝ) * (2 : ℝ) ^ k = (w : ℝ) * (2 : ℝ) ^ d := by
    calc
      (z : ℝ) * (2 : ℝ) ^ k =
          ((z : ℝ) * ((2 : ℝ) ^ d)⁻¹) *
            ((2 : ℝ) ^ d * (2 : ℝ) ^ k) := by
        field_simp
      _ = ((w : ℝ) * ((2 : ℝ) ^ k)⁻¹) *
            ((2 : ℝ) ^ d * (2 : ℝ) ^ k) := by
        rw [hscale]
      _ = (w : ℝ) * (2 : ℝ) ^ d := by
        field_simp
  have hcrossInt :
      z * (2 : ℤ) ^ k = w * (2 : ℤ) ^ d := by
    exact_mod_cast hcross
  have hcancel :
      (2 : ℤ) ^ k * z =
        (2 : ℤ) ^ k * (w * (2 : ℤ) ^ (d - k)) := by
    calc
      (2 : ℤ) ^ k * z = z * (2 : ℤ) ^ k := by ring
      _ = w * (2 : ℤ) ^ d := hcrossInt
      _ = w * ((2 : ℤ) ^ k * (2 : ℤ) ^ (d - k)) := by
        rw [← pow_add]
        congr 2
        omega
      _ = (2 : ℤ) ^ k * (w * (2 : ℤ) ^ (d - k)) := by ring
  have hz :
      z = w * (2 : ℤ) ^ (d - k) :=
    mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)) hcancel
  have hevenPow : Even ((2 : ℤ) ^ (d - k)) :=
    (show Even (2 : ℤ) by norm_num).pow_of_ne_zero (by omega)
  have hzEven : Even z := by
    rw [hz]
    exact hevenPow.mul_left w
  exact (Int.not_even_iff_odd.mpr hzOdd) hzEven

/-- O'Donnell, Proposition 6.24: a `k`-resilient Boolean function has canonical
`𝔽₂` degree at most `n - k - 1` when `k < n - 1`. -/
theorem functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient
    (f : BooleanFunction n) (k : ℕ) (hf : IsResilient k f)
    (hk : k < n - 1) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding f) ≤ n - k - 1 := by
  classical
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hdegree
  have hScard : n - k - 1 < S.card := by omega
  have hSle : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hSlarge : 1 < S.card := by omega
  have hfixed : Fintype.card (FixedIndex S) ≤ k := by
    simp only [FixedIndex, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_coe]
    omega
  have hmeanInvariant :=
    (isLowDegreeFourierRegular_zero_iff_forall_mean_signRestriction_eq
      f.toReal k).mp hf.1 S (zeroFixedSign S) hfixed
  have hmeanZero :
      mean (signRestriction f.toReal S (zeroFixedSign S)) = 0 :=
    hmeanInvariant.trans hf.2
  obtain ⟨z, hzOdd, hz⟩ :=
    exists_odd_restrictionFourierCoeff
      (booleanFunctionF₂Encoding f) S hcoeff (∅ : Finset S)
  have hscale :
      (z : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ =
        ((1 : ℤ) : ℝ) * ((2 : ℝ) ^ 1)⁻¹ := by
    calc
      (z : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ =
          restrictionFourierCoeff
            (binaryFunctionOnSignCube
              (booleanRealEmbedding (booleanFunctionF₂Encoding f)))
            S ∅ (zeroFixedSign S) := hz.symm
      _ = (1 - mean (signRestriction f.toReal S (zeroFixedSign S))) / 2 :=
        restrictionFourierCoeff_encoding_empty f S (zeroFixedSign S)
      _ = ((1 : ℤ) : ℝ) * ((2 : ℝ) ^ 1)⁻¹ := by
        rw [hmeanZero]
        norm_num
  exact not_odd_scaled_eq_finer_scaled (w := (1 : ℤ)) hzOdd hSlarge hscale

/-- Siegenthaler's Theorem: a `k`th-order correlation-immune Boolean function has
canonical `𝔽₂` degree at most `n - k` when `k < n`. -/
theorem functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isCorrelationImmune
    (f : BooleanFunction n) (k : ℕ) (hf : IsCorrelationImmune k f)
    (hk : k < n) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding f) ≤ n - k := by
  classical
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hdegree
  have hScard : n - k < S.card := by omega
  have hSle : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hSnonempty : S.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let i : S := ⟨hSnonempty.choose, hSnonempty.choose_spec⟩
  let A : Finset S := {i}
  obtain ⟨z, hzOdd, hz⟩ :=
    exists_odd_restrictionFourierCoeff
      (booleanFunctionF₂Encoding f) S hcoeff A
  have hrestrictedNe :
      restrictionFourierCoeff
          (binaryFunctionOnSignCube
            (booleanRealEmbedding (booleanFunctionF₂Encoding f)))
          S A (zeroFixedSign S) ≠ 0 := by
    rw [hz]
    apply mul_ne_zero
    · exact_mod_cast (show z ≠ 0 by
        intro hz
        subst z
        exact Int.not_odd_zero hzOdd)
    · positivity
  have hrestrictedZero :
      restrictionFourierCoeff
          (binaryFunctionOnSignCube
            (booleanRealEmbedding (booleanFunctionF₂Encoding f)))
          S A (zeroFixedSign S) = 0 := by
    rw [binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding]
    rw [restrictionFourierCoeff_eq_sum]
    apply Finset.sum_eq_zero
    intro T _
    let U := liftFreeFrequency A ∪ liftFixedFrequency T
    have hfreeNonempty : (liftFreeFrequency A).Nonempty := by
      simp [A, liftFreeFrequency]
    have hUnonempty : U.Nonempty :=
      hfreeNonempty.mono Finset.subset_union_left
    have hTcard : T.card ≤ n - S.card := by
      calc
        T.card ≤ Fintype.card (FixedIndex S) := Finset.card_le_univ T
        _ = n - S.card := by
          simp [FixedIndex]
    have hUcard : U.card ≤ k := by
      have hcard :
          U.card = A.card + T.card := by
        dsimp [U]
        rw [Finset.card_union_of_disjoint
          (disjoint_liftFreeFrequency_liftFixedFrequency A T)]
        simp [liftFreeFrequency, liftFixedFrequency]
      rw [hcard]
      have hAcard : A.card = 1 := by simp [A]
      rw [hAcard]
      omega
    have hcoeffZero : fourierCoeff f.toReal U = 0 := by
      have habs := hf U hUnonempty hUcard
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    rw [fourierCoeff_one_sub_div_two]
    rw [if_neg (Finset.nonempty_iff_ne_empty.mp hUnonempty), hcoeffZero]
    norm_num
  exact hrestrictedNe hrestrictedZero

end FABL
