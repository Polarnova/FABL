/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.Restrictions
public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree
public import FABL.Chapter06.F₂Polynomials.Encoding

/-!
# Algebraic degree from the Fourier spectrum

Book item: Exercise 6.12.

The canonical real embedding of an `𝔽₂`-valued Boolean function has spectral sparsity at least
the exponential of its algebraic degree. Conversely, granularity at scale `2⁻ᵏ` forces algebraic
degree at most `k`.

The sparsity statement explicitly assumes that the function is nonzero. This is the necessary
domain condition for the book's logarithmic formulation: the zero function has algebraic degree
zero under FABL's total convention, while its Fourier sparsity is zero.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private def indexedF₂Support {ι : Type*} [Fintype ι]
    (x : ι → 𝔽₂) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ x i ≠ 0

private noncomputable def indexedF₂CubeOfFinset {ι : Type*} [Fintype ι]
    (S : Finset ι) : ι → 𝔽₂ := by
  classical
  exact fun i ↦ if i ∈ S then 1 else 0

private noncomputable def indexedF₂CubeEquivFinset (ι : Type*) [Fintype ι] :
    (ι → 𝔽₂) ≃ Finset ι := by
  classical
  exact
    { toFun := indexedF₂Support
      invFun := indexedF₂CubeOfFinset
      left_inv := fun x ↦ by
        funext i
        by_cases hi : x i = 0
        · simp [indexedF₂Support, indexedF₂CubeOfFinset, hi]
        · have hi_one : x i = 1 := Fin.eq_one_of_ne_zero _ hi
          simp [indexedF₂Support, indexedF₂CubeOfFinset, hi_one]
      right_inv := fun S ↦ by
        ext i
        simp [indexedF₂Support, indexedF₂CubeOfFinset] }

private noncomputable def indexedSignCubeEquivFinset (ι : Type*) [Fintype ι] :
    IndexedSignCube ι ≃ Finset ι :=
  (Equiv.piCongrRight fun _ ↦ binarySignEquiv).symm.trans
    (indexedF₂CubeEquivFinset ι)

private noncomputable def freeFrequencyPowersetEquiv (J : Finset (Fin n)) :
    Finset J ≃ ↥J.powerset where
  toFun S := ⟨liftFreeFrequency S, by
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact hji ▸ j.property⟩
  invFun U := freeFrequencyPart J U.1
  left_inv S := by
    ext i
    simp [freeFrequencyPart, liftFreeFrequency]
  right_inv U := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ J
    · let j : J := ⟨i, hi⟩
      change i ∈ liftFreeFrequency (freeFrequencyPart J U.1) ↔ i ∈ U.1
      constructor
      · intro h
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
        have hkj : k = j := Subtype.ext hki
        subst k
        exact (mem_freeFrequencyPart J U.1 j).mp hk
      · intro h
        apply Finset.mem_map.mpr
        exact ⟨j, (mem_freeFrequencyPart J U.1 j).mpr h, rfl⟩
    · have hiU : i ∉ U.1 := fun hiU ↦ hi (Finset.mem_powerset.mp U.2 hiU)
      simp [liftFreeFrequency, hi, hiU]

/-- The all-`+1` assignment on the coordinates fixed by a sign restriction. -/
def zeroFixedSign (J : Finset (Fin n)) : FixedSignCube J :=
  fun _ ↦ 1

private theorem binaryPointOfFreeSign_eq_f₂CubeOfFinset
    (J : Finset (Fin n)) (y : FreeSignCube J) :
    (binaryCubeSignEquiv n).symm
        (combineSignCube J y (zeroFixedSign J)) =
      f₂CubeOfFinset
        (liftFreeFrequency (indexedSignCubeEquivFinset J y)) := by
  funext i
  by_cases hi : i ∈ J
  · let j : J := ⟨i, hi⟩
    have hcombine : combineSignCube J y (zeroFixedSign J) i = y j := by
      simpa [j] using combineSignCube_apply_free J y (zeroFixedSign J) j
    rw [show ((binaryCubeSignEquiv n).symm
        (combineSignCube J y (zeroFixedSign J))) i =
        binarySignEquiv.symm (combineSignCube J y (zeroFixedSign J) i) by rfl]
    rw [hcombine, f₂CubeOfFinset_apply]
    change binarySignEquiv.symm (y j) =
      if i ∈ liftFreeFrequency (indexedSignCubeEquivFinset J y) then 1 else 0
    have hmem :
        i ∈ liftFreeFrequency (indexedSignCubeEquivFinset J y) ↔
          binarySignEquiv.symm (y j) ≠ 0 := by
      change i ∈ liftFreeFrequency
          (indexedF₂Support ((Equiv.piCongrRight fun _ : J ↦ binarySignEquiv).symm y)) ↔ _
      constructor
      · intro h
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
        have hkj : k = j := Subtype.ext hki
        subst k
        exact (Finset.mem_filter.mp hk).2
      · intro h
        apply Finset.mem_map.mpr
        refine ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    by_cases hy : binarySignEquiv.symm (y j) = 0
    · simp [hmem, hy]
    · have hy_one : binarySignEquiv.symm (y j) = 1 :=
        Fin.eq_one_of_ne_zero _ hy
      simp [hmem, hy_one]
  · let j : FixedIndex J := ⟨i, hi⟩
    have hcombine : combineSignCube J y (zeroFixedSign J) i = 1 := by
      simpa [j, zeroFixedSign] using
        combineSignCube_apply_fixed J y (zeroFixedSign J) j
    rw [show ((binaryCubeSignEquiv n).symm
        (combineSignCube J y (zeroFixedSign J))) i =
        binarySignEquiv.symm (combineSignCube J y (zeroFixedSign J) i) by rfl]
    rw [hcombine, f₂CubeOfFinset_apply]
    simp [binarySignEquiv, liftFreeFrequency, hi]

private theorem sum_freeSignCube_boolean_eq_anfCoeff
    (f : F₂BooleanFunction n) (S : Finset (Fin n)) :
    (∑ y : FreeSignCube S,
        f ((binaryCubeSignEquiv n).symm
          (combineSignCube S y (zeroFixedSign S)))) = anfCoeff f S := by
  classical
  calc
    (∑ y : FreeSignCube S,
        f ((binaryCubeSignEquiv n).symm
          (combineSignCube S y (zeroFixedSign S)))) =
        ∑ T : Finset S,
          f (f₂CubeOfFinset (liftFreeFrequency T)) := by
      apply Fintype.sum_equiv (indexedSignCubeEquivFinset S)
      intro y
      rw [binaryPointOfFreeSign_eq_f₂CubeOfFinset]
    _ = ∑ U : ↥S.powerset, f (f₂CubeOfFinset U.1) := by
      apply Fintype.sum_equiv (freeFrequencyPowersetEquiv S)
      intro T
      rfl
    _ = ∑ U ∈ S.powerset, f (f₂CubeOfFinset U) := by
      symm
      exact Finset.sum_subtype S.powerset (fun U ↦ Iff.rfl)
        (fun U ↦ f (f₂CubeOfFinset U))
    _ = anfCoeff f S := rfl

private def indexedMonomialInt {ι : Type*} (S : Finset ι)
    (x : IndexedSignCube ι) : ℤ :=
  ∏ i ∈ S, (x i : ℤ)

private theorem indexedMonomialInt_cast
    {ι : Type*} (S : Finset ι) (x : IndexedSignCube ι) :
    (indexedMonomialInt S x : ℝ) = indexedMonomial S x := by
  simp [indexedMonomialInt, indexedMonomial, signValue]

private theorem indexedMonomialInt_cast_f₂_eq_one
    {ι : Type*} (S : Finset ι) (x : IndexedSignCube ι) :
    (indexedMonomialInt S x : 𝔽₂) = 1 := by
  rw [indexedMonomialInt, Int.cast_prod]
  apply Finset.prod_eq_one
  intro i hi
  rcases Int.units_eq_one_or (x i) with h | h <;> simp [h]

/-- A nonzero ANF coefficient produces an odd numerator for every restricted
Fourier coefficient on the same free-coordinate set. -/
theorem exists_odd_restrictionFourierCoeff
    (f : F₂BooleanFunction n) (S : Finset (Fin n))
    (hcoeff : anfCoeff f S ≠ 0) (A : Finset S) :
    ∃ z : ℤ, Odd z ∧
      restrictionFourierCoeff
          (binaryFunctionOnSignCube (booleanRealEmbedding f))
          S A (zeroFixedSign S) =
        (z : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ := by
  classical
  let point : FreeSignCube S → F₂Cube n := fun y ↦
    (binaryCubeSignEquiv n).symm
      (combineSignCube S y (zeroFixedSign S))
  let z : ℤ := ∑ y : FreeSignCube S,
    if f (point y) = 1 then indexedMonomialInt A y else 0
  have hsumCast :
      (∑ y : FreeSignCube S,
          signRestriction
              (binaryFunctionOnSignCube (booleanRealEmbedding f))
              S (zeroFixedSign S) y *
            indexedMonomial A y) =
        (z : ℝ) := by
    change (∑ y, _) = ((∑ y : FreeSignCube S,
      if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : ℝ)
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : f (point y) = 1
    · rw [if_pos hy]
      simp only [signRestriction, binaryFunctionOnSignCube,
        booleanRealEmbedding, point, hy, if_pos, one_mul]
      exact indexedMonomialInt_cast A y |>.symm
    · rw [if_neg hy]
      simp [signRestriction, binaryFunctionOnSignCube,
        booleanRealEmbedding, point, hy]
  have hzmod : (z : 𝔽₂) = anfCoeff f S := by
    change ((∑ y : FreeSignCube S,
      if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : 𝔽₂) = _
    calc
      ((∑ y : FreeSignCube S,
          if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : 𝔽₂) =
          ∑ y : FreeSignCube S,
          if f (point y) = 1 then 1 else 0 := by
        rw [Int.cast_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f (point y) = 1
        · simp [hy, indexedMonomialInt_cast_f₂_eq_one]
        · simp [hy]
      _ = ∑ y : FreeSignCube S, f (point y) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f (point y) = 1
        · simp [hy]
        · have hy0 : f (point y) = 0 := by
            by_contra h
            exact hy (Fin.eq_one_of_ne_zero _ h)
          simp [hy0]
      _ = anfCoeff f S := sum_freeSignCube_boolean_eq_anfCoeff f S
  have hzOdd : Odd z := by
    rw [← Int.not_even_iff_odd]
    intro hzEven
    apply hcoeff
    rw [← hzmod]
    obtain ⟨w, hw⟩ := hzEven
    rw [hw]
    push_cast
    exact CharTwo.add_self_eq_zero (w : 𝔽₂)
  refine ⟨z, hzOdd, ?_⟩
  rw [restrictionFourierCoeff, indexedFourierCoeff,
    Fintype.expect_eq_sum_div_card, hsumCast]
  norm_num [FreeSignCube, Fintype.card_fun, div_eq_mul_inv, Sign]

/-- A nonzero binary Boolean function has a nonzero ANF coefficient at its
algebraic degree. -/
theorem exists_top_anfCoeff
    (f : F₂BooleanFunction n) (hf : f ≠ 0) :
    ∃ S : Finset (Fin n),
      anfCoeff f S ≠ 0 ∧ S.card = functionAlgebraicDegree f := by
  classical
  have hexists : ∃ S : Finset (Fin n), anfCoeff f S ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    funext x
    rw [← congrFun (anfEval_anfCoeff f) x]
    simp [anfEval, h]
  have hsupportNonempty : (anfSupport (anfCoeff f)).Nonempty := by
    obtain ⟨S, hS⟩ := hexists
    exact ⟨S, (mem_anfSupport (anfCoeff f) S).mpr hS⟩
  obtain ⟨S, hSsupport, hdegree⟩ :=
    Finset.exists_mem_eq_sup (anfSupport (anfCoeff f)) hsupportNonempty Finset.card
  refine ⟨S, (mem_anfSupport (anfCoeff f) S).mp hSsupport, ?_⟩
  rw [functionAlgebraicDegree, algebraicDegree]
  exact hdegree.symm

/--
Exercise 6.12(a), in its exponentiated exact form: a nonzero `𝔽₂`-valued Boolean
function has at least `2 ^ degree f` nonzero Fourier coefficients after the canonical
real `0/1` embedding.
-/
theorem two_pow_functionAlgebraicDegree_le_spectralSparsity_booleanRealEmbedding
    (f : F₂BooleanFunction n) (hf : f ≠ 0) :
    2 ^ functionAlgebraicDegree f ≤
      spectralSparsity (booleanRealEmbedding f) := by
  classical
  obtain ⟨S, hcoeff, hdegree⟩ := exists_top_anfCoeff f hf
  let ambient := binaryFunctionOnSignCube (booleanRealEmbedding f)
  have restrictedCoeff_ne_zero (A : Finset S) :
      restrictionFourierCoeff ambient S A (zeroFixedSign S) ≠ 0 := by
    obtain ⟨z, hzOdd, hz⟩ :=
      exists_odd_restrictionFourierCoeff f S hcoeff A
    have hz' :
        restrictionFourierCoeff ambient S A (zeroFixedSign S) =
          (z : ℝ) * ((2 : ℝ) ^ S.card)⁻¹ := by
      simpa [ambient] using hz
    rw [hz']
    apply mul_ne_zero
    · exact_mod_cast (show z ≠ 0 by
        intro hz
        subst z
        exact Int.not_odd_zero hzOdd)
    · positivity
  have exists_nonzero_extension (A : Finset S) :
      ∃ T : Finset (FixedIndex S),
        fourierCoeff ambient
            (liftFreeFrequency A ∪ liftFixedFrequency T) ≠ 0 := by
    have hrestricted := restrictedCoeff_ne_zero A
    rw [restrictionFourierCoeff_eq_sum] at hrestricted
    by_contra hall
    push Not at hall
    apply hrestricted
    apply Finset.sum_eq_zero
    intro T _
    rw [hall T, zero_mul]
  let extensionFrequency : Finset S → Finset (Fin n) := fun A ↦
    liftFreeFrequency A ∪
      liftFixedFrequency (Classical.choose (exists_nonzero_extension A))
  have extensionFrequency_mem (A : Finset S) :
      f₂CubeOfFinset (extensionFrequency A) ∈
        vectorFourierSupport (booleanRealEmbedding f) := by
    apply (mem_vectorFourierSupport _ _).mpr
    rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    have hsupport :
        f₂Support (f₂CubeOfFinset (extensionFrequency A)) =
          extensionFrequency A :=
      (f₂CubeEquivFinset n).right_inv (extensionFrequency A)
    rw [hsupport]
    exact Classical.choose_spec (exists_nonzero_extension A)
  let extension :
      Finset S → ↥(vectorFourierSupport (booleanRealEmbedding f)) :=
    fun A ↦ ⟨f₂CubeOfFinset (extensionFrequency A), extensionFrequency_mem A⟩
  have extension_injective : Function.Injective extension := by
    intro A B h
    apply Finset.ext
    intro i
    have hfrequency : extensionFrequency A = extensionFrequency B := by
      have hsupport := congrArg
        (fun γ : ↥(vectorFourierSupport (booleanRealEmbedding f)) ↦
          f₂Support γ.1) h
      calc
        extensionFrequency A =
            f₂Support (f₂CubeOfFinset (extensionFrequency A)) :=
          ((f₂CubeEquivFinset n).right_inv (extensionFrequency A)).symm
        _ = f₂Support (f₂CubeOfFinset (extensionFrequency B)) := by
          simpa [extension] using hsupport
        _ = extensionFrequency B :=
          (f₂CubeEquivFinset n).right_inv (extensionFrequency B)
    have hmem := congrArg
      (fun U : Finset (Fin n) ↦ ((i : Fin n) ∈ U)) hfrequency
    simpa [extensionFrequency, liftFreeFrequency, liftFixedFrequency,
      i.property] using hmem
  have hcard :
      2 ^ S.card ≤ (vectorFourierSupport (booleanRealEmbedding f)).card := by
    simpa only [Fintype.card_finset, Fintype.card_coe] using
      Fintype.card_le_of_injective extension extension_injective
  calc
    2 ^ functionAlgebraicDegree f = 2 ^ S.card := by rw [hdegree]
    _ ≤ (vectorFourierSupport (booleanRealEmbedding f)).card := hcard
    _ = spectralSparsity (booleanRealEmbedding f) :=
      (spectralSparsity_eq_card_vectorFourierSupport _).symm

private theorem restrictionFourierCoeff_granular
    (φ : F₂Cube n → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (S : Finset J) {ε : ℝ} (hφ : IsVectorFourierGranular φ ε) :
    ∃ q : ℤ,
      restrictionFourierCoeff (binaryFunctionOnSignCube φ) J S z =
        (q : ℝ) * ε := by
  classical
  have hambient : IsFourierGranular (binaryFunctionOnSignCube φ) ε := hφ
  choose q hq using fun T : Finset (FixedIndex J) ↦
    hambient (liftFreeFrequency S ∪ liftFixedFrequency T)
  let qsum : ℤ := ∑ T : Finset (FixedIndex J), q T * indexedMonomialInt T z
  refine ⟨qsum, ?_⟩
  rw [restrictionFourierCoeff_eq_sum]
  dsimp [qsum]
  rw [Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  rw [hq T, Int.cast_mul, indexedMonomialInt_cast]
  ring

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

/--
Exercise 6.12(b): if the Fourier transform of the canonical real `0/1` embedding is
`2⁻ᵏ`-granular, then the algebraic degree over `𝔽₂` is at most `k`.

The result includes the zero function, whose algebraic degree is zero and whose Fourier
transform is granular at every scale.
-/
theorem functionAlgebraicDegree_le_of_isVectorFourierGranular_booleanRealEmbedding
    (f : F₂BooleanFunction n) (k : ℕ)
    (hgranular :
      IsVectorFourierGranular
        (booleanRealEmbedding f) (((2 : ℝ) ^ k)⁻¹)) :
    functionAlgebraicDegree f ≤ k := by
  classical
  by_cases hf : f = 0
  · rw [hf, functionAlgebraicDegree_zero]
    exact Nat.zero_le k
  · obtain ⟨S, hcoeff, hdegree⟩ := exists_top_anfCoeff f hf
    by_contra hle
    have hkS : k < S.card := by
      rw [hdegree]
      omega
    obtain ⟨z, hzOdd, hz⟩ :=
      exists_odd_restrictionFourierCoeff f S hcoeff (∅ : Finset S)
    obtain ⟨w, hw⟩ :=
      restrictionFourierCoeff_granular
        (booleanRealEmbedding f) S (zeroFixedSign S)
          (∅ : Finset S) hgranular
    exact not_odd_scaled_eq_finer_scaled hzOdd hkS (hz.symm.trans hw)

end FABL
