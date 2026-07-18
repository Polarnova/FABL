/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.SocialChoiceFunctions
public import FABL.Chapter03.SubspacesAndDecisionTrees

/-!
# Restrictions

Book items: Definition 3.18, Definition 3.20, Definition 3.23, Definition 3.24, Definition 3.26,
Fact 3.25, Example 3.19, Proposition 3.21, Poisson summation formula, Corollary 3.22.

Formalization of the sign-cube restriction material in Section 3.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

/-! ## Fourier analysis on finitely indexed sign cubes -/

/-- A sign cube whose coordinates are indexed by an arbitrary type. -/
abbrev IndexedSignCube (ι : Type*) := ι → Sign

/-- The monomial indexed by `S` on an arbitrary finitely indexed sign cube. -/
def indexedMonomial {ι : Type*} (S : Finset ι) (x : IndexedSignCube ι) : ℝ :=
  ∏ i ∈ S, signValue (x i)

/-- An indexed sign-cube monomial bundled as an additive character. -/
noncomputable def indexedSignMonomialChar {ι : Type*} (S : Finset ι) :
    AddChar (Additive (IndexedSignCube ι)) ℝ where
  toFun x := indexedMonomial S x.toMul
  map_zero_eq_one' := by simp [indexedMonomial, signValue]
  map_add_eq_mul' x y := by
    simp [indexedMonomial, signValue, Finset.prod_mul_distrib]

/-- Distinct finite coordinate sets give distinct indexed sign-cube characters. -/
theorem indexedSignMonomialChar_injective {ι : Type*} : Function.Injective
    (indexedSignMonomialChar : Finset ι → AddChar (Additive (IndexedSignCube ι)) ℝ) := by
  classical
  intro S T h
  ext i
  have hi := congrArg
    (fun ψ : AddChar (Additive (IndexedSignCube ι)) ℝ ↦
      ψ (.ofMul (fun j ↦ if j = i then -1 else 1))) h
  have hv (j : ι) : signValue (if j = i then -1 else 1) =
      if j = i then (-1 : ℝ) else 1 := by
    split_ifs <;> simp
  have hi' : (if i ∈ S then (-1 : ℝ) else 1) = if i ∈ T then -1 else 1 := by
    simpa [indexedSignMonomialChar, indexedMonomial, hv, Finset.prod_ite_eq'] using hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT] at hi' ⊢ <;> norm_num at hi'

/-- Indexed sign-cube monomials are orthonormal under uniform expectation. -/
theorem expect_indexedMonomial_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) :
    (𝔼 x : IndexedSignCube ι, indexedMonomial S x * indexedMonomial T x) =
      if S = T then 1 else 0 := by
  have hreindex :
      (𝔼 x : IndexedSignCube ι, indexedMonomial S x * indexedMonomial T x) =
        RCLike.wInner RCLike.cWeight
          (indexedSignMonomialChar S) (indexedSignMonomialChar T) := by
    rw [RCLike.wInner_cWeight_eq_expect]
    symm
    apply Fintype.expect_equiv Additive.toMul
    intro x
    simp [RCLike.inner_apply, indexedSignMonomialChar, mul_comm]
  rw [hreindex]
  simpa [indexedSignMonomialChar_injective.eq_iff] using
    (AddChar.wInner_cWeight_eq_boole
      (indexedSignMonomialChar S) (indexedSignMonomialChar T))

/-- Mathlib's finite-character basis, indexed by finite coordinate sets. -/
noncomputable def indexedWalshBasis (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.Basis (Finset ι) ℝ (IndexedSignCube ι → ℝ) := by
  classical
  exact basisOfLinearIndependentOfCardEqFinrank (b := fun S ↦ indexedMonomial S)
    (by
      let e : (Additive (IndexedSignCube ι) → ℝ) ≃ₗ[ℝ] (IndexedSignCube ι → ℝ) :=
        { toFun := fun f x ↦ f (Additive.ofMul x)
          invFun := fun f x ↦ f (Additive.toMul x)
          left_inv := by intro f; ext x; rfl
          right_inv := by intro f; ext x; rfl
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      simpa [e, Function.comp_def, indexedSignMonomialChar] using
        (((AddChar.linearIndependent (Additive (IndexedSignCube ι)) ℝ).comp
          indexedSignMonomialChar indexedSignMonomialChar_injective).map'
            e.toLinearMap e.ker))
    (by
      simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset,
        Fintype.card_units_int])

/-- The uniform Fourier coefficient on an arbitrary finitely indexed sign cube. -/
noncomputable def indexedFourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : IndexedSignCube ι → ℝ) (S : Finset ι) : ℝ :=
  𝔼 x, f x * indexedMonomial S x

/-- Coordinates in `indexedWalshBasis` are the uniform Fourier coefficients. -/
theorem indexedWalshBasis_repr_eq_indexedFourierCoeff {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (f : IndexedSignCube ι → ℝ) (T : Finset ι) :
    (indexedWalshBasis ι).repr f T = indexedFourierCoeff f T := by
  classical
  have hexp (x : IndexedSignCube ι) :
      f x = ∑ S, ((indexedWalshBasis ι).repr f S) * indexedMonomial S x := by
    have h := congrFun ((indexedWalshBasis ι).sum_repr f) x
    simpa [indexedWalshBasis, smul_eq_mul] using h.symm
  rw [indexedFourierCoeff]
  calc
    (indexedWalshBasis ι).repr f T =
        ∑ S, (indexedWalshBasis ι).repr f S * (if S = T then 1 else 0) := by simp
    _ = ∑ S, (indexedWalshBasis ι).repr f S *
          (𝔼 x, indexedMonomial S x * indexedMonomial T x) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [expect_indexedMonomial_mul]
    _ = ∑ S, 𝔼 x,
          ((indexedWalshBasis ι).repr f S * indexedMonomial S x) *
            indexedMonomial T x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 x, ∑ S,
          ((indexedWalshBasis ι).repr f S * indexedMonomial S x) *
            indexedMonomial T x := by
      rw [Finset.expect_sum_comm]
    _ = 𝔼 x, f x * indexedMonomial T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [hexp, Finset.sum_mul]

/-- Fourier expansion on an arbitrary finitely indexed sign cube. -/
theorem indexed_fourier_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : IndexedSignCube ι → ℝ) (x : IndexedSignCube ι) :
    f x = ∑ S, indexedFourierCoeff f S * indexedMonomial S x := by
  classical
  calc
    f x = ∑ S, ((indexedWalshBasis ι).repr f S) * indexedMonomial S x := by
      have h := congrFun ((indexedWalshBasis ι).sum_repr f) x
      simpa [indexedWalshBasis, smul_eq_mul] using h.symm
    _ = ∑ S, indexedFourierCoeff f S * indexedMonomial S x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [indexedWalshBasis_repr_eq_indexedFourierCoeff]

/-- The mean is the empty-set Fourier coefficient on every finitely indexed sign cube. -/
theorem expect_eq_indexedFourierCoeff_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : IndexedSignCube ι → ℝ) :
    (𝔼 x, f x) = indexedFourierCoeff f ∅ := by
  simp [indexedFourierCoeff, indexedMonomial]

/-- Plancherel's identity on an arbitrary finitely indexed sign cube. -/
theorem indexed_plancherel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : IndexedSignCube ι → ℝ) :
    (𝔼 x, f x * g x) =
      ∑ S, indexedFourierCoeff f S * indexedFourierCoeff g S := by
  classical
  calc
    (𝔼 x, f x * g x) =
        𝔼 x, (∑ S, indexedFourierCoeff f S * indexedMonomial S x) * g x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← indexed_fourier_expansion f x]
    _ = 𝔼 x, ∑ S, (indexedFourierCoeff f S * indexedMonomial S x) * g x := by
      congr 1
      funext x
      rw [Finset.sum_mul]
    _ = ∑ S, 𝔼 x, (indexedFourierCoeff f S * indexedMonomial S x) * g x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S, indexedFourierCoeff f S * indexedFourierCoeff g S := by
      apply Finset.sum_congr rfl
      intro S _
      simp_rw [mul_assoc]
      rw [← Finset.mul_expect]
      simp [indexedFourierCoeff, mul_comm]

/-- Parseval's identity on an arbitrary finitely indexed sign cube. -/
theorem indexed_parseval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : IndexedSignCube ι → ℝ) :
    (𝔼 x, f x ^ 2) = ∑ S, indexedFourierCoeff f S ^ 2 := by
  simpa [pow_two] using indexed_plancherel f f

/-- The generic indexed monomial specializes definitionally to Chapter 1's monomial. -/
@[simp] theorem indexedMonomial_fin_eq_monomial {n : ℕ}
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    indexedMonomial S x = monomial S x := rfl

/-- The generic indexed Fourier coefficient specializes definitionally to Chapter 1's
Fourier coefficient. -/
@[simp] theorem indexedFourierCoeff_fin_eq_fourierCoeff {n : ℕ}
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    indexedFourierCoeff f S = fourierCoeff f S := rfl

/-! ## Restrictions to subcubes -/

/-- The coordinates outside `J`, representing the book's `J̄`. -/
abbrev FixedIndex {n : ℕ} (J : Finset (Fin n)) := {i : Fin n // i ∉ J}

/-- Assignments to the free coordinates in `J`. -/
abbrev FreeSignCube {n : ℕ} (J : Finset (Fin n)) := J → Sign

/-- Assignments to the fixed coordinates outside `J`. -/
abbrev FixedSignCube {n : ℕ} (J : Finset (Fin n)) := FixedIndex J → Sign

/-- Mathlib's canonical splitting of a full sign cube into the coordinates in `J` and outside
`J`. -/
def signCubeSplitEquiv {n : ℕ} (J : Finset (Fin n)) :
    {−1,1}^[n] ≃ FreeSignCube J × FixedSignCube J :=
  Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ J) (fun _ ↦ Sign)

/-- Combine assignments on `J` and its complement into a full sign string. -/
def combineSignCube {n : ℕ} (J : Finset (Fin n))
    (y : FreeSignCube J) (z : FixedSignCube J) : {−1,1}^[n] :=
  (signCubeSplitEquiv J).symm (y, z)

@[simp] theorem combineSignCube_apply_free {n : ℕ} (J : Finset (Fin n))
    (y : FreeSignCube J) (z : FixedSignCube J) (i : J) :
    combineSignCube J y z i = y i := by
  simp [combineSignCube, signCubeSplitEquiv,
    Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

@[simp] theorem combineSignCube_apply_fixed {n : ℕ} (J : Finset (Fin n))
    (y : FreeSignCube J) (z : FixedSignCube J) (i : FixedIndex J) :
    combineSignCube J y z i = z i := by
  simp [combineSignCube, signCubeSplitEquiv,
    Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

/-- O'Donnell, Definition 3.18, conservatively generalized in the codomain: restrict a function
to the coordinates in `J` by fixing all complementary coordinates to `z`. -/
def signRestriction {n : ℕ} {α : Type*} (f : {−1,1}^[n] → α)
    (J : Finset (Fin n)) (z : FixedSignCube J) : FreeSignCube J → α :=
  fun y ↦ f (combineSignCube J y z)

@[simp] theorem signRestriction_apply {n : ℕ} {α : Type*} (f : {−1,1}^[n] → α)
    (J : Finset (Fin n)) (z : FixedSignCube J) (y : FreeSignCube J) :
    signRestriction f J z y = f (combineSignCube J y z) := rfl

/-- Embed a frequency on the free coordinates into the full coordinate set. -/
def liftFreeFrequency {n : ℕ} {J : Finset (Fin n)}
    (S : Finset J) : Finset (Fin n) :=
  S.map (Function.Embedding.subtype fun i ↦ i ∈ J)

/-- Embed a frequency on the fixed coordinates into the full coordinate set. -/
def liftFixedFrequency {n : ℕ} {J : Finset (Fin n)}
    (T : Finset (FixedIndex J)) : Finset (Fin n) :=
  T.map (Function.Embedding.subtype fun i ↦ i ∉ J)

/-- The part of an ambient frequency supported on the free coordinates `J`. -/
def freeFrequencyPart {n : ℕ} (J U : Finset (Fin n)) : Finset J :=
  Finset.univ.filter fun i : J ↦ (i : Fin n) ∈ U

/-- The part of an ambient frequency supported outside the free coordinates `J`. -/
def fixedFrequencyPart {n : ℕ} (J U : Finset (Fin n)) :
    Finset (FixedIndex J) :=
  Finset.univ.filter fun i : FixedIndex J ↦ (i : Fin n) ∈ U

@[simp] theorem mem_freeFrequencyPart {n : ℕ} (J U : Finset (Fin n)) (i : J) :
    i ∈ freeFrequencyPart J U ↔ (i : Fin n) ∈ U := by
  simp [freeFrequencyPart]

@[simp] theorem mem_fixedFrequencyPart {n : ℕ} (J U : Finset (Fin n))
    (i : FixedIndex J) :
    i ∈ fixedFrequencyPart J U ↔ (i : Fin n) ∈ U := by
  simp [fixedFrequencyPart]

/-- Frequencies lifted from `J` and its complement are disjoint. -/
theorem disjoint_liftFreeFrequency_liftFixedFrequency {n : ℕ} {J : Finset (Fin n)}
    (S : Finset J) (T : Finset (FixedIndex J)) :
    Disjoint (liftFreeFrequency S) (liftFixedFrequency T) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiS hiT
  obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hiS
  obtain ⟨k, _hk, hki⟩ := Finset.mem_map.mp hiT
  have hjk : (j : Fin n) = (k : Fin n) := hji.trans hki.symm
  exact k.property (hjk ▸ j.property)

/-- The lifted free and fixed parts of an ambient frequency are disjoint. -/
theorem disjoint_liftFreeFrequencyPart_liftFixedFrequencyPart {n : ℕ}
    (J U : Finset (Fin n)) :
    Disjoint (liftFreeFrequency (freeFrequencyPart J U))
      (liftFixedFrequency (fixedFrequencyPart J U)) :=
  disjoint_liftFreeFrequency_liftFixedFrequency _ _

/-- Splitting an ambient frequency along `J` and lifting both parts recovers it. -/
theorem liftFreeFrequencyPart_union_liftFixedFrequencyPart {n : ℕ}
    (J U : Finset (Fin n)) :
    liftFreeFrequency (freeFrequencyPart J U) ∪
        liftFixedFrequency (fixedFrequencyPart J U) = U := by
  classical
  ext i
  by_cases hi : i ∈ J
  · simp [liftFreeFrequency, liftFixedFrequency, freeFrequencyPart,
      fixedFrequencyPart, hi]
  · simp [liftFreeFrequency, liftFixedFrequency, freeFrequencyPart,
      fixedFrequencyPart, hi]

/-- Every ambient frequency has a unique decomposition into frequencies on `J` and its
complement. -/
theorem existsUnique_frequency_split {n : ℕ} (J U : Finset (Fin n)) :
    ∃! ST : Finset J × Finset (FixedIndex J),
      liftFreeFrequency ST.1 ∪ liftFixedFrequency ST.2 = U := by
  classical
  refine ⟨(freeFrequencyPart J U, fixedFrequencyPart J U),
    liftFreeFrequencyPart_union_liftFixedFrequencyPart J U, ?_⟩
  rintro ⟨S, T⟩ hST
  apply Prod.ext
  · ext i
    calc
      i ∈ S ↔ (i : Fin n) ∈ liftFreeFrequency S := by
        simp [liftFreeFrequency]
      _ ↔ (i : Fin n) ∈ liftFreeFrequency S ∪ liftFixedFrequency T := by
        simp [liftFixedFrequency, i.property]
      _ ↔ (i : Fin n) ∈ U := by rw [hST]
      _ ↔ i ∈ freeFrequencyPart J U :=
        (mem_freeFrequencyPart J U i).symm
  · ext i
    have hnotFree : (i : Fin n) ∉ liftFreeFrequency S := by
      intro hiFree
      obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hiFree
      exact i.property (hji ▸ j.property)
    calc
      i ∈ T ↔ (i : Fin n) ∈ liftFixedFrequency T := by
        constructor
        · intro hiT
          exact Finset.mem_map.mpr ⟨i, hiT, rfl⟩
        · intro hiLift
          obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hiLift
          have hji' : j = i := Subtype.ext hji
          simpa [hji'] using hj
      _ ↔ (i : Fin n) ∈ liftFreeFrequency S ∪ liftFixedFrequency T := by
        simp [hnotFree]
      _ ↔ (i : Fin n) ∈ U := by rw [hST]
      _ ↔ i ∈ fixedFrequencyPart J U :=
        (mem_fixedFrequencyPart J U i).symm

/-- A monomial on a composite string factors into its free and fixed parts. -/
theorem indexedMonomial_lift_union_combine {n : ℕ} {J : Finset (Fin n)}
    (S : Finset J) (T : Finset (FixedIndex J))
    (y : FreeSignCube J) (z : FixedSignCube J) :
    monomial (liftFreeFrequency S ∪ liftFixedFrequency T) (combineSignCube J y z) =
      indexedMonomial S y * indexedMonomial T z := by
  classical
  rw [monomial, Finset.prod_union
    (disjoint_liftFreeFrequency_liftFixedFrequency S T)]
  rw [liftFreeFrequency, liftFixedFrequency, Finset.prod_map, Finset.prod_map]
  simp [indexedMonomial]

/-- A monomial supported on the free coordinates ignores the fixed assignment. -/
@[simp] theorem monomial_liftFreeFrequency_combine {n : ℕ} {J : Finset (Fin n)}
    (S : Finset J) (y : FreeSignCube J) (z : FixedSignCube J) :
    monomial (liftFreeFrequency S) (combineSignCube J y z) =
      indexedMonomial S y := by
  simpa [liftFixedFrequency, indexedMonomial] using
    (indexedMonomial_lift_union_combine S
      (∅ : Finset (FixedIndex J)) y z)

/-- O'Donnell, Definition 3.20: the coefficient on `S` after restriction, regarded as a
function of the complementary assignment `z`. -/
noncomputable def restrictionFourierCoeff {n : ℕ} (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset J) : FixedSignCube J → ℝ :=
  fun z ↦ indexedFourierCoeff (signRestriction f J z) S

/-- O'Donnell, Proposition 3.21: the Fourier coefficient on `T` of the function sending a
complementary assignment to the restricted coefficient on `S` is the original coefficient on
`S ∪ T`. The two lifts make the book's subtype-indexed union explicit. -/
theorem indexedFourierCoeff_restrictionFourierCoeff {n : ℕ}
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n))
    (S : Finset J) (T : Finset (FixedIndex J)) :
    indexedFourierCoeff (restrictionFourierCoeff f J S) T =
      fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) := by
  classical
  change (𝔼 z, indexedFourierCoeff (signRestriction f J z) S * indexedMonomial T z) =
    fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T)
  calc
    (𝔼 z, indexedFourierCoeff (signRestriction f J z) S * indexedMonomial T z) =
        𝔼 z, (𝔼 y, (f (combineSignCube J y z) * indexedMonomial S y) *
          indexedMonomial T z) := by
      apply Finset.expect_congr rfl
      intro z _
      rw [indexedFourierCoeff, Finset.expect_mul]
      simp only [signRestriction]
    _ = 𝔼 y, 𝔼 z, (f (combineSignCube J y z) * indexedMonomial S y) *
          indexedMonomial T z := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 yz : FreeSignCube J × FixedSignCube J,
          (f (combineSignCube J yz.1 yz.2) * indexedMonomial S yz.1) *
            indexedMonomial T yz.2 := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (FreeSignCube J))
          (Finset.univ : Finset (FixedSignCube J))
          (fun y z ↦ (f (combineSignCube J y z) * indexedMonomial S y) *
            indexedMonomial T z)).symm
    _ = 𝔼 x : {−1,1}^[n],
          f x * monomial (liftFreeFrequency S ∪ liftFixedFrequency T) x := by
      symm
      apply Fintype.expect_equiv (signCubeSplitEquiv J)
      intro x
      have hx : combineSignCube J
          ((signCubeSplitEquiv J x).1) ((signCubeSplitEquiv J x).2) = x :=
        (signCubeSplitEquiv J).symm_apply_apply x
      calc
        f x * monomial (liftFreeFrequency S ∪ liftFixedFrequency T) x =
            f (combineSignCube J ((signCubeSplitEquiv J x).1)
                ((signCubeSplitEquiv J x).2)) *
              monomial (liftFreeFrequency S ∪ liftFixedFrequency T)
                (combineSignCube J ((signCubeSplitEquiv J x).1)
                  ((signCubeSplitEquiv J x).2)) := by rw [hx]
        _ = (f (combineSignCube J ((signCubeSplitEquiv J x).1)
                ((signCubeSplitEquiv J x).2)) *
              indexedMonomial S ((signCubeSplitEquiv J x).1)) *
            indexedMonomial T ((signCubeSplitEquiv J x).2) := by
          rw [indexedMonomial_lift_union_combine]
          simp [mul_assoc]
    _ = fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) := rfl

/-- The Fourier-expansion form of O'Donnell, Proposition 3.21. -/
theorem restrictionFourierCoeff_eq_sum {n : ℕ}
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n))
    (S : Finset J) (z : FixedSignCube J) :
    restrictionFourierCoeff f J S z =
      ∑ T, fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) *
        indexedMonomial T z := by
  calc
    restrictionFourierCoeff f J S z =
        ∑ T, indexedFourierCoeff (restrictionFourierCoeff f J S) T *
          indexedMonomial T z := indexed_fourier_expansion _ z
    _ = ∑ T, fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) *
          indexedMonomial T z := by
      apply Finset.sum_congr rfl
      intro T _
      rw [indexedFourierCoeff_restrictionFourierCoeff]

/-- The first-moment identity in O'Donnell, Corollary 3.22. -/
theorem expect_restrictionFourierCoeff {n : ℕ}
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    (𝔼 z, restrictionFourierCoeff f J S z) =
      fourierCoeff f (liftFreeFrequency S) := by
  calc
    (𝔼 z, restrictionFourierCoeff f J S z) =
        indexedFourierCoeff (restrictionFourierCoeff f J S) ∅ :=
      expect_eq_indexedFourierCoeff_empty _
    _ = fourierCoeff f (liftFreeFrequency S ∪
          liftFixedFrequency (∅ : Finset (FixedIndex J))) :=
      indexedFourierCoeff_restrictionFourierCoeff f J S ∅
    _ = fourierCoeff f (liftFreeFrequency S) := by
      simp [liftFixedFrequency]

/-- The second-moment identity in O'Donnell, Corollary 3.22. -/
theorem expect_sq_restrictionFourierCoeff {n : ℕ}
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    (𝔼 z, restrictionFourierCoeff f J S z ^ 2) =
      ∑ T : Finset (FixedIndex J),
        fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) ^ 2 := by
  rw [indexed_parseval]
  apply Finset.sum_congr rfl
  intro T _
  rw [indexedFourierCoeff_restrictionFourierCoeff]

/-! ## The four-bit restriction in Example 3.19 -/

/-- The predicate in equation (3.2), with Lean's zero-based coordinates corresponding to the
book's `x₁, …, x₄`. -/
def example3_19Predicate (x : {−1,1}^[4]) : Prop :=
  (x 2 = -1 ∧ x 3 = -1) ∨
    (signValue (x 0) ≥ signValue (x 1) ∧
      signValue (x 1) ≥ signValue (x 2) ∧
      signValue (x 2) ≥ signValue (x 3)) ∨
    (signValue (x 0) ≤ signValue (x 1) ∧
      signValue (x 1) ≤ signValue (x 2) ∧
      signValue (x 2) ≤ signValue (x 3))

/-- O'Donnell, Example 3.19, equation (3.2). -/
noncomputable def example3_19Function : BooleanFunction 4 := by
  classical
  exact fun x ↦ if example3_19Predicate x then 1 else -1

/-- Equation (3.2) stated as the defining `+1` criterion. -/
theorem example3_19Function_eq_one_iff (x : {−1,1}^[4]) :
    example3_19Function x = 1 ↔ example3_19Predicate x := by
  simp [example3_19Function]

/-- O'Donnell, Example 3.19, equation (3.3): the complete Fourier expansion of the four-bit
function. -/
theorem example3_19_fourier_expansion (x : {−1,1}^[4]) :
    signValue (example3_19Function x) =
      1 / 8 - 1 / 8 * signValue (x 0) + 1 / 8 * signValue (x 1) -
        1 / 8 * signValue (x 2) - 1 / 8 * signValue (x 3) +
      3 / 8 * signValue (x 0) * signValue (x 1) +
        1 / 8 * signValue (x 0) * signValue (x 2) -
        3 / 8 * signValue (x 0) * signValue (x 3) +
        3 / 8 * signValue (x 1) * signValue (x 2) -
        1 / 8 * signValue (x 1) * signValue (x 3) +
        5 / 8 * signValue (x 2) * signValue (x 3) +
      1 / 8 * signValue (x 0) * signValue (x 1) * signValue (x 2) +
        1 / 8 * signValue (x 0) * signValue (x 1) * signValue (x 3) -
        1 / 8 * signValue (x 0) * signValue (x 2) * signValue (x 3) +
        1 / 8 * signValue (x 1) * signValue (x 2) * signValue (x 3) -
        1 / 8 * signValue (x 0) * signValue (x 1) * signValue (x 2) *
          signValue (x 3) := by
  rcases Int.units_eq_one_or (x 0) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (x 1) with h₂ | h₂ <;>
    rcases Int.units_eq_one_or (x 2) with h₃ | h₃ <;>
    rcases Int.units_eq_one_or (x 3) with h₄ | h₄ <;>
    simp [example3_19Function, example3_19Predicate, h₁, h₂, h₃, h₄, signValue] <;>
    norm_num

/-- The free coordinates `{1,2}` from Example 3.19, represented with Lean's zero-based
indices. -/
def example3_19FreeCoordinates : Finset (Fin 4) :=
  {0, 1}

/-- The first free coordinate in Example 3.19. -/
def example3_19First : example3_19FreeCoordinates :=
  ⟨0, by simp [example3_19FreeCoordinates]⟩

/-- The second free coordinate in Example 3.19. -/
def example3_19Second : example3_19FreeCoordinates :=
  ⟨1, by simp [example3_19FreeCoordinates]⟩

/-- The complementary assignment `x₃ = 1, x₄ = -1` from Example 3.19. -/
def example3_19FixedAssignment : FixedSignCube example3_19FreeCoordinates :=
  fun i ↦ if i.1 = 2 then 1 else -1

@[simp] theorem example3_19FixedAssignment_two :
    example3_19FixedAssignment
      (⟨2, by simp [example3_19FreeCoordinates]⟩ :
        FixedIndex example3_19FreeCoordinates) = 1 := by
  simp [example3_19FixedAssignment]

@[simp] theorem example3_19FixedAssignment_three :
    example3_19FixedAssignment
      (⟨3, by simp [example3_19FreeCoordinates]⟩ :
        FixedIndex example3_19FreeCoordinates) = -1 := by
  simp [example3_19FixedAssignment]

/-- Reindex the two free coordinates of Example 3.19 by `Fin 2`. -/
def example3_19TwoBitInput
    (y : FreeSignCube example3_19FreeCoordinates) : {−1,1}^[2] :=
  ![y example3_19First, y example3_19Second]

@[simp] theorem example3_19TwoBitInput_zero
    (y : FreeSignCube example3_19FreeCoordinates) :
    example3_19TwoBitInput y 0 = y example3_19First := by
  simp [example3_19TwoBitInput]

@[simp] theorem example3_19TwoBitInput_one
    (y : FreeSignCube example3_19FreeCoordinates) :
    example3_19TwoBitInput y 1 = y example3_19Second := by
  simp [example3_19TwoBitInput]

@[simp] theorem combineSignCube_example3_19_zero
    (y : FreeSignCube example3_19FreeCoordinates) :
    combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment 0 =
      y example3_19First := by
  change combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment
      (example3_19First : Fin 4) = y example3_19First
  exact combineSignCube_apply_free _ _ _ _

@[simp] theorem combineSignCube_example3_19_one
    (y : FreeSignCube example3_19FreeCoordinates) :
    combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment 1 =
      y example3_19Second := by
  change combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment
      (example3_19Second : Fin 4) = y example3_19Second
  exact combineSignCube_apply_free _ _ _ _

@[simp] theorem combineSignCube_example3_19_two
    (y : FreeSignCube example3_19FreeCoordinates) :
    combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment 2 = 1 := by
  change combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment
      (⟨2, by simp [example3_19FreeCoordinates]⟩ :
        FixedIndex example3_19FreeCoordinates) = 1
  rw [combineSignCube_apply_fixed, example3_19FixedAssignment_two]

@[simp] theorem combineSignCube_example3_19_three
    (y : FreeSignCube example3_19FreeCoordinates) :
    combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment 3 = -1 := by
  change combineSignCube example3_19FreeCoordinates y example3_19FixedAssignment
      (⟨3, by simp [example3_19FreeCoordinates]⟩ :
        FixedIndex example3_19FreeCoordinates) = -1
  rw [combineSignCube_apply_fixed, example3_19FixedAssignment_three]

/-- The restriction in Example 3.19 is the two-bit minimum function, represented by the already
established Boolean `orFunction` in the book's `-1 = True` convention. -/
theorem example3_19_restriction_eq_orFunction :
    signRestriction example3_19Function example3_19FreeCoordinates
        example3_19FixedAssignment =
      fun y ↦ orFunction 2 (example3_19TwoBitInput y) := by
  classical
  funext y
  rcases Int.units_eq_one_or (y example3_19First) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (y example3_19Second) with h₂ | h₂ <;>
    simp [signRestriction, example3_19Function, example3_19Predicate, orFunction,
      example3_19TwoBitInput, Fin.forall_fin_two, h₁, h₂, signValue]

/-- The defining `+1` criterion for the restricted two-bit function in Example 3.19. -/
theorem example3_19_restriction_eq_one_iff
    (y : FreeSignCube example3_19FreeCoordinates) :
    signRestriction example3_19Function example3_19FreeCoordinates
        example3_19FixedAssignment y = 1 ↔
      y example3_19First = 1 ∧ y example3_19Second = 1 := by
  rw [congrFun example3_19_restriction_eq_orFunction y]
  simp [orFunction, example3_19TwoBitInput, Fin.forall_fin_two]

/-- O'Donnell, Example 3.19, equation (3.4): the Fourier expansion after fixing
`x₃ = 1, x₄ = -1`. -/
theorem example3_19_restriction_fourier_expansion
    (y : FreeSignCube example3_19FreeCoordinates) :
    signValue (signRestriction example3_19Function example3_19FreeCoordinates
      example3_19FixedAssignment y) =
      -1 / 2 + 1 / 2 * signValue (y example3_19First) +
        1 / 2 * signValue (y example3_19Second) +
        1 / 2 * signValue (y example3_19First) *
          signValue (y example3_19Second) := by
  rw [congrFun example3_19_restriction_eq_orFunction y]
  rcases Int.units_eq_one_or (y example3_19First) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (y example3_19Second) with h₂ | h₂ <;>
    simp [orFunction, example3_19TwoBitInput, Fin.forall_fin_two, h₁, h₂, signValue] <;>
    norm_num

/-- The first-coordinate Fourier coefficient of the concrete restriction in Example 3.19 is
`1 / 2`. This is the typed version of the coefficient computation following equation (3.4). -/
theorem example3_19_restrictionFourierCoeff_first :
    restrictionFourierCoeff example3_19Function.toReal
        example3_19FreeCoordinates {example3_19First}
        example3_19FixedAssignment = 1 / 2 := by
  classical
  have hne : example3_19First ≠ example3_19Second := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num [example3_19First, example3_19Second] at hval
  have hpair :
      ({example3_19First, example3_19Second} :
          Finset example3_19FreeCoordinates) ≠ {example3_19First} := by
    intro h
    have hmem : example3_19Second ∈
        ({example3_19First} : Finset example3_19FreeCoordinates) := by
      rw [← h]
      simp
    exact hne (Finset.mem_singleton.mp hmem).symm
  have hexp (y : FreeSignCube example3_19FreeCoordinates) :
      signValue
          (signRestriction example3_19Function example3_19FreeCoordinates
            example3_19FixedAssignment y) =
        (-1 / 2 : ℝ) * indexedMonomial ∅ y +
          (1 / 2 : ℝ) * indexedMonomial {example3_19First} y +
          (1 / 2 : ℝ) * indexedMonomial {example3_19Second} y +
          (1 / 2 : ℝ) *
            indexedMonomial {example3_19First, example3_19Second} y := by
    rw [example3_19_restriction_fourier_expansion]
    simp [indexedMonomial, hne]
    ring
  rw [restrictionFourierCoeff, indexedFourierCoeff]
  calc
    (𝔼 y, signRestriction example3_19Function.toReal
          example3_19FreeCoordinates example3_19FixedAssignment y *
        indexedMonomial {example3_19First} y) =
        𝔼 y,
          (((-1 / 2 : ℝ) * indexedMonomial ∅ y +
              (1 / 2 : ℝ) * indexedMonomial {example3_19First} y +
              (1 / 2 : ℝ) * indexedMonomial {example3_19Second} y +
              (1 / 2 : ℝ) *
                indexedMonomial {example3_19First, example3_19Second} y) *
            indexedMonomial {example3_19First} y) := by
          apply Finset.expect_congr rfl
          intro y _
          rw [show signRestriction example3_19Function.toReal
              example3_19FreeCoordinates example3_19FixedAssignment y =
                signValue
                  (signRestriction example3_19Function example3_19FreeCoordinates
                    example3_19FixedAssignment y) by rfl]
          rw [hexp]
    _ = 𝔼 y, (
          (-1 / 2 : ℝ) *
              (indexedMonomial ∅ y * indexedMonomial {example3_19First} y) +
            (1 / 2 : ℝ) *
              (indexedMonomial {example3_19First} y *
                indexedMonomial {example3_19First} y) +
            (1 / 2 : ℝ) *
              (indexedMonomial {example3_19Second} y *
                indexedMonomial {example3_19First} y) +
            (1 / 2 : ℝ) *
              (indexedMonomial {example3_19First, example3_19Second} y *
                indexedMonomial {example3_19First} y)) := by
          apply Finset.expect_congr rfl
          intro y _
          ring
    _ = (-1 / 2 : ℝ) *
            (𝔼 y, indexedMonomial ∅ y * indexedMonomial {example3_19First} y) +
          (1 / 2 : ℝ) *
            (𝔼 y, indexedMonomial {example3_19First} y *
              indexedMonomial {example3_19First} y) +
          (1 / 2 : ℝ) *
            (𝔼 y, indexedMonomial {example3_19Second} y *
              indexedMonomial {example3_19First} y) +
          (1 / 2 : ℝ) *
            (𝔼 y, indexedMonomial {example3_19First, example3_19Second} y *
              indexedMonomial {example3_19First} y) := by
          simp_rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ = 1 / 2 := by
          rw [expect_indexedMonomial_mul, expect_indexedMonomial_mul,
            expect_indexedMonomial_mul, expect_indexedMonomial_mul]
          simp [Ne.symm hne, hpair]

/-- The coefficient arithmetic at the end of Example 3.19. -/
theorem example3_19_first_coefficient_arithmetic :
    (-1 / 8 : ℝ) + 1 / 8 + 3 / 8 + 1 / 8 = 1 / 2 := by
  norm_num

/-! ## Restrictions to affine subspaces -/

noncomputable local instance submoduleFintype {n : ℕ}
    (H : Submodule 𝔽₂ 𝔽₂^[n]) : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance submoduleMembershipDecidable {n : ℕ}
    (H : Submodule 𝔽₂ 𝔽₂^[n]) : DecidablePred (fun x : 𝔽₂^[n] ↦ x ∈ H) :=
  Classical.decPred _

/-- O'Donnell, Definition 3.23, conservatively generalized in the codomain: the restriction of
`f` to the binary subspace `H`. -/
def subspaceRestriction {n : ℕ} {α : Type*} (f : 𝔽₂^[n] → α)
    (H : Submodule 𝔽₂ 𝔽₂^[n]) : H → α :=
  fun h ↦ f h.1

@[simp] theorem subspaceRestriction_apply {n : ℕ} {α : Type*} (f : 𝔽₂^[n] → α)
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (h : H) :
    subspaceRestriction f H h = f h.1 := rfl

/-- O'Donnell, Definition 3.24, conservatively generalized in the codomain: translation of the
domain by `z`. -/
def domainTranslate {n : ℕ} {α : Type*} (f : 𝔽₂^[n] → α) (z : 𝔽₂^[n]) : 𝔽₂^[n] → α :=
  fun x ↦ f (x + z)

@[simp] theorem domainTranslate_apply {n : ℕ} {α : Type*} (f : 𝔽₂^[n] → α)
    (z x : 𝔽₂^[n]) :
    domainTranslate f z x = f (x + z) := rfl

/-- O'Donnell, Fact 3.25: translating the domain multiplies a Fourier coefficient by the
corresponding Walsh character evaluated at the translation vector. -/
theorem vectorFourierCoeff_domainTranslate {n : ℕ} (f : 𝔽₂^[n] → ℝ)
    (z γ : 𝔽₂^[n]) :
    vectorFourierCoeff (domainTranslate f z) γ =
      vectorWalshCharacter γ z * vectorFourierCoeff f γ := by
  change vectorFourierCoeff (fun x ↦ f (x + z)) γ =
    vectorWalshCharacter γ z * vectorFourierCoeff f γ
  exact vectorFourierCoeff_translate_add f z γ

/-- The dot-product form of the coefficient identity in O'Donnell, Fact 3.25. -/
theorem vectorFourierCoeff_domainTranslate_eq_binarySign {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (z γ : 𝔽₂^[n]) :
    vectorFourierCoeff (domainTranslate f z) γ =
      binarySign (f₂DotProduct γ z) * vectorFourierCoeff f γ := by
  rw [vectorFourierCoeff_domainTranslate, vectorWalshCharacter_apply]

/-- The Fourier-expansion form of O'Donnell, Fact 3.25. -/
theorem domainTranslate_fourier_expansion {n : ℕ} (f : 𝔽₂^[n] → ℝ)
    (z x : 𝔽₂^[n]) :
    domainTranslate f z x =
      ∑ γ, vectorWalshCharacter γ z * vectorFourierCoeff f γ *
        vectorWalshCharacter γ x := by
  classical
  calc
    domainTranslate f z x =
        ∑ γ, vectorFourierCoeff (domainTranslate f z) γ *
          vectorWalshCharacter γ x := vector_fourier_expansion _ x
    _ = ∑ γ, vectorWalshCharacter γ z * vectorFourierCoeff f γ *
          vectorWalshCharacter γ x := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [vectorFourierCoeff_domainTranslate]

/-- O'Donnell, Definition 3.26, conservatively generalized in the codomain: restriction to the
coset `H + z`, with the representative `z` kept explicit. -/
def affineSubspaceRestriction {n : ℕ} {α : Type*} (f : 𝔽₂^[n] → α)
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) : H → α :=
  subspaceRestriction (domainTranslate f z) H

@[simp] theorem affineSubspaceRestriction_apply {n : ℕ} {α : Type*}
    (f : 𝔽₂^[n] → α) (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) (h : H) :
    affineSubspaceRestriction f H z h = f (h.1 + z) := rfl

/-- The normalized Fourier coefficient of a function on a finite additive commutative group,
indexed by an additive character. -/
noncomputable def finiteAddFourierCoeff {G : Type*} [Fintype G] [AddCommGroup G]
    (g : G → ℝ) (ψ : AddChar G ℝ) : ℝ :=
  uniformInner g ψ

/-- The coefficient at the trivial additive character is the uniform expectation. -/
theorem finiteAddFourierCoeff_zero_eq_expect {G : Type*} [Fintype G] [AddCommGroup G]
    (g : G → ℝ) :
    finiteAddFourierCoeff g (0 : AddChar G ℝ) = 𝔼 x, g x := by
  rw [finiteAddFourierCoeff, uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp [RCLike.inner_apply]

/-- The Fourier coefficient at the trivial character of an affine-subspace restriction is its
uniform average. -/
theorem finiteAddFourierCoeff_affineSubspaceRestriction_zero_eq_expect {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    finiteAddFourierCoeff (affineSubspaceRestriction f H z) (0 : AddChar H ℝ) =
      𝔼 h : H, f (h.1 + z) := by
  calc
    finiteAddFourierCoeff (affineSubspaceRestriction f H z) (0 : AddChar H ℝ) =
        𝔼 h : H, affineSubspaceRestriction f H z h :=
      finiteAddFourierCoeff_zero_eq_expect _
    _ = 𝔼 h : H, f (h.1 + z) := by
      apply Finset.expect_congr rfl
      intro h _
      rw [affineSubspaceRestriction_apply]

/-- A vector-indexed Walsh character averaged over `H` is one precisely when its index lies in
`Hᵖ`, and is zero otherwise. -/
theorem expect_vectorWalshCharacter_submodule {n : ℕ}
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n]) :
    (𝔼 h : H, vectorWalshCharacter γ h.1) =
      if γ ∈ perpendicularSubspace H then 1 else 0 := by
  classical
  letI := Fintype.ofFinite H
  have hcharacter :
      (fun h : H ↦ vectorWalshCharacter γ h.1) = subspaceEvaluationCharacter H γ := by
    funext h
    change vectorWalshCharacter γ h.1 = vectorWalshCharacter h.1 γ
    rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply]
    congr 1
    exact dotProduct_comm γ h.1
  rw [hcharacter]
  simpa [subspaceEvaluationCharacter_eq_zero_iff] using
    AddChar.expect_eq_ite (subspaceEvaluationCharacter H γ)

/-- The uniform inner product of the density of `H` with a translated function is the Fourier
sum over `Hᵖ`. This is the Plancherel calculation immediately preceding the Poisson Summation
Formula. -/
theorem uniformInner_subsetDensity_domainTranslate_eq_sum {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    ⟪subsetDensity (H : Set 𝔽₂^[n]) ⟨0, H.zero_mem⟩, domainTranslate f z⟫ᵤ =
      ∑ γ : perpendicularSubspace H,
        vectorWalshCharacter γ.1 z * vectorFourierCoeff f γ.1 := by
  classical
  letI := Fintype.ofFinite (perpendicularSubspace H)
  calc
    ⟪subsetDensity (H : Set 𝔽₂^[n]) ⟨0, H.zero_mem⟩, domainTranslate f z⟫ᵤ =
        ∑ γ : 𝔽₂^[n],
          vectorFourierCoeff
              (subsetDensity (H : Set 𝔽₂^[n]) ⟨0, H.zero_mem⟩) γ *
            vectorFourierCoeff (domainTranslate f z) γ := by
      simpa [uniformInner, RCLike.wInner_cWeight_eq_expect,
        RCLike.inner_apply, mul_comm] using
          vector_plancherel
            (subsetDensity (H : Set 𝔽₂^[n]) ⟨0, H.zero_mem⟩ : 𝔽₂^[n] → ℝ)
            (domainTranslate f z)
    _ = ∑ γ : 𝔽₂^[n], if γ ∈ perpendicularSubspace H then
          vectorWalshCharacter γ z * vectorFourierCoeff f γ else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      by_cases hγ : γ ∈ perpendicularSubspace H
      · rw [if_pos hγ, vectorFourierCoeff_domainTranslate,
          subsetDensity_submodule_fourier_expansion,
          vectorFourierCoeff_subspaceCharacterSum_of_mem _ _ hγ]
        ring
      · rw [if_neg hγ, subsetDensity_submodule_fourier_expansion,
          vectorFourierCoeff_subspaceCharacterSum_of_not_mem _ _ hγ]
        simp
    _ = ∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦
          γ ∈ perpendicularSubspace H),
          vectorWalshCharacter γ z * vectorFourierCoeff f γ := by
      rw [Finset.sum_filter]
    _ = ∑ γ : perpendicularSubspace H,
          vectorWalshCharacter γ.1 z * vectorFourierCoeff f γ.1 := by
      simpa using
        (Finset.sum_subtype
          (p := fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H)
          (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H)
          (by simp)
          (fun γ ↦ vectorWalshCharacter γ z * vectorFourierCoeff f γ))

/-- The direct finite-character calculation of the average of `f` on the coset `H + z`. -/
theorem expect_affineSubspaceRestriction_eq_sum {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    (𝔼 h : H, affineSubspaceRestriction f H z h) =
      ∑ γ : perpendicularSubspace H,
        vectorWalshCharacter γ.1 z * vectorFourierCoeff f γ.1 := by
  classical
  letI := Fintype.ofFinite H
  letI := Fintype.ofFinite (perpendicularSubspace H)
  calc
    (𝔼 h : H, affineSubspaceRestriction f H z h) =
        𝔼 h : H, ∑ γ : 𝔽₂^[n],
          (vectorWalshCharacter γ z * vectorFourierCoeff f γ) *
            vectorWalshCharacter γ h.1 := by
      apply Finset.expect_congr rfl
      intro h _
      rw [affineSubspaceRestriction_apply,
        ← domainTranslate_apply f z h.1,
        domainTranslate_fourier_expansion]
    _ = ∑ γ : 𝔽₂^[n],
          𝔼 h : H, (vectorWalshCharacter γ z * vectorFourierCoeff f γ) *
            vectorWalshCharacter γ h.1 := by
      rw [Finset.expect_sum_comm]
    _ = ∑ γ : 𝔽₂^[n],
          (vectorWalshCharacter γ z * vectorFourierCoeff f γ) *
            (𝔼 h : H, vectorWalshCharacter γ h.1) := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.mul_expect]
    _ = ∑ γ : 𝔽₂^[n], if γ ∈ perpendicularSubspace H then
          vectorWalshCharacter γ z * vectorFourierCoeff f γ else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [expect_vectorWalshCharacter_submodule]
      by_cases hγ : γ ∈ perpendicularSubspace H <;> simp [hγ]
    _ = ∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦
          γ ∈ perpendicularSubspace H),
          vectorWalshCharacter γ z * vectorFourierCoeff f γ := by
      rw [Finset.sum_filter]
    _ = ∑ γ : perpendicularSubspace H,
          vectorWalshCharacter γ.1 z * vectorFourierCoeff f γ.1 := by
      simpa using
        (Finset.sum_subtype
          (p := fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H)
          (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H)
          (by simp)
          (fun γ ↦ vectorWalshCharacter γ z * vectorFourierCoeff f γ))

/-- The average value of `f` on `H + z` is the uniform inner product of the density of `H`
with the translated function, as stated immediately before the Poisson Summation Formula. -/
theorem expect_affineSubspaceRestriction_eq_uniformInner {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    (𝔼 h : H, affineSubspaceRestriction f H z h) =
      ⟪subsetDensity (H : Set 𝔽₂^[n]) ⟨0, H.zero_mem⟩, domainTranslate f z⟫ᵤ := by
  rw [expect_affineSubspaceRestriction_eq_sum,
    uniformInner_subsetDensity_domainTranslate_eq_sum]

/-- O'Donnell's Poisson Summation Formula on the binary cube. -/
theorem poissonSummationFormula {n : ℕ} (f : 𝔽₂^[n] → ℝ)
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (z : 𝔽₂^[n]) :
    (𝔼 h : H, f (h.1 + z)) =
      ∑ γ : perpendicularSubspace H,
        vectorWalshCharacter γ.1 z * vectorFourierCoeff f γ.1 := by
  simpa using expect_affineSubspaceRestriction_eq_sum f H z

end FABL
