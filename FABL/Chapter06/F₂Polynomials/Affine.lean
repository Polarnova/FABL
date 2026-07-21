/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree

/-!
# Affine Boolean functions

Affine functions on the additive binary cube have algebraic degree at most one, every function of
degree at most one is affine, and algebraic degree is invariant under affine equivalence.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The affine Boolean function `x ↦ b + a · x`. -/
def affineFunction (b : 𝔽₂) (a : F₂Cube n) : F₂BooleanFunction n :=
  fun x ↦ b + f₂DotProduct a x

/-- The ANF coefficients of an affine function. -/
def affineCoefficients (b : 𝔽₂) (a : F₂Cube n) : ANFCoefficients n :=
  fun S ↦ if S = ∅ then b else if S.card = 1 then ∑ i ∈ S, a i else 0

/-- Evaluating the affine coefficient family gives the affine function. -/
theorem anfEval_affineCoefficients
    (b : 𝔽₂) (a : F₂Cube n) :
    anfEval (affineCoefficients b a) = affineFunction b a := by
  classical
  funext x
  rw [anfEval, affineFunction, f₂DotProduct]
  let relevant : Finset (Finset (Fin n)) :=
    {∅} ∪ Finset.univ.filter (fun S ↦ S.card = 1)
  have hreduce :
      ∑ S ∈ relevant, affineCoefficients b a S * anfMonomial S x =
        ∑ S, affineCoefficients b a S * anfMonomial S x := by
    apply Finset.sum_subset
    · intro S hS
      simp
    · intro S _ hS
      have hne : S ≠ ∅ := by
        intro h
        apply hS
        simp [relevant, h]
      have hcard : S.card ≠ 1 := by
        intro h
        apply hS
        simp [relevant, h]
      simp [affineCoefficients, hne, hcard]
  rw [← hreduce]
  have hdisjoint : Disjoint ({∅} : Finset (Finset (Fin n)))
      (Finset.univ.filter (fun S ↦ S.card = 1)) := by
    simp
  rw [Finset.sum_union hdisjoint]
  simp only [Finset.sum_singleton]
  have hsingletons :
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) ↦ S.card = 1),
          affineCoefficients b a S * anfMonomial S x =
        ∑ i, affineCoefficients b a {i} * anfMonomial {i} x := by
    apply Finset.sum_bij (fun S hS ↦ (card_eq_one.mp (by simpa using hS)).choose)
    · intro S hS
      simp
    · intro S hS T hT heq
      obtain ⟨i, hi⟩ := card_eq_one.mp (by simpa using hS)
      obtain ⟨j, hj⟩ := card_eq_one.mp (by simpa using hT)
      subst hi
      subst hj
      simpa using heq
    · intro i _
      refine ⟨{i}, ⟨by simp, ?_⟩⟩
      simp
    · intro S hS
      obtain ⟨i, rfl⟩ := card_eq_one.mp (by simpa using hS)
      simp
  rw [hsingletons]
  simp [affineCoefficients, anfMonomial, dotProduct]

/-- The canonical ANF transform recovers the affine coefficient family. -/
theorem anfCoeff_affineFunction (b : 𝔽₂) (a : F₂Cube n) :
    anfCoeff (affineFunction b a) = affineCoefficients b a := by
  apply anfEval_injective
  rw [anfEval_anfCoeff, anfEval_affineCoefficients]

/-- Affine functions have algebraic degree at most one. -/
theorem functionAlgebraicDegree_affineFunction_le_one
    (b : 𝔽₂) (a : F₂Cube n) :
    functionAlgebraicDegree (affineFunction b a) ≤ 1 := by
  rw [functionAlgebraicDegree, anfCoeff_affineFunction, algebraicDegree_le_iff]
  intro S hS
  by_contra hcard
  have hne : S ≠ ∅ := by
    intro h
    subst h
    simp at hcard
  have hnotone : S.card ≠ 1 := by omega
  exact hS (by simp [affineCoefficients, hne, hnotone])

/-- Every Boolean function of algebraic degree at most one is affine. -/
theorem exists_affineFunction_of_functionAlgebraicDegree_le_one
    (f : F₂BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ 1) :
    ∃ b a, f = affineFunction b a := by
  let b := anfCoeff f ∅
  let a : F₂Cube n := fun i ↦ anfCoeff f {i}
  refine ⟨b, a, ?_⟩
  rw [← anfEval_anfCoeff f, ← anfEval_affineCoefficients]
  congr 1
  funext S
  by_cases hS0 : S = ∅
  · subst S
    simp [affineCoefficients, b]
  · by_cases hScard : S.card = 1
    · obtain ⟨i, rfl⟩ := card_eq_one.mp hScard
      simp [affineCoefficients, a]
    · have hcard : 1 < S.card := by
        have hpos : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hS0)
        omega
      have hzero : anfCoeff f S = 0 := by
        by_contra hne
        have hle := (algebraicDegree_le_iff (anfCoeff f) 1).mp hdegree S hne
        omega
      simp [affineCoefficients, hS0, hScard, hzero]

/-- Every coordinate of an affine map on the binary cube has algebraic degree at most one. -/
theorem functionAlgebraicDegree_affineMap_coordinate_le_one
    (L : F₂Cube n →ᵃ[𝔽₂] F₂Cube n) (i : Fin n) :
    functionAlgebraicDegree (fun x ↦ L x i) ≤ 1 := by
  have hlinear : IsF₂Linear (fun x ↦ L.linear x i) := by
    intro x y
    exact congrArg (fun z ↦ z i) (L.linear.map_add x y)
  obtain ⟨a, ha⟩ := (isF₂Linear_iff_exists_dotProduct _).mp hlinear
  have hcoordinate : (fun x ↦ L x i) = affineFunction (L 0 i) a := by
    funext x
    have hdecomp : L x = L.linear x + L 0 := by
      simpa using congrFun (AffineMap.decomp L) x
    calc
      L x i = L.linear x i + L 0 i := by
        simpa using congrArg (fun z ↦ z i) hdecomp
      _ = f₂DotProduct a x + L 0 i := by rw [ha x]
      _ = L 0 i + f₂DotProduct a x := add_comm _ _
      _ = affineFunction (L 0 i) a x := rfl
  rw [hcoordinate]
  exact functionAlgebraicDegree_affineFunction_le_one (L 0 i) a

/-- Substituting affine coordinates into a square-free monomial does not increase its degree. -/
theorem functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card
    (L : F₂Cube n →ᵃ[𝔽₂] F₂Cube n)
    (S : Finset (Fin n)) :
    functionAlgebraicDegree (fun x ↦ anfMonomial S (L x)) ≤ S.card := by
  calc
    functionAlgebraicDegree (fun x ↦ anfMonomial S (L x)) ≤
        ∑ i ∈ S, functionAlgebraicDegree (fun x ↦ L x i) := by
      have hfunctions : (∏ i ∈ S, (fun x ↦ L x i)) =
          (fun x ↦ anfMonomial S (L x)) := by
        funext x
        simp [anfMonomial, Finset.prod_apply]
      rw [← hfunctions]
      exact functionAlgebraicDegree_finset_prod_le S (fun i x ↦ L x i)
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact functionAlgebraicDegree_affineMap_coordinate_le_one L i
    _ = S.card := by simp

/-- Composition with an affine map on the binary cube cannot increase algebraic degree. -/
theorem functionAlgebraicDegree_comp_affineMap_le
    (f : F₂BooleanFunction n)
    (L : F₂Cube n →ᵃ[𝔽₂] F₂Cube n) :
    functionAlgebraicDegree (f ∘ L) ≤ functionAlgebraicDegree f := by
  classical
  let term : Finset (Fin n) → F₂BooleanFunction n :=
    fun S x ↦ anfCoeff f S * anfMonomial S (L x)
  have hsum : f ∘ L = ∑ S, term S := by
    funext x
    simp only [Function.comp_apply, Fintype.sum_apply, term]
    exact (congrFun (anfEval_anfCoeff f) (L x)).symm
  rw [hsum]
  exact functionAlgebraicDegree_finset_sum_le Finset.univ term
      (functionAlgebraicDegree f) (by
        intro S _
        by_cases hS : anfCoeff f S = 0
        · have hterm : term S = 0 := by
            funext x
            simp [term, hS]
          rw [hterm]
          rw [functionAlgebraicDegree_zero]
          exact Nat.zero_le _
        · have hSone : anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
          have hterm : term S = fun x ↦ anfMonomial S (L x) := by
            funext x
            simp [term, hSone]
          rw [hterm]
          apply (functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card L S).trans
          exact (algebraicDegree_le_iff (anfCoeff f) _).mp
            (by rfl) S hS)

/-- Algebraic degree is invariant under affine equivalences of the binary cube. -/
theorem functionAlgebraicDegree_comp_affineEquiv
    (f : F₂BooleanFunction n)
    (L : F₂Cube n ≃ᵃ[𝔽₂] F₂Cube n) :
    functionAlgebraicDegree (f ∘ L) = functionAlgebraicDegree f := by
  apply Nat.le_antisymm
  · exact functionAlgebraicDegree_comp_affineMap_le f L.toAffineMap
  · have h := functionAlgebraicDegree_comp_affineMap_le (f ∘ L) L.symm.toAffineMap
    have hcomp : (f ∘ L) ∘ L.symm.toAffineMap = f := by
      funext x
      simp
    rw [hcomp] at h
    exact h

end FABL
