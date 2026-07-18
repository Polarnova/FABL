/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.SubspacesAndDecisionTrees.DecisionTrees

/-!
# Degree-one weight

Book items: Exercise 5.29 and Proposition 5.24.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

open F₂DecisionTree

/-- A binary frequency lies in the perpendicular of a coordinate-zero subspace exactly when
its support is contained in the fixed coordinates. -/
theorem mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
    (coordinates : Finset (Fin n)) (γ : 𝔽₂^[n]) :
    γ ∈ perpendicularSubspace (coordinateZeroSubspace coordinates) ↔
      f₂Support γ ⊆ coordinates := by
  constructor
  · exact f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace coordinates γ
  · intro hsupport
    rw [mem_perpendicularSubspace_iff]
    intro x hx
    rw [f₂DotProduct_eq_coordinateSum_f₂Support]
    change (∑ i ∈ f₂Support γ, x i) = 0
    apply Finset.sum_eq_zero
    intro i hi
    exact (mem_coordinateZeroSubspace_iff coordinates x).1 hx i (hsupport hi)

/-- Exercise 5.29: the Fourier coefficients of a coordinate-subcube indicator have magnitude
`2⁻ᵏ` exactly on frequencies supported inside its `k` fixed coordinates. -/
theorem abs_vectorFourierCoeff_setIndicator_coordinateSubcube
    (coordinates : Finset (Fin n)) (basePoint γ : 𝔽₂^[n]) :
    |vectorFourierCoeff (setIndicator (coordinateSubcube coordinates basePoint)) γ| =
      if f₂Support γ ⊆ coordinates then ((2 : ℝ) ^ coordinates.card)⁻¹ else 0 := by
  rw [coordinateSubcube_eq_binaryAffineSubspace]
  by_cases hsupport : f₂Support γ ⊆ coordinates
  · rw [if_pos hsupport,
      abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _
        ((mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
          coordinates γ).2 hsupport),
      inversePerpendicularCard, f₂Codimension_coordinateZeroSubspace]
  · rw [if_neg hsupport,
      abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _
        (fun hmem ↦ hsupport
          ((mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
            coordinates γ).1 hmem))]

/-- Exercise 5.29: a coordinate subcube of codimension `k` has uniform expectation `2⁻ᵏ`. -/
theorem expect_setIndicator_coordinateSubcube
    (coordinates : Finset (Fin n)) (basePoint : 𝔽₂^[n]) :
    (𝔼 x, setIndicator (coordinateSubcube coordinates basePoint) x) =
      ((2 : ℝ) ^ coordinates.card)⁻¹ := by
  rw [coordinateSubcube_eq_binaryAffineSubspace]
  calc
    (𝔼 x, setIndicator
        (binaryAffineSubspace (coordinateZeroSubspace coordinates) basePoint :
          Set 𝔽₂^[n]) x) =
        vectorFourierCoeff
          (setIndicator
            (binaryAffineSubspace (coordinateZeroSubspace coordinates) basePoint :
              Set 𝔽₂^[n])) 0 := by
      rw [vectorFourierCoeff_eq_expect]
      simp
    _ = vectorWalshCharacter 0 basePoint *
        inversePerpendicularCard (coordinateZeroSubspace coordinates) := by
      exact vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem
        (coordinateZeroSubspace coordinates) basePoint 0
        (perpendicularSubspace (coordinateZeroSubspace coordinates)).zero_mem
    _ = ((2 : ℝ) ^ coordinates.card)⁻¹ := by
      simp [inversePerpendicularCard, f₂Codimension_coordinateZeroSubspace]

/-- Exercise 5.29: the level-one Fourier weight of a coordinate-subcube indicator is
`k 2⁻²ᵏ`, written directly in vector-indexed Fourier notation. -/
theorem sum_sq_vectorFourierCoeff_support_card_one_setIndicator_coordinateSubcube
    (coordinates : Finset (Fin n)) (basePoint : 𝔽₂^[n]) :
    (∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ (f₂Support γ).card = 1),
        vectorFourierCoeff (setIndicator (coordinateSubcube coordinates basePoint)) γ ^ 2) =
      (coordinates.card : ℝ) * (((2 : ℝ) ^ coordinates.card)⁻¹) ^ 2 := by
  classical
  calc
    (∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ (f₂Support γ).card = 1),
        vectorFourierCoeff (setIndicator (coordinateSubcube coordinates basePoint)) γ ^ 2) =
        ∑ i : Fin n,
          vectorFourierCoeff
            (setIndicator (coordinateSubcube coordinates basePoint))
            (f₂CubeOfFinset ({i} : Finset (Fin n))) ^ 2 := by
      symm
      apply Finset.sum_bij
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
          f₂CubeOfFinset ({i} : Finset (Fin n)))
      · intro i _
        have hsupport :
            f₂Support (f₂CubeOfFinset ({i} : Finset (Fin n))) = {i} :=
          (f₂CubeEquivFinset n).right_inv {i}
        simp [hsupport]
      · intro i _ j _ hij
        apply Finset.singleton_injective
        have hsupport := congrArg f₂Support hij
        calc
          ({i} : Finset (Fin n)) =
              f₂Support (f₂CubeOfFinset ({i} : Finset (Fin n))) :=
            ((f₂CubeEquivFinset n).right_inv {i}).symm
          _ = f₂Support (f₂CubeOfFinset ({j} : Finset (Fin n))) := hsupport
          _ = {j} := (f₂CubeEquivFinset n).right_inv {j}
      · intro γ hγ
        obtain ⟨i, hi⟩ :=
          Finset.card_eq_one.mp (Finset.mem_filter.mp hγ).2
        refine ⟨i, Finset.mem_univ i, ?_⟩
        apply (f₂CubeEquivFinset n).injective
        simpa [hi] using (f₂CubeEquivFinset n).right_inv ({i} : Finset (Fin n))
      · intro i _
        rfl
    _ = (coordinates.card : ℝ) * (((2 : ℝ) ^ coordinates.card)⁻¹) ^ 2 := by
      calc
        (∑ i : Fin n,
            vectorFourierCoeff
              (setIndicator (coordinateSubcube coordinates basePoint))
              (f₂CubeOfFinset ({i} : Finset (Fin n))) ^ 2) =
            ∑ i : Fin n,
              if i ∈ coordinates then (((2 : ℝ) ^ coordinates.card)⁻¹) ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          have hsupport :
              f₂Support (f₂CubeOfFinset ({i} : Finset (Fin n))) = {i} :=
            (f₂CubeEquivFinset n).right_inv {i}
          rw [← sq_abs,
            abs_vectorFourierCoeff_setIndicator_coordinateSubcube coordinates basePoint]
          simp [hsupport]
        _ = (coordinates.card : ℝ) * (((2 : ℝ) ^ coordinates.card)⁻¹) ^ 2 := by
          simp

/-- Proposition 5.24: a nontrivial coordinate-subcube indicator has expectation `2⁻ᵏ` and
degree-one Fourier weight `k 2⁻²ᵏ`. -/
theorem expectation_and_degreeOneWeight_setIndicator_coordinateSubcube
    (coordinates : Finset (Fin n)) (basePoint : 𝔽₂^[n])
    (_hcoordinates : coordinates.Nonempty) :
    (𝔼 x, setIndicator (coordinateSubcube coordinates basePoint) x) =
        ((2 : ℝ) ^ coordinates.card)⁻¹ ∧
      (∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ (f₂Support γ).card = 1),
          vectorFourierCoeff (setIndicator (coordinateSubcube coordinates basePoint)) γ ^ 2) =
        (coordinates.card : ℝ) * (((2 : ℝ) ^ coordinates.card)⁻¹) ^ 2 :=
  ⟨expect_setIndicator_coordinateSubcube coordinates basePoint,
    sum_sq_vectorFourierCoeff_support_card_one_setIndicator_coordinateSubcube
      coordinates basePoint⟩

end FABL
