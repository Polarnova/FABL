/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.SmallBias
public import FABL.Chapter01.ProbabilityDensityPushforward

/-!
# Marginals of small-bias densities

Book item: Definition 6.5.

A coordinate marginal is the finite-density pushforward through the corresponding coordinate
projection. Its Fourier coefficients are the source coefficients at the dual lifted frequency.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Restriction to the coordinates in `J`, canonically enumerated by `Fin J.card`. -/
noncomputable def coordinateProjectionLinear (J : Finset (Fin n)) :
    F₂Cube n →ₗ[𝔽₂] F₂Cube J.card where
  toFun x q := x (J.equivFin.symm q)
  map_add' := by
    intro x y
    funext q
    simp
  map_smul' := by
    intro c x
    funext q
    simp

@[simp] theorem coordinateProjectionLinear_apply
    (J : Finset (Fin n)) (x : F₂Cube n) (q : Fin J.card) :
    coordinateProjectionLinear J x q = x (J.equivFin.symm q) :=
  rfl

/-- Extend a vector on `J` by zero outside `J`. -/
noncomputable def coordinateExtension (J : Finset (Fin n))
    (z : F₂Cube J.card) : F₂Cube n :=
  fun i ↦ if hi : i ∈ J then z (J.equivFin ⟨i, hi⟩) else 0

/-- Coordinate projection is onto. -/
@[simp] theorem coordinateProjectionLinear_coordinateExtension
    (J : Finset (Fin n)) (z : F₂Cube J.card) :
    coordinateProjectionLinear J (coordinateExtension J z) = z := by
  funext q
  simp [coordinateProjectionLinear, coordinateExtension]

/-- The ambient frequency representing pullback of a character through coordinate projection. -/
noncomputable def coordinateFrequencyLift (J : Finset (Fin n))
    (γ : F₂Cube J.card) : F₂Cube n :=
  (dotProductEquiv 𝔽₂ (Fin n)).symm
    (((dotProductEquiv 𝔽₂ (Fin J.card)) γ).comp
      (coordinateProjectionLinear J))

/-- The lifted frequency represents precomposition of the dot-product functional by coordinate
projection. -/
theorem f₂DotProduct_coordinateFrequencyLift
    (J : Finset (Fin n)) (γ : F₂Cube J.card) (x : F₂Cube n) :
    f₂DotProduct (coordinateFrequencyLift J γ) x =
      f₂DotProduct γ (coordinateProjectionLinear J x) := by
  change
    dotProduct (coordinateFrequencyLift J γ) x =
      dotProduct γ (coordinateProjectionLinear J x)
  calc
    dotProduct (coordinateFrequencyLift J γ) x =
        ((dotProductEquiv 𝔽₂ (Fin n)) (coordinateFrequencyLift J γ)) x :=
      (dotProductEquiv_apply_apply 𝔽₂ (Fin n) _ _).symm
    _ = (((dotProductEquiv 𝔽₂ (Fin J.card)) γ).comp
          (coordinateProjectionLinear J)) x := by
      exact DFunLike.congr_fun
        ((dotProductEquiv 𝔽₂ (Fin n)).apply_symm_apply
          (((dotProductEquiv 𝔽₂ (Fin J.card)) γ).comp
            (coordinateProjectionLinear J))) x
    _ = ((dotProductEquiv 𝔽₂ (Fin J.card)) γ)
          (coordinateProjectionLinear J x) := rfl
    _ = dotProduct γ (coordinateProjectionLinear J x) :=
      dotProductEquiv_apply_apply 𝔽₂ (Fin J.card) _ _

/-- Walsh characters pull back through coordinate projection at the lifted frequency. -/
theorem vectorWalshCharacter_coordinateProjection
    (J : Finset (Fin n)) (γ : F₂Cube J.card) (x : F₂Cube n) :
    vectorWalshCharacter γ (coordinateProjectionLinear J x) =
      vectorWalshCharacter (coordinateFrequencyLift J γ) x := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply,
    f₂DotProduct_coordinateFrequencyLift]

/-- A nonzero frequency remains nonzero after the dual coordinate lift. -/
theorem coordinateFrequencyLift_ne_zero
    (J : Finset (Fin n)) {γ : F₂Cube J.card} (hγ : γ ≠ 0) :
    coordinateFrequencyLift J γ ≠ 0 := by
  intro hlift
  apply hγ
  apply (dotProductEquiv 𝔽₂ (Fin J.card)).injective
  apply LinearMap.ext
  intro z
  change f₂DotProduct γ z = f₂DotProduct 0 z
  have hdot :=
    f₂DotProduct_coordinateFrequencyLift J γ (coordinateExtension J z)
  rw [coordinateProjectionLinear_coordinateExtension, hlift] at hdot
  simpa [f₂DotProduct] using hdot.symm

namespace ProbabilityDensity

/-- The marginal density on the coordinates in `J`. -/
noncomputable def coordinateMarginal (φ : ProbabilityDensity n)
    (J : Finset (Fin n)) : ProbabilityDensity J.card :=
  φ.pushforward (coordinateProjectionLinear J)

/-- Fourier coefficients of a coordinate marginal are the source coefficients at the lifted
frequency. -/
theorem vectorFourierCoeff_coordinateMarginal
    (φ : ProbabilityDensity n) (J : Finset (Fin n)) (γ : F₂Cube J.card) :
    vectorFourierCoeff (φ.coordinateMarginal J) γ =
      vectorFourierCoeff φ (coordinateFrequencyLift J γ) := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  change
    (φ.coordinateMarginal J).expectation
        (fun z ↦ vectorWalshCharacter γ z) =
      φ.expectation (fun x ↦ vectorWalshCharacter (coordinateFrequencyLift J γ) x)
  rw [coordinateMarginal, pushforward_expectation]
  apply congrArg φ.expectation
  funext x
  exact vectorWalshCharacter_coordinateProjection J γ x

/-- O'Donnell, Definition 6.5: every coordinate marginal of an `ε`-biased density is
again `ε`-biased. -/
theorem IsBiased.coordinateMarginal
    {φ : ProbabilityDensity n} {ε : ℝ} (hφ : φ.IsBiased ε)
    (J : Finset (Fin n)) :
    (φ.coordinateMarginal J).IsBiased ε := by
  intro γ hγ
  rw [vectorFourierCoeff_coordinateMarginal]
  exact hφ (coordinateFrequencyLift J γ)
    (coordinateFrequencyLift_ne_zero J hγ)

end ProbabilityDensity

end FABL
