/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.FunctionsAsMultilinearPolynomials
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite-field infrastructure for pseudorandom constructions

Book support items: the binary extension-field model, the finite-field root bound, and
Vandermonde nonsingularity in Section 6.3.
-/

open Finset Polynomial
open scoped BooleanCube Matrix

@[expose] public section

namespace FABL

/-- The canonical field with `2 ^ ℓ` elements supplied by Mathlib. -/
abbrev BinaryExtensionField (ℓ : ℕ) := GaloisField 2 ℓ

/-- A positive-degree binary extension field has dimension `ℓ` over `𝔽₂`. -/
theorem binaryExtensionField_finrank {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Module.finrank 𝔽₂ (BinaryExtensionField ℓ) = ℓ :=
  GaloisField.finrank 2 hℓ

/-- A positive-degree binary extension field has exactly `2 ^ ℓ` elements. -/
theorem binaryExtensionField_natCard {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Nat.card (BinaryExtensionField ℓ) = 2 ^ ℓ :=
  GaloisField.card 2 ℓ hℓ

/-- A basis of the binary extension field indexed by its `ℓ` binary coordinates. -/
noncomputable def binaryExtensionBasis {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Module.Basis (Fin ℓ) 𝔽₂ (BinaryExtensionField ℓ) :=
  Module.finBasisOfFinrankEq 𝔽₂ (BinaryExtensionField ℓ)
    (binaryExtensionField_finrank hℓ)

/-- The coordinate encoding of a binary extension field as the additive binary cube. -/
noncomputable def binaryExtensionEncode {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    BinaryExtensionField ℓ ≃ₗ[𝔽₂] F₂Cube ℓ :=
  (binaryExtensionBasis hℓ).equivFun

@[simp] theorem binaryExtensionEncode_zero {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    binaryExtensionEncode hℓ 0 = 0 :=
  map_zero (binaryExtensionEncode hℓ)

@[simp] theorem binaryExtensionEncode_add {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (a b : BinaryExtensionField ℓ) :
    binaryExtensionEncode hℓ (a + b) =
      binaryExtensionEncode hℓ a + binaryExtensionEncode hℓ b :=
  map_add (binaryExtensionEncode hℓ) a b

/-- A nonzero polynomial over a field has at most its degree many roots. -/
theorem ncard_rootSet_le_natDegree {K : Type*} [Field K]
    (p : K[X]) :
    Set.ncard (p.rootSet K) ≤ p.natDegree :=
  Polynomial.ncard_rootSet_le p K

/-- Distinct evaluation points give a nonsingular Vandermonde matrix. -/
theorem det_vandermonde_ne_zero_of_injective
    {K : Type*} [Field K] {k : ℕ} (α : Fin k → K)
    (hα : Function.Injective α) :
    (Matrix.vandermonde α).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr hα

/-- A vector annihilated by a Vandermonde matrix at distinct points is zero. -/
theorem eq_zero_of_vandermonde_mulVec_eq_zero
    {K : Type*} [Field K] {k : ℕ} (α : Fin k → K)
    (hα : Function.Injective α) (v : Fin k → K)
    (hv : Matrix.vandermonde α *ᵥ v = 0) :
    v = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero
    (det_vandermonde_ne_zero_of_injective α hα) hv

end FABL
