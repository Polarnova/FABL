/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.SmallBias
public import FABL.Chapter01.ProbabilityDensityPushforward
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear constructions of almost k-wise independent distributions

Book items: Proposition 6.31 and Lemma 6.34.

The row space of a binary matrix is represented as the range of Mathlib's row-combination
linear map.  Mathlib identifies this range with the span of the matrix rows.  The law of
`yᵀH` is represented by the normalized pushforward of a probability density.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {m n : ℕ}

/-! ## Matrix row spaces and column sums -/

/-- The row space of `H`, represented as the range of its row-combination linear map. -/
def matrixRowSpan (H : Matrix (Fin m) (Fin n) 𝔽₂) :
    Submodule 𝔽₂ 𝔽₂^[n] :=
  LinearMap.range H.vecMulLinear

/-- The range representation of `matrixRowSpan` is exactly the span of the rows. -/
theorem matrixRowSpan_eq_span_rows (H : Matrix (Fin m) (Fin n) 𝔽₂) :
    matrixRowSpan H = Submodule.span 𝔽₂ (Set.range H.row) :=
  range_vecMulLinear H

/-- The sum of the columns indexed by `S`, expressed as multiplication by its indicator vector. -/
def matrixColumnSum (H : Matrix (Fin m) (Fin n) 𝔽₂)
    (S : Finset (Fin n)) : 𝔽₂^[m] :=
  H *ᵥ f₂CubeOfFinset S

/-- The column sum indexed by the support of `γ` is matrix multiplication by `γ`. -/
@[simp] theorem matrixColumnSum_f₂Support
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (γ : 𝔽₂^[n]) :
    matrixColumnSum H (f₂Support γ) = H *ᵥ γ := by
  have hsupport := (f₂CubeEquivFinset n).left_inv γ
  change f₂CubeOfFinset (f₂Support γ) = γ at hsupport
  change H *ᵥ f₂CubeOfFinset (f₂Support γ) = H *ᵥ γ
  rw [hsupport]

/-- Every nonempty sum of at most `k` columns of `H` is nonzero. -/
def HasNonzeroColumnSumsUpTo (H : Matrix (Fin m) (Fin n) 𝔽₂)
    (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k → matrixColumnSum H S ≠ 0

/-- A vector has nonempty binary support exactly when it is nonzero. -/
theorem f₂Support_nonempty_iff (γ : 𝔽₂^[n]) :
    (f₂Support γ).Nonempty ↔ γ ≠ 0 := by
  constructor
  · intro hsupport hzero
    subst γ
    simp [f₂Support] at hsupport
  · intro hγ
    rw [Finset.nonempty_iff_ne_empty]
    intro hsupport
    apply hγ
    apply (f₂CubeEquivFinset n).injective
    simpa [f₂Support] using hsupport

/-- Dot products commute with row-vector/matrix multiplication by transposing the
matrix action to the Fourier frequency. -/
theorem f₂DotProduct_vecMul (H : Matrix (Fin m) (Fin n) 𝔽₂)
    (γ : 𝔽₂^[n]) (y : 𝔽₂^[m]) :
    f₂DotProduct γ (y ᵥ* H) = f₂DotProduct (H *ᵥ γ) y := by
  simp only [f₂DotProduct]
  calc
    γ ⬝ᵥ (y ᵥ* H) = (y ᵥ* H) ⬝ᵥ γ := dotProduct_comm _ _
    _ = y ⬝ᵥ (H *ᵥ γ) := (Matrix.dotProduct_mulVec y H γ).symm
    _ = (H *ᵥ γ) ⬝ᵥ y := dotProduct_comm _ _

/-- A Walsh character pulled back through `y ↦ yᵀH` has frequency `Hγ`. -/
theorem vectorWalshCharacter_vecMul (H : Matrix (Fin m) (Fin n) 𝔽₂)
    (γ : 𝔽₂^[n]) (y : 𝔽₂^[m]) :
    vectorWalshCharacter γ (y ᵥ* H) =
      vectorWalshCharacter (H *ᵥ γ) y := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply,
    f₂DotProduct_vecMul]

/-- The perpendicular of the row span is the kernel of multiplication by `H`. -/
theorem mem_perpendicular_matrixRowSpan_iff_mulVec_eq_zero
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (γ : 𝔽₂^[n]) :
    γ ∈ perpendicularSubspace (matrixRowSpan H) ↔ H *ᵥ γ = 0 := by
  constructor
  · intro hγ
    funext i
    have hrow : H.row i ∈ matrixRowSpan H := by
      rw [matrixRowSpan_eq_span_rows]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hdot :=
      (mem_perpendicularSubspace_iff (matrixRowSpan H) γ).1 hγ
        (H.row i) hrow
    change f₂DotProduct (H.row i) γ = 0
    simpa [f₂DotProduct, dotProduct_comm] using hdot
  · intro hzero
    rw [mem_perpendicularSubspace_iff]
    intro x hx
    rw [matrixRowSpan] at hx
    rcases hx with ⟨y, rfl⟩
    change f₂DotProduct γ (y ᵥ* H) = 0
    rw [f₂DotProduct_vecMul, hzero]
    simp [f₂DotProduct]

/-! ## Low-degree Fourier regularity on the binary cube -/

/-- Low-degree regularity after the binary/sign equivalence is the corresponding
vector-indexed Fourier bound on low-weight nonzero frequencies. -/
theorem isLowDegreeFourierRegular_binaryFunctionOnSignCube_iff
    (ε : ℝ) (k : ℕ) (f : 𝔽₂^[n] → ℝ) :
    IsLowDegreeFourierRegular ε k (binaryFunctionOnSignCube f) ↔
      ∀ γ : 𝔽₂^[n], γ ≠ 0 → (f₂Support γ).card ≤ k →
        |vectorFourierCoeff f γ| ≤ ε := by
  constructor
  · intro h γ hγ hcard
    rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h (f₂Support γ) ((f₂Support_nonempty_iff γ).2 hγ) hcard
  · intro h S hS hcard
    let γ : 𝔽₂^[n] := (f₂CubeEquivFinset n).symm S
    have hsupport : f₂Support γ = S :=
      (f₂CubeEquivFinset n).apply_symm_apply S
    have hγ : γ ≠ 0 :=
      (f₂Support_nonempty_iff γ).1 (hsupport.symm ▸ hS)
    rw [← hsupport,
      ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h γ hγ (by simpa [hsupport] using hcard)

/-! ## Proposition 6.31 -/

/-- The normalized uniform density on the row span of `H`. -/
noncomputable def matrixRowSpanDensity
    (H : Matrix (Fin m) (Fin n) 𝔽₂) : ProbabilityDensity n :=
  subsetDensity (matrixRowSpan H : Set 𝔽₂^[n])
    ⟨0, (matrixRowSpan H).zero_mem⟩

/-- The row-span density has coefficient one exactly on the kernel of `H`. -/
theorem vectorFourierCoeff_matrixRowSpanDensity
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (matrixRowSpanDensity H) γ =
      if H *ᵥ γ = 0 then 1 else 0 := by
  rw [matrixRowSpanDensity, subsetDensity_submodule_fourier_expansion]
  by_cases hzero : H *ᵥ γ = 0
  · rw [if_pos hzero]
    exact vectorFourierCoeff_subspaceCharacterSum_of_mem _ _
      ((mem_perpendicular_matrixRowSpan_iff_mulVec_eq_zero H γ).2 hzero)
  · rw [if_neg hzero]
    exact vectorFourierCoeff_subspaceCharacterSum_of_not_mem _ _
      ((mem_perpendicular_matrixRowSpan_iff_mulVec_eq_zero H γ).not.mpr hzero)

/-- O'Donnell, Proposition 6.31: the row-span density is `k`-wise independent
exactly when every nonempty sum of at most `k` columns is nonzero. -/
theorem matrixRowSpanDensity_isKWiseIndependent_iff
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (k : ℕ) :
    IsLowDegreeFourierRegular 0 k
        (binaryFunctionOnSignCube (matrixRowSpanDensity H)) ↔
      HasNonzeroColumnSumsUpTo H k := by
  rw [isLowDegreeFourierRegular_binaryFunctionOnSignCube_iff]
  constructor
  · intro hregular S hS hcard hsum
    let γ : 𝔽₂^[n] := f₂CubeOfFinset S
    have hsupport : f₂Support γ = S :=
      (f₂CubeEquivFinset n).right_inv S
    have hγ : γ ≠ 0 :=
      (f₂Support_nonempty_iff γ).1 (hsupport.symm ▸ hS)
    have hcoeff := hregular γ hγ (by simpa [hsupport] using hcard)
    have hmul : H *ᵥ γ = 0 := by
      simpa [γ, matrixColumnSum] using hsum
    rw [vectorFourierCoeff_matrixRowSpanDensity, if_pos hmul] at hcoeff
    norm_num at hcoeff
  · intro hcolumns γ hγ hcard
    have hsum :=
      hcolumns (f₂Support γ) ((f₂Support_nonempty_iff γ).2 hγ) hcard
    have hmul : H *ᵥ γ ≠ 0 := by
      simpa using hsum
    rw [vectorFourierCoeff_matrixRowSpanDensity, if_neg hmul]
    simp

/-! ## Lemma 6.34 -/

/-- The density of `yᵀH` when `y` has density `φ`. -/
noncomputable def matrixPushforwardDensity
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (φ : ProbabilityDensity m) :
    ProbabilityDensity n :=
  φ.pushforward fun y ↦ y ᵥ* H

/-- Fourier coefficients of the pushed density are the source coefficients at `Hγ`. -/
theorem vectorFourierCoeff_matrixPushforwardDensity
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (φ : ProbabilityDensity m)
    (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (matrixPushforwardDensity H φ) γ =
      vectorFourierCoeff φ (H *ᵥ γ) := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  change
    (matrixPushforwardDensity H φ).expectation
        (fun z ↦ vectorWalshCharacter γ z) =
      φ.expectation (fun y ↦ vectorWalshCharacter (H *ᵥ γ) y)
  rw [matrixPushforwardDensity, ProbabilityDensity.pushforward_expectation]
  apply congrArg φ.expectation
  funext y
  exact vectorWalshCharacter_vecMul H γ y

/-- O'Donnell, Lemma 6.34: pushing an `ε`-biased density through `y ↦ yᵀH`
is `(ε,k)`-wise independent when all nonempty sums of at most `k` columns
are nonzero. -/
theorem matrixPushforwardDensity_isApproximatelyKWiseIndependent
    (H : Matrix (Fin m) (Fin n) 𝔽₂) (φ : ProbabilityDensity m)
    (ε : ℝ) (k : ℕ) (hcolumns : HasNonzeroColumnSumsUpTo H k)
    (hbiased : φ.IsBiased ε) :
    IsLowDegreeFourierRegular ε k
      (binaryFunctionOnSignCube (matrixPushforwardDensity H φ)) := by
  rw [isLowDegreeFourierRegular_binaryFunctionOnSignCube_iff]
  intro γ hγ hcard
  rw [vectorFourierCoeff_matrixPushforwardDensity]
  apply hbiased
  have hsum :=
    hcolumns (f₂Support γ) ((f₂Support_nonempty_iff γ).2 hγ) hcard
  simpa using hsum

end FABL
