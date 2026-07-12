/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.SubspacesAndDecisionTrees.VectorFourier

/-!
# Subspaces and affine subspaces

Book items: Proposition 3.11, Proposition 3.12, Exercise 3.11.

Perpendicular subspaces and Fourier expansions of subspace indicators.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Perpendicular subspaces -/

/-- The standard dot product as a bilinear form on `𝔽₂ⁿ`. -/
def f₂DotProductBilin (n : ℕ) : LinearMap.BilinForm 𝔽₂ 𝔽₂^[n] :=
  (dotProductEquiv 𝔽₂ (Fin n)).toLinearMap

@[simp] theorem f₂DotProductBilin_apply (x y : 𝔽₂^[n]) :
    f₂DotProductBilin n x y = f₂DotProduct x y := rfl

/-- The standard binary dot product is symmetric. -/
theorem f₂DotProductBilin_isSymm : (f₂DotProductBilin n).IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  exact dotProduct_comm x y

/-- The standard binary dot product is reflexive in Mathlib's orthogonality sense. -/
theorem f₂DotProductBilin_isRefl : (f₂DotProductBilin n).IsRefl :=
  f₂DotProductBilin_isSymm.isRefl

/-- The standard binary dot product is nondegenerate. -/
theorem f₂DotProductBilin_nondegenerate : (f₂DotProductBilin n).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply (dotProductEquiv 𝔽₂ (Fin n)).injective
  apply LinearMap.ext
  intro y
  change f₂DotProduct x y = f₂DotProduct 0 y
  have hxy : f₂DotProduct x y = 0 := by
    simpa using hx y
  rw [hxy, f₂DotProduct, zero_dotProduct]

/-- The perpendicular subspace `Aᵖ` with respect to the standard binary dot product. -/
def perpendicularSubspace (A : Submodule 𝔽₂ 𝔽₂^[n]) : Submodule 𝔽₂ 𝔽₂^[n] :=
  (f₂DotProductBilin n).orthogonal A

/-- Membership in `Aᵖ` is the book's pointwise dot-product condition. -/
theorem mem_perpendicularSubspace_iff (A : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n]) :
    γ ∈ perpendicularSubspace A ↔ ∀ x ∈ A, f₂DotProduct γ x = 0 := by
  rw [perpendicularSubspace, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have hxy : f₂DotProduct x γ = 0 := by
      simpa [LinearMap.BilinForm.IsOrtho] using h x hx
    simpa [f₂DotProduct, dotProduct_comm] using hxy
  · intro h x hx
    change f₂DotProduct x γ = 0
    simpa [f₂DotProduct, dotProduct_comm] using h x hx

/-- The codimension of a binary subspace, defined as the dimension of its perpendicular. -/
noncomputable def f₂Codimension (A : Submodule 𝔽₂ 𝔽₂^[n]) : ℕ :=
  Module.finrank 𝔽₂ (perpendicularSubspace A)

/-- Mathlib's nondegenerate-form dimension theorem gives the dimension of `Aᵖ`. -/
theorem finrank_perpendicularSubspace (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    Module.finrank 𝔽₂ (perpendicularSubspace A) =
      n - Module.finrank 𝔽₂ A := by
  rw [perpendicularSubspace,
    LinearMap.BilinForm.finrank_orthogonal f₂DotProductBilin_nondegenerate]
  simp

/-- Taking the perpendicular twice recovers the original binary subspace. -/
theorem perpendicularSubspace_perpendicularSubspace
    (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    perpendicularSubspace (perpendicularSubspace A) = A := by
  exact LinearMap.BilinForm.orthogonal_orthogonal
    f₂DotProductBilin_nondegenerate f₂DotProductBilin_isRefl A

/-- A binary subspace has cardinality `2` raised to its dimension. -/
theorem card_submodule_eq_two_pow_finrank (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    Nat.card A = 2 ^ Module.finrank 𝔽₂ A := by
  simpa using (Module.natCard_eq_pow_finrank (K := 𝔽₂) (V := A))

/-- The perpendicular of a codimension-`k` binary subspace has `2ᵏ` elements. -/
theorem card_perpendicularSubspace (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    Nat.card (perpendicularSubspace A) = 2 ^ f₂Codimension A := by
  simpa [f₂Codimension] using card_submodule_eq_two_pow_finrank (perpendicularSubspace A)

/-! ## Fourier expansion of subspace indicators -/

/-- Evaluation at `x` restricts vector-indexed Walsh characters to an additive character on a
binary subspace. -/
noncomputable def subspaceEvaluationCharacter (H : Submodule 𝔽₂ 𝔽₂^[n])
    (x : 𝔽₂^[n]) : AddChar H ℝ where
  toFun γ := vectorWalshCharacter γ.1 x
  map_zero_eq_one' := by simp
  map_add_eq_mul' β γ := by
    have h := congrArg (fun ψ : AddChar 𝔽₂^[n] ℝ ↦ ψ x)
      (vectorWalshCharacter_mul β.1 γ.1)
    simpa using h.symm

/-- The restricted evaluation character is trivial exactly on the perpendicular subspace. -/
theorem subspaceEvaluationCharacter_eq_zero_iff
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (x : 𝔽₂^[n]) :
    subspaceEvaluationCharacter H x = 0 ↔ x ∈ perpendicularSubspace H := by
  constructor
  · intro h
    rw [mem_perpendicularSubspace_iff]
    intro γ hγ
    have heval := DFunLike.congr_fun h ⟨γ, hγ⟩
    have hsign : binarySign (f₂DotProduct γ x) = 1 := by
      simpa [subspaceEvaluationCharacter, vectorWalshCharacter_apply] using heval
    have hdot : f₂DotProduct γ x = 0 := (binarySign_eq_one_iff _).1 hsign
    simpa [f₂DotProduct, dotProduct_comm] using hdot
  · intro hx
    ext γ
    have hdot := (mem_perpendicularSubspace_iff H x).1 hx γ.1 γ.2
    have hdot' : f₂DotProduct γ.1 x = 0 := by
      simpa [f₂DotProduct, dotProduct_comm] using hdot
    simp [subspaceEvaluationCharacter, vectorWalshCharacter_apply, hdot']

/-- The sum of all vector-indexed characters whose indices lie in `H`. -/
noncomputable def subspaceCharacterSum (H : Submodule 𝔽₂ 𝔽₂^[n])
    (x : 𝔽₂^[n]) : ℝ := by
  letI := Fintype.ofFinite H
  exact ∑ γ : H, subspaceEvaluationCharacter H x γ

/-- Character orthogonality on a subspace at a point in its perpendicular, delegated to
Mathlib's additive-character sum. -/
theorem subspaceCharacterSum_eq_card_of_mem (H : Submodule 𝔽₂ 𝔽₂^[n])
    (x : 𝔽₂^[n]) (hx : x ∈ perpendicularSubspace H) :
    subspaceCharacterSum H x = (Nat.card H : ℝ) := by
  classical
  letI := Fintype.ofFinite H
  simp only [subspaceCharacterSum]
  rw [AddChar.sum_eq_ite]
  simp [subspaceEvaluationCharacter_eq_zero_iff, hx, Nat.card_eq_fintype_card]

/-- Character orthogonality on a subspace at a point outside its perpendicular. -/
theorem subspaceCharacterSum_eq_zero_of_not_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (x : 𝔽₂^[n])
    (hx : x ∉ perpendicularSubspace H) :
    subspaceCharacterSum H x = 0 := by
  classical
  letI := Fintype.ofFinite H
  simp only [subspaceCharacterSum]
  rw [AddChar.sum_eq_ite]
  simp [subspaceEvaluationCharacter_eq_zero_iff, hx]

/-- The uniform expectation of a subspace character sum is one. -/
theorem expect_subspaceCharacterSum (H : Submodule 𝔽₂ 𝔽₂^[n]) :
    (𝔼 x, subspaceCharacterSum H x) = 1 := by
  classical
  letI := Fintype.ofFinite H
  simp only [subspaceCharacterSum]
  rw [Finset.expect_sum_comm]
  simp [subspaceEvaluationCharacter, expect_vectorWalshCharacter]

/-- The coefficient `2⁻ᵏ` attached to a subspace of codimension `k`. -/
noncomputable def inversePerpendicularCard (A : Submodule 𝔽₂ 𝔽₂^[n]) : ℝ :=
  ((2 : ℝ) ^ f₂Codimension A)⁻¹

theorem inversePerpendicularCard_pos (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    0 < inversePerpendicularCard A := by
  unfold inversePerpendicularCard
  positivity

theorem inversePerpendicularCard_ne_zero (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    inversePerpendicularCard A ≠ 0 :=
  (inversePerpendicularCard_pos A).ne'

/-- O'Donnell, Proposition 3.11: the pointwise Fourier expansion of a binary subspace
indicator. -/
theorem setIndicator_submodule_apply (A : Submodule 𝔽₂ 𝔽₂^[n]) (x : 𝔽₂^[n]) :
    setIndicator (A : Set 𝔽₂^[n]) x =
      inversePerpendicularCard A * subspaceCharacterSum (perpendicularSubspace A) x := by
  classical
  by_cases hx : x ∈ A
  · have hxperp : x ∈ perpendicularSubspace (perpendicularSubspace A) := by
      simpa [perpendicularSubspace_perpendicularSubspace] using hx
    rw [subspaceCharacterSum_eq_card_of_mem _ _ hxperp]
    have hcard : (Nat.card (perpendicularSubspace A) : ℝ) =
        (2 : ℝ) ^ f₂Codimension A := by
      exact_mod_cast card_perpendicularSubspace A
    rw [hcard]
    simp [setIndicator, hx, inversePerpendicularCard]
  · have hxperp : x ∉ perpendicularSubspace (perpendicularSubspace A) := by
      simpa [perpendicularSubspace_perpendicularSubspace] using hx
    rw [subspaceCharacterSum_eq_zero_of_not_mem _ _ hxperp]
    simp [setIndicator, hx]

/-- O'Donnell, Proposition 3.11: the subspace indicator as a sum of the characters indexed by
the perpendicular subspace. -/
theorem setIndicator_submodule_fourier_expansion
    (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    setIndicator (A : Set 𝔽₂^[n]) =
      fun x ↦ inversePerpendicularCard A *
        subspaceCharacterSum (perpendicularSubspace A) x := by
  funext x
  exact setIndicator_submodule_apply A x

/-- A subspace character sum has coefficient one on its indexing subspace. -/
theorem vectorFourierCoeff_subspaceCharacterSum_of_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n]) (hγ : γ ∈ H) :
    vectorFourierCoeff (subspaceCharacterSum H) γ = 1 := by
  classical
  letI := Fintype.ofFinite H
  rw [vectorFourierCoeff_eq_expect]
  simp only [subspaceCharacterSum]
  calc
    (𝔼 x, (∑ β : H, subspaceEvaluationCharacter H x β) *
        vectorWalshCharacter γ x) =
        𝔼 x, ∑ β : H, vectorWalshCharacter β.1 x *
          vectorWalshCharacter γ x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
      rfl
    _ = ∑ β : H, 𝔼 x, vectorWalshCharacter β.1 x *
          vectorWalshCharacter γ x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ β : H, if β.1 = γ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro β _
      rw [expect_vectorWalshCharacter_mul]
    _ = 1 := by
      have heq (β : H) : β.1 = γ ↔ β = ⟨γ, hγ⟩ := by
        constructor
        · exact fun h ↦ Subtype.ext h
        · exact fun h ↦ congrArg Subtype.val h
      simp_rw [heq]
      simp

/-- A subspace character sum has coefficient zero outside its indexing subspace. -/
theorem vectorFourierCoeff_subspaceCharacterSum_of_not_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n]) (hγ : γ ∉ H) :
    vectorFourierCoeff (subspaceCharacterSum H) γ = 0 := by
  classical
  letI := Fintype.ofFinite H
  rw [vectorFourierCoeff_eq_expect]
  simp only [subspaceCharacterSum]
  calc
    (𝔼 x, (∑ β : H, subspaceEvaluationCharacter H x β) *
        vectorWalshCharacter γ x) =
        𝔼 x, ∑ β : H, vectorWalshCharacter β.1 x *
          vectorWalshCharacter γ x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
      rfl
    _ = ∑ β : H, 𝔼 x, vectorWalshCharacter β.1 x *
          vectorWalshCharacter γ x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ β : H, if β.1 = γ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro β _
      rw [expect_vectorWalshCharacter_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro β _
      have hne : β.1 ≠ γ := by
        intro h
        apply hγ
        rw [← h]
        exact β.2
      simp [hne]

/-- Proposition 3.11 in coefficient form, on the perpendicular subspace. -/
theorem vectorFourierCoeff_setIndicator_submodule_of_mem
    (A : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n])
    (hγ : γ ∈ perpendicularSubspace A) :
    vectorFourierCoeff (setIndicator (A : Set 𝔽₂^[n])) γ = inversePerpendicularCard A := by
  rw [vectorFourierCoeff_eq_expect]
  simp_rw [setIndicator_submodule_apply]
  calc
    (𝔼 x, inversePerpendicularCard A *
        subspaceCharacterSum (perpendicularSubspace A) x * vectorWalshCharacter γ x) =
        𝔼 x, inversePerpendicularCard A *
          (subspaceCharacterSum (perpendicularSubspace A) x * vectorWalshCharacter γ x) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = inversePerpendicularCard A *
        (𝔼 x, subspaceCharacterSum (perpendicularSubspace A) x *
          vectorWalshCharacter γ x) := by
      rw [Finset.mul_expect]
    _ = inversePerpendicularCard A *
        vectorFourierCoeff (subspaceCharacterSum (perpendicularSubspace A)) γ := by
      rw [vectorFourierCoeff_eq_expect]
    _ = inversePerpendicularCard A := by
      rw [vectorFourierCoeff_subspaceCharacterSum_of_mem _ _ hγ, mul_one]

/-- Proposition 3.11 in coefficient form, off the perpendicular subspace. -/
theorem vectorFourierCoeff_setIndicator_submodule_of_not_mem
    (A : Submodule 𝔽₂ 𝔽₂^[n]) (γ : 𝔽₂^[n])
    (hγ : γ ∉ perpendicularSubspace A) :
    vectorFourierCoeff (setIndicator (A : Set 𝔽₂^[n])) γ = 0 := by
  rw [vectorFourierCoeff_eq_expect]
  simp_rw [setIndicator_submodule_apply]
  calc
    (𝔼 x, inversePerpendicularCard A *
        subspaceCharacterSum (perpendicularSubspace A) x * vectorWalshCharacter γ x) =
        𝔼 x, inversePerpendicularCard A *
          (subspaceCharacterSum (perpendicularSubspace A) x * vectorWalshCharacter γ x) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = inversePerpendicularCard A *
        (𝔼 x, subspaceCharacterSum (perpendicularSubspace A) x *
          vectorWalshCharacter γ x) := by
      rw [Finset.mul_expect]
    _ = inversePerpendicularCard A *
        vectorFourierCoeff (subspaceCharacterSum (perpendicularSubspace A)) γ := by
      rw [vectorFourierCoeff_eq_expect]
    _ = 0 := by
      rw [vectorFourierCoeff_subspaceCharacterSum_of_not_mem _ _ hγ, mul_zero]

/-- The uniform probability of membership in a binary subspace. -/
noncomputable def subspaceUniformProbability (A : Submodule 𝔽₂ 𝔽₂^[n]) : ℝ := by
  classical
  exact uniformProbability fun x : 𝔽₂^[n] ↦ x ∈ A

/-- The uniform probability of a binary subspace is the reciprocal of the size of its
perpendicular. -/
theorem subspaceUniformProbability_eq_inversePerpendicularCard
    (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    subspaceUniformProbability A = inversePerpendicularCard A := by
  classical
  calc
    subspaceUniformProbability A =
        𝔼 x, setIndicator (A : Set 𝔽₂^[n]) x := by
      unfold subspaceUniformProbability uniformProbability
      apply Finset.expect_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [setIndicator, hx]
    _ = 𝔼 x, inversePerpendicularCard A *
          subspaceCharacterSum (perpendicularSubspace A) x := by
      apply Finset.expect_congr rfl
      intro x _
      exact setIndicator_submodule_apply A x
    _ = inversePerpendicularCard A *
        (𝔼 x, subspaceCharacterSum (perpendicularSubspace A) x) := by
      rw [Finset.mul_expect]
    _ = inversePerpendicularCard A := by
      rw [expect_subspaceCharacterSum, mul_one]

/-- O'Donnell, Proposition 3.11: the normalized uniform density of a subspace is the unscaled
sum of the characters in its perpendicular. -/
theorem subsetDensity_submodule_apply (A : Submodule 𝔽₂ 𝔽₂^[n]) (x : 𝔽₂^[n]) :
    subsetDensity (A : Set 𝔽₂^[n]) ⟨0, A.zero_mem⟩ x =
      subspaceCharacterSum (perpendicularSubspace A) x := by
  rw [subsetDensity_apply]
  unfold subsetDensityValue
  change (subspaceUniformProbability A)⁻¹ * setIndicator (A : Set 𝔽₂^[n]) x = _
  rw [subspaceUniformProbability_eq_inversePerpendicularCard,
    setIndicator_submodule_apply]
  simp [inversePerpendicularCard]

/-- O'Donnell, Proposition 3.11: functional form of the subspace-density Fourier expansion. -/
theorem subsetDensity_submodule_fourier_expansion
    (A : Submodule 𝔽₂ 𝔽₂^[n]) :
    (subsetDensity (A : Set 𝔽₂^[n]) ⟨0, A.zero_mem⟩ : 𝔽₂^[n] → ℝ) =
      subspaceCharacterSum (perpendicularSubspace A) := by
  funext x
  exact subsetDensity_submodule_apply A x

/-! ## Affine subspaces -/

/-- The affine translate `H + a`, represented by Mathlib's `AffineSubspace.mk'`. -/
def binaryAffineSubspace (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    AffineSubspace 𝔽₂ 𝔽₂^[n] :=
  AffineSubspace.mk' a H

@[simp] theorem binaryAffineSubspace_direction
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    (binaryAffineSubspace H a).direction = H := by
  exact AffineSubspace.direction_mk' a H

/-- In characteristic two, membership in `H + a` is equivalent to `x + a ∈ H`. -/
theorem mem_binaryAffineSubspace_iff_add_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a x : 𝔽₂^[n]) :
    x ∈ binaryAffineSubspace H a ↔ x + a ∈ H := by
  rw [binaryAffineSubspace, AffineSubspace.mem_mk']
  change x - a ∈ H ↔ x + a ∈ H
  have hneg : -a = a := by
    funext i
    exact ZMod.neg_eq_self_mod_two (a i)
  rw [sub_eq_add_neg, hneg]

/-- Membership in an affine binary subspace is equivalently the system of all perpendicular
parity equations. -/
theorem mem_binaryAffineSubspace_iff_forall_perpendicular_parity
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a x : 𝔽₂^[n]) :
    x ∈ binaryAffineSubspace H a ↔
      ∀ γ ∈ perpendicularSubspace H,
        f₂DotProduct γ x = f₂DotProduct γ a := by
  constructor
  · intro hx γ hγ
    have hxa : x + a ∈ H := (mem_binaryAffineSubspace_iff_add_mem H a x).1 hx
    have hzero := (mem_perpendicularSubspace_iff H γ).1 hγ (x + a) hxa
    rw [f₂DotProduct, dotProduct_add] at hzero
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans
      (ZMod.neg_eq_self_mod_two (f₂DotProduct γ a))
  · intro h
    rw [mem_binaryAffineSubspace_iff_add_mem]
    have hperp : x + a ∈ perpendicularSubspace (perpendicularSubspace H) := by
      rw [mem_perpendicularSubspace_iff]
      intro γ hγ
      rw [show f₂DotProduct (x + a) γ = f₂DotProduct γ (x + a) by
          exact dotProduct_comm _ _, f₂DotProduct, dotProduct_add]
      have heq := h γ hγ
      change γ ⬝ᵥ x = γ ⬝ᵥ a at heq
      rw [heq]
      exact ZModModule.add_self _
    simpa [perpendicularSubspace_perpendicularSubspace] using hperp

/-- Translating the input multiplies each vector-indexed Fourier coefficient by the
corresponding character value. -/
theorem vectorFourierCoeff_translate_add (f : 𝔽₂^[n] → ℝ) (a γ : 𝔽₂^[n]) :
    vectorFourierCoeff (fun x ↦ f (x + a)) γ =
      vectorWalshCharacter γ a * vectorFourierCoeff f γ := by
  rw [vectorFourierCoeff_eq_expect]
  calc
    (𝔼 x, f (x + a) * vectorWalshCharacter γ x) =
        𝔼 y, f y * vectorWalshCharacter γ (y + a) := by
      apply Fintype.expect_equiv (Equiv.addRight a)
      intro x
      change f (x + a) * vectorWalshCharacter γ x =
        f (x + a) * vectorWalshCharacter γ ((x + a) + a)
      rw [add_assoc, ZModModule.add_self a, add_zero]
    _ = 𝔼 y, vectorWalshCharacter γ a *
          (f y * vectorWalshCharacter γ y) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [AddChar.map_add_eq_mul]
      ring
    _ = vectorWalshCharacter γ a *
        (𝔼 y, f y * vectorWalshCharacter γ y) := by
      rw [Finset.mul_expect]
    _ = vectorWalshCharacter γ a * vectorFourierCoeff f γ := by
      rw [vectorFourierCoeff_eq_expect]

/-- The affine-subspace indicator is the translate of the direction-subspace indicator. -/
theorem setIndicator_binaryAffineSubspace_eq_translate
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]) =
      fun x ↦ setIndicator (H : Set 𝔽₂^[n]) (x + a) := by
  funext x
  by_cases hx : x ∈ binaryAffineSubspace H a
  · have hxa := (mem_binaryAffineSubspace_iff_add_mem H a x).1 hx
    simp [setIndicator, hx, hxa]
  · have hxa : x + a ∉ H := fun h ↦ hx ((mem_binaryAffineSubspace_iff_add_mem H a x).2 h)
    simp [setIndicator, hx, hxa]

/-- O'Donnell, Proposition 3.12: pointwise Fourier expansion of an affine-subspace indicator. -/
theorem setIndicator_binaryAffineSubspace_apply
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a x : 𝔽₂^[n]) :
    setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]) x =
      inversePerpendicularCard H *
        subspaceCharacterSum (perpendicularSubspace H) (x + a) := by
  rw [setIndicator_binaryAffineSubspace_eq_translate]
  exact setIndicator_submodule_apply H (x + a)

/-- O'Donnell, Proposition 3.12: functional form of the affine indicator expansion. -/
theorem setIndicator_binaryAffineSubspace_fourier_expansion
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]) =
      fun x ↦ inversePerpendicularCard H *
        subspaceCharacterSum (perpendicularSubspace H) (x + a) := by
  funext x
  exact setIndicator_binaryAffineSubspace_apply H a x

/-- Proposition 3.12 in coefficient form, on the perpendicular direction. -/
theorem vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n])
    (hγ : γ ∈ perpendicularSubspace H) :
    vectorFourierCoeff (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ =
      vectorWalshCharacter γ a * inversePerpendicularCard H := by
  rw [setIndicator_binaryAffineSubspace_eq_translate, vectorFourierCoeff_translate_add,
    vectorFourierCoeff_setIndicator_submodule_of_mem _ _ hγ]

/-- Proposition 3.12 in coefficient form, off the perpendicular direction. -/
theorem vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n])
    (hγ : γ ∉ perpendicularSubspace H) :
    vectorFourierCoeff (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ = 0 := by
  rw [setIndicator_binaryAffineSubspace_eq_translate, vectorFourierCoeff_translate_add,
    vectorFourierCoeff_setIndicator_submodule_of_not_mem _ _ hγ, mul_zero]

/-- Every affine translate of a subspace is nonempty. -/
theorem binaryAffineSubspace_nonempty
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    (binaryAffineSubspace H a : Set 𝔽₂^[n]).Nonempty := by
  refine ⟨a, ?_⟩
  simp [binaryAffineSubspace]

/-- Uniform probability of membership in an affine binary subspace. -/
noncomputable def affineSubspaceUniformProbability
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) : ℝ := by
  classical
  exact uniformProbability fun x : 𝔽₂^[n] ↦ x ∈ binaryAffineSubspace H a

/-- Translation preserves the uniform probability of a binary subspace. -/
theorem affineSubspaceUniformProbability_eq_subspaceUniformProbability
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    affineSubspaceUniformProbability H a = subspaceUniformProbability H := by
  classical
  calc
    affineSubspaceUniformProbability H a =
        𝔼 x, setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]) x := by
      unfold affineSubspaceUniformProbability uniformProbability
      apply Finset.expect_congr rfl
      intro x _
      by_cases hx : x ∈ binaryAffineSubspace H a <;> simp [setIndicator, hx]
    _ = 𝔼 x, setIndicator (H : Set 𝔽₂^[n]) (x + a) := by
      apply Finset.expect_congr rfl
      intro x _
      exact congrFun (setIndicator_binaryAffineSubspace_eq_translate H a) x
    _ = 𝔼 x, setIndicator (H : Set 𝔽₂^[n]) x := by
      apply Fintype.expect_equiv (Equiv.addRight a)
      intro x
      rfl
    _ = subspaceUniformProbability H := by
      symm
      unfold subspaceUniformProbability uniformProbability
      apply Finset.expect_congr rfl
      intro x _
      by_cases hx : x ∈ H <;> simp [setIndicator, hx]

/-- The uniform probability of an affine subspace is `2⁻ᵏ`, where `k` is its
codimension. -/
theorem affineSubspaceUniformProbability_eq_inversePerpendicularCard
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    affineSubspaceUniformProbability H a = inversePerpendicularCard H := by
  rw [affineSubspaceUniformProbability_eq_subspaceUniformProbability,
    subspaceUniformProbability_eq_inversePerpendicularCard]

/-- O'Donnell, Proposition 3.12: the density of an affine subspace is its translated
perpendicular character sum. -/
theorem subsetDensity_binaryAffineSubspace_apply
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a x : 𝔽₂^[n]) :
    subsetDensity (binaryAffineSubspace H a : Set 𝔽₂^[n])
        (binaryAffineSubspace_nonempty H a) x =
      subspaceCharacterSum (perpendicularSubspace H) (x + a) := by
  rw [subsetDensity_apply]
  unfold subsetDensityValue
  change (affineSubspaceUniformProbability H a)⁻¹ *
      setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]) x = _
  rw [affineSubspaceUniformProbability_eq_inversePerpendicularCard,
    setIndicator_binaryAffineSubspace_apply]
  simp [inversePerpendicularCard]

/-- O'Donnell, Proposition 3.12: functional form of the affine-density Fourier expansion. -/
theorem subsetDensity_binaryAffineSubspace_fourier_expansion
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    (subsetDensity (binaryAffineSubspace H a : Set 𝔽₂^[n])
        (binaryAffineSubspace_nonempty H a) : 𝔽₂^[n] → ℝ) =
      fun x ↦ subspaceCharacterSum (perpendicularSubspace H) (x + a) := by
  funext x
  exact subsetDensity_binaryAffineSubspace_apply H a x

/-- The Fourier support of an affine-subspace indicator is exactly the perpendicular direction. -/
theorem vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n]) :
    vectorFourierCoeff (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ ≠ 0 ↔
      γ ∈ perpendicularSubspace H := by
  classical
  by_cases hγ : γ ∈ perpendicularSubspace H
  · constructor
    · exact fun _ ↦ hγ
    · intro _
      rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _ hγ]
      apply mul_ne_zero
      · rcases vectorWalshCharacter_eq_neg_one_or_one γ a with h | h <;> simp [h]
      · exact inversePerpendicularCard_ne_zero H
  · constructor
    · intro hcoeff
      rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _ hγ] at hcoeff
      exact (hcoeff rfl).elim
    · intro hmem
      exact (hγ hmem).elim

/-- O'Donnell, Proposition 3.12: the affine indicator spectrum is `2⁻ᵏ`-granular. -/
theorem isVectorFourierGranular_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    IsVectorFourierGranular
      (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n]))
      (inversePerpendicularCard H) := by
  rw [isVectorFourierGranular_iff]
  intro γ
  by_cases hγ : γ ∈ perpendicularSubspace H
  · rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _ hγ]
    rcases vectorWalshCharacter_eq_neg_one_or_one γ a with h | h
    · exact ⟨-1, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _ hγ]
    exact ⟨0, by simp⟩

/-- O'Donnell, Proposition 3.12: an affine subspace of codimension `k` has Fourier sparsity
`2ᵏ`. -/
theorem spectralSparsity_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    spectralSparsity (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) =
      2 ^ f₂Codimension H := by
  classical
  unfold spectralSparsity
  have hfilter :
      (Finset.univ.filter fun γ : 𝔽₂^[n] ↦
        vectorFourierCoeff
          (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ ≠ 0) =
      Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H := by
    ext γ
    simp [vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff]
  rw [hfilter]
  letI := Fintype.ofFinite (perpendicularSubspace H)
  calc
    (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H).card =
        Fintype.card (perpendicularSubspace H) := by
      symm
      exact Fintype.card_subtype fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H
    _ = Nat.card (perpendicularSubspace H) := by
      rw [Nat.card_eq_fintype_card]
    _ = 2 ^ f₂Codimension H := card_perpendicularSubspace H

/-- Every Fourier coefficient on the perpendicular direction has absolute value `2⁻ᵏ`. -/
theorem abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n])
    (hγ : γ ∈ perpendicularSubspace H) :
    |vectorFourierCoeff (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ| =
      inversePerpendicularCard H := by
  rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _ hγ, abs_mul,
    abs_vectorWalshCharacter, one_mul, abs_of_pos (inversePerpendicularCard_pos H)]

/-- Every Fourier coefficient off the perpendicular direction has absolute value zero. -/
theorem abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n])
    (hγ : γ ∉ perpendicularSubspace H) :
    |vectorFourierCoeff (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ| = 0 := by
  rw [vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _ hγ, abs_zero]

/-- O'Donnell, Proposition 3.12: the Fourier infinity norm of an affine-subspace indicator is
`2⁻ᵏ`. -/
theorem spectralInfinityNorm_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    spectralInfinityNorm (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) =
      inversePerpendicularCard H := by
  classical
  unfold spectralInfinityNorm
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro γ _
    by_cases hγ : γ ∈ perpendicularSubspace H
    · rw [abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _ hγ]
    · rw [abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _ hγ]
      exact (inversePerpendicularCard_pos H).le
  · have hle := Finset.le_sup'
        (fun γ : 𝔽₂^[n] ↦
          |vectorFourierCoeff
            (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ|)
        (Finset.mem_univ (0 : 𝔽₂^[n]))
    rw [abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem H a 0
      (perpendicularSubspace H).zero_mem] at hle
    exact hle

/-- The absolute Fourier coefficients of an affine-subspace indicator sum to one. -/
theorem sum_abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    (∑ γ, |vectorFourierCoeff
      (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ|) = 1 := by
  classical
  have hcard :
      (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H).card =
        2 ^ f₂Codimension H := by
    letI := Fintype.ofFinite (perpendicularSubspace H)
    calc
      (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H).card =
          Fintype.card (perpendicularSubspace H) := by
        symm
        exact Fintype.card_subtype fun γ : 𝔽₂^[n] ↦ γ ∈ perpendicularSubspace H
      _ = Nat.card (perpendicularSubspace H) := by
        rw [Nat.card_eq_fintype_card]
      _ = 2 ^ f₂Codimension H := card_perpendicularSubspace H
  calc
    (∑ γ, |vectorFourierCoeff
        (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) γ|) =
        ∑ γ, if γ ∈ perpendicularSubspace H then inversePerpendicularCard H else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      by_cases hγ : γ ∈ perpendicularSubspace H
      · rw [if_pos hγ,
          abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem _ _ _ hγ]
      · rw [if_neg hγ,
          abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem _ _ _ hγ]
    _ = ∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦
        γ ∈ perpendicularSubspace H), inversePerpendicularCard H := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter fun γ : 𝔽₂^[n] ↦
        γ ∈ perpendicularSubspace H).card : ℝ) * inversePerpendicularCard H := by
      simp
    _ = ((2 : ℝ) ^ f₂Codimension H) * inversePerpendicularCard H := by
      rw [hcard, Nat.cast_pow]
      norm_num
    _ = 1 := by
      simp [inversePerpendicularCard]

/-- O'Donnell, Proposition 3.12: the Fourier one-norm of an affine-subspace indicator is one. -/
theorem spectralPNorm_one_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) :
    spectralPNorm 1 (setIndicator (binaryAffineSubspace H a : Set 𝔽₂^[n])) = 1 := by
  unfold spectralPNorm
  simp [sum_abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace]

end FABL
