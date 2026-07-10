/-
Copyright (c) 2026 FABL contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FABL contributors
-/
module

public import FABL.Chapter01.FunctionsAsMultilinearPolynomials

/-!
# The orthonormal basis of parity functions

Formalization of Section 1.3 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The normalized inner product `⟨f,g⟩ = 𝔼[f g]` from O'Donnell, Definition 1.3. -/
noncomputable def uniformInner {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) : ℝ :=
  RCLike.wInner RCLike.cWeight f g

scoped[BooleanCube] notation "⟪" f ", " g "⟫ᵤ" => FABL.uniformInner f g

/-- The normalized `Lᵖ` quantity `(𝔼[|f|ᵖ])¹ᐟᵖ` from O'Donnell, Definition 1.3. -/
noncomputable def uniformLpNorm {Ω : Type*} [Fintype Ω] (p : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.rpow (𝔼 x, Real.rpow |f x| p) p⁻¹

/-- The uniform distribution denoted by `x ∼ Ω`; see O'Donnell, Notation 1.4. -/
noncomputable def uniformPMF (Ω : Type*) [Fintype Ω] [Nonempty Ω] : PMF Ω :=
  PMF.uniformOfFintype Ω

/-- Integration against the uniform PMF is Mathlib's normalized finite expectation. -/
theorem integral_uniformPMF_eq_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (f : Ω → ℝ) :
    ∫ x, f x ∂(uniformPMF Ω).toMeasure = 𝔼 x, f x := by
  rw [PMF.integral_eq_sum, uniformPMF]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, smul_eq_mul]
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- The subset parameterization of real parity characters on `𝔽₂ⁿ` is injective. -/
theorem binaryWalshCharacter_injective :
    Function.Injective (χ : Finset (Fin n) → AddChar 𝔽₂^[n] ℝ) := by
  classical
  intro S T h
  ext i
  have hi := congrArg
    (fun ψ : AddChar 𝔽₂^[n] ℝ ↦ ψ (fun j ↦ if j = i then 1 else 0)) h
  simp [χ, coordinateSum, binarySign, AddChar.zmodChar_apply] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT] at hi ⊢ <;> norm_num [ZMod.val_one] at hi

/-- The subset-indexed real Walsh basis on `𝔽₂ⁿ`. Its construction delegates linear independence
to Mathlib's finite-character orthogonality infrastructure. -/
noncomputable def binaryWalshBasis (n : ℕ) :
    Module.Basis (Finset (Fin n)) ℝ (𝔽₂^[n] → ℝ) := by
  classical
  exact basisOfLinearIndependentOfCardEqFinrank (b := fun S ↦ χ S)
    ((AddChar.linearIndependent 𝔽₂^[n] ℝ).comp χ binaryWalshCharacter_injective)
    (by
      have hz : Fintype.card 𝔽₂ = 2 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_zmod]
      simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, hz])

/-- The subset-indexed real Walsh basis on the sign cube. Its construction regards the
multiplicative sign cube as an additive group and reuses Mathlib's `AddChar` linear independence. -/
noncomputable def walshBasis (n : ℕ) :
    Module.Basis (Finset (Fin n)) ℝ ({−1,1}^[n] → ℝ) := by
  classical
  exact basisOfLinearIndependentOfCardEqFinrank (b := fun S ↦ monomial S)
    (by
      simpa [Function.comp_def, signMonomialChar] using
        ((AddChar.linearIndependent (Additive ({−1,1}^[n])) ℝ).comp signMonomialChar
          signMonomialChar_injective))
    (by
      simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset,
        Fintype.card_units_int])

/-- O'Donnell, Theorem 1.5: the parity functions form an orthonormal basis. -/
theorem parity_orthonormal_basis :
    (∀ S : Finset (Fin n), walshBasis n S = monomial S) ∧
      ∀ S T : Finset (Fin n),
        ⟪monomial S, monomial T⟫ᵤ = if S = T then 1 else 0 := by
  constructor
  · intro S
    simp [walshBasis]
  · intro S T
    have hreindex : ⟪monomial S, monomial T⟫ᵤ =
        RCLike.wInner RCLike.cWeight (signMonomialChar S) (signMonomialChar T) := by
      rw [uniformInner, RCLike.wInner_cWeight_eq_expect,
        RCLike.wInner_cWeight_eq_expect]
      symm
      apply Fintype.expect_equiv Additive.toMul
      intro x
      rfl
    rw [hreindex]
    simpa [signMonomialChar_injective.eq_iff] using
      (AddChar.wInner_cWeight_eq_boole (signMonomialChar S) (signMonomialChar T))

/-- O'Donnell, Fact 1.6 on its stated domain `{-1,1}ⁿ`. -/
theorem monomial_mul_monomial (S T : Finset (Fin n)) (x : {−1,1}^[n]) :
    monomial S x * monomial T x = monomial (S ∆ T) x := by
  classical
  change (∏ i ∈ S, signValue (x i)) * (∏ i ∈ T, signValue (x i)) =
    ∏ i ∈ S ∆ T, signValue (x i)
  rw [← Fintype.prod_ite_mem S, ← Fintype.prod_ite_mem T,
    ← Fintype.prod_ite_mem (S ∆ T)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi : signValue (x i) * signValue (x i) = 1 := by
    rcases signValue_eq_neg_one_or_one (x i) with h | h <;> rw [h] <;> norm_num
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, hi]

/-- O'Donnell, Fact 1.7 on its stated domain `{-1,1}ⁿ`. -/
theorem expect_monomial (S : Finset (Fin n)) :
    𝔼 x : {−1,1}^[n], monomial S x = if S = ∅ then 1 else 0 := by
  have hempty : signMonomialChar (∅ : Finset (Fin n)) = 0 := by
    ext x
    simp [signMonomialChar, monomial]
  have hzero : signMonomialChar S = 0 ↔ S = ∅ := by
    rw [← hempty]
    exact signMonomialChar_injective.eq_iff
  have hreindex : (𝔼 x : {−1,1}^[n], monomial S x) =
      𝔼 x : Additive ({−1,1}^[n]), signMonomialChar S x := by
    symm
    apply Fintype.expect_equiv Additive.toMul
    intro x
    rfl
  rw [hreindex]
  simpa [hzero] using AddChar.expect_eq_ite (signMonomialChar S)

end FABL
