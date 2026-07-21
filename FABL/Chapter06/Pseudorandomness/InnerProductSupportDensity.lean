/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.Examples
public import FABL.Chapter06.Pseudorandomness.SmallBias

/-!
# The density on the support of inner product modulo two

Book items: Exercise 6.7 and Example 6.47.

The density is Mathlib/FABL's normalized indicator of the one-set of the binary
inner-product function. Its exact bias and expectation gap are obtained from the
flat Fourier spectrum proved in Chapter 5.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

noncomputable section

private theorem f₂_eq_zero_or_one (a : 𝔽₂) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The one-set of the binary inner-product-mod-two function. -/
def innerProductModTwoOneSet (m : ℕ) : Set (F₂Cube (m + m)) :=
  {z | innerProductModTwoBit z = 1}

local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The inner-product one-set is nonempty in every positive block dimension. -/
theorem innerProductModTwoOneSet_nonempty (m : ℕ) (hm : 0 < m) :
    (innerProductModTwoOneSet m).Nonempty := by
  let i : Fin m := ⟨0, hm⟩
  let e : F₂Cube m := Pi.single i 1
  refine ⟨joinF₂CubeBlocks e e, ?_⟩
  simp [innerProductModTwoOneSet, innerProductModTwoBit_joinF₂CubeBlocks,
    f₂DotProduct, e, dotProduct_single]

/-- The uniform density on inputs where inner product modulo two equals one. -/
noncomputable def innerProductModTwoSupportDensity
    (m : ℕ) (hm : 0 < m) : ProbabilityDensity (m + m) :=
  subsetDensity
    (innerProductModTwoOneSet m)
    (innerProductModTwoOneSet_nonempty m hm)

/-- The zero-one embedding of inner product is the affine rescaling of its sign encoding. -/
theorem booleanRealEmbedding_innerProductModTwoBit
    (m : ℕ) (z : F₂Cube (m + m)) :
    booleanRealEmbedding innerProductModTwoBit z =
      (1 - innerProductModTwo m z) / 2 := by
  rcases f₂_eq_zero_or_one (innerProductModTwoBit z) with h | h <;>
    simp [booleanRealEmbedding, innerProductModTwo, realSignEncodedFunction,
      signEncodedFunction, h]

/-- The uniform mean of the sign encoding of inner product modulo two. -/
theorem expect_innerProductModTwo (m : ℕ) :
    (𝔼 z, innerProductModTwo m z) = ((2 : ℝ) ^ m)⁻¹ := by
  have h :=
    vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks
      (n := m) (0 : F₂Cube m) (0 : F₂Cube m)
  have hzero :
      joinF₂CubeBlocks (0 : F₂Cube m) (0 : F₂Cube m) = 0 := by
    change Fin.append (0 : F₂Cube m) (0 : F₂Cube m) = 0
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact Fin.append_left _ _ j
    · intro j
      simpa using Fin.append_right (0 : F₂Cube m) (0 : F₂Cube m) j
  rw [hzero] at h
  rw [vectorFourierCoeff_eq_expect] at h
  simpa [f₂DotProduct] using h

/-- The exact uniform probability that inner product modulo two equals one. -/
theorem expect_booleanRealEmbedding_innerProductModTwoBit (m : ℕ) :
    (𝔼 z, booleanRealEmbedding (innerProductModTwoBit (n := m)) z) =
      (1 - ((2 : ℝ) ^ m)⁻¹) / 2 := by
  calc
    (𝔼 z, booleanRealEmbedding (innerProductModTwoBit (n := m)) z) =
        𝔼 z, (1 - innerProductModTwo m z) / 2 := by
      apply Finset.expect_congr rfl
      intro z _
      exact booleanRealEmbedding_innerProductModTwoBit m z
    _ = (1 - (𝔼 z, innerProductModTwo m z)) / 2 := by
      rw [← Finset.expect_div, Finset.expect_sub_distrib, Fintype.expect_const]
    _ = (1 - ((2 : ℝ) ^ m)⁻¹) / 2 := by
      rw [expect_innerProductModTwo]

/-- The normalized indicator set has the same exact uniform probability. -/
theorem uniformProbability_innerProductModTwoOneSet (m : ℕ) :
    uniformProbability (fun z ↦ z ∈ innerProductModTwoOneSet m) =
      (1 - ((2 : ℝ) ^ m)⁻¹) / 2 := by
  classical
  unfold uniformProbability
  calc
    (𝔼 z, if z ∈ innerProductModTwoOneSet m then (1 : ℝ) else 0) =
        𝔼 z, booleanRealEmbedding (innerProductModTwoBit (n := m)) z := by
      apply Finset.expect_congr rfl
      intro z _
      rcases f₂_eq_zero_or_one (innerProductModTwoBit z) with h | h <;>
        simp [innerProductModTwoOneSet, booleanRealEmbedding, h]
    _ = (1 - ((2 : ℝ) ^ m)⁻¹) / 2 :=
      expect_booleanRealEmbedding_innerProductModTwoBit m

/-- The set indicator of the inner-product one-set is its zero-one embedding. -/
theorem setIndicator_innerProductModTwoOneSet (m : ℕ) :
    setIndicator (innerProductModTwoOneSet m) =
      booleanRealEmbedding innerProductModTwoBit := by
  classical
  funext z
  rcases f₂_eq_zero_or_one (innerProductModTwoBit z) with h | h <;>
    simp [setIndicator, innerProductModTwoOneSet, booleanRealEmbedding, h]

/-- The explicit value of the support density. -/
theorem innerProductModTwoSupportDensity_apply
    (m : ℕ) (hm : 0 < m) (z : F₂Cube (m + m)) :
    innerProductModTwoSupportDensity m hm z =
      (uniformProbability fun y ↦ y ∈ innerProductModTwoOneSet m)⁻¹ *
        booleanRealEmbedding innerProductModTwoBit z := by
  classical
  rw [innerProductModTwoSupportDensity, subsetDensity_apply]
  unfold subsetDensityValue
  rw [setIndicator_innerProductModTwoOneSet]

/-- Away from the origin, the zero-one IP spectrum is one half of the sign spectrum. -/
theorem vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero
    (m : ℕ) (γ : F₂Cube (m + m)) (hγ : γ ≠ 0) :
    vectorFourierCoeff
        (booleanRealEmbedding (innerProductModTwoBit (n := m))) γ =
      -(1 / 2) * vectorFourierCoeff (innerProductModTwo m) γ := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  simp_rw [booleanRealEmbedding_innerProductModTwoBit]
  calc
    (𝔼 z, ((1 - innerProductModTwo m z) / 2) *
        vectorWalshCharacter γ z) =
        𝔼 z, (vectorWalshCharacter γ z -
          innerProductModTwo m z * vectorWalshCharacter γ z) / 2 := by
      apply Finset.expect_congr rfl
      intro z _
      ring
    _ = ((𝔼 z, vectorWalshCharacter γ z) -
          (𝔼 z, innerProductModTwo m z * vectorWalshCharacter γ z)) / 2 := by
      rw [← Finset.expect_div, Finset.expect_sub_distrib]
    _ = -(1 / 2) *
        (𝔼 z, innerProductModTwo m z * vectorWalshCharacter γ z) := by
      rw [expect_vectorWalshCharacter, if_neg hγ]
      ring

/-- Every nontrivial zero-one IP coefficient has exact magnitude `2⁻ᵐ / 2`. -/
theorem abs_vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero
    (m : ℕ) (γ : F₂Cube (m + m)) (hγ : γ ≠ 0) :
    |vectorFourierCoeff
        (booleanRealEmbedding (innerProductModTwoBit (n := m))) γ| =
      ((2 : ℝ) ^ m)⁻¹ / 2 := by
  rw [vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero
    m γ hγ, abs_mul,
    abs_vectorFourierCoeff_innerProductModTwo]
  ring

/-- Every nontrivial coefficient of the support density has the same exact magnitude. -/
theorem abs_vectorFourierCoeff_innerProductModTwoSupportDensity
    (m : ℕ) (hm : 0 < m) (γ : F₂Cube (m + m)) (hγ : γ ≠ 0) :
    |vectorFourierCoeff (innerProductModTwoSupportDensity m hm) γ| =
      ((2 : ℝ) ^ m)⁻¹ / (1 - ((2 : ℝ) ^ m)⁻¹) := by
  classical
  have hp :
      0 < uniformProbability
        (fun z ↦ z ∈ innerProductModTwoOneSet m) := by
    unfold uniformProbability
    apply Finset.expect_pos'
    · intro z _
      by_cases hz : z ∈ innerProductModTwoOneSet m <;> simp [hz]
    · obtain ⟨z, hz⟩ := innerProductModTwoOneSet_nonempty m hm
      exact ⟨z, Finset.mem_univ z, by simp [hz]⟩
  have hdensity :
      (innerProductModTwoSupportDensity m hm :
          F₂Cube (m + m) → ℝ) =
        fun z ↦
          (uniformProbability
            fun y ↦ y ∈ innerProductModTwoOneSet m)⁻¹ *
              booleanRealEmbedding innerProductModTwoBit z := by
    funext z
    exact innerProductModTwoSupportDensity_apply m hm z
  rw [hdensity, vectorFourierCoeff_const_mul, abs_mul,
    abs_inv, abs_of_pos hp,
    abs_vectorFourierCoeff_booleanRealEmbedding_innerProductModTwoBit_of_ne_zero
      m γ hγ,
    uniformProbability_innerProductModTwoOneSet]
  have hden :
      1 - ((2 : ℝ) ^ m)⁻¹ ≠ 0 := by
    have := hp
    rw [uniformProbability_innerProductModTwoOneSet] at this
    linarith
  field_simp

/-- Exercise 6.7: the support density has the exact smallest possible bias parameter. -/
theorem innerProductModTwoSupportDensity_isBiased_iff
    (m : ℕ) (hm : 0 < m) (ε : ℝ) :
    (innerProductModTwoSupportDensity m hm).IsBiased ε ↔
      ((2 : ℝ) ^ m)⁻¹ / (1 - ((2 : ℝ) ^ m)⁻¹) ≤ ε := by
  constructor
  · intro hbiased
    let i : Fin m := ⟨0, hm⟩
    let γ : F₂Cube (m + m) := Pi.single (Fin.castAdd m i) 1
    have hγ : γ ≠ 0 := by
      intro hzero
      have hvalue := congrFun hzero (Fin.castAdd m i)
      simp [γ] at hvalue
    simpa [abs_vectorFourierCoeff_innerProductModTwoSupportDensity
      m hm γ hγ] using hbiased γ hγ
  · intro hε γ hγ
    rw [abs_vectorFourierCoeff_innerProductModTwoSupportDensity m hm γ hγ]
    exact hε

/-- Under the support density, inner product modulo two has expectation one. -/
theorem innerProductModTwoSupportDensity_expectation (m : ℕ) (hm : 0 < m) :
    (innerProductModTwoSupportDensity m hm).expectation
        (booleanRealEmbedding (innerProductModTwoBit (n := m))) = 1 := by
  classical
  let p :=
    uniformProbability fun y ↦ y ∈ innerProductModTwoOneSet m
  have hp : 0 < p := by
    dsimp [p]
    rw [uniformProbability_innerProductModTwoOneSet]
    have hpow : ((2 : ℝ) ^ m)⁻¹ < 1 := by
      exact (inv_lt_one₀ (by positivity)).2
        (one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hm))
    linarith
  unfold ProbabilityDensity.expectation
  simp_rw [innerProductModTwoSupportDensity_apply]
  calc
    (𝔼 z, p⁻¹ *
        booleanRealEmbedding (innerProductModTwoBit (n := m)) z *
        booleanRealEmbedding (innerProductModTwoBit (n := m)) z) =
        p⁻¹ *
          (𝔼 z, booleanRealEmbedding (innerProductModTwoBit (n := m)) z) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro z _
      rcases f₂_eq_zero_or_one
        (innerProductModTwoBit (n := m) z) with h | h <;>
        simp [booleanRealEmbedding, h]
    _ = p⁻¹ * p := by
      rw [expect_booleanRealEmbedding_innerProductModTwoBit]
      rw [show p = (1 - ((2 : ℝ) ^ m)⁻¹) / 2 by
        exact uniformProbability_innerProductModTwoOneSet m]
    _ = 1 := inv_mul_cancel₀ hp.ne'

/-- Example 6.47: the support density and the uniform cube have the stated exact gap. -/
theorem innerProductModTwoSupportDensity_expectation_gap
    (m : ℕ) (hm : 0 < m) :
    |(innerProductModTwoSupportDensity m hm).expectation
          (booleanRealEmbedding (innerProductModTwoBit (n := m))) -
        (𝔼 z, booleanRealEmbedding (innerProductModTwoBit (n := m)) z)| =
      (1 + ((2 : ℝ) ^ m)⁻¹) / 2 := by
  rw [innerProductModTwoSupportDensity_expectation,
    expect_booleanRealEmbedding_innerProductModTwoBit]
  have hnonneg : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  rw [abs_of_nonneg]
  · ring
  · linarith

end

end FABL
