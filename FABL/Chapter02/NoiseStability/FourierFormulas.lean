/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.NoiseOperator

/-!
# Fourier formulas for noise stability

Book items: Example 2.44, Proposition 2.47, Theorem 2.49, Exercise 2.42.

The Fourier and spectral-moment formulas for noise stability and noise sensitivity from Section 2.4
of O'Donnell's *Analysis of Boolean Functions*.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Proposition 2.47: pointwise Fourier expansion of the noise operator. -/
theorem noiseOperator_fourier_expansion (ρ : ℝ) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    noiseOperator ρ f x =
      ∑ S, ρ ^ S.card * fourierCoeff f S * monomial S x := by
  classical
  have hf : f = ∑ S, fourierCoeff f S • monomial S := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact fourier_expansion f y
  conv_lhs => rw [hf]
  rw [map_sum]
  simp_rw [map_smul, noiseOperator_monomial]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- O'Donnell, Proposition 2.47: the noise operator is the degreewise multiplier
`∑ₖ ρᵏ f⁼ᵏ`. -/
theorem noiseOperator_eq_sum_degreePart (ρ : ℝ) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    noiseOperator ρ f x =
      ∑ k ∈ Finset.range (n + 1), ρ ^ k * degreePart k f x := by
  rw [noiseOperator_fourier_expansion]
  calc
    (∑ S, ρ ^ S.card * fourierCoeff f S * monomial S x) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k,
            ρ ^ S.card * fourierCoeff f S * monomial S x := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    _ = ∑ k ∈ Finset.range (n + 1), ρ ^ k * degreePart k f x := by
      apply Finset.sum_congr rfl
      intro k _
      rw [degreePart, Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = k
      · rw [hcard]
        simpa using mul_assoc (ρ ^ k) (fourierCoeff f S) (monomial S x)
      · simp [hcard]

/-- O'Donnell, Theorem 2.49: the subset-indexed Fourier formula for noise stability. -/
theorem noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : {−1,1}^[n] → ℝ) :
    noiseStability ρ hρ f =
      ∑ S, ρ ^ S.card * fourierCoeff f S ^ 2 := by
  rw [noiseStability_eq_uniformInner_noiseOperator]
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  calc
    (𝔼 x, noiseOperator ρ f x * f x) =
        𝔼 x, (∑ S, ρ ^ S.card * fourierCoeff f S * monomial S x) * f x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [noiseOperator_fourier_expansion]
    _ = 𝔼 x, ∑ S, (ρ ^ S.card * fourierCoeff f S * monomial S x) * f x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ S, 𝔼 x, (ρ ^ S.card * fourierCoeff f S * monomial S x) * f x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S, ρ ^ S.card * fourierCoeff f S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [show (𝔼 x, (ρ ^ S.card * fourierCoeff f S * monomial S x) * f x) =
          ρ ^ S.card * fourierCoeff f S * (𝔼 x, f x * monomial S x) by
        symm
        calc
          ρ ^ S.card * fourierCoeff f S * (𝔼 x, f x * monomial S x) =
              𝔼 x, (ρ ^ S.card * fourierCoeff f S) * (f x * monomial S x) :=
            Finset.mul_expect Finset.univ (fun x ↦ f x * monomial S x)
              (ρ ^ S.card * fourierCoeff f S)
          _ = 𝔼 x, (ρ ^ S.card * fourierCoeff f S * monomial S x) * f x := by
            apply Finset.expect_congr rfl
            intro x _
            ring]
      rw [← fourierCoeff]
      ring

/-- O'Donnell, Theorem 2.49: regrouping the stability formula by Fourier level. -/
theorem noiseStability_eq_sum_level_rho_pow_mul_fourierWeight
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : {−1,1}^[n] → ℝ) :
    noiseStability ρ hρ f =
      ∑ k ∈ Finset.range (n + 1), ρ ^ k * fourierWeightAtLevel k f := by
  rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  calc
    (∑ S, ρ ^ S.card * fourierCoeff f S ^ 2) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k, ρ ^ S.card * fourierCoeff f S ^ 2 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    _ = ∑ k ∈ Finset.range (n + 1), ρ ^ k * fourierWeightAtLevel k f := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierWeightAtLevel, Finset.mul_sum]
      simp only [Finset.sum_filter, fourierWeight]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = k <;> simp [hcard]

/-- Theorem 2.49, Equation (2.6): Boolean stability is the spectral moment of `ρ^|S|`. -/
theorem noiseStability_toReal_eq_spectralSample_moment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    noiseStability ρ hρ f.toReal =
      pmfExpectation (spectralSample f) (fun S ↦ ρ ^ S.card) := by
  rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  unfold pmfExpectation
  apply Finset.sum_congr rfl
  intro S _
  rw [spectralSample_apply_toReal]
  simp [fourierWeight, mul_comm]

/-- O'Donnell, Theorem 2.49 bookkeeping: regrouping all Fourier levels recovers the full squared
Fourier mass. -/
theorem sum_fourierWeightAtLevel_range (f : {−1,1}^[n] → ℝ) :
    (∑ k ∈ Finset.range (n + 1), fourierWeightAtLevel k f) =
      ∑ S, fourierCoeff f S ^ 2 := by
  calc
    (∑ k ∈ Finset.range (n + 1), fourierWeightAtLevel k f) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k, fourierCoeff f S ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      simp [fourierWeightAtLevel, fourierWeight]
    _ = ∑ S, fourierCoeff f S ^ 2 := by
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega

/-- O'Donnell, Theorem 2.49, Equation (2.7): the level-weight formula for Boolean noise
sensitivity. -/
theorem noiseSensitivity_eq_sum_level
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    noiseSensitivity δ hδ f =
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n + 1),
        (1 - (1 - 2 * δ) ^ k) * fourierWeightAtLevel k f.toReal := by
  rw [noiseSensitivity_eq_half_sub_half_noiseStability,
    noiseStability_eq_sum_level_rho_pow_mul_fourierWeight]
  have hmass : ∑ k ∈ Finset.range (n + 1), fourierWeightAtLevel k f.toReal = 1 := by
    rw [sum_fourierWeightAtLevel_range, sum_sq_fourierCoeff_eq_one]
  calc
    (1 - ∑ k ∈ Finset.range (n + 1),
        (1 - 2 * δ) ^ k * fourierWeightAtLevel k f.toReal) / 2 =
        (1 / 2 : ℝ) *
          ((∑ k ∈ Finset.range (n + 1), fourierWeightAtLevel k f.toReal) -
            ∑ k ∈ Finset.range (n + 1),
              (1 - 2 * δ) ^ k * fourierWeightAtLevel k f.toReal) := by
      rw [hmass]
      ring
    _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n + 1),
          (fourierWeightAtLevel k f.toReal -
            (1 - 2 * δ) ^ k * fourierWeightAtLevel k f.toReal) := by
      rw [Finset.sum_sub_distrib]
    _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.range (n + 1),
          (1 - (1 - 2 * δ) ^ k) * fourierWeightAtLevel k f.toReal := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- O'Donnell, Exercise 2.42: noise sensitivity is at most the noise rate times total
influence. -/
theorem noiseSensitivity_le_delta_mul_totalInfluence
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    noiseSensitivity δ hδ f ≤ δ * totalInfluence f.toReal := by
  have hcoefficient (k : ℕ) :
      1 - (1 - 2 * δ) ^ k ≤ 2 * δ * k := by
    have hbernoulli :=
      one_add_mul_le_pow
        (a := -(2 * δ)) (by linarith [hδ.2] : (-2 : ℝ) ≤ -(2 * δ)) k
    calc
      1 - (1 - 2 * δ) ^ k ≤
          1 - (1 + (k : ℝ) * (-(2 * δ))) :=
        sub_le_sub_left hbernoulli 1
      _ = 2 * δ * k := by ring
  rw [noiseSensitivity_eq_sum_level,
    totalInfluence_eq_sum_level_mul_fourierWeight]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hweight : 0 ≤ fourierWeightAtLevel k f.toReal := by
    unfold fourierWeightAtLevel fourierWeight
    positivity
  calc
    (1 / 2 : ℝ) *
        ((1 - (1 - 2 * δ) ^ k) * fourierWeightAtLevel k f.toReal) ≤
      (1 / 2 : ℝ) *
        ((2 * δ * k) * fourierWeightAtLevel k f.toReal) := by
      gcongr
      exact hcoefficient k
    _ = δ * ((k : ℝ) * fourierWeightAtLevel k f.toReal) := by ring

/-- O'Donnell, Theorem 1.5: the Fourier coefficient of a Walsh monomial is its Kronecker delta. -/
theorem fourierCoeff_monomial (S T : Finset (Fin n)) :
    fourierCoeff (monomial S) T = if S = T then 1 else 0 := by
  rw [fourierCoeff_eq_uniformInner]
  exact (parity_orthonormal_basis.2 S T)

/-- O'Donnell, Example 2.44: a parity monomial has noise stability `ρ ^ |S|`. -/
theorem noiseStability_monomial
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (S : Finset (Fin n)) :
    noiseStability ρ hρ (monomial S) = ρ ^ S.card := by
  rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  simp_rw [fourierCoeff_monomial]
  simp

/-- O'Donnell, Example 2.44: the constant `+1` function has stability one. -/
theorem noiseStability_const_one
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    noiseStability (n := n) ρ hρ (fun _ ↦ 1) = 1 := by
  rw [show (fun _ : {−1,1}^[n] ↦ (1 : ℝ)) = monomial ∅ by
    funext x
    simp [monomial]]
  exact noiseStability_monomial (n := n) ρ hρ ∅

/-- O'Donnell, Example 2.44: the constant `-1` function has stability one. -/
theorem noiseStability_const_neg_one
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    noiseStability (n := n) ρ hρ (fun _ ↦ -1) = 1 := by
  unfold noiseStability
  simpa using pmfExpectation_const_one (correlatedPairPMF (n := n) ρ hρ)

/-- O'Donnell, Example 2.44: the Boolean parity function associated to a subset of coordinates. -/
def parityFunction (S : Finset (Fin n)) : BooleanFunction n :=
  fun x ↦ ∏ i ∈ S, x i

/-- O'Donnell, Example 2.44: the real coercion of the Boolean parity function is the Walsh
monomial. -/
theorem parityFunction_toReal (S : Finset (Fin n)) :
    (parityFunction S).toReal = monomial S := by
  funext x
  simp [parityFunction, BooleanFunction.toReal, monomial, signValue]

/-- O'Donnell, Example 2.44: Boolean parity has stability `ρ ^ |S|`. -/
theorem noiseStability_parityFunction
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (S : Finset (Fin n)) :
    noiseStability ρ hρ (parityFunction S).toReal = ρ ^ S.card := by
  rw [parityFunction_toReal, noiseStability_monomial]

/-- O'Donnell, Example 2.44: Boolean parity has noise sensitivity
`(1 - (1 - 2δ)^|S|) / 2`. -/
theorem noiseSensitivity_parityFunction
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin n)) :
    noiseSensitivity δ hδ (parityFunction S) =
      (1 - (1 - 2 * δ) ^ S.card) / 2 := by
  rw [noiseSensitivity_eq_half_sub_half_noiseStability,
    parityFunction_toReal, noiseStability_monomial]

/-- O'Donnell, Example 2.44: a dictator has noise stability `ρ`. -/
theorem noiseStability_dictator
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    noiseStability ρ hρ (dictator i).toReal = ρ := by
  rw [show (dictator i).toReal = (parityFunction {i}).toReal by
    rw [parityFunction_toReal]
    funext x
    exact dictator_toReal_eq_monomial_singleton i x]
  simpa using noiseStability_parityFunction ρ hρ ({i} : Finset (Fin n))

/-- O'Donnell, Example 2.44: a dictator has noise sensitivity `δ`. -/
theorem noiseSensitivity_dictator
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    noiseSensitivity δ hδ (dictator i) = δ := by
  rw [show dictator i = parityFunction {i} by
    funext x
    simp [dictator, parityFunction]]
  simpa using noiseSensitivity_parityFunction δ hδ ({i} : Finset (Fin n))


end FABL
