/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.Peres

/-!
# Noise-sensitivity derivative of linear threshold functions

Book item: Exercise 5.39.
-/

open Finset Set
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The Fourier-weight consequence of Peres's theorem used in Exercise 5.39:
`W^{≥ k}[f] ≤ 4 / √k` for every positive integer `k`. -/
theorem fourierWeightAbove_pred_le_four_div_sqrt_of_isLinearThreshold
    (f : BooleanFunction n) (hf : IsLinearThreshold f) (k : ℕ) (hk : 0 < k) :
    fourierWeightAbove (k - 1) f.toReal ≤ 4 / Real.sqrt (k : ℝ) := by
  classical
  by_cases hkOne : k = 1
  · subst k
    have htail :
        fourierWeightAbove 0 f.toReal ≤
          ∑ S : Finset (Fin n), fourierCoeff f.toReal S ^ 2 := by
      unfold fourierWeightAbove fourierWeight
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun S _ _ ↦ sq_nonneg (fourierCoeff f.toReal S))
    rw [sum_sq_fourierCoeff_eq_one] at htail
    simpa using htail.trans (by norm_num : (1 : ℝ) ≤ 4)
  · have hkTwo : 2 ≤ k := by omega
    have hkReal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkTwo
    have hkRealPos : (0 : ℝ) < (k : ℝ) := by positivity
    let δ : PositiveHalfNoiseParameter :=
      ⟨1 / (k : ℝ), by positivity, by
        rw [div_le_iff₀ hkRealPos]
        nlinarith⟩
    let c : ℝ := 1 - Real.exp (-2)
    have hc : 0 < c := by
      dsimp [c]
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    have hδrecip : 1 / (δ : ℝ) = (k : ℝ) := by
      dsimp [δ]
      field_simp
    have hmul :
        c * fourierWeightAbove (k - 1) f.toReal ≤
          2 * noiseSensitivity (δ : ℝ)
            ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := by
      calc
        c * fourierWeightAbove (k - 1) f.toReal =
            ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
              k - 1 < S.card), c * fourierWeight f.toReal S := by
          rw [fourierWeightAbove, Finset.mul_sum]
        _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
              k - 1 < S.card),
            (1 - (1 - 2 * (δ : ℝ)) ^ S.card) * fourierWeight f.toReal S := by
          apply Finset.sum_le_sum
          intro S hS
          have hcardNat : k ≤ S.card := by
            have := (Finset.mem_filter.mp hS).2
            omega
          have hcard : 1 / (δ : ℝ) ≤ (S.card : ℝ) := by
            rw [hδrecip]
            exact_mod_cast hcardNat
          have hpow :
              (1 - 2 * (δ : ℝ)) ^ S.card ≤ Real.exp (-2) :=
            one_sub_two_mul_pow_le_exp_neg_two δ.2.1 δ.2.2 hcard
          apply mul_le_mul_of_nonneg_right
          · dsimp [c]
            linarith
          · exact sq_nonneg (fourierCoeff f.toReal S)
        _ ≤ ∑ S : Finset (Fin n),
            (1 - (1 - 2 * (δ : ℝ)) ^ S.card) * fourierWeight f.toReal S := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun S _ _ ↦ mul_nonneg
              (one_sub_one_sub_two_mul_pow_nonneg δ.2.1.le δ.2.2 S.card)
              (sq_nonneg (fourierCoeff f.toReal S)))
        _ = 2 * noiseSensitivity (δ : ℝ)
            ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := by
          simpa [fourierWeight] using
            (two_mul_noiseSensitivity_eq_sum_fourier (δ : ℝ)
              ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f).symm
    have htail :
        fourierWeightAbove (k - 1) f.toReal ≤
          3 * noiseSensitivity (δ : ℝ)
            ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := by
      calc
        fourierWeightAbove (k - 1) f.toReal ≤
            (2 * noiseSensitivity (δ : ℝ)
              ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f) / c :=
          (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
        _ = (2 / c) * noiseSensitivity (δ : ℝ)
              ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := by ring
        _ ≤ 3 * noiseSensitivity (δ : ℝ)
              ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [c] using two_div_one_sub_exp_neg_two_le_three)
            (noiseSensitivity_nonneg (δ : ℝ)
              ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f)
    have hperes := peresNoiseSensitivityBound f hf δ
    have hconstant : 3 * Real.sqrt (3 / 2 : ℝ) ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2),
        Real.sqrt_nonneg (3 / 2 : ℝ)]
    have hsqrtδ :
        Real.sqrt (δ : ℝ) = 1 / Real.sqrt (k : ℝ) := by
      dsimp [δ]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    calc
      fourierWeightAbove (k - 1) f.toReal ≤
          3 * noiseSensitivity (δ : ℝ)
            ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f := htail
      _ ≤ 3 * (Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left hperes (by norm_num)
      _ = (3 * Real.sqrt (3 / 2 : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
        rw [hsqrtδ]
        ring
      _ ≤ 4 * (1 / Real.sqrt (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = 4 / Real.sqrt (k : ℝ) := by ring

private theorem two_mul_delta_mul_card_mul_pow_le_one_sub_pow
    {δ : ℝ} (hδnonneg : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (k : ℕ) :
    2 * δ * (k : ℝ) * (1 - 2 * δ) ^ (k - 1) ≤
      1 - (1 - 2 * δ) ^ k := by
  let ρ : ℝ := 1 - 2 * δ
  have hρnonneg : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρone : ρ ≤ 1 := by dsimp [ρ]; linarith
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ρ ^ (k - 1) ≤ ρ ^ j :=
    pow_le_pow_of_le_one hρnonneg hρone (by
      rw [Finset.mem_range] at hj
      omega)
  have hsum :
      (k : ℝ) * ρ ^ (k - 1) ≤ ∑ j ∈ Finset.range k, ρ ^ j := by
    calc
      (k : ℝ) * ρ ^ (k - 1) =
          ∑ _j ∈ Finset.range k, ρ ^ (k - 1) := by simp
      _ ≤ ∑ j ∈ Finset.range k, ρ ^ j :=
        Finset.sum_le_sum fun j hj ↦ hterm j hj
  calc
    2 * δ * (k : ℝ) * (1 - 2 * δ) ^ (k - 1) =
        ((k : ℝ) * ρ ^ (k - 1)) * (1 - ρ) := by
      dsimp [ρ]
      ring
    _ ≤ (∑ j ∈ Finset.range k, ρ ^ j) * (1 - ρ) :=
      mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hρone)
    _ = 1 - ρ ^ k := geom_sum_mul_of_le_one hρone k
    _ = 1 - (1 - 2 * δ) ^ k := by rfl

private theorem delta_mul_totalStableInfluence_le_noiseSensitivity
    (f : BooleanFunction n) {δ : ℝ} (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    δ * totalStableInfluence (1 - 2 * δ) f.toReal ≤
      noiseSensitivity δ ⟨hδpos.le, hδhalf.trans (by norm_num)⟩ f := by
  have htwice :
      2 * δ * totalStableInfluence (1 - 2 * δ) f.toReal ≤
        2 * noiseSensitivity δ
          ⟨hδpos.le, hδhalf.trans (by norm_num)⟩ f := by
    rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff,
      two_mul_noiseSensitivity_eq_sum_fourier]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    calc
      2 * δ *
          ((S.card : ℝ) * (1 - 2 * δ) ^ (S.card - 1) *
            fourierCoeff f.toReal S ^ 2) =
          (2 * δ * (S.card : ℝ) * (1 - 2 * δ) ^ (S.card - 1)) *
            fourierCoeff f.toReal S ^ 2 := by ring
      _ ≤ (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f.toReal S ^ 2 :=
        mul_le_mul_of_nonneg_right
          (two_mul_delta_mul_card_mul_pow_le_one_sub_pow hδpos.le hδhalf S.card)
          (sq_nonneg (fourierCoeff f.toReal S))
  linarith

/-- O'Donnell, Exercise 5.39: the derivative of the noise sensitivity of every linear
threshold function is at most a universal constant times `1 / √δ`. -/
theorem deriv_noiseSensitivityCurve_le_sqrt_three_halves_div_sqrt_of_isLinearThreshold
    (f : BooleanFunction n) (hf : IsLinearThreshold f)
    (δ : PositiveHalfNoiseParameter) :
    deriv (noiseSensitivityCurve f.toReal) (δ : ℝ) ≤
      Real.sqrt (3 / 2 : ℝ) / Real.sqrt (δ : ℝ) := by
  rw [(hasDerivAt_noiseSensitivityCurve f.toReal (δ : ℝ)).deriv]
  have hweighted :=
    delta_mul_totalStableInfluence_le_noiseSensitivity f δ.2.1 δ.2.2
  have hbound :
      (δ : ℝ) * totalStableInfluence (1 - 2 * (δ : ℝ)) f.toReal ≤
        Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) :=
    hweighted.trans (peresNoiseSensitivityBound f hf δ)
  have hsqrtpos : 0 < Real.sqrt (δ : ℝ) := Real.sqrt_pos.2 δ.2.1
  rw [le_div_iff₀ hsqrtpos]
  exact le_of_mul_le_mul_right (by
    calc
      (totalStableInfluence (1 - 2 * (δ : ℝ)) f.toReal *
          Real.sqrt (δ : ℝ)) * Real.sqrt (δ : ℝ) =
          (δ : ℝ) * totalStableInfluence (1 - 2 * (δ : ℝ)) f.toReal := by
        rw [mul_assoc, Real.mul_self_sqrt δ.2.1.le]
        ring
      _ ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) := hbound) hsqrtpos

end FABL
