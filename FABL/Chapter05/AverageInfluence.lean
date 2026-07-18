/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LowDegreeSpectralConcentration

/-!
# Average influence

Book item: Exercise 2.43(a), recalled in Section 5.5.

The average influence and its comparison with noise sensitivity at inverse dimension.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Exercise 2.43(a): average influence is total influence divided by the
dimension. -/
noncomputable def averageInfluence (f : {−1,1}^[n] → ℝ) : ℝ :=
  totalInfluence f / n

/-- The probability of a Boolean function changing after independently choosing a uniform input
and a uniform coordinate and flipping that coordinate. -/
noncomputable def averageCoordinateFlipProbability (f : BooleanFunction n) : ℝ :=
  𝔼 i : Fin n, uniformProbability fun x : {−1,1}^[n] ↦
    f x ≠ f (flipCoordinate x i)

/-- For positive dimension, average influence is the random-coordinate flip probability. -/
theorem averageInfluence_toReal_eq_averageCoordinateFlipProbability
    (f : BooleanFunction n) (_hn : 0 < n) :
    averageInfluence f.toReal = averageCoordinateFlipProbability f := by
  classical
  rw [averageInfluence, averageCoordinateFlipProbability, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fin]
  congr 1
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro i _
  rw [← booleanInfluence_eq_influence_toReal]
  rw [booleanInfluence]
  rw [show IsPivotal f i =
      (fun x : {−1,1}^[n] ↦ f x ≠ f (flipCoordinate x i)) from rfl]
  unfold uniformProbability
  apply Finset.expect_congr rfl
  intro x _
  by_cases h : f x ≠ f (flipCoordinate x i) <;> simp [h]

private theorem natCast_mul_one_sub_pow_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {k n : ℕ} (hkn : k ≤ n) :
    (k : ℝ) * (1 - a ^ n) ≤ (n : ℝ) * (1 - a ^ k) := by
  by_cases hk : k = 0
  · simp [hk]
  have hpow_le (j : ℕ) (hj : j ∈ Finset.range k) : a ^ k ≤ a ^ j :=
    pow_le_pow_of_le_one ha0 ha1 (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hsum :
      (k : ℝ) * a ^ k ≤ ∑ j ∈ Finset.range k, a ^ j := by
    calc
      (k : ℝ) * a ^ k = ∑ _j ∈ Finset.range k, a ^ k := by simp
      _ ≤ ∑ j ∈ Finset.range k, a ^ j :=
        Finset.sum_le_sum fun j hj ↦ hpow_le j hj
  have honeSub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hkstep : (k : ℝ) * a ^ k * (1 - a) ≤ 1 - a ^ k := by
    calc
      (k : ℝ) * a ^ k * (1 - a) ≤
          (∑ j ∈ Finset.range k, a ^ j) * (1 - a) :=
        mul_le_mul_of_nonneg_right hsum honeSub
      _ = 1 - a ^ k := geom_sum_mul_of_le_one ha1 k
  have htail :
      1 - a ^ (n - k) ≤ ((n - k : ℕ) : ℝ) * (1 - a) := by
    have hbernoulli :=
      one_add_mul_sub_le_pow (a := a) (by linarith : (-1 : ℝ) ≤ a) (n - k)
    nlinarith
  have hka : 0 ≤ (k : ℝ) * a ^ k :=
    mul_nonneg (Nat.cast_nonneg k) (pow_nonneg ha0 k)
  have htail' :
      (k : ℝ) * a ^ k * (1 - a ^ (n - k)) ≤
        (k : ℝ) * a ^ k * (((n - k : ℕ) : ℝ) * (1 - a)) :=
    mul_le_mul_of_nonneg_left htail hka
  have hdiff : 0 ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkstep' :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) * a ^ k * (1 - a)) ≤
        ((n - k : ℕ) : ℝ) * (1 - a ^ k) :=
    mul_le_mul_of_nonneg_left hkstep hdiff
  have hnCast : (n : ℝ) = (k : ℝ) + ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkn]
    ring
  have hpow : a ^ n = a ^ k * a ^ (n - k) := by
    conv_lhs => rw [show n = k + (n - k) by omega, pow_add]
  rw [hpow, hnCast]
  nlinarith

private theorem one_sub_inverse_dimension_pow_upper
    {n k : ℕ} (hn : 0 < n) :
    1 - (1 - 2 / (n : ℝ)) ^ k ≤ 2 * (k : ℝ) / n := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOneReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : 2 / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hnReal]
    nlinarith
  have hbernoulli :=
    one_add_mul_le_pow
      (a := -(2 / (n : ℝ))) (by linarith : (-2 : ℝ) ≤ -(2 / (n : ℝ))) k
  calc
    1 - (1 - 2 / (n : ℝ)) ^ k ≤
        1 - (1 + (k : ℝ) * (-(2 / (n : ℝ)))) :=
      sub_le_sub_left hbernoulli 1
    _ = 2 * (k : ℝ) / n := by ring

private theorem one_sub_inverse_dimension_pow_lower
    {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    (1 - Real.exp (-2)) * (k : ℝ) / n ≤
      1 - (1 - 2 / (n : ℝ)) ^ k := by
  have hnOne : 1 ≤ n := hn
  rcases eq_or_lt_of_le hnOne with hnEq | hnTwo
  · subst n
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · simp
    · norm_num
      nlinarith [Real.exp_pos (-2)]
  · have hnReal : 0 < (n : ℝ) := by positivity
    let a : ℝ := 1 - 2 / (n : ℝ)
    have ha0 : 0 ≤ a := by
      dsimp [a]
      rw [sub_nonneg, div_le_iff₀ hnReal]
      have hnTwoReal : (2 : ℝ) ≤ n := by exact_mod_cast hnTwo
      simpa only [one_mul] using hnTwoReal
    have ha1 : a ≤ 1 := by
      dsimp [a]
      have : 0 < 2 / (n : ℝ) := div_pos (by norm_num) hnReal
      linarith
    have hpow :
        a ^ n ≤ Real.exp (-2) := by
      have hδpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnReal
      have hδhalf : 1 / (n : ℝ) ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hnTwo)
      have hinv : 1 / (1 / (n : ℝ)) ≤ (n : ℝ) := by
        field_simp
        norm_num
      simpa [a, div_eq_mul_inv] using
        one_sub_two_mul_pow_le_exp_neg_two
          (δ := 1 / (n : ℝ)) (m := n) hδpos hδhalf hinv
    have hchord :=
      natCast_mul_one_sub_pow_le ha0 ha1 hkn
    have hconstant :
        (k : ℝ) * (1 - Real.exp (-2)) ≤ (n : ℝ) * (1 - a ^ k) := by
      calc
        (k : ℝ) * (1 - Real.exp (-2)) ≤
            (k : ℝ) * (1 - a ^ n) := by
          gcongr
        _ ≤ (n : ℝ) * (1 - a ^ k) := hchord
    rw [div_le_iff₀ hnReal]
    simpa [a, mul_comm, mul_left_comm, mul_assoc] using hconstant

/-- O'Donnell, Exercise 2.43(a), lower comparison at inverse dimension. -/
theorem averageInfluence_mul_one_sub_exp_neg_two_div_two_le_noiseSensitivity
    (f : BooleanFunction n) (hn : 0 < n) :
    (1 - Real.exp (-2)) / 2 * averageInfluence f.toReal ≤
      noiseSensitivity (1 / (n : ℝ))
        ⟨by positivity, by
          have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
          have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
          exact (div_le_one hnPos).2 hnReal⟩ f := by
  classical
  let δ : ℝ := 1 / (n : ℝ)
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (div_le_one hnPos).2 hnReal⟩
  have hcoeff (S : Finset (Fin n)) :
      (1 - Real.exp (-2)) * (S.card : ℝ) / n ≤
        1 - (1 - 2 * δ) ^ S.card := by
    have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
    simpa [δ, div_eq_mul_inv] using one_sub_inverse_dimension_pow_lower hn hcard
  have hsum :
      (1 - Real.exp (-2)) / n * totalInfluence f.toReal ≤
        2 * noiseSensitivity δ hδ f := by
    rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff,
      two_mul_noiseSensitivity_eq_sum_fourier]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    calc
      (1 - Real.exp (-2)) / n *
          ((S.card : ℝ) * fourierCoeff f.toReal S ^ 2) =
          ((1 - Real.exp (-2)) * (S.card : ℝ) / n) *
            fourierCoeff f.toReal S ^ 2 := by ring
      _ ≤ (1 - (1 - 2 * δ) ^ S.card) *
          fourierCoeff f.toReal S ^ 2 :=
        mul_le_mul_of_nonneg_right (hcoeff S) (sq_nonneg _)
  change (1 - Real.exp (-2)) / 2 * (totalInfluence f.toReal / n) ≤ _
  change _ ≤ noiseSensitivity δ hδ f
  calc
    (1 - Real.exp (-2)) / 2 * (totalInfluence f.toReal / n) =
        ((1 - Real.exp (-2)) / n * totalInfluence f.toReal) / 2 := by ring
    _ ≤ (2 * noiseSensitivity δ hδ f) / 2 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = noiseSensitivity δ hδ f := by ring

/-- O'Donnell, Exercise 2.43(a), upper comparison at inverse dimension. -/
theorem noiseSensitivity_inverse_dimension_le_averageInfluence
    (f : BooleanFunction n) (hn : 0 < n) :
    noiseSensitivity (1 / (n : ℝ))
        ⟨by positivity, by
          have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
          have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
          exact (div_le_one hnPos).2 hnReal⟩ f ≤
      averageInfluence f.toReal := by
  classical
  let δ : ℝ := 1 / (n : ℝ)
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact (div_le_one hnPos).2 hnReal⟩
  have hcoeff (S : Finset (Fin n)) :
      1 - (1 - 2 * δ) ^ S.card ≤ 2 * (S.card : ℝ) / n := by
    simpa [δ, div_eq_mul_inv] using one_sub_inverse_dimension_pow_upper
      (k := S.card) hn
  have hsum :
      2 * noiseSensitivity δ hδ f ≤
        2 / n * totalInfluence f.toReal := by
    rw [two_mul_noiseSensitivity_eq_sum_fourier,
      totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    calc
      (1 - (1 - 2 * δ) ^ S.card) *
          fourierCoeff f.toReal S ^ 2 ≤
          (2 * (S.card : ℝ) / n) * fourierCoeff f.toReal S ^ 2 :=
        mul_le_mul_of_nonneg_right (hcoeff S) (sq_nonneg _)
      _ = 2 / n * ((S.card : ℝ) * fourierCoeff f.toReal S ^ 2) := by ring
  change noiseSensitivity δ hδ f ≤ totalInfluence f.toReal / n
  calc
    noiseSensitivity δ hδ f = (2 * noiseSensitivity δ hδ f) / 2 := by ring
    _ ≤ (2 / n * totalInfluence f.toReal) / 2 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = totalInfluence f.toReal / n := by ring

end FABL
