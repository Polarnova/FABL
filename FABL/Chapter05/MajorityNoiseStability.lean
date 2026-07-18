/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/

import FABL.Chapter05.MajorityWeightMonotonicity
import FABL.Chapter05.RegularThresholdNoiseStability

/-!
# Noise stability of majority

Book items: Theorem 5.18 and Exercise 5.23.
-/

open Filter Finset Set
open scoped BigOperators BooleanCube Topology

namespace FABL

private theorem fourierWeightAtLevel_majority_odd_eq_zero_of_even
    (m k : ℕ) (hk : Even k) :
    fourierWeightAtLevel k (majority (2 * m + 1)).toReal = 0 := by
  classical
  unfold fourierWeightAtLevel
  apply Finset.sum_eq_zero
  intro S hS
  have hScard : S.card = k := (Finset.mem_filter.mp hS).2
  have hSeven : Even S.card := hScard.symm ▸ hk
  rw [fourierWeight,
    fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      ⟨m, rfl⟩ S hSeven]
  norm_num

private theorem fourierWeightAtLevel_eq_zero_of_dimension_lt
    {n k : ℕ} (f : {−1,1}^[n] → ℝ) (hnk : n < k) :
    fourierWeightAtLevel k f = 0 := by
  classical
  unfold fourierWeightAtLevel
  apply Finset.sum_eq_zero
  intro S hS
  have hScard : S.card = k := (Finset.mem_filter.mp hS).2
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  exfalso
  omega

private theorem fourierWeightAtLevel_majority_next_odd_le_of_lt_top
    (m k : ℕ) (hk : k < 2 * m + 3) :
    fourierWeightAtLevel k (majority (2 * (m + 1) + 1)).toReal ≤
      fourierWeightAtLevel k (majority (2 * m + 1)).toReal := by
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · rw [fourierWeightAtLevel_majority_odd_eq_zero_of_even (m + 1) k hkEven,
      fourierWeightAtLevel_majority_odd_eq_zero_of_even m k hkEven]
  · rcases hkOdd with ⟨j, rfl⟩
    exact (fourierWeightAtLevel_majority_next_odd_lt m j (by omega)).le

private theorem noiseStability_majority_next_odd_comparison
    (m : ℕ) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * (m + 1) + 1)).toReal ≤
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal ∧
    (0 < ρ →
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
          (majority (2 * (m + 1) + 1)).toReal <
        noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
          (majority (2 * m + 1)).toReal) := by
  let hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  let a : ℕ → ℝ := fun k ↦
    fourierWeightAtLevel k (majority (2 * m + 1)).toReal
  let b : ℕ → ℝ := fun k ↦
    fourierWeightAtLevel k (majority (2 * (m + 1) + 1)).toReal
  let top : ℕ := 2 * m + 3
  have haHigh₁ : a (2 * m + 2) = 0 := by
    dsimp [a]
    exact fourierWeightAtLevel_eq_zero_of_dimension_lt
      (majority (2 * m + 1)).toReal (by omega)
  have haHigh₂ : a (2 * m + 3) = 0 := by
    dsimp [a]
    exact fourierWeightAtLevel_eq_zero_of_dimension_lt
      (majority (2 * m + 1)).toReal (by omega)
  have hmassSmallBase :
      (∑ k ∈ Finset.range ((2 * m + 1) + 1), a k) = 1 := by
    dsimp [a]
    rw [sum_fourierWeightAtLevel_range, sum_sq_fourierCoeff_eq_one]
  have hmassSmall :
      (∑ k ∈ Finset.range (top + 1), a k) = 1 := by
    dsimp [top]
    calc
      (∑ k ∈ Finset.range ((2 * m + 3) + 1), a k) =
          (∑ k ∈ Finset.range (2 * m + 3), a k) + a (2 * m + 3) := by
            rw [Finset.sum_range_succ]
      _ = ∑ k ∈ Finset.range (2 * m + 3), a k := by
        rw [haHigh₂, add_zero]
      _ = (∑ k ∈ Finset.range (2 * m + 2), a k) + a (2 * m + 2) := by
        rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega,
          Finset.sum_range_succ]
      _ = ∑ k ∈ Finset.range (2 * m + 2), a k := by
        rw [haHigh₁, add_zero]
      _ = 1 := by
        simpa only [show (2 * m + 1) + 1 = 2 * m + 2 by omega] using
          hmassSmallBase
  have hmassBigBase :
      (∑ k ∈ Finset.range ((2 * (m + 1) + 1) + 1), b k) = 1 := by
    dsimp [b]
    rw [sum_fourierWeightAtLevel_range, sum_sq_fourierCoeff_eq_one]
  have hmassBig :
      (∑ k ∈ Finset.range (top + 1), b k) = 1 := by
    dsimp [top]
    simpa only [
      show (2 * (m + 1) + 1) + 1 = (2 * m + 3) + 1 by omega] using
      hmassBigBase
  have hmassDiff :
      (∑ k ∈ Finset.range (top + 1), (a k - b k)) = 0 := by
    rw [Finset.sum_sub_distrib, hmassSmall, hmassBig, sub_self]
  have hweightedSmallBase :
      noiseStability ρ hρclosed (majority (2 * m + 1)).toReal =
        ∑ k ∈ Finset.range ((2 * m + 1) + 1), ρ ^ k * a k := by
    simpa only [a] using
      noiseStability_eq_sum_level_rho_pow_mul_fourierWeight
        ρ hρclosed (majority (2 * m + 1)).toReal
  have hweightedSmallExtend :
      (∑ k ∈ Finset.range (top + 1), ρ ^ k * a k) =
        ∑ k ∈ Finset.range ((2 * m + 1) + 1), ρ ^ k * a k := by
    dsimp [top]
    calc
      (∑ k ∈ Finset.range ((2 * m + 3) + 1), ρ ^ k * a k) =
          (∑ k ∈ Finset.range (2 * m + 3), ρ ^ k * a k) +
            ρ ^ (2 * m + 3) * a (2 * m + 3) := by
              rw [Finset.sum_range_succ]
      _ = ∑ k ∈ Finset.range (2 * m + 3), ρ ^ k * a k := by
        rw [haHigh₂, mul_zero, add_zero]
      _ = (∑ k ∈ Finset.range (2 * m + 2), ρ ^ k * a k) +
          ρ ^ (2 * m + 2) * a (2 * m + 2) := by
        rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega,
          Finset.sum_range_succ]
      _ = ∑ k ∈ Finset.range (2 * m + 2), ρ ^ k * a k := by
        rw [haHigh₁, mul_zero, add_zero]
      _ = ∑ k ∈ Finset.range ((2 * m + 1) + 1), ρ ^ k * a k := by
        rfl
  have hweightedSmall :
      noiseStability ρ hρclosed (majority (2 * m + 1)).toReal =
        ∑ k ∈ Finset.range (top + 1), ρ ^ k * a k :=
    hweightedSmallBase.trans hweightedSmallExtend.symm
  have hweightedBig :
      noiseStability ρ hρclosed (majority (2 * (m + 1) + 1)).toReal =
        ∑ k ∈ Finset.range (top + 1), ρ ^ k * b k := by
    dsimp [top, b]
    simpa only [
      show (2 * (m + 1) + 1) + 1 = (2 * m + 3) + 1 by omega] using
      noiseStability_eq_sum_level_rho_pow_mul_fourierWeight
        ρ hρclosed (majority (2 * (m + 1) + 1)).toReal
  have hlevelLe :
      ∀ {k : ℕ}, k < top → b k ≤ a k := by
    intro k hk
    dsimp [top] at hk
    dsimp [a, b]
    exact fourierWeightAtLevel_majority_next_odd_le_of_lt_top m k hk
  have htermNonneg :
      ∀ k ∈ Finset.range (top + 1),
        0 ≤ (ρ ^ k - ρ ^ top) * (a k - b k) := by
    intro k hk
    have hkTop : k ≤ top := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hktop : k = top
    · subst k
      simp
    · have hklt : k < top := lt_of_le_of_ne hkTop hktop
      exact mul_nonneg
        (sub_nonneg.mpr (pow_le_pow_of_le_one hρ.1 hρ.2.le hkTop))
        (sub_nonneg.mpr (hlevelLe hklt))
  have hweightedDiff :
      (∑ k ∈ Finset.range (top + 1), ρ ^ k * a k) -
          (∑ k ∈ Finset.range (top + 1), ρ ^ k * b k) =
        ∑ k ∈ Finset.range (top + 1),
          (ρ ^ k - ρ ^ top) * (a k - b k) := by
    calc
      (∑ k ∈ Finset.range (top + 1), ρ ^ k * a k) -
          (∑ k ∈ Finset.range (top + 1), ρ ^ k * b k) =
          ∑ k ∈ Finset.range (top + 1),
            (ρ ^ k * a k - ρ ^ k * b k) :=
        (Finset.sum_sub_distrib
          (fun k ↦ ρ ^ k * a k) (fun k ↦ ρ ^ k * b k)).symm
      _ = ∑ k ∈ Finset.range (top + 1),
          ((ρ ^ k - ρ ^ top) * (a k - b k) +
            ρ ^ top * (a k - b k)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (∑ k ∈ Finset.range (top + 1),
            (ρ ^ k - ρ ^ top) * (a k - b k)) +
          ∑ k ∈ Finset.range (top + 1), ρ ^ top * (a k - b k) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.range (top + 1),
            (ρ ^ k - ρ ^ top) * (a k - b k)) +
          ρ ^ top * ∑ k ∈ Finset.range (top + 1), (a k - b k) := by
        rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (top + 1),
          (ρ ^ k - ρ ^ top) * (a k - b k) := by
        rw [hmassDiff, mul_zero, add_zero]
  constructor
  · calc
      noiseStability ρ hρclosed
          (majority (2 * (m + 1) + 1)).toReal =
          ∑ k ∈ Finset.range (top + 1), ρ ^ k * b k :=
        hweightedBig
      _ ≤ ∑ k ∈ Finset.range (top + 1), ρ ^ k * a k := by
        have hsum :
            0 ≤ ∑ k ∈ Finset.range (top + 1),
              (ρ ^ k - ρ ^ top) * (a k - b k) :=
          Finset.sum_nonneg htermNonneg
        linarith [hweightedDiff]
      _ = noiseStability ρ hρclosed (majority (2 * m + 1)).toReal :=
        hweightedSmall.symm
  · intro hρpos
    have honeMem : 1 ∈ Finset.range (top + 1) := by
      simp [top]
    have honeTerm :
        0 < (ρ ^ 1 - ρ ^ top) * (a 1 - b 1) := by
      have honeTop : 1 < top := by
        dsimp [top]
        omega
      have hpow : 0 < ρ ^ 1 - ρ ^ top :=
        sub_pos.mpr (pow_lt_pow_right_of_lt_one₀ hρpos hρ.2 honeTop)
      have hweight : 0 < a 1 - b 1 := by
        dsimp [a, b]
        exact sub_pos.mpr
          (fourierWeightAtLevel_majority_next_odd_lt m 0 (by omega))
      exact mul_pos hpow hweight
    have hsum :
        0 < ∑ k ∈ Finset.range (top + 1),
          (ρ ^ k - ρ ^ top) * (a k - b k) :=
      Finset.sum_pos' htermNonneg ⟨1, honeMem, honeTerm⟩
    calc
      noiseStability ρ hρclosed
          (majority (2 * (m + 1) + 1)).toReal =
          ∑ k ∈ Finset.range (top + 1), ρ ^ k * b k :=
        hweightedBig
      _ < ∑ k ∈ Finset.range (top + 1), ρ ^ k * a k := by
        linarith [hweightedDiff]
      _ = noiseStability ρ hρclosed (majority (2 * m + 1)).toReal :=
        hweightedSmall.symm

/-- Exercise 5.23, adjacent-step form: odd-majority noise stability is nonincreasing
for every nonnegative correlation below one. -/
theorem noiseStability_majority_next_odd_le
    (m : ℕ) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * (m + 1) + 1)).toReal ≤
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal :=
  (noiseStability_majority_next_odd_comparison m hρ).1

/-- Exercise 5.23, strict adjacent-step form: the decrease is strict when
the correlation is strictly between zero and one. -/
theorem noiseStability_majority_next_odd_lt
    (m : ℕ) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * (m + 1) + 1)).toReal <
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal :=
  (noiseStability_majority_next_odd_comparison m ⟨hρ.1.le, hρ.2⟩).2 hρ.1

/-- Exercise 5.23: at every `ρ ∈ [0,1)`, odd-majority noise stability is
antitone in the half-arity parameter. At `ρ = 0` every term is zero. -/
theorem noiseStability_majority_odd_antitone
    (ρ : ℝ) (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    Antitone (fun m : ℕ ↦
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal) := by
  apply antitone_nat_of_succ_le
  intro m
  exact noiseStability_majority_next_odd_le m hρ

/-- Exercise 5.23, strengthened away from the endpoint: at every
`ρ ∈ (0,1)`, odd-majority noise stability is strictly antitone. -/
theorem noiseStability_majority_odd_strictAnti
    (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    StrictAnti (fun m : ℕ ↦
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal) := by
  apply strictAnti_nat_of_succ_lt
  intro m
  exact noiseStability_majority_next_odd_lt m hρ

/-- The lower bound in Theorem 5.18: finite odd majority lies above its
Gaussian arcsine limit. -/
theorem two_div_pi_mul_arcsin_le_noiseStability_majority_odd
    (m : ℕ) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    2 / Real.pi * Real.arcsin ρ ≤
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
        (majority (2 * m + 1)).toReal := by
  let hρclosed : ρ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  have hanti :
      Antitone (fun k : ℕ ↦
        noiseStability ρ hρclosed (majority (2 * k + 1)).toReal) := by
    apply antitone_nat_of_succ_le
    intro k
    exact noiseStability_majority_next_odd_le k hρ
  exact hanti.le_of_tendsto
    (tendsto_noiseStability_majority_odd ρ hρclosed) m

private theorem majority_odd_isBalanced (m : ℕ) :
    IsBalanced (majority (2 * m + 1)).toReal := by
  have hodd : Function.Odd (majority (2 * m + 1)).toReal := by
    intro x
    rw [BooleanFunction.toReal, BooleanFunction.toReal,
      majority_odd ⟨m, rfl⟩ x]
    rcases Int.units_eq_one_or (majority (2 * m + 1) x) with hx | hx <;>
      simp [hx]
  rw [IsBalanced, mean, Fintype.expect_eq_sum_div_card,
    hodd.sum_eq_zero, zero_div]

private theorem majority_eq_thresholdSign_normalizedLinearForm
    (m : ℕ) (x : {−1,1}^[2 * m + 1]) :
    majority (2 * m + 1) x =
      thresholdSign
        (linearForm
          (fun _ : Fin (2 * m + 1) ↦
            (Real.sqrt (2 * m + 1 : ℕ))⁻¹) x) := by
  have hdim : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (2 * m + 1 : ℕ) :=
    Real.sqrt_pos.2 hdim
  have hinv : 0 < (Real.sqrt (2 * m + 1 : ℕ))⁻¹ := inv_pos.mpr hsqrt
  unfold majority linearForm
  rw [← Finset.mul_sum]
  by_cases hsum : 0 ≤ ∑ i, signValue (x i)
  · rw [thresholdSign_of_nonneg hsum,
      thresholdSign_of_nonneg (mul_nonneg hinv.le hsum)]
  · have hsumNeg : (∑ i, signValue (x i)) < 0 := lt_of_not_ge hsum
    rw [thresholdSign_of_neg hsumNeg,
      thresholdSign_of_neg (mul_neg_of_pos_of_neg hinv hsumNeg)]

private theorem sum_normalizedMajorityCoefficient_sq (m : ℕ) :
    ∑ _ : Fin (2 * m + 1),
      (Real.sqrt (2 * m + 1 : ℕ))⁻¹ ^ 2 = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsqrtNe : Real.sqrt (2 * m + 1 : ℕ) ≠ 0 :=
    (Real.sqrt_ne_zero').2 (by positivity)
  rw [inv_pow]
  field_simp
  exact
    (Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ))).symm

/-- The quantitative upper bound in Theorem 5.18, obtained by specializing
the regular homogeneous-threshold invariance bound to equal majority weights. -/
theorem exists_noiseStability_majority_odd_le_arcsine_add_inv_sqrt :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1),
        noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
            (majority (2 * m + 1)).toReal ≤
          2 / Real.pi * Real.arcsin ρ +
            C /
              (Real.sqrt (1 - ρ ^ 2) *
                Real.sqrt (2 * m + 1 : ℕ)) := by
  obtain ⟨C, hC, hregularThreshold⟩ :=
    exists_noiseStability_sub_arcsine_le_of_regular_homogeneous_threshold
  refine ⟨C, hC, ?_⟩
  intro m ρ hρ
  have hdim : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hsqrtDim : 0 < Real.sqrt (2 * m + 1 : ℕ) :=
    Real.sqrt_pos.2 hdim
  have hρopen : ρ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
  have habs := hregularThreshold
    (f := majority (2 * m + 1))
    (a := fun _ : Fin (2 * m + 1) ↦
      (Real.sqrt (2 * m + 1 : ℕ))⁻¹)
    (ε := (Real.sqrt (2 * m + 1 : ℕ))⁻¹)
    (ρ := ρ)
    (majority_odd_isBalanced m)
    (majority_eq_thresholdSign_normalizedLinearForm m)
    (sum_normalizedMajorityCoefficient_sq m)
    (by
      intro i
      rw [abs_of_pos (inv_pos.mpr hsqrtDim)])
    hρopen
  have hquad : 0 < 1 - ρ ^ 2 := by
    nlinarith [mul_pos
      (show 0 < 1 + ρ by linarith [hρopen.1])
      (show 0 < 1 - ρ by linarith [hρopen.2])]
  have hsqrtQuad : 0 < Real.sqrt (1 - ρ ^ 2) :=
    Real.sqrt_pos.2 hquad
  have herror :
      C * (Real.sqrt (2 * m + 1 : ℕ))⁻¹ /
          Real.sqrt (1 - ρ ^ 2) =
        C /
          (Real.sqrt (1 - ρ ^ 2) *
            Real.sqrt (2 * m + 1 : ℕ)) := by
    field_simp [hsqrtDim.ne', hsqrtQuad.ne']
  have hdiff :
      noiseStability ρ ⟨hρopen.1.le, hρopen.2.le⟩
            (majority (2 * m + 1)).toReal -
          2 / Real.pi * Real.arcsin ρ ≤
        C /
          (Real.sqrt (1 - ρ ^ 2) *
            Real.sqrt (2 * m + 1 : ℕ)) := by
    calc
      noiseStability ρ ⟨hρopen.1.le, hρopen.2.le⟩
            (majority (2 * m + 1)).toReal -
          2 / Real.pi * Real.arcsin ρ ≤
          |noiseStability ρ ⟨hρopen.1.le, hρopen.2.le⟩
              (majority (2 * m + 1)).toReal -
            2 / Real.pi * Real.arcsin ρ| :=
        le_abs_self _
      _ ≤ C * (Real.sqrt (2 * m + 1 : ℕ))⁻¹ /
            Real.sqrt (1 - ρ ^ 2) :=
        habs
      _ = C /
            (Real.sqrt (1 - ρ ^ 2) *
              Real.sqrt (2 * m + 1 : ℕ)) :=
        herror
  linarith

/-- O'Donnell, Theorem 5.18 and Exercise 5.23. The endpoint `ρ = 0`
is non-strict: all odd-majority stabilities there equal zero. -/
theorem exists_majorityNoiseStability_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : ℝ) (hρ : ρ ∈ Ico (0 : ℝ) 1),
        Antitone (fun m : ℕ ↦
          noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
            (majority (2 * m + 1)).toReal) ∧
        ∀ m : ℕ,
          2 / Real.pi * Real.arcsin ρ ≤
              noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
                (majority (2 * m + 1)).toReal ∧
            noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩
                (majority (2 * m + 1)).toReal ≤
              2 / Real.pi * Real.arcsin ρ +
                C /
                  (Real.sqrt (1 - ρ ^ 2) *
                    Real.sqrt (2 * m + 1 : ℕ)) := by
  obtain ⟨C, hC, hupper⟩ :=
    exists_noiseStability_majority_odd_le_arcsine_add_inv_sqrt
  refine ⟨C, hC, ?_⟩
  intro ρ hρ
  refine ⟨noiseStability_majority_odd_antitone ρ hρ, ?_⟩
  intro m
  exact
    ⟨two_div_pi_mul_arcsin_le_noiseStability_majority_odd m hρ,
      hupper m hρ⟩

end FABL
