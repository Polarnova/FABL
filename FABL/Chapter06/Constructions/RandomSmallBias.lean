/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.FourierEstimation
public import FABL.Chapter05.RandomBooleanFourierMaximum
public import FABL.Chapter06.Constructions.SmallBiasGenerator

/-!
# Random small-bias multisets

Book item: Exercise 6.24.

A uniformly sampled multiset of `ceil (8n / ε²)` points is `ε`-biased except with
probability at most `2⁻ⁿ`.  The zero-dimensional case has an empty sample and hence no
normalized empirical density; its character condition is vacuous.  In positive dimension the
sample predicate is exactly `ProbabilityDensity.IsBiased` for the uniform empirical density.
-/

open Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal

set_option autoImplicit false

@[expose] public section

namespace FABL

/-- The explicit universal constant used in Exercise 6.24. -/
def randomSmallBiasConstant : ℕ := 8

/-- The number of independent uniform points drawn in Exercise 6.24. -/
noncomputable def randomSmallBiasSampleCount (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈(randomSmallBiasConstant : ℝ) * (n : ℝ) / ε ^ 2⌉₊

/-- Positive dimension and positive accuracy give a nonempty sample. -/
theorem randomSmallBiasSampleCount_pos
    {n : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε) :
    0 < randomSmallBiasSampleCount n ε := by
  rw [randomSmallBiasSampleCount, Nat.ceil_pos]
  exact div_pos
    (mul_pos (by norm_num [randomSmallBiasConstant]) (Nat.cast_pos.mpr hn))
    (sq_pos_of_pos hε)

/-- In dimension zero, Exercise 6.24 draws the empty multiset. -/
@[simp] theorem randomSmallBiasSampleCount_zero (ε : ℝ) :
    randomSmallBiasSampleCount 0 ε = 0 := by
  simp [randomSmallBiasSampleCount]

/-- The multiset represented by an indexed sample, retaining repeated points. -/
def randomSmallBiasMultiset {n m : ℕ}
    (samples : Fin m → F₂Cube n) : Multiset (F₂Cube n) :=
  (Finset.univ : Finset (Fin m)).1.map samples

/-- The indexed sample and its multiset representation have the same cardinality. -/
@[simp] theorem randomSmallBiasMultiset_card
    {n m : ℕ} (samples : Fin m → F₂Cube n) :
    (randomSmallBiasMultiset samples).card = m := by
  simp [randomSmallBiasMultiset]

/-- The direct character condition for a finite indexed sample.  This remains meaningful for the
empty zero-dimensional multiset, where there are no nonzero frequencies. -/
def IsSmallBiasedSample {n m : ℕ}
    (samples : Fin m → F₂Cube n) (ε : ℝ) : Prop :=
  ∀ γ : F₂Cube n, γ ≠ 0 →
    |finiteUniformEmpiricalMean (vectorWalshCharacter γ) samples| ≤ ε

/-- Every zero-dimensional sample satisfies the character condition, including the empty one. -/
theorem isSmallBiasedSample_zero
    {m : ℕ} (samples : Fin m → F₂Cube 0) (ε : ℝ) :
    IsSmallBiasedSample samples ε := by
  intro γ hγ
  exact (hγ (Subsingleton.elim γ 0)).elim

/-- The probability density obtained by choosing an index of a nonempty sample uniformly. -/
noncomputable def randomSmallBiasDensity
    {n m : ℕ} (hm : 0 < m) (samples : Fin m → F₂Cube n) :
    ProbabilityDensity n :=
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  ProbabilityDensity.uniformPushforward samples

/-- A coefficient of the empirical density is the corresponding empirical character mean. -/
theorem vectorFourierCoeff_randomSmallBiasDensity
    {n m : ℕ} (hm : 0 < m) (samples : Fin m → F₂Cube n)
    (γ : F₂Cube n) :
    vectorFourierCoeff (randomSmallBiasDensity hm samples) γ =
      finiteUniformEmpiricalMean (vectorWalshCharacter γ) samples := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  rw [vectorFourierCoeff_eq_expect]
  change
    (ProbabilityDensity.uniformPushforward samples).expectation
        (vectorWalshCharacter γ) = _
  rw [ProbabilityDensity.expectation_uniformPushforward,
    Fintype.expect_eq_sum_div_card]
  simp [finiteUniformEmpiricalMean]

/-- For a nonempty sample, the direct character condition is exactly density small bias. -/
theorem randomSmallBiasDensity_isBiased_iff
    {n m : ℕ} (hm : 0 < m) (samples : Fin m → F₂Cube n) (ε : ℝ) :
    (randomSmallBiasDensity hm samples).IsBiased ε ↔
      IsSmallBiasedSample samples ε := by
  unfold ProbabilityDensity.IsBiased IsSmallBiasedSample
  simp_rw [vectorFourierCoeff_randomSmallBiasDensity hm samples]

/-- The bad event for one frequency.  Including `γ ≠ 0` makes the union range over the
whole dual cube without changing the mathematical event. -/
def randomSmallBiasFrequencyBadSet
    (n : ℕ) (ε : ℝ) (γ : F₂Cube n) :
    Set (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n) :=
  {samples |
    γ ≠ 0 ∧
      ε ≤ |finiteUniformEmpiricalMean (vectorWalshCharacter γ) samples|}

/-- The failure event for the direct finite-sample bias condition. -/
def randomSmallBiasFailureSet (n : ℕ) (ε : ℝ) :
    Set (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n) :=
  {samples | ¬ IsSmallBiasedSample samples ε}

/-- The Hoeffding bound for one nonzero frequency, strengthened using the prescribed sample
count. -/
theorem measure_randomSmallBiasFrequencyBadSet_le
    {n : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε)
    (γ : F₂Cube n) :
    (uniformPMF
      (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
        (randomSmallBiasFrequencyBadSet n ε γ) ≤
      2 * Real.exp (-(4 * (n : ℝ))) := by
  by_cases hγ : γ = 0
  · subst γ
    have hset : randomSmallBiasFrequencyBadSet n ε 0 = ∅ := by
      ext samples
      simp [randomSmallBiasFrequencyBadSet]
    simp [hset, (Real.exp_pos _).le]
  · have hm : 0 < randomSmallBiasSampleCount n ε :=
      randomSmallBiasSampleCount_pos hn hε
    have hHoeffding :=
      measure_finiteUniformEmpiricalMean_sub_expect_ge_le
        (observation := vectorWalshCharacter γ)
        (fun x ↦ by
          rcases vectorWalshCharacter_eq_neg_one_or_one γ x with hx | hx
          · simp [hx]
          · simp [hx])
        hm ε hε.le
    rw [expect_vectorWalshCharacter, if_neg hγ] at hHoeffding
    have hbad :
        (uniformPMF
          (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
            (randomSmallBiasFrequencyBadSet n ε γ) ≤
          2 * Real.exp
            (-(randomSmallBiasSampleCount n ε : ℝ) * ε ^ 2 / 2) := by
      simpa [randomSmallBiasFrequencyBadSet, hγ] using hHoeffding
    have hceil :
        (randomSmallBiasConstant : ℝ) * (n : ℝ) / ε ^ 2 ≤
          (randomSmallBiasSampleCount n ε : ℝ) := by
      exact Nat.le_ceil _
    have hmass :
        (randomSmallBiasConstant : ℝ) * (n : ℝ) ≤
          (randomSmallBiasSampleCount n ε : ℝ) * ε ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hε)).1 hceil
    have hexponent :
        -(randomSmallBiasSampleCount n ε : ℝ) * ε ^ 2 / 2 ≤
          -(4 * (n : ℝ)) := by
      norm_num [randomSmallBiasConstant] at hmass
      linarith
    exact hbad.trans <|
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) (by norm_num)

/-- The numerical union-bound estimate used for all positive dimensions. -/
private theorem two_pow_mul_two_exp_neg_four_mul_le_rpow_neg
    {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n * (2 * Real.exp (-(4 * (n : ℝ)))) ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  by_cases hnOne : n = 1
  · subst n
    have hexp : (8 : ℝ) ≤ Real.exp 4 := by
      calc
        (8 : ℝ) ≤ 16 := by norm_num
        _ = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 :=
          (pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)).le
        _ = Real.exp 4 := by
          rw [← Real.exp_nat_mul]
          norm_num
    calc
      (2 : ℝ) ^ (1 : ℕ) * (2 * Real.exp (-(4 * ((1 : ℕ) : ℝ)))) =
          4 / Real.exp 4 := by
        rw [Real.exp_neg]
        norm_num
        ring
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ (Real.exp_pos 4)).2
        nlinarith
      _ = (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  · have hnTwo : 2 ≤ n := by omega
    have hexp :
        Real.exp (-(4 * (n : ℝ))) ≤
          Real.exp (-(2 * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    calc
      (2 : ℝ) ^ n * (2 * Real.exp (-(4 * (n : ℝ)))) ≤
          (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) := by
        gcongr
      _ ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
        two_pow_mul_two_exp_neg_two_mul_le_rpow_neg hnTwo

/-- O'Donnell, Exercise 6.24: for all dimensions, including `n = 0`, the random indexed
multiset fails the direct `ε`-bias condition with probability at most `2⁻ⁿ`. -/
theorem measure_randomSmallBiasSample_not_isBiased_le
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) (_hε_one : ε < 1) :
    (uniformPMF
      (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
        (randomSmallBiasFailureSet n ε) ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    have hfailure : randomSmallBiasFailureSet 0 ε = ∅ := by
      ext samples
      simp [randomSmallBiasFailureSet, isSmallBiasedSample_zero]
    rw [hfailure]
    norm_num
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hsubset :
        randomSmallBiasFailureSet n ε ⊆
          ⋃ γ : F₂Cube n, randomSmallBiasFrequencyBadSet n ε γ := by
      intro samples hsamples
      rw [randomSmallBiasFailureSet] at hsamples
      simp only [Set.mem_setOf_eq] at hsamples
      unfold IsSmallBiasedSample at hsamples
      push Not at hsamples
      obtain ⟨γ, hγ, hbad⟩ := hsamples
      refine Set.mem_iUnion.2 ⟨γ, ?_⟩
      simpa [randomSmallBiasFrequencyBadSet] using And.intro hγ hbad.le
    calc
      (uniformPMF
        (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
          (randomSmallBiasFailureSet n ε) ≤
          (uniformPMF
            (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
            (⋃ γ : F₂Cube n, randomSmallBiasFrequencyBadSet n ε γ) :=
        measureReal_mono hsubset
      _ ≤ ∑ γ : F₂Cube n,
          (uniformPMF
            (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
              (randomSmallBiasFrequencyBadSet n ε γ) :=
        MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _γ : F₂Cube n, 2 * Real.exp (-(4 * (n : ℝ))) := by
        apply Finset.sum_le_sum
        intro γ _
        exact measure_randomSmallBiasFrequencyBadSet_le hnPos hε γ
      _ = (Fintype.card (F₂Cube n) : ℝ) *
          (2 * Real.exp (-(4 * (n : ℝ)))) := by
        simp [nsmul_eq_mul]
      _ = (2 : ℝ) ^ n * (2 * Real.exp (-(4 * (n : ℝ)))) := by
        have hcard : Fintype.card (F₂Cube n) = 2 ^ n := by simp
        rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
        two_pow_mul_two_exp_neg_four_mul_le_rpow_neg
          (Nat.one_le_iff_ne_zero.mpr hn)

/-- The positive-dimensional density form of Exercise 6.24, with the exact
`ProbabilityDensity.IsBiased ε` conclusion. -/
theorem measure_randomSmallBiasDensity_not_isBiased_le
    (n : ℕ) {ε : ℝ} (hn : 0 < n) (hε : 0 < ε) (hε_one : ε < 1) :
    (uniformPMF
      (Fin (randomSmallBiasSampleCount n ε) → F₂Cube n)).toMeasure.real
        {samples |
          ¬ (randomSmallBiasDensity
            (randomSmallBiasSampleCount_pos hn hε) samples).IsBiased ε} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  have hset :
      {samples : Fin (randomSmallBiasSampleCount n ε) → F₂Cube n |
        ¬ (randomSmallBiasDensity
          (randomSmallBiasSampleCount_pos hn hε) samples).IsBiased ε} =
        randomSmallBiasFailureSet n ε := by
    ext samples
    simp only [Set.mem_setOf_eq, randomSmallBiasFailureSet,
      randomSmallBiasDensity_isBiased_iff]
  rw [hset]
  exact measure_randomSmallBiasSample_not_isBiased_le n hε hε_one

end FABL
