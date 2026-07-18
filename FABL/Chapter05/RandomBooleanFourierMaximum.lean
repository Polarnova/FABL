/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.FourierEstimation

/-!
# Fourier maximum of a random Boolean function

Book item: Exercise 5.8.
-/

open Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance randomBooleanSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance randomBooleanSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The endpoint norm of the subset-indexed Fourier coefficients on the sign cube. -/
noncomputable def fourierInfinityNorm (f : {−1,1}^[n] → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun S ↦ |fourierCoeff f S|

/-- The threshold in Exercise 5.8. -/
noncomputable def randomBooleanFourierThreshold (n : ℕ) : ℝ :=
  2 * Real.sqrt n * (2 : ℝ) ^ (-(n : ℝ) / 2)

private def paritySign (S : Finset (Fin n)) (x : {−1,1}^[n]) : Sign :=
  ∏ i ∈ S, x i

private theorem signValue_paritySign
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    signValue (paritySign S x) = monomial S x := by
  simp [paritySign, monomial, signValue]

private theorem signValue_mul (a b : Sign) :
    signValue (a * b) = signValue a * signValue b := by
  simp [signValue]

private noncomputable def randomBooleanCoefficientSampleEquiv
    (n : ℕ) (S : Finset (Fin n)) :
    BooleanFunction n ≃
      (Fin (Fintype.card ({−1,1}^[n])) → Sign) :=
  (Equiv.arrowCongr
      (Fintype.equivFin ({−1,1}^[n])) (Equiv.refl Sign)).trans
    (Equiv.mulRight fun i ↦
      paritySign S ((Fintype.equivFin ({−1,1}^[n])).symm i))

private theorem finiteUniformEmpiricalMean_randomBooleanCoefficientSampleEquiv
    (S : Finset (Fin n)) (f : BooleanFunction n) :
    finiteUniformEmpiricalMean signValue
        (randomBooleanCoefficientSampleEquiv n S f) =
      fourierCoeff f.toReal S := by
  classical
  rw [fourierCoeff, Fintype.expect_eq_sum_div_card]
  unfold finiteUniformEmpiricalMean
  congr 1
  symm
  apply Fintype.sum_equiv (Fintype.equivFin ({−1,1}^[n]))
  intro x
  simp [randomBooleanCoefficientSampleEquiv, Equiv.arrowCongr,
    BooleanFunction.toReal, signValue_mul, signValue_paritySign]

private theorem expect_signValue_eq_zero :
    (𝔼 s : Sign, signValue s) = 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [Sign, signValue]

private theorem signValue_mem_Icc (s : Sign) :
    signValue s ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

private theorem measure_randomBooleanFunction_fourierCoeff_ge_le
    (S : Finset (Fin n)) (ε : ℝ) (hε : 0 ≤ ε) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ε ≤ |fourierCoeff f.toReal S|} ≤
      2 * Real.exp
        (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2) := by
  classical
  let m := Fintype.card ({−1,1}^[n])
  let e := randomBooleanCoefficientSampleEquiv n S
  let failure : Set (Fin m → Sign) :=
    {samples | ε ≤ |finiteUniformEmpiricalMean signValue samples|}
  have h :=
    measure_finiteUniformEmpiricalMean_sub_expect_ge_le
      signValue signValue_mem_Icc (m := m) Fintype.card_pos ε hε
  rw [expect_signValue_eq_zero] at h
  simp only [sub_zero] at h
  change (uniformPMF (Fin m → Sign)).toMeasure.real failure ≤ _ at h
  have hmap :
      (uniformPMF (BooleanFunction n)).map e =
        uniformPMF (Fin m → Sign) :=
    map_uniformPMF_equiv e
  rw [← hmap] at h
  have hmeasure :
      ((uniformPMF (BooleanFunction n)).map e).toMeasure.real failure =
        (uniformPMF (BooleanFunction n)).toMeasure.real (e ⁻¹' failure) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply e _ failure (measurable_of_finite e)
        (Set.toFinite failure).measurableSet)
  rw [hmeasure] at h
  simpa [m, e, failure,
    finiteUniformEmpiricalMean_randomBooleanCoefficientSampleEquiv] using h

private theorem randomBooleanFourierThreshold_nonneg (n : ℕ) :
    0 ≤ randomBooleanFourierThreshold n := by
  unfold randomBooleanFourierThreshold
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (by norm_num) _)

private theorem card_mul_randomBooleanFourierThreshold_sq_div_two
    (n : ℕ) :
    (Fintype.card ({−1,1}^[n]) : ℝ) *
        randomBooleanFourierThreshold n ^ 2 / 2 =
      2 * (n : ℝ) := by
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, Sign]
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hrpow :
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
    calc
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 =
          (2 : ℝ) ^ ((-(n : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (x := (2 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 2) (-(n : ℝ) / 2) 2).symm
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        congr 1
        norm_num
      _ = ((2 : ℝ) ^ n)⁻¹ := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_neg (x := (2 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ))
  rw [hcard, randomBooleanFourierThreshold, mul_pow, mul_pow, hsqrt, hrpow]
  field_simp

private theorem measure_randomBooleanFunction_fourierCoeff_atThreshold_ge_le
    (S : Finset (Fin n)) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f |
          randomBooleanFourierThreshold n ≤
            |fourierCoeff f.toReal S|} ≤
      2 * Real.exp (-(2 * (n : ℝ))) := by
  have h :=
    measure_randomBooleanFunction_fourierCoeff_ge_le
      S (randomBooleanFourierThreshold n)
        (randomBooleanFourierThreshold_nonneg n)
  have hexponent :
      -(Fintype.card ({−1,1}^[n]) : ℝ) *
          randomBooleanFourierThreshold n ^ 2 / 2 =
        -(2 * (n : ℝ)) := by
    rw [show
      -(Fintype.card ({−1,1}^[n]) : ℝ) *
            randomBooleanFourierThreshold n ^ 2 / 2 =
          -((Fintype.card ({−1,1}^[n]) : ℝ) *
            randomBooleanFourierThreshold n ^ 2 / 2) by ring,
      card_mul_randomBooleanFourierThreshold_sq_div_two]
  rw [hexponent] at h
  exact h

private theorem randomBooleanFourierMaximumBad_subset (n : ℕ) :
    {f : BooleanFunction n |
        randomBooleanFourierThreshold n < fourierInfinityNorm f.toReal} ⊆
      ⋃ S : Finset (Fin n),
        {f : BooleanFunction n |
          randomBooleanFourierThreshold n ≤ |fourierCoeff f.toReal S|} := by
  intro f hf
  change randomBooleanFourierThreshold n <
    Finset.univ.sup' Finset.univ_nonempty
      (fun S : Finset (Fin n) ↦ |fourierCoeff f.toReal S|) at hf
  rw [Finset.lt_sup'_iff] at hf
  obtain ⟨S, _, hS⟩ := hf
  exact Set.mem_iUnion.2 ⟨S, hS.le⟩

private theorem two_pow_two_mul_add_one_lt_exp_two_mul
    {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ (2 * n + 1) < Real.exp (2 * (n : ℝ)) := by
  have hExpTwo : (4 : ℝ) < Real.exp 2 := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 :=
        pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
      _ = Real.exp 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hExpFour : (32 : ℝ) < Real.exp 4 := by
    have hbase : (8 / 3 : ℝ) < Real.exp 1 :=
      (by norm_num : (8 / 3 : ℝ) < 2.7182818283).trans
        Real.exp_one_gt_d9
    calc
      (32 : ℝ) < (8 / 3 : ℝ) ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 :=
        pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)
      _ = Real.exp 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc
    (2 : ℝ) ^ (2 * (2 + k) + 1) = 32 * (4 : ℝ) ^ k := by
      rw [show 2 * (2 + k) + 1 = 5 + 2 * k by omega, pow_add, pow_mul]
      norm_num
    _ < Real.exp 4 * (4 : ℝ) ^ k :=
      mul_lt_mul_of_pos_right hExpFour (by positivity)
    _ ≤ Real.exp 4 * Real.exp 2 ^ k :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hExpTwo.le k)
        (Real.exp_pos _).le
    _ = Real.exp (2 * ((2 + k : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

private theorem two_pow_mul_two_exp_neg_two_mul_le_rpow_neg
    {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  have hpow :=
    (two_pow_two_mul_add_one_lt_exp_two_mul hn).le
  calc
    (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) =
        (2 : ℝ) ^ (n + 1) / Real.exp (2 * (n : ℝ)) := by
      rw [Real.exp_neg, div_eq_mul_inv, pow_succ]
      ring
    _ ≤ 1 / (2 : ℝ) ^ n := by
      apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos (by norm_num) _)).2
      rw [one_mul]
      calc
        (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n =
            (2 : ℝ) ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ Real.exp (2 * (n : ℝ)) := hpow
    _ = (2 : ℝ) ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_natCast]
      simp [one_div]

/-- O'Donnell, Exercise 5.8: except with probability at most `2⁻ⁿ`, every Fourier coefficient
of a uniformly random Boolean function has magnitude at most
`2 √n · 2⁻ⁿᐟ²`. -/
theorem measure_randomBooleanFunction_fourierInfinityNorm_gt_le
    (n : ℕ) (hn : 2 ≤ n) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f |
          randomBooleanFourierThreshold n <
            fourierInfinityNorm f.toReal} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  have hcard :
      (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_finset]
  calc
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f |
          randomBooleanFourierThreshold n <
            fourierInfinityNorm f.toReal} ≤
        (uniformPMF (BooleanFunction n)).toMeasure.real
          (⋃ S : Finset (Fin n),
            {f : BooleanFunction n |
              randomBooleanFourierThreshold n ≤
                |fourierCoeff f.toReal S|}) :=
      measureReal_mono (randomBooleanFourierMaximumBad_subset n)
    _ ≤ ∑ S : Finset (Fin n),
        (uniformPMF (BooleanFunction n)).toMeasure.real
          {f : BooleanFunction n |
            randomBooleanFourierThreshold n ≤
              |fourierCoeff f.toReal S|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : Finset (Fin n),
        2 * Real.exp (-(2 * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_randomBooleanFunction_fourierCoeff_atThreshold_ge_le S
    _ = (Fintype.card (Finset (Fin n)) : ℝ) *
        (2 * Real.exp (-(2 * (n : ℝ)))) := by
      simp [nsmul_eq_mul]
    _ = (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) := by
      rw [hcard]
    _ ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
      two_pow_mul_two_exp_neg_two_mul_le_rpow_neg hn

end FABL
