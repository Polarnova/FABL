/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/

import FABL.Chapter05.RademacherFirstMoment

/-!
# The Level-1 inequality

Book items: Lemma 5.31 and the Level-1 Inequality.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal Topology

namespace FABL

variable {n : ℕ}

local instance levelOneSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance levelOneSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

private theorem uniformRademacher_abs_linearForm_gt_le
    (a : Fin n → ℝ)
    (hnormalized : ∑ i, a i ^ 2 = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (uniformPMF {−1,1}^[n]).toMeasure.real
        {x | t < |linearForm a x|} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hcoefficient (i : Fin n) : |a i| ≤ (1 : ℝ) := by
    have hi : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (a j)) (Finset.mem_univ i)
    rw [hnormalized, ← sq_abs] at hi
    nlinarith [abs_nonneg (a i)]
  have htail :=
    (exercise5_31a a (ε := 1) hnormalized hcoefficient ht).1
  change
    (uniformPMF {−1,1}^[n]).toMeasure.real
        {x | t ≤ |linearForm a x|} ≤
      2 * Real.exp (-t ^ 2 / 2) at htail
  exact
    (measureReal_mono (fun x hx ↦ by
      change t < |linearForm a x| at hx
      change t ≤ |linearForm a x|
      exact hx.le) (by finiteness)).trans htail

private theorem excess_abs_linearForm_expect_le
    (a : Fin n → ℝ)
    (hnormalized : ∑ i, a i ^ 2 = 1)
    {s : ℝ} (hs : 1 ≤ s) :
    (𝔼 x : {−1,1}^[n], (|linearForm a x| - s)⁺) ≤
      2 * Real.exp (-s ^ 2 / 2) := by
  let excess : {−1,1}^[n] → ℝ :=
    fun x ↦ (|linearForm a x| - s)⁺
  have hexcessIntegrable :
      Integrable excess (uniformPMF {−1,1}^[n]).toMeasure :=
    Integrable.of_finite
  have hlayerCake :
      (∫ x, excess x ∂(uniformPMF {−1,1}^[n]).toMeasure) =
        ∫ t in Ioi 0,
          (uniformPMF {−1,1}^[n]).toMeasure.real
            {x | t < excess x} :=
    hexcessIntegrable.integral_eq_integral_meas_lt
      (ae_of_all _ fun x ↦ posPart_nonneg (|linearForm a x| - s))
  let bound : ℝ → ℝ :=
    fun t ↦ 2 * Real.exp (-s ^ 2 / 2) * Real.exp (-t)
  have hboundIntegrable : IntegrableOn bound (Ioi 0) := by
    change Integrable bound (volume.restrict (Ioi 0))
    simpa only [bound] using
      (integrableOn_exp_neg_Ioi 0).const_mul
        (2 * Real.exp (-s ^ 2 / 2))
  have htail (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | t < excess x} ≤
        bound t := by
    change 0 < t at ht
    have hset :
        {x : {−1,1}^[n] | t < excess x} ⊆
          {x | s + t < |linearForm a x|} := by
      intro x hx
      change t < (|linearForm a x| - s)⁺ at hx
      change s + t < |linearForm a x|
      by_cases hsub : 0 ≤ |linearForm a x| - s
      · rw [posPart_eq_self.mpr hsub] at hx
        linarith
      · rw [posPart_eq_zero.mpr (le_of_not_ge hsub)] at hx
        linarith
    have htail' :
        (uniformPMF {−1,1}^[n]).toMeasure.real
            {x | s + t < |linearForm a x|} ≤
          2 * Real.exp (-(s + t) ^ 2 / 2) :=
      uniformRademacher_abs_linearForm_gt_le
        a hnormalized (by linarith)
    have hst : 0 ≤ (s - 1) * t :=
      mul_nonneg (sub_nonneg.mpr hs) ht.le
    have hexponent :
        -(s + t) ^ 2 / 2 ≤ -s ^ 2 / 2 - t := by
      nlinarith [sq_nonneg t]
    calc
      (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | t < excess x} ≤
          (uniformPMF {−1,1}^[n]).toMeasure.real
            {x | s + t < |linearForm a x|} :=
        measureReal_mono hset (by finiteness)
      _ ≤ 2 * Real.exp (-(s + t) ^ 2 / 2) := htail'
      _ ≤ 2 * Real.exp (-s ^ 2 / 2 - t) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexponent) (by norm_num)
      _ = bound t := by
        rw [show -s ^ 2 / 2 - t = -s ^ 2 / 2 + -t by ring,
          Real.exp_add]
        simp only [bound]
        ring
  have hintegral :
      (∫ t in Ioi 0,
        (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | t < excess x}) ≤
        2 * Real.exp (-s ^ 2 / 2) := by
    calc
      (∫ t in Ioi 0,
          (uniformPMF {−1,1}^[n]).toMeasure.real
            {x | t < excess x}) ≤
          ∫ t in Ioi 0, bound t := by
        apply setIntegral_mono_of_nonneg
        · intro t _
          exact measureReal_nonneg
        · exact htail
        · exact hboundIntegrable
      _ = 2 * Real.exp (-s ^ 2 / 2) := by
        rw [show bound =
            fun t ↦ (2 * Real.exp (-s ^ 2 / 2)) * Real.exp (-t) by rfl,
          integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [← integral_uniformPMF_eq_expect] at *
  exact hlayerCake.trans_le hintegral

/-- O'Donnell, Lemma 5.31: the absolute first moment of the part of a normalized
Rademacher linear form above `s ≥ 1` has the stated subgaussian bound. -/
theorem expect_abs_linearForm_indicator_gt_le
    (a : Fin n → ℝ)
    (hnormalized : ∑ i, a i ^ 2 = 1)
    {s : ℝ} (hs : 1 ≤ s) :
    (𝔼 x : {−1,1}^[n],
      if s < |linearForm a x| then |linearForm a x| else 0) ≤
      (2 * s + 2) * Real.exp (-s ^ 2 / 2) := by
  let excess : {−1,1}^[n] → ℝ :=
    fun x ↦ (|linearForm a x| - s)⁺
  have hdecomposition (x : {−1,1}^[n]) :
      (if s < |linearForm a x| then |linearForm a x| else 0) =
        s * (if s < |linearForm a x| then 1 else 0) + excess x := by
    by_cases hx : s < |linearForm a x|
    · rw [if_pos hx, if_pos hx]
      simp only [excess, posPart_eq_self.mpr (sub_nonneg.mpr hx.le)]
      ring
    · rw [if_neg hx, if_neg hx]
      simp only [excess, posPart_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hx))]
      ring
  have hindicator :
      (𝔼 x : {−1,1}^[n],
        if s < |linearForm a x| then (1 : ℝ) else 0) =
        (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | s < |linearForm a x|} := by
    rw [← integral_uniformPMF_eq_expect]
    rw [← integral_indicator_one
      (Set.toFinite {x : {−1,1}^[n] |
        s < |linearForm a x|}).measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      by_cases hx : s < |linearForm a x| <;>
        simp [Set.indicator, hx]
  have htail :
      (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | s < |linearForm a x|} ≤
        2 * Real.exp (-s ^ 2 / 2) :=
    uniformRademacher_abs_linearForm_gt_le
      a hnormalized (zero_le_one.trans hs)
  have hexcess :
      (𝔼 x : {−1,1}^[n], excess x) ≤
        2 * Real.exp (-s ^ 2 / 2) := by
    simpa only [excess] using
      excess_abs_linearForm_expect_le a hnormalized hs
  calc
    (𝔼 x : {−1,1}^[n],
        if s < |linearForm a x| then |linearForm a x| else 0) =
        𝔼 x : {−1,1}^[n], (
          s * (if s < |linearForm a x| then 1 else 0) +
            excess x) := by
      apply Finset.expect_congr rfl
      intro x _
      exact hdecomposition x
    _ = s * (𝔼 x : {−1,1}^[n],
          if s < |linearForm a x| then 1 else 0) +
        𝔼 x : {−1,1}^[n], excess x := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ = s *
          (uniformPMF {−1,1}^[n]).toMeasure.real
            {x | s < |linearForm a x|} +
        𝔼 x : {−1,1}^[n], excess x := by
      rw [hindicator]
    _ ≤ s * (2 * Real.exp (-s ^ 2 / 2)) +
        2 * Real.exp (-s ^ 2 / 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left htail (zero_le_one.trans hs))
        hexcess
    _ = (2 * s + 2) * Real.exp (-s ^ 2 / 2) := by ring

private theorem expect_mul_levelOneLinearForm_eq
    (f : {−1,1}^[n] → ℝ) (a : Fin n → ℝ) :
    (𝔼 x, f x * linearForm a x) =
      ∑ i, a i * fourierCoeff f {i} := by
  rw [show
      (fun x : {−1,1}^[n] ↦ f x * linearForm a x) =
        fun x ↦ ∑ i, a i * (f x * monomial {i} x) by
    funext x
    rw [linearForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [monomial]
    ring]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_expect]
  rfl

/-- The zero-density case of the Level-1 Inequality: a `{0,1}`-valued
function of uniform mean zero has no level-one Fourier weight. -/
theorem fourierWeightAtLevel_one_eq_zero_of_zero_one_mean_eq_zero
    (f : {−1,1}^[n] → ℝ)
    (hvalues : ∀ x, f x = 0 ∨ f x = 1)
    (hmean : mean f = 0) :
    fourierWeightAtLevel 1 f = 0 := by
  have hfnonneg : 0 ≤ f := by
    intro x
    rcases hvalues x with hx | hx <;> simp [hx]
  have hfzero : f = 0 := by
    apply (Fintype.expect_eq_zero_iff_of_nonneg hfnonneg).mp
    simpa only [mean] using hmean
  rw [hfzero, fourierWeightAtLevel_one_eq_sum_singleton]
  simp [fourierCoeff]

/-- O'Donnell's Level-1 Inequality: the level-one Fourier weight of a
`{0,1}`-valued function of density `0 < α ≤ 1/2` is at most a universal
constant times `α² log₂(1/α)`. -/
theorem exists_levelOneInequality_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : {−1,1}^[n] → ℝ) {α : ℝ},
        (∀ x, f x = 0 ∨ f x = 1) →
        mean f = α →
        0 < α →
        α ≤ 1 / 2 →
          fourierWeightAtLevel 1 f ≤
            C * α ^ 2 * Real.logb 2 (1 / α) := by
  refine ⟨50, by norm_num, ?_⟩
  intro n f α hvalues hmean hα hαhalf
  change (𝔼 x, f x) = α at hmean
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f {i}
  let W : ℝ := fourierWeightAtLevel 1 f
  let L : ℝ := Real.log (1 / α)
  let s : ℝ := Real.sqrt (2 * L)
  have haSum : ∑ i, a i ^ 2 = W := by
    dsimp only [a, W]
    exact (fourierWeightAtLevel_one_eq_sum_singleton f).symm
  have hWnonneg : 0 ≤ W := by
    rw [← haSum]
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (a i)
  have hinvLower : (2 : ℝ) ≤ 1 / α := by
    apply (le_div_iff₀ hα).2
    nlinarith
  have hlogTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hlogLower : Real.log 2 ≤ L := by
    dsimp only [L]
    exact Real.log_le_log (by norm_num) hinvLower
  have hLnonneg : 0 ≤ L :=
    hlogTwoPos.le.trans hlogLower
  have hlogTwoLower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    norm_num at h
    linarith
  have hs : 1 ≤ s := by
    dsimp only [s]
    rw [Real.one_le_sqrt]
    nlinarith
  have hsSq : s ^ 2 = 2 * L := by
    dsimp only [s]
    rw [Real.sq_sqrt]
    nlinarith
  have htail : Real.exp (-s ^ 2 / 2) = α := by
    rw [hsSq]
    have hexpLog : Real.exp L = 1 / α := by
      dsimp only [L]
      rw [Real.exp_log (div_pos zero_lt_one hα)]
    calc
      Real.exp (-(2 * L) / 2) = Real.exp (-L) := by ring_nf
      _ = (Real.exp L)⁻¹ := Real.exp_neg L
      _ = (1 / α)⁻¹ := by rw [hexpLog]
      _ = α := by
        rw [one_div, inv_inv]
  have hlogbNonneg : 0 ≤ Real.logb 2 (1 / α) := by
    change 0 ≤ L / Real.log 2
    exact div_nonneg hLnonneg hlogTwoPos.le
  have hlogTwoLeOne : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hLLeLogb : L ≤ Real.logb 2 (1 / α) := by
    change L ≤ L / Real.log 2
    apply (le_div_iff₀ hlogTwoPos).2
    have hproduct : 0 ≤ L * (1 - Real.log 2) :=
      mul_nonneg hLnonneg (sub_nonneg.mpr hlogTwoLeOne)
    nlinarith
  have hrightNonneg :
      0 ≤ (50 : ℝ) * α ^ 2 * Real.logb 2 (1 / α) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hlogbNonneg
  by_cases hWzero : W = 0
  · change W ≤ (50 : ℝ) * α ^ 2 * Real.logb 2 (1 / α)
    rw [hWzero]
    exact hrightNonneg
  · have hWpos : 0 < W :=
      lt_of_le_of_ne hWnonneg (Ne.symm hWzero)
    let σ : ℝ := Real.sqrt W
    let b : Fin n → ℝ := fun i ↦ a i / σ
    have hσnonneg : 0 ≤ σ := Real.sqrt_nonneg W
    have hσpos : 0 < σ := Real.sqrt_pos.2 hWpos
    have hσSq : σ ^ 2 = W :=
      Real.sq_sqrt hWnonneg
    have hbNormalized : ∑ i, b i ^ 2 = 1 := by
      calc
        (∑ i, b i ^ 2) = (∑ i, a i ^ 2) / σ ^ 2 := by
          simp_rw [b, div_pow]
          exact
            (Finset.sum_div Finset.univ (fun i ↦ a i ^ 2) (σ ^ 2)).symm
        _ = W / σ ^ 2 := by rw [haSum]
        _ = 1 := by
          rw [hσSq, div_self hWzero]
    have hinner :
        (𝔼 x : {−1,1}^[n], f x * linearForm b x) = σ := by
      rw [expect_mul_levelOneLinearForm_eq]
      calc
        (∑ i, b i * fourierCoeff f {i}) =
            (∑ i, a i ^ 2) / σ := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [a, b]
          ring
        _ = W / σ := by rw [haSum]
        _ = σ := by
          apply (div_eq_iff hσpos.ne').2
          nlinarith
    have hσLeAbs :
        σ ≤ 𝔼 x : {−1,1}^[n], f x * |linearForm b x| := by
      rw [← hinner]
      apply Finset.expect_le_expect
      intro x _
      rcases hvalues x with hx | hx
      · rw [hx, zero_mul, zero_mul]
      · rw [hx, one_mul, one_mul]
        exact le_abs_self (linearForm b x)
    have hsplitPoint (x : {−1,1}^[n]) :
        f x * |linearForm b x| ≤
          s * f x +
            (if s < |linearForm b x| then |linearForm b x| else 0) := by
      rcases hvalues x with hx | hx
      · rw [hx, zero_mul, mul_zero, zero_add]
        by_cases hlarge : s < |linearForm b x|
        · simpa only [if_pos hlarge] using abs_nonneg (linearForm b x)
        · simp only [if_neg hlarge]
          exact le_rfl
      · rw [hx, one_mul, mul_one]
        by_cases hlarge : s < |linearForm b x|
        · rw [if_pos hlarge]
          linarith [zero_le_one.trans hs]
        · simpa only [if_neg hlarge, add_zero] using le_of_not_gt hlarge
    have htailMoment :
        (𝔼 x : {−1,1}^[n],
          if s < |linearForm b x| then |linearForm b x| else 0) ≤
            (2 * s + 2) * α := by
      have h :=
        expect_abs_linearForm_indicator_gt_le b hbNormalized hs
      rw [htail] at h
      exact h
    have hsplit :
        (𝔼 x : {−1,1}^[n], f x * |linearForm b x|) ≤
          s * α + (2 * s + 2) * α := by
      calc
        (𝔼 x : {−1,1}^[n], f x * |linearForm b x|) ≤
            𝔼 x : {−1,1}^[n], (
              s * f x +
                if s < |linearForm b x| then |linearForm b x| else 0) :=
          Finset.expect_le_expect fun x _ ↦ hsplitPoint x
        _ = s * (𝔼 x : {−1,1}^[n], f x) +
              𝔼 x : {−1,1}^[n],
                if s < |linearForm b x| then |linearForm b x| else 0 := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect]
        _ = s * α +
              𝔼 x : {−1,1}^[n],
                if s < |linearForm b x| then |linearForm b x| else 0 := by
          rw [hmean]
        _ ≤ s * α + (2 * s + 2) * α :=
          add_le_add le_rfl htailMoment
    have hσUpper : σ ≤ 5 * s * α := by
      have hproduct : 0 ≤ (s - 1) * α :=
        mul_nonneg (sub_nonneg.mpr hs) hα.le
      calc
        σ ≤ 𝔼 x : {−1,1}^[n], f x * |linearForm b x| := hσLeAbs
        _ ≤ s * α + (2 * s + 2) * α := hsplit
        _ ≤ 5 * s * α := by nlinarith
    have hboundNonneg : 0 ≤ 5 * s * α :=
      mul_nonneg
        (mul_nonneg (by norm_num) (zero_le_one.trans hs))
        hα.le
    have hsqBound : σ ^ 2 ≤ (5 * s * α) ^ 2 :=
      (sq_le_sq₀ hσnonneg hboundNonneg).2 hσUpper
    have hnatural :
        W ≤ 50 * α ^ 2 * L := by
      calc
        W = σ ^ 2 := hσSq.symm
        _ ≤ (5 * s * α) ^ 2 := hsqBound
        _ = 50 * α ^ 2 * L := by
          rw [show (5 * s * α) ^ 2 = 25 * s ^ 2 * α ^ 2 by ring, hsSq]
          ring
    change W ≤ (50 : ℝ) * α ^ 2 * Real.logb 2 (1 / α)
    exact hnatural.trans
      (mul_le_mul_of_nonneg_left hLLeLogb
        (mul_nonneg (by norm_num) (sq_nonneg α)))

end FABL
