/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.BerryEsseenConsequences
import FABL.Chapter05.BerryEsseenIntervals
import FABL.Chapter05.RademacherFirstMoment

/-!
# The 2/pi theorem

Book item: the 2/pi Theorem in Section 5.4.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

namespace FABL

variable {n : ℕ}

local instance twoDivPiSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance twoDivPiSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

private noncomputable def twoDivPiRademacherMeasure (n : ℕ) :
    Measure {−1,1}^[n] :=
  (uniformPMF {−1,1}^[n]).toMeasure

private instance twoDivPiRademacherMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (twoDivPiRademacherMeasure n) := by
  unfold twoDivPiRademacherMeasure
  infer_instance

private def twoDivPiRademacherSummand
    (a : Fin n → ℝ) (i : Fin n) (x : {−1,1}^[n]) : ℝ :=
  a i * signValue (x i)

private theorem sum_twoDivPiRademacherSummand
    (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    ∑ i, twoDivPiRademacherSummand a i x = linearForm a x := by
  rfl

private theorem twoDivPiRademacherMeasure_eq_pi :
    twoDivPiRademacherMeasure n =
      Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure := by
  exact uniformSample_toMeasure_eq_pi Sign n

private theorem integral_twoDivPiSignCoordinate_eq_zero (i : Fin n) :
    ∫ x, signValue (x i) ∂twoDivPiRademacherMeasure n = 0 := by
  rw [twoDivPiRademacherMeasure, integral_uniformPMF_eq_expect]
  have hmonomial :
      (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} := by
    funext x
    simp [monomial]
  rw [hmonomial, expect_monomial]
  simp

private theorem integral_twoDivPiRademacherSummand_eq_zero
    (a : Fin n → ℝ) (i : Fin n) :
    ∫ x, twoDivPiRademacherSummand a i x ∂twoDivPiRademacherMeasure n = 0 := by
  simp only [twoDivPiRademacherSummand, integral_const_mul,
    integral_twoDivPiSignCoordinate_eq_zero, mul_zero]

private theorem twoDivPiRademacherSummands_iIndep (a : Fin n → ℝ) :
    iIndepFun (twoDivPiRademacherSummand a) (twoDivPiRademacherMeasure n) := by
  rw [twoDivPiRademacherMeasure_eq_pi]
  change iIndepFun
    (fun i x ↦ (fun s : Sign ↦ a i * signValue s) (x i))
    (Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure)
  exact iIndepFun_pi fun i ↦
    (measurable_of_finite fun s : Sign ↦ a i * signValue s).aemeasurable

private theorem twoDivPiRademacherSummand_memLp
    (a : Fin n → ℝ) (i : Fin n) (p : ℝ≥0∞) :
    MemLp (twoDivPiRademacherSummand a i) p
      (twoDivPiRademacherMeasure n) := by
  refine MemLp.of_bound
    (measurable_of_finite (twoDivPiRademacherSummand a i)).aestronglyMeasurable
    |a i| (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, twoDivPiRademacherSummand, abs_mul]
  rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]

private theorem variance_twoDivPiRademacherSummand
    (a : Fin n → ℝ) (i : Fin n) :
    ProbabilityTheory.variance (twoDivPiRademacherSummand a i)
        (twoDivPiRademacherMeasure n) =
      a i ^ 2 := by
  rw [variance_of_integral_eq_zero
    (measurable_of_finite (twoDivPiRademacherSummand a i)).aemeasurable
    (integral_twoDivPiRademacherSummand_eq_zero a i)]
  rw [twoDivPiRademacherMeasure, integral_uniformPMF_eq_expect]
  rw [show
      (fun x : {−1,1}^[n] ↦ twoDivPiRademacherSummand a i x ^ 2) =
        fun _ ↦ a i ^ 2 by
    funext x
    rw [twoDivPiRademacherSummand]
    rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]]
  exact Fintype.expect_const _

private theorem twoDivPiUniformMeasure_real_event
    (P : {−1,1}^[n] → Prop) [DecidablePred P] :
    (twoDivPiRademacherMeasure n).real {x | P x} =
      uniformProbability P := by
  rw [← integral_indicator_one (Set.toFinite {x | P x}).measurableSet]
  rw [twoDivPiRademacherMeasure, integral_uniformPMF_eq_expect, uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

private theorem gaussianPDFReal_zero_one_le_one (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsqrt
  have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, sub_zero, mul_one]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ 1 * 1 :=
      mul_le_mul hinv hexp (Real.exp_pos _).le (by norm_num)
    _ = 1 := one_mul 1

private theorem gaussianReal_real_Icc_neg_le_two_mul
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Icc (-t) t) ≤ 2 * t := by
  have hnonneg :
      0 ≤ ∫ x in Icc (-t) t, gaussianPDFReal 0 1 x := by
    exact setIntegral_nonneg measurableSet_Icc fun x _ ↦
      gaussianPDFReal_nonneg 0 1 x
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num) (Icc (-t) t),
    ENNReal.toReal_ofReal hnonneg]
  calc
    (∫ x in Icc (-t) t, gaussianPDFReal 0 1 x) ≤
        ∫ _x in Icc (-t) t, (1 : ℝ) := by
      exact setIntegral_mono_on
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrableOn_const (measure_Icc_lt_top.ne))
        measurableSet_Icc fun x _ ↦ gaussianPDFReal_zero_one_le_one x
    _ = volume.real (Icc (-t) t) := setIntegral_one_eq_measureReal
    _ = t - (-t) := Real.volume_real_Icc_of_le (by linarith)
    _ = 2 * t := by ring

private theorem uniformProbability_abs_linearForm_le
    (a : Fin n → ℝ) {δ t : ℝ}
    (hnormalized : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ δ)
    (ht : 0 ≤ t) :
    uniformProbability (fun x : {−1,1}^[n] ↦ |linearForm a x| ≤ t) ≤
      2 * t + 2 * thirdMomentBerryEsseenConstant * δ := by
  let μ : Measure {−1,1}^[n] := twoDivPiRademacherMeasure n
  let X : Fin n → {−1,1}^[n] → ℝ := twoDivPiRademacherSummand a
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_of_finite (X i)
  have hX2 : ∀ i, MemLp (X i) 2 μ := by
    intro i
    simpa only [X, μ] using twoDivPiRademacherSummand_memLp a i 2
  have hXindep : iIndepFun X μ := by
    simpa only [X, μ] using twoDivPiRademacherSummands_iIndep a
  have hXmean : ∀ i, ∫ x, X i x ∂μ = 0 := by
    intro i
    simpa only [X, μ] using integral_twoDivPiRademacherSummand_eq_zero a i
  have hvar : ∑ i, ProbabilityTheory.variance (X i) μ = 1 := by
    simpa only [X, μ, variance_twoDivPiRademacherSummand] using hnormalized
  have hX3 : ∀ i, Integrable (fun x ↦ |X i x| ^ 3) μ := by
    intro i
    exact Integrable.of_finite
  have hδ :
      thirdMomentSum X μ ≤ δ := by
    apply sum_integral_abs_cube_le_of_ae_abs_le X μ hX2 hXmean hvar
    intro i
    exact ae_of_all _ fun x ↦ by
      dsimp only [X, twoDivPiRademacherSummand]
      rw [abs_mul]
      rcases signValue_eq_neg_one_or_one (x i) with h | h <;>
        simpa [h] using hbound i
  have hinterval :=
    exercise5_16_interval hX2 hXmeas hXindep hXmean hvar hX3
      (.bounded true true (-t) t)
  have hsum :
      (μ.map (sumX X)).real (Icc (-t) t) ≤
        (gaussianReal 0 1).real (Icc (-t) t) +
          2 * thirdMomentBerryEsseenConstant * thirdMomentSum X μ := by
    have habs :
        |(μ.map (sumX X)).real (Icc (-t) t) -
            (gaussianReal 0 1).real (Icc (-t) t)| ≤
          2 * thirdMomentBerryEsseenConstant * thirdMomentSum X μ := by
      simpa only [RealInterval.toSet] using hinterval
    linarith [le_abs_self
      ((μ.map (sumX X)).real (Icc (-t) t) -
        (gaussianReal 0 1).real (Icc (-t) t))]
  have hmap :
      (μ.map (sumX X)).real (Icc (-t) t) =
        uniformProbability
          (fun x : {−1,1}^[n] ↦ |linearForm a x| ≤ t) := by
    rw [map_measureReal_apply (measurable_sumX hXmeas) measurableSet_Icc]
    change (twoDivPiRademacherMeasure n).real
        ((sumX X) ⁻¹' Icc (-t) t) = _
    calc
      (twoDivPiRademacherMeasure n).real
          ((sumX X) ⁻¹' Icc (-t) t) =
          (twoDivPiRademacherMeasure n).real
            {x | |linearForm a x| ≤ t} := by
              congr 1
              ext x
              simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
              rw [show sumX X x = linearForm a x by
                change (∑ i, twoDivPiRademacherSummand a i x) =
                  linearForm a x
                exact sum_twoDivPiRademacherSummand a x]
              exact abs_le.symm
      _ = uniformProbability
          (fun x : {−1,1}^[n] ↦ |linearForm a x| ≤ t) :=
        twoDivPiUniformMeasure_real_event _
  rw [hmap] at hsum
  calc
    uniformProbability (fun x : {−1,1}^[n] ↦ |linearForm a x| ≤ t) ≤
        (gaussianReal 0 1).real (Icc (-t) t) +
          2 * thirdMomentBerryEsseenConstant * thirdMomentSum X μ := hsum
    _ ≤ 2 * t + 2 * thirdMomentBerryEsseenConstant * δ := by
      exact add_le_add (gaussianReal_real_Icc_neg_le_two_mul ht)
        (mul_le_mul_of_nonneg_left hδ
          (mul_nonneg (by norm_num) thirdMomentBerryEsseenConstant_pos.le))

private theorem expect_mul_linearForm_eq
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

private theorem thresholdSign_gap_eq
    (s : Sign) (z : ℝ) :
    (signValue (thresholdSign z) - signValue s) * z =
      if s ≠ thresholdSign z then 2 * |z| else 0 := by
  by_cases hdiff : s ≠ thresholdSign z
  · rw [if_pos hdiff]
    by_cases hz : 0 ≤ z
    · have hsNe : s ≠ 1 := by
        simpa only [thresholdSign_of_nonneg hz] using hdiff
      have hs : s = -1 := (Int.units_eq_one_or s).resolve_left hsNe
      rw [hs, thresholdSign_of_nonneg hz]
      simp only [signValue_one, signValue_neg_one, abs_of_nonneg hz]
      ring
    · have hz' : z < 0 := lt_of_not_ge hz
      have hsNe : s ≠ -1 := by
        simpa only [thresholdSign_of_neg hz'] using hdiff
      have hs : s = 1 := (Int.units_eq_one_or s).resolve_right hsNe
      rw [hs, thresholdSign_of_neg hz']
      simp only [signValue_one, signValue_neg_one, abs_of_neg hz']
      ring
  · have hs : s = thresholdSign z := not_ne_iff.mp hdiff
    simp [hs]

private theorem weighted_mismatch_sub_smallBall_le
    (f : BooleanFunction n) (ell : {−1,1}^[n] → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    2 * t *
        (uniformProbability (fun x ↦ f x ≠ thresholdSign (ell x)) -
          uniformProbability (fun x ↦ |ell x| ≤ t)) ≤
      𝔼 x, (signValue (thresholdSign (ell x)) - f.toReal x) * ell x := by
  rw [uniformProbability, uniformProbability, ← Finset.expect_sub_distrib,
    Finset.mul_expect]
  apply Finset.expect_le_expect
  intro x _
  change
    2 * t *
          ((if f x ≠ thresholdSign (ell x) then 1 else 0) -
            if |ell x| ≤ t then 1 else 0) ≤
      (signValue (thresholdSign (ell x)) - signValue (f x)) * ell x
  rw [thresholdSign_gap_eq (f x) (ell x)]
  by_cases hmismatch : f x ≠ thresholdSign (ell x)
  · by_cases hsmall : |ell x| ≤ t
    · simp [hmismatch, hsmall]
    · have hlarge : t < |ell x| := lt_of_not_ge hsmall
      simp [hmismatch, hsmall]
      linarith
  · by_cases hsmall : |ell x| ≤ t
    · simp [hmismatch, hsmall]
      linarith
    · simp [hmismatch, hsmall]

private theorem exists_two_div_pi_near_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : BooleanFunction n) {ε : ℝ},
        0 < ε →
        ε ≤ 1 →
        (∀ i, |fourierCoeff f.toReal {i}| ≤ ε) →
        2 / Real.pi - ε ≤ fourierWeightAtLevel 1 f.toReal →
          relativeHammingDist f
            (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤
              C * Real.sqrt ε := by
  obtain ⟨C₀, hC₀, habs⟩ :=
    exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular
  let B : ℝ := thirdMomentBerryEsseenConstant
  let C : ℝ := 8 * (1 + C₀ + C₀ ^ 2 + B)
  have hB : 0 < B := by
    exact thirdMomentBerryEsseenConstant_pos
  have hC : 0 < C := by
    dsimp only [C, B]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n f ε hε hεle hregular
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f.toReal {i}
  let W : ℝ := fourierWeightAtLevel 1 f.toReal
  let q : ℝ := Real.sqrt (2 / Real.pi)
  have hWnonneg : 0 ≤ W := by
    exact (fourierWeightAtLevel_one_mem_Icc f).1
  have haSum : ∑ i, a i ^ 2 = W := by
    exact (fourierWeightAtLevel_one_eq_sum_singleton f.toReal).symm
  have hqnonneg : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 2 / Real.pi := by
    exact Real.sq_sqrt (div_nonneg (by norm_num) Real.pi_pos.le)
  have hTwoDivPiLower : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_le_four]
  by_cases hWhigh : (1 / 4 : ℝ) < W
  · let σ : ℝ := Real.sqrt W
    let b : Fin n → ℝ := fun i ↦ a i / σ
    have hσnonneg : 0 ≤ σ := Real.sqrt_nonneg W
    have hσSq : σ ^ 2 = W := Real.sq_sqrt hWnonneg
    have hσpos : 0 < σ := Real.sqrt_pos.2 (by linarith)
    have hσhalf : (1 / 2 : ℝ) < σ := by
      nlinarith
    have hbNormalized : ∑ i, b i ^ 2 = 1 := by
      calc
        (∑ i, b i ^ 2) = (∑ i, a i ^ 2) / σ ^ 2 := by
          simp_rw [b, div_pow]
          exact
            (Finset.sum_div Finset.univ (fun i ↦ a i ^ 2) (σ ^ 2)).symm
        _ = W / σ ^ 2 := by rw [haSum]
        _ = 1 := by
          rw [hσSq, div_self (ne_of_gt (by linarith : 0 < W))]
    have hbRegular : ∀ i, |b i| ≤ 2 * ε := by
      intro i
      dsimp only [b]
      rw [abs_div, abs_of_pos hσpos]
      apply (div_le_iff₀ hσpos).2
      have hai : |a i| ≤ ε := hregular i
      nlinarith [mul_pos hε hσpos]
    have hfirstMoment :
        (𝔼 x : {−1,1}^[n], |linearForm b x|) ≤
          q + 2 * C₀ * ε := by
      have h := habs b hbNormalized hbRegular
      have hupper := (abs_le.mp h).2
      dsimp only [q]
      nlinarith
    have hinner :
        (𝔼 x : {−1,1}^[n], f.toReal x * linearForm b x) = σ := by
      rw [expect_mul_linearForm_eq]
      calc
        (∑ i, b i * fourierCoeff f.toReal {i}) =
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
    intro hnear
    change 2 / Real.pi - ε ≤ W at hnear
    have hsign (x : {−1,1}^[n]) :
        thresholdSign (linearForm b x) =
          thresholdSign (degreePart 1 f.toReal x) := by
      rw [degreePart_one_eq_linearForm]
      have hscale : linearForm a x = σ * linearForm b x := by
        rw [linearForm, linearForm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [b]
        field_simp [hσpos.ne']
      rw [hscale]
      by_cases hx : 0 ≤ linearForm b x
      · rw [thresholdSign_of_nonneg hx,
          thresholdSign_of_nonneg (mul_nonneg hσpos.le hx)]
      · have hx' : linearForm b x < 0 := lt_of_not_ge hx
        rw [thresholdSign_of_neg hx',
          thresholdSign_of_neg (mul_neg_of_pos_of_neg hσpos hx')]
    by_cases hεlarge : (1 / 16 : ℝ) ≤ ε
    · have hsqrtQuarter : (1 / 4 : ℝ) ≤ Real.sqrt ε := by
        have := Real.sqrt_le_sqrt hεlarge
        norm_num at this ⊢
        exact this
      have hdist :
          relativeHammingDist f
            (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤ 1 :=
        relativeHammingDist_le_one _ _
      have hFourLeC : (4 : ℝ) ≤ C := by
        dsimp only [C, B]
        nlinarith [sq_nonneg C₀, hB.le]
      calc
        relativeHammingDist f
            (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤ 1 := hdist
        _ ≤ 4 * Real.sqrt ε := by nlinarith
        _ ≤ C * Real.sqrt ε :=
          mul_le_mul_of_nonneg_right hFourLeC (Real.sqrt_nonneg ε)
    · have hεsmall : ε < 1 / 16 := lt_of_not_ge hεlarge
      have hqHalf : (1 / 2 : ℝ) ≤ q := by
        nlinarith
      have hσLower : q - 2 * ε ≤ σ := by
        have hleftNonneg : 0 ≤ q - 2 * ε := by linarith
        have hfactor : 0 ≤ 4 * q - 4 * ε - 1 := by linarith
        have hproduct : 0 ≤ ε * (4 * q - 4 * ε - 1) :=
          mul_nonneg hε.le hfactor
        have hsquares : (q - 2 * ε) ^ 2 ≤ σ ^ 2 := by
          rw [hσSq]
          nlinarith [hqSq, hproduct]
        exact (sq_le_sq₀ hleftNonneg hσnonneg).1 hsquares
      have hgap :
          (𝔼 x : {−1,1}^[n],
            (signValue (thresholdSign (linearForm b x)) - f.toReal x) *
              linearForm b x) =
            (𝔼 x : {−1,1}^[n], |linearForm b x|) - σ := by
        rw [show
            (fun x : {−1,1}^[n] ↦
              (signValue (thresholdSign (linearForm b x)) - f.toReal x) *
                linearForm b x) =
              fun x ↦ |linearForm b x| -
                f.toReal x * linearForm b x by
          funext x
          rw [sub_mul]
          have hthreshold :
              signValue (thresholdSign (linearForm b x)) *
                  linearForm b x =
                |linearForm b x| := by
            rw [signValue_thresholdSign]
            by_cases hx : 0 ≤ linearForm b x
            · simp [hx, abs_of_nonneg hx]
            · have hx' : linearForm b x < 0 := lt_of_not_ge hx
              simp [hx, abs_of_neg hx']
          rw [hthreshold]]
        rw [Finset.expect_sub_distrib, hinner]
      have hgapUpper :
          (𝔼 x : {−1,1}^[n],
            (signValue (thresholdSign (linearForm b x)) - f.toReal x) *
              linearForm b x) ≤
            (2 * C₀ + 2) * ε := by
        calc
          (𝔼 x : {−1,1}^[n],
              (signValue (thresholdSign (linearForm b x)) - f.toReal x) *
                linearForm b x) =
              (𝔼 x : {−1,1}^[n], |linearForm b x|) - σ := hgap
          _ ≤ (2 * C₀ + 2) * ε := by
            linarith only [hfirstMoment, hσLower]
      let r : ℝ := Real.sqrt ε
      have hrpos : 0 < r := Real.sqrt_pos.2 hε
      have hrnonneg : 0 ≤ r := hrpos.le
      have hrSq : r ^ 2 = ε := Real.sq_sqrt hε.le
      have hrLeOne : r ≤ 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hεle
      have hsmall :
          uniformProbability
              (fun x : {−1,1}^[n] ↦ |linearForm b x| ≤ r) ≤
            2 * r + 4 * B * ε := by
        calc
          uniformProbability
              (fun x : {−1,1}^[n] ↦ |linearForm b x| ≤ r) ≤
              2 * r + 2 * thirdMomentBerryEsseenConstant * (2 * ε) :=
            uniformProbability_abs_linearForm_le
              (n := n) b (δ := 2 * ε) (t := r)
              hbNormalized hbRegular hrnonneg
          _ = 2 * r + 4 * B * ε := by
            dsimp only [B]
            ring
      have hsmallSqrt :
          uniformProbability
              (fun x : {−1,1}^[n] ↦ |linearForm b x| ≤ r) ≤
            (2 + 4 * B) * r := by
        calc
          uniformProbability
              (fun x : {−1,1}^[n] ↦ |linearForm b x| ≤ r) ≤
              2 * r + 4 * B * ε := hsmall
          _ = 2 * r + 4 * B * r ^ 2 := by rw [hrSq]
          _ ≤ (2 + 4 * B) * r := by
            have hrSqLe : r ^ 2 ≤ r := by
              calc
                r ^ 2 = r * r := pow_two r
                _ ≤ r * 1 :=
                  mul_le_mul_of_nonneg_left hrLeOne hrnonneg
                _ = r := mul_one r
            calc
              2 * r + 4 * B * r ^ 2 ≤ 2 * r + 4 * B * r :=
                add_le_add le_rfl
                  (mul_le_mul_of_nonneg_left hrSqLe
                    (mul_nonneg (by norm_num) hB.le))
              _ = (2 + 4 * B) * r := by ring
      have hweighted :=
        weighted_mismatch_sub_smallBall_le f (linearForm b) hrnonneg
      have hmismatchSub :
          uniformProbability
              (fun x ↦ f x ≠ thresholdSign (linearForm b x)) -
            uniformProbability
              (fun x ↦ |linearForm b x| ≤ r) ≤
            (C₀ + 1) * r := by
        apply le_of_mul_le_mul_left
        · calc
            2 * r *
                (uniformProbability
                    (fun x ↦ f x ≠ thresholdSign (linearForm b x)) -
                  uniformProbability
                    (fun x ↦ |linearForm b x| ≤ r)) ≤
                (𝔼 x : {−1,1}^[n],
                  (signValue (thresholdSign (linearForm b x)) - f.toReal x) *
                    linearForm b x) := hweighted
            _ ≤ (2 * C₀ + 2) * ε := hgapUpper
            _ = 2 * r * ((C₀ + 1) * r) := by rw [← hrSq]; ring
        · exact mul_pos (by norm_num) hrpos
      have hmismatch :
          uniformProbability
              (fun x ↦ f x ≠ thresholdSign (linearForm b x)) ≤
            (C₀ + 3 + 4 * B) * r := by
        nlinarith
      have hnearCoefficient : C₀ + 3 + 4 * B ≤ C := by
        dsimp only [C, B]
        nlinarith [sq_nonneg C₀, hC₀.le, hB.le]
      calc
        relativeHammingDist f
            (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) =
            relativeHammingDist f
              (fun x ↦ thresholdSign (linearForm b x)) := by
                congr 1
                funext x
                exact (hsign x).symm
        _ = uniformProbability
            (fun x ↦ f x ≠ thresholdSign (linearForm b x)) := by
              rw [uniformProbability_ne_eq_relativeHammingDist]
        _ ≤ (C₀ + 3 + 4 * B) * r := hmismatch
        _ ≤ C * r :=
          mul_le_mul_of_nonneg_right hnearCoefficient hrnonneg
        _ = C * Real.sqrt ε := rfl
  · have hWlow : W ≤ 1 / 4 := le_of_not_gt hWhigh
    intro hnear
    change 2 / Real.pi - ε ≤ W at hnear
    have hεquarter : (1 / 4 : ℝ) ≤ ε := by
      linarith [hTwoDivPiLower, hWlow]
    have hsqrtHalf : (1 / 2 : ℝ) ≤ Real.sqrt ε := by
      have := Real.sqrt_le_sqrt hεquarter
      norm_num at this ⊢
      exact this
    have hdist :
        relativeHammingDist f
          (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤ 1 :=
      relativeHammingDist_le_one _ _
    have hTwoLeC : (2 : ℝ) ≤ C := by
      dsimp only [C, B]
      nlinarith [sq_nonneg C₀, hB.le]
    calc
      relativeHammingDist f
          (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤ 1 := hdist
      _ ≤ 2 * Real.sqrt ε := by nlinarith
      _ ≤ C * Real.sqrt ε :=
        mul_le_mul_of_nonneg_right hTwoLeC (Real.sqrt_nonneg ε)

private theorem exists_two_div_pi_upper_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : BooleanFunction n) {ε : ℝ},
        0 < ε →
        ε ≤ 1 →
        (∀ i, |fourierCoeff f.toReal {i}| ≤ ε) →
        fourierWeightAtLevel 1 f.toReal ≤ 2 / Real.pi + C * ε := by
  obtain ⟨C₀, hC₀, habs⟩ :=
    exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular
  let C : ℝ := 4 * (1 + C₀ + C₀ ^ 2)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n f ε hε hεle hregular
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f.toReal {i}
  let W : ℝ := fourierWeightAtLevel 1 f.toReal
  let q : ℝ := Real.sqrt (2 / Real.pi)
  have hWnonneg : 0 ≤ W := by
    exact (fourierWeightAtLevel_one_mem_Icc f).1
  have haSum : ∑ i, a i ^ 2 = W := by
    exact (fourierWeightAtLevel_one_eq_sum_singleton f.toReal).symm
  have hqnonneg : 0 ≤ q := Real.sqrt_nonneg _
  have hqSq : q ^ 2 = 2 / Real.pi := by
    exact Real.sq_sqrt (div_nonneg (by norm_num) Real.pi_pos.le)
  have hTwoDivPiLower : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_le_four]
  have hTwoDivPiUpper : 2 / Real.pi ≤ 1 := by
    apply (div_le_iff₀ Real.pi_pos).2
    simpa using Real.two_le_pi
  have hqLeOne : q ≤ 1 := by
    nlinarith
  by_cases hWhigh : (1 / 4 : ℝ) < W
  · let σ : ℝ := Real.sqrt W
    let b : Fin n → ℝ := fun i ↦ a i / σ
    have hσnonneg : 0 ≤ σ := Real.sqrt_nonneg W
    have hσSq : σ ^ 2 = W := Real.sq_sqrt hWnonneg
    have hσpos : 0 < σ := Real.sqrt_pos.2 (by linarith)
    have hσhalf : (1 / 2 : ℝ) < σ := by
      nlinarith
    have hbNormalized : ∑ i, b i ^ 2 = 1 := by
      calc
        (∑ i, b i ^ 2) = (∑ i, a i ^ 2) / σ ^ 2 := by
          simp_rw [b, div_pow]
          exact
            (Finset.sum_div Finset.univ (fun i ↦ a i ^ 2) (σ ^ 2)).symm
        _ = W / σ ^ 2 := by rw [haSum]
        _ = 1 := by
          rw [hσSq, div_self (ne_of_gt (by linarith : 0 < W))]
    have hbRegular : ∀ i, |b i| ≤ 2 * ε := by
      intro i
      dsimp only [b]
      rw [abs_div, abs_of_pos hσpos]
      apply (div_le_iff₀ hσpos).2
      have hai : |a i| ≤ ε := hregular i
      nlinarith [mul_pos hε hσpos]
    have hfirstMoment :
        (𝔼 x : {−1,1}^[n], |linearForm b x|) ≤
          q + 2 * C₀ * ε := by
      have h := habs b hbNormalized hbRegular
      have hupper := (abs_le.mp h).2
      dsimp only [q]
      nlinarith
    have hinner :
        (𝔼 x : {−1,1}^[n], f.toReal x * linearForm b x) = σ := by
      rw [expect_mul_linearForm_eq]
      calc
        (∑ i, b i * fourierCoeff f.toReal {i}) =
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
    have hσLeFirstMoment :
        σ ≤ 𝔼 x : {−1,1}^[n], |linearForm b x| := by
      rw [← hinner]
      apply Finset.expect_le_expect
      intro x _
      rcases Int.units_eq_one_or (f x) with hf | hf
      · simp only [BooleanFunction.toReal, hf, signValue_one, one_mul]
        exact le_abs_self (linearForm b x)
      · simp only [BooleanFunction.toReal, hf, signValue_neg_one, neg_one_mul]
        exact neg_le_abs (linearForm b x)
    have hupperCoefficient :
        4 * C₀ + 4 * C₀ ^ 2 ≤ C := by
      dsimp only [C]
      nlinarith [sq_nonneg C₀]
    have hεsq : ε ^ 2 ≤ ε := by
      nlinarith
    have hcross :
        q * C₀ * ε ≤ C₀ * ε := by
      calc
        q * C₀ * ε = q * (C₀ * ε) := by ring
        _ ≤ 1 * (C₀ * ε) :=
          mul_le_mul_of_nonneg_right hqLeOne
            (mul_nonneg hC₀.le hε.le)
        _ = C₀ * ε := one_mul _
    have hσUpper : σ ≤ q + 2 * C₀ * ε :=
      hσLeFirstMoment.trans hfirstMoment
    have hboundNonneg : 0 ≤ q + 2 * C₀ * ε := by positivity
    have hsquare :
        σ ^ 2 ≤ (q + 2 * C₀ * ε) ^ 2 :=
      (sq_le_sq₀ hσnonneg hboundNonneg).2 hσUpper
    calc
      W = σ ^ 2 := hσSq.symm
      _ ≤ (q + 2 * C₀ * ε) ^ 2 := hsquare
      _ = q ^ 2 + 4 * (q * C₀ * ε) + 4 * C₀ ^ 2 * ε ^ 2 := by ring
      _ ≤ q ^ 2 + (4 * C₀ + 4 * C₀ ^ 2) * ε := by
        have hsquareTerm :
            C₀ ^ 2 * ε ^ 2 ≤ C₀ ^ 2 * ε :=
          mul_le_mul_of_nonneg_left hεsq (sq_nonneg C₀)
        nlinarith
      _ = 2 / Real.pi + (4 * C₀ + 4 * C₀ ^ 2) * ε := by rw [hqSq]
      _ ≤ 2 / Real.pi + C * ε :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hupperCoefficient hε.le)
  · have hWlow : W ≤ 1 / 4 := le_of_not_gt hWhigh
    calc
      W ≤ 1 / 4 := hWlow
      _ ≤ 2 / Real.pi := by linarith
      _ ≤ 2 / Real.pi + C * ε :=
        le_add_of_nonneg_right (mul_nonneg hC.le hε.le)

/-- O'Donnell's 2/pi Theorem: regular Boolean functions have level-one weight at most
`2/pi + O(ε)`, and every near-extremizer is `O(sqrt ε)`-close to the sign of its
degree-one Fourier projection. -/
theorem exists_two_div_pi_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : BooleanFunction n) {ε : ℝ},
        0 < ε →
        ε ≤ 1 →
        (∀ i, |fourierCoeff f.toReal {i}| ≤ ε) →
        fourierWeightAtLevel 1 f.toReal ≤ 2 / Real.pi + C * ε ∧
          (2 / Real.pi - ε ≤ fourierWeightAtLevel 1 f.toReal →
            relativeHammingDist f
              (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤
                C * Real.sqrt ε) := by
  obtain ⟨Cᵤ, hCᵤ, hupper⟩ := exists_two_div_pi_upper_constant
  obtain ⟨Cₙ, hCₙ, hnear⟩ := exists_two_div_pi_near_constant
  refine ⟨Cᵤ + Cₙ, add_pos hCᵤ hCₙ, ?_⟩
  intro n f ε hε hεle hregular
  constructor
  · calc
      fourierWeightAtLevel 1 f.toReal ≤ 2 / Real.pi + Cᵤ * ε :=
        hupper f hε hεle hregular
      _ ≤ 2 / Real.pi + (Cᵤ + Cₙ) * ε := by
        have hcoeff : Cᵤ ≤ Cᵤ + Cₙ := by linarith [hCₙ.le]
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right hcoeff hε.le) _
  · intro hnearWeight
    calc
      relativeHammingDist f
          (fun x ↦ thresholdSign (degreePart 1 f.toReal x)) ≤
          Cₙ * Real.sqrt ε :=
        hnear f hε hεle hregular hnearWeight
      _ ≤ (Cᵤ + Cₙ) * Real.sqrt ε := by
        have hcoeff : Cₙ ≤ Cᵤ + Cₙ := by linarith [hCᵤ.le]
        exact mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg ε)

end FABL
