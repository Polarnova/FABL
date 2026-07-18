/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.GaussianIsoperimetric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The standard Gaussian Mills ratio

Book item: the standard Gaussian Mills-ratio support lemma preceding Proposition 5.27.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace FABL

private theorem standardGaussianDensity_formula_mills (t : ℝ) :
    gaussianPDFReal 0 1 t =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  congr 2
  ring_nf

private theorem hasDerivAt_standardGaussianDensity_mills (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-t * gaussianPDFReal 0 1 t) t := by
  rw [show
      gaussianPDFReal 0 1 =
        fun x : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2) by
    funext x
    exact standardGaussianDensity_formula_mills x]
  have hinner :
      HasDerivAt (fun x : ℝ ↦ -(1 / 2 : ℝ) * x ^ 2)
        (-t) t := by
    exact
      ((hasDerivAt_pow 2 t).const_mul
        (-(1 / 2 : ℝ))).congr_deriv (by ring_nf)
  exact (hinner.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv
    (by ring_nf)

private theorem tendsto_standardGaussianDensity_mills_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have hinner :
      Tendsto (fun x : ℝ ↦ -(1 / 2 : ℝ) * x ^ 2)
        atTop atBot :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (by norm_num)
  have hexp :
      Tendsto (fun x : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hinner
  have hmul :=
    Tendsto.const_mul (Real.sqrt (2 * Real.pi))⁻¹ hexp
  rw [show
      gaussianPDFReal 0 1 =
        fun x : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2) by
    funext x
    exact standardGaussianDensity_formula_mills x]
  simpa only [mul_zero] using hmul

/-- The standard Gaussian upper tail is the integral of its density over the
corresponding upper half-line. -/
theorem standardGaussianUpperTail_eq_integral_density (t : ℝ) :
    standardGaussianUpperTail t =
      ∫ x : ℝ in Ioi t, gaussianPDFReal 0 1 x := by
  rw [standardGaussianUpperTail_eq_measureReal_Ioi, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num) (Ioi t),
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi fun x _ ↦
    gaussianPDFReal_nonneg 0 1 x

/-- The elementary upper half of the standard Gaussian Mills-ratio estimate. -/
theorem standardGaussianUpperTail_le_density_div
    {t : ℝ} (ht : 0 < t) :
    standardGaussianUpperTail t ≤ gaussianPDFReal 0 1 t / t := by
  have hstop : 0 ≤ standardGaussianStopLoss t := by
    rw [standardGaussianStopLoss]
    exact integral_nonneg fun z ↦ posPart_nonneg (z - t)
  rw [standardGaussianStopLoss_eq] at hstop
  exact (le_div_iff₀ ht).2 (by linarith)

private theorem hasDerivAt_standardGaussianDensity_div
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ gaussianPDFReal 0 1 y / y)
      (-gaussianPDFReal 0 1 x -
        gaussianPDFReal 0 1 x / x ^ 2) x := by
  have h :=
    (hasDerivAt_standardGaussianDensity_mills x).div
      (hasDerivAt_id x) hx
  have h' :
      HasDerivAt (fun y : ℝ ↦ gaussianPDFReal 0 1 y / y)
        ((-x * gaussianPDFReal 0 1 x * x -
          gaussianPDFReal 0 1 x) / x ^ 2) x := by
    change
      HasDerivAt (fun y : ℝ ↦ gaussianPDFReal 0 1 y / y)
        ((-x * gaussianPDFReal 0 1 x * x -
          gaussianPDFReal 0 1 x * 1) / x ^ 2) x at h
    simpa only [mul_one] using h
  exact h'.congr_deriv (by
    field_simp [hx])

private theorem tendsto_standardGaussianDensity_div_atTop :
    Tendsto (fun x : ℝ ↦ gaussianPDFReal 0 1 x / x)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  simpa only [div_eq_mul_inv, zero_mul] using
    tendsto_standardGaussianDensity_mills_atTop.mul hinv

private theorem integral_standardGaussianDensity_add_div_sq
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in Ioi t,
      gaussianPDFReal 0 1 x +
        gaussianPDFReal 0 1 x / x ^ 2) =
      gaussianPDFReal 0 1 t / t := by
  let p : ℝ → ℝ :=
    fun x ↦ gaussianPDFReal 0 1 x +
      gaussianPDFReal 0 1 x / x ^ 2
  let d : ℝ → ℝ := fun x ↦ -p x
  have hderiv :
      ∀ x ∈ Ici t,
        HasDerivAt
          (fun y : ℝ ↦ gaussianPDFReal 0 1 y / y)
          (d x) x := by
    intro x hx
    have hxpos : 0 < x := ht.trans_le hx
    apply
      (hasDerivAt_standardGaussianDensity_div hxpos.ne').congr_deriv
    dsimp only [d, p]
    ring
  have hdnonpos : ∀ x ∈ Ioi t, d x ≤ 0 := by
    intro x hx
    have hxpos : 0 < x := ht.trans hx
    dsimp only [d, p]
    have hdensity : 0 ≤ gaussianPDFReal 0 1 x :=
      gaussianPDFReal_nonneg 0 1 x
    have hdiv : 0 ≤ gaussianPDFReal 0 1 x / x ^ 2 :=
      div_nonneg hdensity (sq_nonneg x)
    linarith
  have hdint : IntegrableOn d (Ioi t) :=
    integrableOn_Ioi_deriv_of_nonpos' hderiv hdnonpos
      tendsto_standardGaussianDensity_div_atTop
  have hfundamental :
      (∫ x : ℝ in Ioi t, d x) =
        -(gaussianPDFReal 0 1 t / t) := by
    have h :=
      integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hdint
        tendsto_standardGaussianDensity_div_atTop
    simpa only [zero_sub] using h
  calc
    (∫ x : ℝ in Ioi t,
        gaussianPDFReal 0 1 x +
          gaussianPDFReal 0 1 x / x ^ 2) =
        -(∫ x : ℝ in Ioi t, d x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp [d, p]
    _ = gaussianPDFReal 0 1 t / t := by
      rw [hfundamental]
      ring

/-- The elementary lower half of the standard Gaussian Mills-ratio estimate. -/
theorem density_mul_t_div_one_add_sq_le_standardGaussianUpperTail
    {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * gaussianPDFReal 0 1 t ≤
      standardGaussianUpperTail t := by
  let p : ℝ → ℝ :=
    fun x ↦ gaussianPDFReal 0 1 x +
      gaussianPDFReal 0 1 x / x ^ 2
  have hpint : IntegrableOn p (Ioi t) := by
    have hdensity :
        IntegrableOn (gaussianPDFReal 0 1) (Ioi t) :=
      (integrable_gaussianPDFReal 0 1).integrableOn
    have hdiv :
        IntegrableOn
          (fun x : ℝ ↦ gaussianPDFReal 0 1 x / x ^ 2)
          (Ioi t) := by
      apply Integrable.mono'
        (hdensity.const_mul (1 / t ^ 2))
        ((measurable_gaussianPDFReal 0 1).div
          (measurable_id.pow_const 2)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change
        |gaussianPDFReal 0 1 x / x ^ 2| ≤
          1 / t ^ 2 * gaussianPDFReal 0 1 x
      rw [abs_of_nonneg
        (div_nonneg (gaussianPDFReal_nonneg 0 1 x) (sq_nonneg x))]
      have hsq : t ^ 2 ≤ x ^ 2 :=
        sq_le_sq₀ ht.le (ht.trans hx).le |>.2 hx.le
      have hinv :
          1 / x ^ 2 ≤ 1 / t ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
      calc
        gaussianPDFReal 0 1 x / x ^ 2 =
            (1 / x ^ 2) * gaussianPDFReal 0 1 x := by ring
        _ ≤ (1 / t ^ 2) * gaussianPDFReal 0 1 x :=
          mul_le_mul_of_nonneg_right hinv
            (gaussianPDFReal_nonneg 0 1 x)
    exact hdensity.add hdiv
  have hmajor :
      ∀ᵐ x ∂volume.restrict (Ioi t),
        p x ≤
          (1 + 1 / t ^ 2) * gaussianPDFReal 0 1 x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hsq : t ^ 2 ≤ x ^ 2 :=
      sq_le_sq₀ ht.le (ht.trans hx).le |>.2 hx.le
    have hinv :
        1 / x ^ 2 ≤ 1 / t ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
    have hmul :=
      mul_le_mul_of_nonneg_right hinv
        (gaussianPDFReal_nonneg 0 1 x)
    dsimp only [p]
    calc
      gaussianPDFReal 0 1 x +
          gaussianPDFReal 0 1 x / x ^ 2 ≤
        gaussianPDFReal 0 1 x +
          (1 / t ^ 2) * gaussianPDFReal 0 1 x := by
        rw [show gaussianPDFReal 0 1 x / x ^ 2 =
          (1 / x ^ 2) * gaussianPDFReal 0 1 x by ring]
        simpa only [add_comm] using
          add_le_add_left hmul (gaussianPDFReal 0 1 x)
      _ = (1 + 1 / t ^ 2) * gaussianPDFReal 0 1 x := by ring
  have hright :
      IntegrableOn
        (fun x : ℝ ↦
          (1 + 1 / t ^ 2) * gaussianPDFReal 0 1 x)
        (Ioi t) :=
    (integrable_gaussianPDFReal 0 1).integrableOn.const_mul _
  have hcore :
      gaussianPDFReal 0 1 t / t ≤
        (1 + 1 / t ^ 2) * standardGaussianUpperTail t := by
    calc
      gaussianPDFReal 0 1 t / t =
          ∫ x : ℝ in Ioi t, p x := by
        simpa only [p] using
          (integral_standardGaussianDensity_add_div_sq ht).symm
      _ ≤ ∫ x : ℝ in Ioi t,
          (1 + 1 / t ^ 2) * gaussianPDFReal 0 1 x :=
        integral_mono_ae hpint hright hmajor
      _ = (1 + 1 / t ^ 2) *
          standardGaussianUpperTail t := by
        rw [integral_const_mul,
          ← standardGaussianUpperTail_eq_integral_density]
  have hscaled :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg t)
  have hmul :
      t * gaussianPDFReal 0 1 t ≤
        (1 + t ^ 2) * standardGaussianUpperTail t := by
    field_simp [ht.ne'] at hscaled
    nlinarith
  rw [show t / (1 + t ^ 2) * gaussianPDFReal 0 1 t =
      (t * gaussianPDFReal 0 1 t) / (1 + t ^ 2) by ring]
  exact (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
    (by simpa [mul_comm] using hmul)

/-- The standard Gaussian Mills ratio tends to one at positive infinity. -/
theorem tendsto_standardGaussianUpperTail_div_density_div :
    Tendsto
      (fun t : ℝ ↦
        standardGaussianUpperTail t /
          (gaussianPDFReal 0 1 t / t))
      atTop (𝓝 1) := by
  have hlower :
      Tendsto (fun t : ℝ ↦ t ^ 2 / (1 + t ^ 2))
        atTop (𝓝 1) := by
    have hinv :
        Tendsto (fun t : ℝ ↦ (t ^ 2)⁻¹) atTop (𝓝 0) := by
      exact tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop two_ne_zero)
    have hform :
        ∀ᶠ t : ℝ in atTop,
          t ^ 2 / (1 + t ^ 2) =
            1 / (1 + (t ^ 2)⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      field_simp [ht.ne']
      ring
    have hformSymm :
        (fun t : ℝ ↦ 1 / (1 + (t ^ 2)⁻¹)) =ᶠ[atTop]
          fun t ↦ t ^ 2 / (1 + t ^ 2) := by
      filter_upwards [hform] with t h
      exact h.symm
    apply Tendsto.congr' hformSymm
    have honePlus :
        Tendsto (fun t : ℝ ↦ 1 + (t ^ 2)⁻¹)
          atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add hinv :
        Tendsto (fun t : ℝ ↦ 1 + (t ^ 2)⁻¹)
          atTop (𝓝 ((1 : ℝ) + 0)))
    simpa only [one_div, inv_one] using
      honePlus.inv₀ one_ne_zero
  have hupper : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hdensity : 0 < gaussianPDFReal 0 1 t :=
      gaussianPDFReal_pos 0 1 t (by norm_num)
    have hlowerBound :=
      density_mul_t_div_one_add_sq_le_standardGaussianUpperTail ht
    have hdenom : 0 < gaussianPDFReal 0 1 t / t :=
      div_pos hdensity ht
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)
      hdenom]
    calc
      t ^ 2 * (gaussianPDFReal 0 1 t / t) =
          t * gaussianPDFReal 0 1 t := by
        field_simp [ht.ne']
      _ = (1 + t ^ 2) *
          (t / (1 + t ^ 2) * gaussianPDFReal 0 1 t) := by
        field_simp
      _ ≤ (1 + t ^ 2) * standardGaussianUpperTail t :=
        mul_le_mul_of_nonneg_left hlowerBound (by positivity)
      _ = standardGaussianUpperTail t * (1 + t ^ 2) := by ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (div_le_one
      (div_pos (gaussianPDFReal_pos 0 1 t (by norm_num)) ht)).2
        (standardGaussianUpperTail_le_density_div ht)

/-- The standard Gaussian upper tail is asymptotic to its density divided by
the threshold. -/
theorem standardGaussianUpperTail_isEquivalent_density_div :
    Asymptotics.IsEquivalent atTop
      standardGaussianUpperTail
      (fun t : ℝ ↦ gaussianPDFReal 0 1 t / t) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).2
    tendsto_standardGaussianUpperTail_div_density_div
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (div_pos (gaussianPDFReal_pos 0 1 t (by norm_num)) ht).ne'

end FABL
