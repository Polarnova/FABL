/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/

import FABL.Chapter05.GaussianMillsRatio
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Asymptotics of the Gaussian isoperimetric function

Book item: Proposition 5.27.
-/

open Filter ProbabilityTheory Set
open scoped Asymptotics Topology

namespace FABL

/-- The standard Gaussian upper quantile tends to positive infinity as its
open-unit probability tends to zero. -/
theorem tendsto_standardGaussianUpperQuantile_atBot :
    Tendsto standardGaussianUpperQuantile
      (atBot : Filter (Ioo (0 : ℝ) 1)) atTop :=
  standardGaussianUpperTailOrderIso.symm.tendsto_atBot

private theorem log_inv_standardGaussianDensity_div
    {t : ℝ} (ht : 0 < t) :
    Real.log ((gaussianPDFReal 0 1 t / t)⁻¹) =
      t ^ 2 / 2 + Real.log t +
        Real.log (Real.sqrt (2 * Real.pi)) := by
  have hsqrtPos : 0 < Real.sqrt (2 * Real.pi) := by
    positivity
  have hdensity : gaussianPDFReal 0 1 t ≠ 0 :=
    (gaussianPDFReal_pos 0 1 t (by norm_num)).ne'
  rw [Real.log_inv, Real.log_div hdensity ht.ne']
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Real.log_mul (inv_ne_zero hsqrtPos.ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

private theorem
    log_inv_standardGaussianDensity_div_isEquivalent_sq :
    Asymptotics.IsEquivalent atTop
      (fun t : ℝ ↦
        Real.log ((gaussianPDFReal 0 1 t / t)⁻¹))
      (fun t : ℝ ↦ t ^ 2 / 2) := by
  have hdenom :
      ∀ᶠ t : ℝ in atTop, t ^ 2 / 2 ≠ 0 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    exact div_ne_zero (pow_ne_zero 2 ht) (by norm_num)
  apply (Asymptotics.isEquivalent_iff_tendsto_one hdenom).2
  have hlogDiv :
      Tendsto (fun t : ℝ ↦ Real.log t / t)
        atTop (𝓝 0) := by
    simpa using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlogDivSq :
      Tendsto (fun t : ℝ ↦ Real.log t / t ^ 2)
        atTop (𝓝 0) := by
    have hproduct :
        Tendsto (fun t : ℝ ↦
          (Real.log t / t) * t⁻¹) atTop (𝓝 0) := by
      simpa using hlogDiv.mul tendsto_inv_atTop_zero
    apply hproduct.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  have hconstantDivSq :
      Tendsto (fun t : ℝ ↦
        Real.log (Real.sqrt (2 * Real.pi)) / t ^ 2)
        atTop (𝓝 0) := by
    have hinvSq :
        Tendsto (fun t : ℝ ↦ (t ^ 2)⁻¹)
          atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop two_ne_zero)
    simpa only [div_eq_mul_inv, mul_zero] using
      hinvSq.const_mul
        (Real.log (Real.sqrt (2 * Real.pi)))
  have hsmall :
      Tendsto (fun t : ℝ ↦
        2 * (Real.log t / t ^ 2) +
          2 * (Real.log (Real.sqrt (2 * Real.pi)) / t ^ 2))
        atTop (𝓝 0) := by
    simpa using
      (hlogDivSq.const_mul 2).add
        (hconstantDivSq.const_mul 2)
  have hratio :
      Tendsto (fun t : ℝ ↦
        1 + (2 * (Real.log t / t ^ 2) +
          2 * (Real.log (Real.sqrt (2 * Real.pi)) / t ^ 2)))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  change
    1 + (2 * (Real.log t / t ^ 2) +
        2 * (Real.log (Real.sqrt (2 * Real.pi)) / t ^ 2)) =
      Real.log ((gaussianPDFReal 0 1 t / t)⁻¹) /
        (t ^ 2 / 2)
  rw [log_inv_standardGaussianDensity_div ht]
  field_simp [ht.ne']
  ring

/-- On the Gaussian upper-tail scale,
`log (1 / barPhi(t))` is asymptotic to `t² / 2`. -/
theorem log_inv_standardGaussianUpperTail_isEquivalent_sq :
    Asymptotics.IsEquivalent atTop
      (fun t : ℝ ↦
        Real.log (1 / standardGaussianUpperTail t))
      (fun t : ℝ ↦ t ^ 2 / 2) := by
  have htailWithin :
      Tendsto standardGaussianUpperTail atTop
        (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_standardGaussianUpperTail_atTop,
        Eventually.of_forall
          (fun t ↦ standardGaussianUpperTail_pos t)⟩
  have htailInv :
      Tendsto standardGaussianUpperTail⁻¹
        atTop atTop :=
    htailWithin.inv_tendsto_nhdsGT_zero
  have hinvEquivalent :=
    standardGaussianUpperTail_isEquivalent_density_div.inv
  have hdensityInv :
      Tendsto (fun t : ℝ ↦
        gaussianPDFReal 0 1 t / t)⁻¹
        atTop atTop :=
    hinvEquivalent.tendsto_atTop htailInv
  have hlog :
      Asymptotics.IsEquivalent atTop
        (fun t : ℝ ↦
          Real.log (1 / standardGaussianUpperTail t))
        (fun t : ℝ ↦
          Real.log ((gaussianPDFReal 0 1 t / t)⁻¹)) := by
    simpa only [Pi.inv_apply, one_div] using
      hinvEquivalent.log hdensityInv
  exact hlog.trans
    log_inv_standardGaussianDensity_div_isEquivalent_sq

/-- The logarithmic upper-tail scale recovers the Gaussian threshold:
`sqrt (2 log (1 / barPhi(t))) / t` tends to one. -/
theorem tendsto_sqrt_two_mul_log_inv_standardGaussianUpperTail_div :
    Tendsto (fun t : ℝ ↦
      Real.sqrt
          (2 * Real.log (1 / standardGaussianUpperTail t)) / t)
      atTop (𝓝 1) := by
  have hdenom :
      ∀ᶠ t : ℝ in atTop, t ^ 2 / 2 ≠ 0 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    exact div_ne_zero (pow_ne_zero 2 ht) (by norm_num)
  have hratio :=
    (Asymptotics.isEquivalent_iff_tendsto_one hdenom).1
      log_inv_standardGaussianUpperTail_isEquivalent_sq
  have hinner :
      Tendsto (fun t : ℝ ↦
        2 * Real.log (1 / standardGaussianUpperTail t) / t ^ 2)
        atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    change
      Real.log (1 / standardGaussianUpperTail t) /
          (t ^ 2 / 2) =
        2 * Real.log (1 / standardGaussianUpperTail t) / t ^ 2
    field_simp [ht]
  have hsqrt :
      Tendsto (fun t : ℝ ↦
        Real.sqrt
          (2 * Real.log (1 / standardGaussianUpperTail t) / t ^ 2))
        atTop (𝓝 1) := by
    simpa using hinner.sqrt
  apply hsqrt.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htailPos : 0 < standardGaussianUpperTail t :=
    standardGaussianUpperTail_pos t
  have hone :
      1 ≤ 1 / standardGaussianUpperTail t := by
    rw [le_div_iff₀ htailPos]
    simpa using (standardGaussianUpperTail_lt_one t).le
  have hlogNonneg :
      0 ≤ Real.log (1 / standardGaussianUpperTail t) :=
    Real.log_nonneg hone
  rw [Real.sqrt_div (mul_nonneg (by norm_num) hlogNonneg)]
  rw [Real.sqrt_sq ht.le]

/-- On the open probability interval, the upper quantile is asymptotic to
`sqrt (2 log (1 / α))` as `α` tends to zero. -/
theorem standardGaussianUpperQuantile_isEquivalent_sqrt_log_inv :
    Asymptotics.IsEquivalent
      (atBot : Filter (Ioo (0 : ℝ) 1))
      standardGaussianUpperQuantile
      (fun α : Ioo (0 : ℝ) 1 ↦
        Real.sqrt (2 * Real.log (1 / (α : ℝ)))) := by
  have hratio :
      Tendsto (fun α : Ioo (0 : ℝ) 1 ↦
        Real.sqrt
            (2 * Real.log
              (1 / standardGaussianUpperTail
                (standardGaussianUpperQuantile α))) /
          standardGaussianUpperQuantile α)
        atBot (𝓝 1) :=
    tendsto_sqrt_two_mul_log_inv_standardGaussianUpperTail_div.comp
      tendsto_standardGaussianUpperQuantile_atBot
  have hratio' :
      Tendsto (fun α : Ioo (0 : ℝ) 1 ↦
        Real.sqrt (2 * Real.log (1 / (α : ℝ))) /
          standardGaussianUpperQuantile α)
        atBot (𝓝 1) := by
    apply hratio.congr'
    exact Eventually.of_forall fun α ↦ by
      change
        Real.sqrt
              (2 * Real.log
                (1 / standardGaussianUpperTail
                  (standardGaussianUpperQuantile α))) /
            standardGaussianUpperQuantile α =
          Real.sqrt (2 * Real.log (1 / (α : ℝ))) /
            standardGaussianUpperQuantile α
      rw [standardGaussianUpperTail_quantile]
  exact (Asymptotics.isEquivalent_of_tendsto_one hratio').symm

/-- Mills' ratio gives the first factorization in Proposition 5.27:
`U(α)` is asymptotic to `α` times its upper quantile. -/
theorem gaussianIsoperimetric_isEquivalent_probability_mul_quantile :
    Asymptotics.IsEquivalent
      (atBot : Filter (Ioo (0 : ℝ) 1))
      (fun α : Ioo (0 : ℝ) 1 ↦
        gaussianIsoperimetric
          ⟨(α : ℝ), α.2.1.le, α.2.2.le⟩)
      (fun α : Ioo (0 : ℝ) 1 ↦
        (α : ℝ) * standardGaussianUpperQuantile α) := by
  have hmills :=
    standardGaussianUpperTail_isEquivalent_density_div.symm.comp_tendsto
      tendsto_standardGaussianUpperQuantile_atBot
  have hquantileRefl :
      Asymptotics.IsEquivalent
        (atBot : Filter (Ioo (0 : ℝ) 1))
        standardGaussianUpperQuantile
        standardGaussianUpperQuantile :=
    Asymptotics.IsEquivalent.refl
  have hmul := hmills.mul hquantileRefl
  refine (hmul.congr_left ?_).congr_right ?_
  · filter_upwards
      [tendsto_standardGaussianUpperQuantile_atBot.eventually_gt_atTop 0]
      with α hα
    change
      (gaussianPDFReal 0 1
          (standardGaussianUpperQuantile α) /
          standardGaussianUpperQuantile α) *
          standardGaussianUpperQuantile α =
        gaussianIsoperimetric
          ⟨(α : ℝ), α.2.1.le, α.2.2.le⟩
    rw [div_mul_cancel₀ _ hα.ne']
    exact
      (gaussianIsoperimetric_apply_of_mem_Ioo
        ⟨(α : ℝ), α.2.1.le, α.2.2.le⟩ α.2).symm
  · exact Eventually.of_forall fun α ↦ by
      change
        standardGaussianUpperTail
            (standardGaussianUpperQuantile α) *
            standardGaussianUpperQuantile α =
          (α : ℝ) * standardGaussianUpperQuantile α
      rw [standardGaussianUpperTail_quantile]

/-- Proposition 5.27: on the natural open probability domain, where `atBot`
means `α → 0⁺`, the Gaussian isoperimetric function satisfies
`U(α) ~ α sqrt (2 log (1 / α))`. -/
theorem gaussianIsoperimetric_isEquivalent_atBot :
    Asymptotics.IsEquivalent
      (atBot : Filter (Ioo (0 : ℝ) 1))
      (fun α : Ioo (0 : ℝ) 1 ↦
        gaussianIsoperimetric
          ⟨(α : ℝ), α.2.1.le, α.2.2.le⟩)
      (fun α : Ioo (0 : ℝ) 1 ↦
        (α : ℝ) *
          Real.sqrt (2 * Real.log (1 / (α : ℝ)))) := by
  apply
    gaussianIsoperimetric_isEquivalent_probability_mul_quantile.trans
  exact
    (Asymptotics.IsEquivalent.refl :
      Asymptotics.IsEquivalent
        (atBot : Filter (Ioo (0 : ℝ) 1))
        (fun α : Ioo (0 : ℝ) 1 ↦ (α : ℝ))
        (fun α : Ioo (0 : ℝ) 1 ↦ (α : ℝ))).mul
      standardGaussianUpperQuantile_isEquivalent_sqrt_log_inv

end FABL
