/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.GaussianIsoperimetric
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Order.ExtendFrom

/-!
# Concavity of the Gaussian isoperimetric function

Book item: Exercise 5.43.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Interval

namespace FABL

private theorem continuous_standardGaussianDensity :
    Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

private theorem standardGaussianDensity_formula (t : ℝ) :
    gaussianPDFReal 0 1 t =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  (congr 2; ring_nf)

private theorem hasDerivAt_standardGaussianDensity (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-t * gaussianPDFReal 0 1 t) t := by
  rw [show
      gaussianPDFReal 0 1 =
        fun x : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2) by
    funext x
    exact standardGaussianDensity_formula x]
  have hinner :
      HasDerivAt (fun x : ℝ ↦ -(1 / 2 : ℝ) * x ^ 2)
        (-t) t := by
    exact
      ((hasDerivAt_pow 2 t).const_mul
        (-(1 / 2 : ℝ))).congr_deriv (by ring_nf)
  exact (hinner.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv
    (by ring_nf)

private theorem standardGaussianDensity_neg (t : ℝ) :
    gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
  rw [standardGaussianDensity_formula,
    standardGaussianDensity_formula]
  congr 1
  ring_nf

private theorem tendsto_standardGaussianDensity_atTop :
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
    exact standardGaussianDensity_formula x]
  simpa only [mul_zero] using hmul

private theorem tendsto_standardGaussianDensity_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (𝓝 0) := by
  have h :=
    tendsto_standardGaussianDensity_atTop.comp
      tendsto_neg_atBot_atTop
  have heven :
      gaussianPDFReal 0 1 ∘ Neg.neg =
        gaussianPDFReal 0 1 := by
    funext x
    exact standardGaussianDensity_neg x
  rw [heven] at h
  exact h

private theorem standardGaussianUpperTail_eq_integral_Ioi (t : ℝ) :
    standardGaussianUpperTail t =
      ∫ z : ℝ in Ioi t, gaussianPDFReal 0 1 z := by
  rw [standardGaussianUpperTail_eq_measureReal_Ioi, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num) (Ioi t),
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi fun z _ ↦
    gaussianPDFReal_nonneg 0 1 z

private theorem standardGaussianUpperTail_eq_anchor_integral (t : ℝ) :
    standardGaussianUpperTail t =
      standardGaussianUpperTail 0 -
        ∫ z : ℝ in (0 : ℝ)..t, gaussianPDFReal 0 1 z := by
  rw [standardGaussianUpperTail_eq_integral_Ioi,
    standardGaussianUpperTail_eq_integral_Ioi]
  have h :=
    intervalIntegral.integral_Ioi_sub_Ioi'
      (a := (0 : ℝ)) (b := t)
      (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn
  linarith

/-- The derivative of the standard Gaussian upper tail is minus its density. -/
theorem hasDerivAt_standardGaussianUpperTail (t : ℝ) :
    HasDerivAt standardGaussianUpperTail
      (-gaussianPDFReal 0 1 t) t := by
  have hfun :
      standardGaussianUpperTail =
        fun u ↦ standardGaussianUpperTail 0 -
          ∫ z : ℝ in (0 : ℝ)..u, gaussianPDFReal 0 1 z := by
    funext u
    exact standardGaussianUpperTail_eq_anchor_integral u
  rw [hfun]
  exact
    (continuous_standardGaussianDensity.integral_hasStrictDerivAt
      0 t).hasDerivAt.const_sub (standardGaussianUpperTail 0)

private noncomputable def standardGaussianUpperQuantileReal
    (α : ℝ) : ℝ :=
  if hα : α ∈ Ioo (0 : ℝ) 1 then
    standardGaussianUpperQuantile ⟨α, hα⟩
  else
    0

private theorem standardGaussianUpperQuantileReal_eq
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    standardGaussianUpperQuantileReal α =
      standardGaussianUpperQuantile ⟨α, hα⟩ := by
  rw [standardGaussianUpperQuantileReal, dif_pos hα]

private theorem continuous_standardGaussianUpperQuantile :
    Continuous standardGaussianUpperQuantile := by
  change Continuous
    (fun α : Ioo (0 : ℝ) 1 ↦
      ((standardGaussianUpperTailOrderIso.symm α : ℝᵒᵈ) : ℝ))
  exact standardGaussianUpperTailOrderIso.symm.continuous

private theorem continuousOn_standardGaussianUpperQuantileReal :
    ContinuousOn standardGaussianUpperQuantileReal
      (Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  convert continuous_standardGaussianUpperQuantile using 1
  funext α
  exact standardGaussianUpperQuantileReal_eq α.2

private theorem continuousAt_standardGaussianUpperQuantileReal
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt standardGaussianUpperQuantileReal α :=
  (continuousOn_standardGaussianUpperQuantileReal α hα).continuousAt
    (isOpen_Ioo.mem_nhds hα)

private theorem tendsto_standardGaussianUpperQuantileReal_zero :
    Tendsto standardGaussianUpperQuantileReal
      (𝓝[>] (0 : ℝ)) atTop := by
  apply (tendsto_comp_coe_Ioo_atBot (show (0 : ℝ) < 1 by norm_num)).mp
  rw [show
      (fun α : Ioo (0 : ℝ) 1 ↦
        standardGaussianUpperQuantileReal α) =
        standardGaussianUpperQuantile by
    funext α
    exact standardGaussianUpperQuantileReal_eq α.2]
  have h :
      Tendsto standardGaussianUpperQuantile atBot atTop :=
    standardGaussianUpperTailOrderIso.symm.tendsto_atBot
  exact h

private theorem tendsto_standardGaussianUpperQuantileReal_one :
    Tendsto standardGaussianUpperQuantileReal
      (𝓝[<] (1 : ℝ)) atBot := by
  apply (tendsto_comp_coe_Ioo_atTop (show (0 : ℝ) < 1 by norm_num)).mp
  rw [show
      (fun α : Ioo (0 : ℝ) 1 ↦
        standardGaussianUpperQuantileReal α) =
        standardGaussianUpperQuantile by
    funext α
    exact standardGaussianUpperQuantileReal_eq α.2]
  have h :
      Tendsto standardGaussianUpperQuantile atTop atBot :=
    standardGaussianUpperTailOrderIso.symm.tendsto_atTop
  exact h

private noncomputable def gaussianIsoperimetricInterior
    (α : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (standardGaussianUpperQuantileReal α)

private theorem continuousOn_gaussianIsoperimetricInterior :
    ContinuousOn gaussianIsoperimetricInterior
      (Ioo (0 : ℝ) 1) := by
  exact continuous_standardGaussianDensity.comp_continuousOn'
    continuousOn_standardGaussianUpperQuantileReal

private theorem tendsto_gaussianIsoperimetricInterior_zero :
    Tendsto gaussianIsoperimetricInterior
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_standardGaussianDensity_atTop.comp
    tendsto_standardGaussianUpperQuantileReal_zero

private theorem tendsto_gaussianIsoperimetricInterior_one :
    Tendsto gaussianIsoperimetricInterior
      (𝓝[<] (1 : ℝ)) (𝓝 0) :=
  tendsto_standardGaussianDensity_atBot.comp
    tendsto_standardGaussianUpperQuantileReal_one

/-- The ambient-real realization of the Gaussian isoperimetric function,
obtained by continuously extending its interior formula to `[0,1]`. -/
noncomputable def gaussianIsoperimetricReal (α : ℝ) : ℝ :=
  extendFrom (Ioo (0 : ℝ) 1) gaussianIsoperimetricInterior α

/-- The ambient-real Gaussian isoperimetric function vanishes at zero. -/
@[simp] theorem gaussianIsoperimetricReal_zero :
    gaussianIsoperimetricReal 0 = 0 := by
  rw [gaussianIsoperimetricReal,
    eq_lim_at_left_extendFrom_Ioo (show (0 : ℝ) < 1 by norm_num)
      tendsto_gaussianIsoperimetricInterior_zero]

/-- The ambient-real Gaussian isoperimetric function vanishes at one. -/
@[simp] theorem gaussianIsoperimetricReal_one :
    gaussianIsoperimetricReal 1 = 0 := by
  rw [gaussianIsoperimetricReal,
    eq_lim_at_right_extendFrom_Ioo (show (0 : ℝ) < 1 by norm_num)
      tendsto_gaussianIsoperimetricInterior_one]

/-- On the open unit interval, the ambient-real function is the Gaussian
density at the upper-tail quantile. -/
theorem gaussianIsoperimetricReal_apply_of_mem_Ioo
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    gaussianIsoperimetricReal α =
      gaussianPDFReal 0 1
        (standardGaussianUpperQuantile ⟨α, hα⟩) := by
  rw [gaussianIsoperimetricReal,
    extendFrom_extends continuousOn_gaussianIsoperimetricInterior α hα,
    gaussianIsoperimetricInterior,
    standardGaussianUpperQuantileReal_eq hα]

/-- The ambient-real realization agrees with Definition 5.26 throughout
the closed unit interval. -/
theorem gaussianIsoperimetricReal_eq_gaussianIsoperimetric
    (α : unitInterval) :
    gaussianIsoperimetricReal α = gaussianIsoperimetric α := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc α.2 with hα | hα | hα
  · have hzero : α = (0 : unitInterval) := Subtype.ext hα
    subst α
    simp
  · have hone : α = (1 : unitInterval) := Subtype.ext hα
    subst α
    simp
  · rw [gaussianIsoperimetricReal_apply_of_mem_Ioo hα,
      gaussianIsoperimetric_apply_of_mem_Ioo α hα]

/-- The ambient-real Gaussian isoperimetric function is continuous on
the closed unit interval. -/
theorem continuousOn_gaussianIsoperimetricReal :
    ContinuousOn gaussianIsoperimetricReal
      (Icc (0 : ℝ) 1) := by
  exact continuousOn_Icc_extendFrom_Ioo
    continuousOn_gaussianIsoperimetricInterior
    tendsto_gaussianIsoperimetricInterior_zero
    tendsto_gaussianIsoperimetricInterior_one

/-- The Gaussian isoperimetric function is positive in the open unit
interval. -/
theorem gaussianIsoperimetricReal_pos
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    0 < gaussianIsoperimetricReal α := by
  rw [gaussianIsoperimetricReal_apply_of_mem_Ioo hα]
  exact gaussianPDFReal_pos 0 1 _ (by norm_num)

private theorem hasDerivAt_standardGaussianUpperQuantileReal
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt standardGaussianUpperQuantileReal
      (-(gaussianIsoperimetricReal α)⁻¹) α := by
  have hleft :
      ∀ᶠ β in 𝓝 α,
        standardGaussianUpperTail
            (standardGaussianUpperQuantileReal β) =
          β := by
    filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
    rw [standardGaussianUpperQuantileReal_eq hβ,
      standardGaussianUpperTail_quantile]
  have hpdf :
      gaussianPDFReal 0 1
          (standardGaussianUpperQuantileReal α) ≠
        0 := by
    exact ne_of_gt (gaussianPDFReal_pos 0 1 _ (by norm_num))
  have hinverse :=
    (hasDerivAt_standardGaussianUpperTail
      (standardGaussianUpperQuantileReal α)).of_local_left_inverse
        (continuousAt_standardGaussianUpperQuantileReal hα)
        (neg_ne_zero.mpr hpdf) hleft
  rw [gaussianIsoperimetricReal_apply_of_mem_Ioo hα]
  simpa only [standardGaussianUpperQuantileReal_eq hα,
    inv_neg] using hinverse

private theorem hasDerivAt_gaussianIsoperimetricInterior
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gaussianIsoperimetricInterior
      (standardGaussianUpperQuantile ⟨α, hα⟩) α := by
  have hquantile :=
    hasDerivAt_standardGaussianUpperQuantileReal hα
  have hdensity :=
    (hasDerivAt_standardGaussianDensity
      (standardGaussianUpperQuantileReal α)).comp α hquantile
  have hpdf :
      gaussianPDFReal 0 1
          (standardGaussianUpperQuantileReal α) ≠
        0 := by
    exact ne_of_gt (gaussianPDFReal_pos 0 1 _ (by norm_num))
  change HasDerivAt
    (fun β : ℝ ↦
      gaussianPDFReal 0 1
        (standardGaussianUpperQuantileReal β))
    (standardGaussianUpperQuantile ⟨α, hα⟩) α
  refine hdensity.congr_deriv ?_
  rw [standardGaussianUpperQuantileReal_eq hα] at hpdf
  rw [standardGaussianUpperQuantileReal_eq hα,
    gaussianIsoperimetricReal_apply_of_mem_Ioo hα]
  field_simp [hpdf]

/-- In the open unit interval, the first derivative of the Gaussian
isoperimetric function is its upper-tail quantile. -/
theorem hasDerivAt_gaussianIsoperimetricReal
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gaussianIsoperimetricReal
      (standardGaussianUpperQuantile ⟨α, hα⟩) α := by
  apply (hasDerivAt_gaussianIsoperimetricInterior hα).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
  exact extendFrom_extends
    continuousOn_gaussianIsoperimetricInterior β hβ

/-- Exercise 5.43: on `0 < α < 1`, the Gaussian isoperimetric function
satisfies `U''(α) = -1 / U(α)`. -/
theorem gaussianIsoperimetric_second_derivative
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (deriv^[2]) gaussianIsoperimetricReal α =
      -1 / gaussianIsoperimetricReal α := by
  have hderiv :
      HasDerivAt (deriv gaussianIsoperimetricReal)
        (-(gaussianIsoperimetricReal α)⁻¹) α := by
    apply
      (hasDerivAt_standardGaussianUpperQuantileReal hα).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hα] with β hβ
    rw [standardGaussianUpperQuantileReal_eq hβ]
    exact (hasDerivAt_gaussianIsoperimetricReal hβ).deriv
  change deriv (deriv gaussianIsoperimetricReal) α =
    -1 / gaussianIsoperimetricReal α
  simpa only [div_eq_mul_inv, neg_mul, one_mul] using hderiv.deriv

/-- Exercise 5.43: the Gaussian isoperimetric function, with its zero
endpoint extension, is concave on `[0,1]`. -/
theorem concaveOn_gaussianIsoperimetricReal :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) gaussianIsoperimetricReal := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (convex_Icc (0 : ℝ) 1)
    continuousOn_gaussianIsoperimetricReal
    (f' := standardGaussianUpperQuantileReal)
    (f'' := fun α ↦ -(gaussianIsoperimetricReal α)⁻¹)
  · intro α hα
    rw [interior_Icc] at hα
    rw [standardGaussianUpperQuantileReal_eq hα]
    exact (hasDerivAt_gaussianIsoperimetricReal hα).hasDerivWithinAt
  · intro α hα
    rw [interior_Icc] at hα
    exact
      (hasDerivAt_standardGaussianUpperQuantileReal hα).hasDerivWithinAt
  · intro α hα
    rw [interior_Icc] at hα
    exact neg_nonpos.mpr
      (inv_nonneg.mpr (gaussianIsoperimetricReal_pos hα).le)

end FABL
