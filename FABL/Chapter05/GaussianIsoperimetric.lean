/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.UnitInterval

/-!
# The Gaussian isoperimetric function

Book items:
- Definition 5.26.
- Gaussian stop-loss support identity for Exercise 5.44.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

@[expose] public section

namespace FABL

private instance standardGaussianIsOpenPosMeasure :
    Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num)).isOpenPosMeasure

private theorem standardGaussianCDF_leftLim (x : ℝ) :
    Function.leftLim (cdf (gaussianReal 0 1)) x =
      cdf (gaussianReal 0 1) x := by
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hzero : (cdf (gaussianReal 0 1)).measure {x} = 0 := by
    rw [measure_cdf]
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hzero
  exact le_antisymm
    ((monotone_cdf (gaussianReal 0 1)).leftLim_le le_rfl)
    (sub_nonpos.mp hzero)

private theorem continuous_standardGaussianCDF :
    Continuous (cdf (gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  exact standardGaussianCDF_leftLim x

private theorem strictMono_standardGaussianCDF :
    StrictMono (cdf (gaussianReal 0 1)) := by
  intro x y hxy
  rw [cdf_eq_real, cdf_eq_real, ← Iic_union_Ioc_eq_Iic hxy.le,
    measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  have hIocPosENN :
      0 < (gaussianReal 0 1) (Ioc x y) :=
    ((Measure.measure_Ioo_pos (gaussianReal 0 1)).2 hxy).trans_le
      (measure_mono Ioo_subset_Ioc_self)
  have hIocPos :
      0 < (gaussianReal 0 1).real (Ioc x y) :=
    lt_of_le_of_ne measureReal_nonneg
      (Ne.symm ((measureReal_ne_zero_iff).2 hIocPosENN.ne'))
  linarith

/-- The standard Gaussian upper-tail probability
`\bar Φ(t) = Pr[Z > t]`. -/
noncomputable def standardGaussianUpperTail (t : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) t

/-- The CDF complement is the real mass of the strict upper ray. -/
theorem standardGaussianUpperTail_eq_measureReal_Ioi (t : ℝ) :
    standardGaussianUpperTail t =
      (gaussianReal 0 1).real (Ioi t) := by
  rw [standardGaussianUpperTail, cdf_eq_real,
    ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic]

/-- Every finite threshold has positive standard Gaussian upper tail. -/
theorem standardGaussianUpperTail_pos (t : ℝ) :
    0 < standardGaussianUpperTail t := by
  rw [standardGaussianUpperTail]
  have hlt :
      cdf (gaussianReal 0 1) t < 1 :=
    (strictMono_standardGaussianCDF (lt_add_one t)).trans_le
      (cdf_le_one (gaussianReal 0 1) (t + 1))
  linarith

/-- Every finite threshold has standard Gaussian upper tail strictly below one. -/
theorem standardGaussianUpperTail_lt_one (t : ℝ) :
    standardGaussianUpperTail t < 1 := by
  rw [standardGaussianUpperTail]
  have hpos :
      0 < cdf (gaussianReal 0 1) t :=
    (cdf_nonneg (gaussianReal 0 1) (t - 1)).trans_lt
      (strictMono_standardGaussianCDF (sub_one_lt t))
  linarith

/-- The standard Gaussian upper tail is strictly decreasing. -/
theorem standardGaussianUpperTail_strictAnti :
    StrictAnti standardGaussianUpperTail := by
  intro x y hxy
  rw [standardGaussianUpperTail, standardGaussianUpperTail]
  linarith [strictMono_standardGaussianCDF hxy]

/-- The standard Gaussian upper tail is continuous. -/
theorem continuous_standardGaussianUpperTail :
    Continuous standardGaussianUpperTail :=
  continuous_const.sub continuous_standardGaussianCDF

/-- The standard Gaussian upper tail tends to zero at positive infinity. -/
theorem tendsto_standardGaussianUpperTail_atTop :
    Tendsto standardGaussianUpperTail atTop (𝓝 0) := by
  change
    Tendsto (fun x : ℝ ↦ 1 - cdf (gaussianReal 0 1) x)
      atTop (𝓝 0)
  simpa only [sub_self] using
    (tendsto_cdf_atTop (gaussianReal 0 1)).const_sub 1

/-- The standard Gaussian upper tail tends to one at negative infinity. -/
theorem tendsto_standardGaussianUpperTail_atBot :
    Tendsto standardGaussianUpperTail atBot (𝓝 1) := by
  change
    Tendsto (fun x : ℝ ↦ 1 - cdf (gaussianReal 0 1) x)
      atBot (𝓝 1)
  simpa only [sub_zero] using
    (tendsto_cdf_atBot (gaussianReal 0 1)).const_sub 1

private theorem standardGaussianCDF_neg (t : ℝ) :
    cdf (gaussianReal 0 1) (-t) = standardGaussianUpperTail t := by
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hmap :
      (gaussianReal 0 1).map (fun x : ℝ ↦ -x) =
        gaussianReal 0 1 := by
    simpa using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  calc
    cdf (gaussianReal 0 1) (-t) =
        (gaussianReal 0 1).real (Iic (-t)) := by
      rw [cdf_eq_real]
    _ = ((gaussianReal 0 1).map (fun x : ℝ ↦ -x)).real
        (Iic (-t)) := by rw [hmap]
    _ = (gaussianReal 0 1).real
        ((fun x : ℝ ↦ -x) ⁻¹' Iic (-t)) := by
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    _ = (gaussianReal 0 1).real (Ici t) := by
      congr 1
      ext x
      simp only [mem_preimage, mem_Iic, mem_Ici]
      constructor <;> intro hx <;> linarith
    _ = (gaussianReal 0 1).real (Ioi t) := by
      simp only [measureReal_def,
        measure_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1)).symm]
    _ = standardGaussianUpperTail t :=
      (standardGaussianUpperTail_eq_measureReal_Ioi t).symm

/-- Gaussian reflection exchanges an upper tail with its complement. -/
theorem standardGaussianUpperTail_neg (t : ℝ) :
    standardGaussianUpperTail (-t) =
      1 - standardGaussianUpperTail t := by
  calc
    standardGaussianUpperTail (-t) =
        1 - cdf (gaussianReal 0 1) (-t) := rfl
    _ = 1 - standardGaussianUpperTail t := by
      rw [standardGaussianCDF_neg]

/-- The standard Gaussian upper tail, restricted to its exact open-unit range. -/
noncomputable def standardGaussianUpperTailOpen
    (t : ℝᵒᵈ) : Ioo (0 : ℝ) 1 :=
  ⟨standardGaussianUpperTail t,
    standardGaussianUpperTail_pos t,
    standardGaussianUpperTail_lt_one t⟩

/-- Reverse-ordered thresholds map strictly increasingly to upper-tail probabilities. -/
theorem strictMono_standardGaussianUpperTailOpen :
    StrictMono standardGaussianUpperTailOpen := by
  intro x y hxy
  exact standardGaussianUpperTail_strictAnti hxy

/-- Every probability strictly between zero and one is a standard Gaussian upper tail. -/
theorem surjective_standardGaussianUpperTailOpen :
    Function.Surjective standardGaussianUpperTailOpen := by
  intro α
  have hbelow :
      ∃ x : ℝ, standardGaussianUpperTail x ≤ (α : ℝ) := by
    have heventually :
        ∀ᶠ x in atTop, standardGaussianUpperTail x < (α : ℝ) :=
      tendsto_standardGaussianUpperTail_atTop.eventually
        (Iio_mem_nhds α.2.1)
    obtain ⟨x, hx⟩ := heventually.exists
    exact ⟨x, hx.le⟩
  have habove :
      ∃ x : ℝ, (α : ℝ) ≤ standardGaussianUpperTail x := by
    have heventually :
        ∀ᶠ x in atBot, (α : ℝ) < standardGaussianUpperTail x :=
      tendsto_standardGaussianUpperTail_atBot.eventually
        (Ioi_mem_nhds α.2.2)
    obtain ⟨x, hx⟩ := heventually.exists
    exact ⟨x, hx.le⟩
  obtain ⟨x, hx⟩ :=
    mem_range_of_exists_le_of_exists_ge
      continuous_standardGaussianUpperTail hbelow habove
  refine ⟨OrderDual.toDual x, Subtype.ext ?_⟩
  exact hx

/-- The order isomorphism from reverse-ordered thresholds to Gaussian
upper-tail probabilities in `(0,1)`. -/
noncomputable def standardGaussianUpperTailOrderIso :
    ℝᵒᵈ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective standardGaussianUpperTailOpen
    strictMono_standardGaussianUpperTailOpen
    surjective_standardGaussianUpperTailOpen

/-- The Gaussian upper-tail order isomorphism has the expected underlying function. -/
@[simp] theorem standardGaussianUpperTailOrderIso_apply (t : ℝᵒᵈ) :
    (standardGaussianUpperTailOrderIso t : ℝ) =
      standardGaussianUpperTail t := by
  rfl

/-- The unique threshold whose standard Gaussian upper tail is `α`. -/
noncomputable def standardGaussianUpperQuantile
    (α : Ioo (0 : ℝ) 1) : ℝ :=
  ((standardGaussianUpperTailOrderIso.symm α : ℝᵒᵈ) : ℝ)

/-- Taking the upper tail of its quantile returns the original probability. -/
theorem standardGaussianUpperTail_quantile
    (α : Ioo (0 : ℝ) 1) :
    standardGaussianUpperTail (standardGaussianUpperQuantile α) = α := by
  have h :=
    congrArg Subtype.val
      (standardGaussianUpperTailOrderIso.apply_symm_apply α)
  simpa only [standardGaussianUpperTailOrderIso_apply,
    standardGaussianUpperQuantile] using h

/-- Taking the quantile of a finite threshold's upper tail returns the threshold. -/
theorem standardGaussianUpperQuantile_upperTail (t : ℝ) :
    standardGaussianUpperQuantile
        ⟨standardGaussianUpperTail t,
          standardGaussianUpperTail_pos t,
          standardGaussianUpperTail_lt_one t⟩ =
      t := by
  let α : Ioo (0 : ℝ) 1 :=
    ⟨standardGaussianUpperTail t,
      standardGaussianUpperTail_pos t,
      standardGaussianUpperTail_lt_one t⟩
  have hα :
      α = standardGaussianUpperTailOrderIso (OrderDual.toDual t) := by
    apply Subtype.ext
    change standardGaussianUpperTail t = standardGaussianUpperTail t
    rfl
  change standardGaussianUpperQuantile α = t
  rw [hα]
  change
    (standardGaussianUpperTailOrderIso.symm
      (standardGaussianUpperTailOrderIso (OrderDual.toDual t)) : ℝᵒᵈ) =
      OrderDual.toDual t
  exact standardGaussianUpperTailOrderIso.symm_apply_apply
    (OrderDual.toDual t)

/-- Complementary upper-tail probabilities have opposite quantiles. -/
theorem standardGaussianUpperQuantile_one_sub
    (α : Ioo (0 : ℝ) 1) :
    standardGaussianUpperQuantile
        ⟨1 - (α : ℝ), Set.Ioo.one_sub_mem α.2⟩ =
      -standardGaussianUpperQuantile α := by
  apply standardGaussianUpperTail_strictAnti.injective
  calc
    standardGaussianUpperTail
        (standardGaussianUpperQuantile
          ⟨1 - (α : ℝ), Set.Ioo.one_sub_mem α.2⟩) =
        (⟨1 - (α : ℝ), Set.Ioo.one_sub_mem α.2⟩ :
          Ioo (0 : ℝ) 1) :=
      standardGaussianUpperTail_quantile _
    _ = 1 - (α : ℝ) := rfl
    _ = 1 - standardGaussianUpperTail
        (standardGaussianUpperQuantile α) := by
      rw [standardGaussianUpperTail_quantile]
    _ = standardGaussianUpperTail
        (-standardGaussianUpperQuantile α) :=
      (standardGaussianUpperTail_neg _).symm

private theorem standardGaussianDensity_neg (t : ℝ) :
    gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  congr 1
  ring_nf

private theorem standardGaussianDensity_le_peak (t : ℝ) :
    gaussianPDFReal 0 1 t ≤
      (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have hexp :
      Real.exp (-t ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-t ^ 2 / 2) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _

/-- Definition 5.26: the Gaussian isoperimetric function on `[0,1]`,
extended by zero at both endpoints. -/
noncomputable def gaussianIsoperimetric (α : unitInterval) : ℝ :=
  if hα : (α : ℝ) ∈ Ioo (0 : ℝ) 1 then
    gaussianPDFReal 0 1
      (standardGaussianUpperQuantile ⟨α, hα⟩)
  else
    0

/-- The Gaussian isoperimetric function vanishes at zero. -/
@[simp] theorem gaussianIsoperimetric_zero :
    gaussianIsoperimetric (0 : unitInterval) = 0 := by
  simp [gaussianIsoperimetric]

/-- The Gaussian isoperimetric function vanishes at one. -/
@[simp] theorem gaussianIsoperimetric_one :
    gaussianIsoperimetric (1 : unitInterval) = 0 := by
  simp [gaussianIsoperimetric]

/-- In the open unit interval, `U` is the density evaluated at the upper quantile. -/
theorem gaussianIsoperimetric_apply_of_mem_Ioo
    (α : unitInterval) (hα : (α : ℝ) ∈ Ioo (0 : ℝ) 1) :
    gaussianIsoperimetric α =
      gaussianPDFReal 0 1
        (standardGaussianUpperQuantile ⟨α, hα⟩) := by
  rw [gaussianIsoperimetric, dif_pos hα]

/-- The Gaussian isoperimetric function takes values in
`[0, 1 / sqrt (2π)]`. -/
theorem gaussianIsoperimetric_mem_Icc (α : unitInterval) :
    gaussianIsoperimetric α ∈
      Icc (0 : ℝ) (Real.sqrt (2 * Real.pi))⁻¹ := by
  by_cases hα : (α : ℝ) ∈ Ioo (0 : ℝ) 1
  · rw [gaussianIsoperimetric_apply_of_mem_Ioo α hα]
    exact ⟨gaussianPDFReal_nonneg 0 1 _, standardGaussianDensity_le_peak _⟩
  · rw [gaussianIsoperimetric, dif_neg hα]
    exact ⟨le_rfl, inv_nonneg.mpr (Real.sqrt_nonneg _)⟩

/-- The Gaussian isoperimetric function is symmetric about `1/2`. -/
theorem gaussianIsoperimetric_symm (α : unitInterval) :
    gaussianIsoperimetric (unitInterval.symm α) =
      gaussianIsoperimetric α := by
  by_cases hα : (α : ℝ) ∈ Ioo (0 : ℝ) 1
  · have hsymm :
        (unitInterval.symm α : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      exact Set.Ioo.one_sub_mem hα
    rw [gaussianIsoperimetric_apply_of_mem_Ioo _ hsymm,
      gaussianIsoperimetric_apply_of_mem_Ioo α hα]
    have hquantile :
        standardGaussianUpperQuantile
            ⟨(unitInterval.symm α : ℝ), hsymm⟩ =
          -standardGaussianUpperQuantile ⟨(α : ℝ), hα⟩ := by
      have hsub :
          (⟨(unitInterval.symm α : ℝ), hsymm⟩ :
              Ioo (0 : ℝ) 1) =
            ⟨1 - (α : ℝ), Set.Ioo.one_sub_mem hα⟩ := by
        apply Subtype.ext
        rfl
      rw [hsub]
      exact standardGaussianUpperQuantile_one_sub
        ⟨(α : ℝ), hα⟩
    rw [hquantile, standardGaussianDensity_neg]
  · have hsymm :
        ¬(unitInterval.symm α : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      intro hs
      apply hα
      exact Set.Ioo.mem_iff_one_sub_mem.mpr hs
    rw [gaussianIsoperimetric, dif_neg hsymm,
      gaussianIsoperimetric, dif_neg hα]

/-- The Gaussian stop-loss transform used in the sharp Level-1 argument. -/
noncomputable def standardGaussianStopLoss (t : ℝ) : ℝ :=
  ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1

private theorem integral_Ioi_mul_exp_neg_half_mul_sq (t : ℝ) :
    (∫ x : ℝ in Ioi t,
      x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  have hderiv :
      ∀ x ∈ Ici t,
        HasDerivAt
          (fun y : ℝ ↦ -Real.exp (-(1 / 2 : ℝ) * y ^ 2))
          (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) x := by
    intro x _
    have hinner :
        HasDerivAt
          (fun y : ℝ ↦ -(1 / 2 : ℝ) * y ^ 2)
          (-x) x := by
      exact
        ((hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))).congr_deriv
          (by norm_num; ring)
    exact hinner.exp.neg.congr_deriv (by ring)
  have hintegrable :
      IntegrableOn
        (fun x : ℝ ↦ x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (Ioi t) := by
    exact (integrable_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn
  have htendsto :
      Tendsto
        (fun x : ℝ ↦ -Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        atTop (𝓝 0) := by
    have hinner :
        Tendsto (fun x : ℝ ↦ -(1 / 2 : ℝ) * x ^ 2)
          atTop atBot :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
        (by norm_num)
    have hexp :
        Tendsto (fun x : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * x ^ 2))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hinner
    simpa only [neg_zero] using hexp.neg
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hintegrable htendsto
  simpa using h

private theorem integral_Ioi_mul_standardGaussianDensity (t : ℝ) :
    (∫ x : ℝ in Ioi t, gaussianPDFReal 0 1 x * x) =
      gaussianPDFReal 0 1 t := by
  rw [show
      (fun x : ℝ ↦ gaussianPDFReal 0 1 x * x) =
        fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
          (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    rw [show -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring]
  rw [integral_const_mul, integral_Ioi_mul_exp_neg_half_mul_sq,
    gaussianPDFReal]
  simp only [NNReal.coe_one, sub_zero, mul_one]
  rw [show -t ^ 2 / 2 = -(1 / 2 : ℝ) * t ^ 2 by ring]

private theorem integral_Ioi_standardGaussianDensity (t : ℝ) :
    (∫ x : ℝ in Ioi t, gaussianPDFReal 0 1 x) =
      standardGaussianUpperTail t := by
  rw [standardGaussianUpperTail_eq_measureReal_Ioi, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num) (Ioi t)]
  rw [ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioi fun x _ ↦
    gaussianPDFReal_nonneg 0 1 x

/-- For `Z ~ N(0,1)`,
`E[(Z-t)₊] = φ(t) - t \bar Φ(t)`. -/
theorem standardGaussianStopLoss_eq (t : ℝ) :
    standardGaussianStopLoss t =
      gaussianPDFReal 0 1 t -
        t * standardGaussianUpperTail t := by
  rw [standardGaussianStopLoss,
    integral_gaussianReal_eq_integral_smul (by norm_num)]
  change (∫ x : ℝ, gaussianPDFReal 0 1 x * (x - t)⁺) = _
  calc
    (∫ x : ℝ, gaussianPDFReal 0 1 x * (x - t)⁺) =
        ∫ x : ℝ in Ioi t,
          gaussianPDFReal 0 1 x * (x - t) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        by_cases hx : t < x
        · simp [hx, PosPart.posPart, sub_nonneg.mpr hx.le]
        · have hxle : x ≤ t := le_of_not_gt hx
          simp [hx, PosPart.posPart, sub_nonpos.mpr hxle]
    _ = (∫ x : ℝ in Ioi t, gaussianPDFReal 0 1 x * x) -
        t * ∫ x : ℝ in Ioi t, gaussianPDFReal 0 1 x := by
      have hfirst :
          IntegrableOn
            (fun x : ℝ ↦ gaussianPDFReal 0 1 x * x) (Ioi t) := by
        rw [show
            (fun x : ℝ ↦ gaussianPDFReal 0 1 x * x) =
              fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
                (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
          funext x
          simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
          rw [show -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
          ring]
        exact ((integrable_mul_exp_neg_mul_sq
          (b := (1 / 2 : ℝ)) (by norm_num)).const_mul _).integrableOn
      have hmass :
          IntegrableOn (gaussianPDFReal 0 1) (Ioi t) :=
        (integrable_gaussianPDFReal 0 1).integrableOn
      rw [show
          (fun x : ℝ ↦ gaussianPDFReal 0 1 x * (x - t)) =
            fun x ↦ gaussianPDFReal 0 1 x * x -
              t * gaussianPDFReal 0 1 x by
        funext x
        ring]
      rw [integral_sub hfirst (hmass.const_mul t),
        integral_const_mul]
    _ = gaussianPDFReal 0 1 t -
        t * standardGaussianUpperTail t := by
      rw [integral_Ioi_mul_standardGaussianDensity,
        integral_Ioi_standardGaussianDensity]

end FABL
