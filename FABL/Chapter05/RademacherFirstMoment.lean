/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter02.FKN
import FABL.Chapter03.LearningTheory.FourierEstimation
import FABL.Chapter05.BerryEsseenConsequences
import FABL.Chapter05.BerryEsseenIntervals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import ProbabilityApproximation.ChenShao.NonuniformBerryEsseen

/-!
# Absolute first moments of Rademacher sums

Book items: Exercise 5.31, Theorem 5.16, and the stop-loss support lemma for
Exercise 5.44.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal NNReal Topology

namespace FABL

variable {n : ℕ}

local instance rademacherSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance rademacherSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

private noncomputable def rademacherMeasure (n : ℕ) : Measure {−1,1}^[n] :=
  (uniformPMF {−1,1}^[n]).toMeasure

private instance rademacherMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (rademacherMeasure n) := by
  unfold rademacherMeasure
  infer_instance

private def rademacherSummand
    (a : Fin n → ℝ) (i : Fin n) (x : {−1,1}^[n]) : ℝ :=
  a i * signValue (x i)

private theorem sum_rademacherSummand
    (a : Fin n → ℝ) (x : {−1,1}^[n]) :
    ∑ i, rademacherSummand a i x = linearForm a x := by
  rfl

private theorem rademacherMeasure_eq_pi :
    rademacherMeasure n =
      Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure := by
  exact uniformSample_toMeasure_eq_pi Sign n

private theorem integral_signCoordinate_eq_zero (i : Fin n) :
    ∫ x, signValue (x i) ∂rademacherMeasure n = 0 := by
  rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  have hmonomial :
      (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} := by
    funext x
    simp [monomial]
  rw [hmonomial, expect_monomial]
  simp

private theorem integral_rademacherSummand_eq_zero
    (a : Fin n → ℝ) (i : Fin n) :
    ∫ x, rademacherSummand a i x ∂rademacherMeasure n = 0 := by
  simp only [rademacherSummand, integral_const_mul, integral_signCoordinate_eq_zero, mul_zero]

private theorem rademacherSummands_iIndep (a : Fin n → ℝ) :
    iIndepFun (rademacherSummand a) (rademacherMeasure n) := by
  rw [rademacherMeasure_eq_pi]
  change iIndepFun
    (fun i x ↦ (fun s : Sign ↦ a i * signValue s) (x i))
    (Measure.pi fun _ : Fin n ↦ (uniformPMF Sign).toMeasure)
  exact iIndepFun_pi fun i ↦
    (measurable_of_finite fun s : Sign ↦ a i * signValue s).aemeasurable

private theorem rademacherSummand_memLp
    (a : Fin n → ℝ) (i : Fin n) (p : ℝ≥0∞) :
    MemLp (rademacherSummand a i) p (rademacherMeasure n) := by
  refine MemLp.of_bound
    (measurable_of_finite (rademacherSummand a i)).aestronglyMeasurable |a i|
      (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, rademacherSummand, abs_mul]
  rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]

private theorem variance_rademacherSummand
    (a : Fin n → ℝ) (i : Fin n) :
    ProbabilityTheory.variance (rademacherSummand a i) (rademacherMeasure n) =
      a i ^ 2 := by
  rw [variance_of_integral_eq_zero
    (measurable_of_finite (rademacherSummand a i)).aemeasurable
    (integral_rademacherSummand_eq_zero a i)]
  rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  rw [show (fun x : {−1,1}^[n] ↦ rademacherSummand a i x ^ 2) =
      fun _ ↦ a i ^ 2 by
    funext x
    rw [rademacherSummand]
    rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]]
  exact Fintype.expect_const _

private theorem thirdMomentSum_rademacherSummand
    (a : Fin n → ℝ) :
    thirdMomentSum (rademacherSummand a) (rademacherMeasure n) =
      ∑ i, |a i| ^ 3 := by
  unfold thirdMomentSum
  apply Finset.sum_congr rfl
  intro i _
  rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  rw [show (fun x : {−1,1}^[n] ↦ |rademacherSummand a i x| ^ 3) =
      fun _ ↦ |a i| ^ 3 by
    funext x
    rw [rademacherSummand, abs_mul]
    rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]]
  exact Fintype.expect_const _

private theorem thirdMomentSum_rademacherSummand_le
    (a : Fin n → ℝ) {ε : ℝ}
    (hnormalized : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ ε) :
    thirdMomentSum (rademacherSummand a) (rademacherMeasure n) ≤ ε := by
  rw [thirdMomentSum_rademacherSummand]
  calc
    (∑ i, |a i| ^ 3) =
        ∑ i, |a i| * a i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show a i ^ 2 = |a i| ^ 2 by exact (sq_abs (a i)).symm]
      ring
    _ ≤ ∑ i, ε * a i ^ 2 :=
      Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg _)
    _ = ε := by rw [← mul_sum, hnormalized, mul_one]

private theorem rademacherLinearForm_hasSubgaussianMGF
    (a : Fin n → ℝ) (hnormalized : ∑ i, a i ^ 2 = 1) :
    HasSubgaussianMGF (linearForm a) 1 (rademacherMeasure n) := by
  let c : Fin n → ℝ≥0 := fun i ↦ ⟨a i ^ 2, sq_nonneg _⟩
  have hcoordinate (i : Fin n) :
      HasSubgaussianMGF (rademacherSummand a i) (c i) (rademacherMeasure n) := by
    have hsign :
        HasSubgaussianMGF (fun x : {−1,1}^[n] ↦ signValue (x i)) 1
          (rademacherMeasure n) := by
      have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := rademacherMeasure n)
        (X := fun x : {−1,1}^[n] ↦ signValue (x i))
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (measurable_of_finite fun x : {−1,1}^[n] ↦ signValue (x i)).aemeasurable
        (ae_of_all _ fun x ↦ by
          rcases signValue_eq_neg_one_or_one (x i) with hx | hx <;> simp [hx])
        (integral_signCoordinate_eq_zero i)
      norm_num at h ⊢
      exact h
    change HasSubgaussianMGF
      (fun x : {−1,1}^[n] ↦ a i * signValue (x i)) (c i)
        (rademacherMeasure n)
    simpa only [c, rademacherSummand, NNReal.coe_mk, mul_one] using
      hsign.const_mul (a i)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    (rademacherSummands_iIndep a)
    (s := Finset.univ) (c := c)
    fun i _ ↦ hcoordinate i
  have hc : (∑ i : Fin n, c i) = 1 := by
    apply NNReal.eq
    rw [NNReal.coe_sum, NNReal.coe_one]
    calc
      (∑ i, (c i : ℝ)) = ∑ i, a i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      _ = 1 := hnormalized
  rw [hc] at hsum
  exact hsum.congr (ae_of_all _ fun x ↦ sum_rademacherSummand a x)

private theorem standardGaussian_hasSubgaussianMGF :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := by
    simpa only [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    norm_num

private theorem measureReal_abs_ge_le_two_mul_exp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : HasSubgaussianMGF Y 1 μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Y ω|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  have hupper := hY.measure_ge_le ht
  have hlower := hY.neg.measure_ge_le ht
  have hset :
      {ω | t ≤ |Y ω|} = {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [le_abs']
    constructor
    · rintro (h | h)
      · right
        linarith
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · left
        linarith
  rw [hset]
  calc
    μ.real ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω}) ≤
        μ.real {ω | t ≤ Y ω} + μ.real {ω | t ≤ -Y ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (1 : ℝ))) +
        Real.exp (-t ^ 2 / (2 * (1 : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t ^ 2 / 2) := by ring_nf

/-- O'Donnell, Exercise 5.31(a): normalized Rademacher sums and a standard Gaussian
have the same two-sided subgaussian tail bound. -/
theorem exercise5_31a
    (a : Fin n → ℝ) {ε t : ℝ}
    (hnormalized : ∑ i, a i ^ 2 = 1)
    (_hbound : ∀ i, |a i| ≤ ε)
    (ht : 0 ≤ t) :
    (rademacherMeasure n).real {x | t ≤ |linearForm a x|} ≤
        2 * Real.exp (-t ^ 2 / 2) ∧
      (gaussianReal 0 1).real {z | t ≤ |z|} ≤
        2 * Real.exp (-t ^ 2 / 2) := by
  constructor
  · exact measureReal_abs_ge_le_two_mul_exp
      (rademacherLinearForm_hasSubgaussianMGF a hnormalized) ht
  · simpa only [id_eq] using
      measureReal_abs_ge_le_two_mul_exp standardGaussian_hasSubgaussianMGF ht

private def absoluteTail (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ν.real {x | t < |x|}

private theorem measurable_absoluteTail (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measurable (absoluteTail ν) := by
  exact Antitone.measurable fun _ _ hst ↦
    measureReal_mono (fun _ hx ↦ lt_of_le_of_lt hst hx) (by finiteness)

private theorem integrableOn_absoluteTail
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (habs : Integrable (fun x : ℝ ↦ |x|) ν) :
    IntegrableOn (absoluteTail ν) (Ioi 0) := by
  refine ⟨(measurable_absoluteTail ν).aestronglyMeasurable.restrict, ?_⟩
  change HasFiniteIntegral
    (fun t : ℝ ↦ ν.real {x : ℝ | t < |x|})
    (volume.restrict (Ioi 0))
  rw [hasFiniteIntegral_iff_ofReal (μ := volume.restrict (Ioi 0))
    (ae_of_all _ fun _ ↦ measureReal_nonneg)]
  have hkey := lintegral_eq_lintegral_meas_lt ν
    (ae_of_all _ fun x : ℝ ↦ abs_nonneg x)
    measurable_abs.aemeasurable
  have hlt := habs.lintegral_lt_top
  rw [hkey] at hlt
  have heq :
      (fun t : ℝ ↦ ENNReal.ofReal (ν.real {x : ℝ | t < |x|})) =
        fun t : ℝ ↦ ν {x : ℝ | t < |x|} := by
    funext t
    exact ofReal_measureReal
  rw [heq]
  exact hlt

private theorem abs_integral_abs_sub_le_of_absoluteTail
    (ν τ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure τ]
    (hν : Integrable (fun x : ℝ ↦ |x|) ν)
    (hτ : Integrable (fun x : ℝ ↦ |x|) τ)
    (B : ℝ → ℝ)
    (hB : IntegrableOn B (Ioi 0))
    (htail : ∀ t, 0 < t →
      |absoluteTail ν t - absoluteTail τ t| ≤ B t) :
    |(∫ x, |x| ∂ν) - ∫ x, |x| ∂τ| ≤
      ∫ t in Ioi 0, B t := by
  rw [hν.integral_eq_integral_meas_lt
      (ae_of_all _ fun x : ℝ ↦ abs_nonneg x),
    hτ.integral_eq_integral_meas_lt
      (ae_of_all _ fun x : ℝ ↦ abs_nonneg x)]
  change
    |(∫ t in Ioi 0, absoluteTail ν t) -
        ∫ t in Ioi 0, absoluteTail τ t| ≤ _
  rw [← integral_sub (integrableOn_absoluteTail ν hν)
    (integrableOn_absoluteTail τ hτ)]
  calc
    |∫ t in Ioi 0, absoluteTail ν t - absoluteTail τ t| ≤
        ∫ t in Ioi 0, |absoluteTail ν t - absoluteTail τ t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi 0, B t := by
      apply integral_mono_ae
      · exact (integrableOn_absoluteTail ν hν |>.sub
          (integrableOn_absoluteTail τ hτ)).abs
      · exact hB
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact htail t ht

private theorem absoluteTail_eq_one_sub_interval
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {t : ℝ} (_ht : 0 ≤ t) :
    absoluteTail ν t = 1 - ν.real (Icc (-t) t) := by
  have hset : {x : ℝ | t < |x|} = (Icc (-t) t)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc]
    constructor
    · intro h hx
      exact (not_lt_of_ge (abs_le.2 hx)) h
    · intro h
      exact lt_of_not_ge fun habs ↦ h (abs_le.1 habs)
  rw [absoluteTail, hset, probReal_compl_eq_one_sub measurableSet_Icc]

private theorem absoluteTail_error_le_of_interval_error
    (ν τ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {B t : ℝ} (ht : 0 ≤ t)
    (hinterval : |ν.real (Icc (-t) t) - τ.real (Icc (-t) t)| ≤ B) :
    |absoluteTail ν t - absoluteTail τ t| ≤ B := by
  rw [absoluteTail_eq_one_sub_interval ν ht,
    absoluteTail_eq_one_sub_interval τ ht]
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hinterval

private lemma measureReal_Iio_eq_leftLim_cdf
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Iio x) = Function.leftLim (cdf ν) x := by
  have hnonneg : 0 ≤ Function.leftLim (cdf ν) x := by
    exact (cdf_nonneg ν (x - 1)).trans
      ((monotone_cdf ν).le_leftLim (sub_one_lt x))
  calc
    ν.real (Iio x) = (cdf ν).measure.real (Iio x) := by rw [measure_cdf]
    _ = ENNReal.toReal
        (ENNReal.ofReal (Function.leftLim (cdf ν) x - 0)) := by
      rw [measureReal_def, StieltjesFunction.measure_Iio _
        (tendsto_cdf_atBot ν)]
    _ = Function.leftLim (cdf ν) x := by
      rw [sub_zero, ENNReal.toReal_ofReal hnonneg]

private lemma gaussianReal_cdf_leftLim (x : ℝ) :
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

private lemma strictCdfError_le_nonuniform
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {K : ℝ}
    (h : ∀ y,
      |cdf ν y - cdf (gaussianReal 0 1) y| ≤
        K / (1 + |y| ^ 3))
    (x : ℝ) :
    |ν.real (Iio x) - (gaussianReal 0 1).real (Iio x)| ≤
      K / (1 + |x| ^ 3) := by
  rw [measureReal_Iio_eq_leftLim_cdf ν x,
    measureReal_Iio_eq_leftLim_cdf (gaussianReal 0 1) x]
  have hlhs :
      Tendsto
        (fun y ↦ |cdf ν y - cdf (gaussianReal 0 1) y|)
        (𝓝[<] x)
        (𝓝 |Function.leftLim (cdf ν) x -
          Function.leftLim (cdf (gaussianReal 0 1)) x|) :=
    (((monotone_cdf ν).tendsto_leftLim x).sub
      ((monotone_cdf (gaussianReal 0 1)).tendsto_leftLim x)).abs
  have hrhs :
      Tendsto (fun y ↦ K / (1 + |y| ^ 3)) (𝓝[<] x)
        (𝓝 (K / (1 + |x| ^ 3))) := by
    have hcontinuous :
        Continuous (fun y : ℝ ↦ K / (1 + |y| ^ 3)) := by
      apply Continuous.div continuous_const
      · fun_prop
      · intro y
        positivity
    exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left
  have hlimit := le_of_tendsto_of_tendsto hlhs hrhs
    (Eventually.of_forall h)
  rw [gaussianReal_cdf_leftLim] at hlimit
  rw [gaussianReal_cdf_leftLim]
  exact hlimit

private theorem absoluteTail_error_le_nonuniform
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {K t : ℝ}
    (ht : 0 ≤ t)
    (h : ∀ x,
      |cdf ν x - cdf (gaussianReal 0 1) x| ≤
        K / (1 + |x| ^ 3)) :
    |absoluteTail ν t - absoluteTail (gaussianReal 0 1) t| ≤
      2 * K / (1 + t ^ 3) := by
  have hclosed :
      |ν.real (Iic t) - (gaussianReal 0 1).real (Iic t)| ≤
        K / (1 + t ^ 3) := by
    simpa only [cdf_eq_real, abs_of_nonneg ht] using h t
  have hopen :
      |ν.real (Iio (-t)) - (gaussianReal 0 1).real (Iio (-t))| ≤
        K / (1 + t ^ 3) := by
    simpa only [abs_neg, abs_of_nonneg ht] using
      strictCdfError_le_nonuniform ν h (-t)
  have hsubset : Iio (-t) ⊆ Iic t := fun x hx ↦ by
    change x < -t at hx
    change x ≤ t
    linarith
  have hν :
      ν.real (Icc (-t) t) =
        ν.real (Iic t) - ν.real (Iio (-t)) := by
    rw [← measureReal_sdiff hsubset measurableSet_Iio]
    congr 1
    ext x
    simp
  have hG :
      (gaussianReal 0 1).real (Icc (-t) t) =
        (gaussianReal 0 1).real (Iic t) -
          (gaussianReal 0 1).real (Iio (-t)) := by
    rw [← measureReal_sdiff hsubset measurableSet_Iio]
    congr 1
    ext x
    simp
  apply absoluteTail_error_le_of_interval_error ν (gaussianReal 0 1) ht
  rw [hν, hG]
  calc
    |(ν.real (Iic t) - ν.real (Iio (-t))) -
        ((gaussianReal 0 1).real (Iic t) -
          (gaussianReal 0 1).real (Iio (-t)))| =
        |(ν.real (Iic t) - (gaussianReal 0 1).real (Iic t)) -
          (ν.real (Iio (-t)) -
            (gaussianReal 0 1).real (Iio (-t)))| := by ring_nf
    _ ≤ |ν.real (Iic t) - (gaussianReal 0 1).real (Iic t)| +
        |ν.real (Iio (-t)) -
          (gaussianReal 0 1).real (Iio (-t))| := abs_sub _ _
    _ ≤ K / (1 + t ^ 3) + K / (1 + t ^ 3) :=
      add_le_add hclosed hopen
    _ = 2 * K / (1 + t ^ 3) := by ring

private theorem inv_one_add_cube_le_two_mul_inv_one_add_sq
    {t : ℝ} (ht : 0 ≤ t) :
    (1 + t ^ 3)⁻¹ ≤ 2 * (1 + t ^ 2)⁻¹ := by
  have hcube : 0 < 1 + t ^ 3 := by positivity
  have hsq : 0 < 1 + t ^ 2 := by positivity
  have hpoly : 1 + t ^ 2 ≤ 2 * (1 + t ^ 3) := by
    by_cases ht1 : t ≤ 1
    · nlinarith [sq_nonneg t]
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hmul : 0 ≤ t ^ 2 * (t - 1) :=
        mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1')
      nlinarith
  have hdiv :
      1 / (1 + t ^ 3) ≤ 2 / (1 + t ^ 2) :=
    (div_le_div_iff₀ hcube hsq).2 (by simpa using hpoly)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hdiv

private theorem integrableOn_inv_one_add_cube :
    IntegrableOn (fun t : ℝ ↦ (1 + t ^ 3)⁻¹) (Ioi 0) := by
  have hmajor :
      IntegrableOn (fun t : ℝ ↦ 2 * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 2).integrableOn
  refine hmajor.mono'
    (by fun_prop : AEStronglyMeasurable
      (fun t : ℝ ↦ (1 + t ^ 3)⁻¹) (volume.restrict (Ioi 0))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (inv_nonneg.mpr (add_nonneg zero_le_one (pow_nonneg ht.le 3)))]
  exact inv_one_add_cube_le_two_mul_inv_one_add_sq ht.le

private theorem integral_Ioi_inv_one_add_cube_le_four :
    (∫ (t : ℝ) in Ioi 0, (1 + t ^ 3)⁻¹) ≤ 4 := by
  have hmajor :
      IntegrableOn (fun t : ℝ ↦ 2 * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 2).integrableOn
  calc
    (∫ t in Ioi 0, (1 + t ^ 3)⁻¹) ≤
        ∫ t in Ioi 0, 2 * (1 + t ^ 2)⁻¹ := by
      apply integral_mono_ae integrableOn_inv_one_add_cube hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact inv_one_add_cube_le_two_mul_inv_one_add_sq ht.le
    _ = Real.pi := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
      simp only [Real.arctan_zero, sub_zero]
      ring
    _ ≤ 4 := Real.pi_le_four

private theorem integrableOn_nonuniformTailBound (K : ℝ) :
    IntegrableOn (fun t : ℝ ↦ 2 * K / (1 + t ^ 3)) (Ioi 0) := by
  simpa only [IntegrableOn, div_eq_mul_inv] using
    integrableOn_inv_one_add_cube.const_mul (2 * K)

private theorem integral_nonuniformTailBound_le
    {K : ℝ} (hK : 0 ≤ K) :
    (∫ (t : ℝ) in Ioi 0, 2 * K / (1 + t ^ 3)) ≤ 8 * K := by
  rw [show (fun t : ℝ ↦ 2 * K / (1 + t ^ 3)) =
      fun t ↦ (2 * K) * (1 + t ^ 3)⁻¹ by
    funext t
    ring]
  rw [integral_const_mul]
  nlinarith [integral_Ioi_inv_one_add_cube_le_four]

private theorem measureReal_Ioi_eq_one_sub_cdf
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    ν.real (Ioi t) = 1 - cdf ν t := by
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic,
    compl_Iic]

private theorem measurable_upperTailFrom
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    Measurable (fun u : ℝ ↦ ν.real (Ioi (t + u))) := by
  refine Antitone.measurable fun u v huv ↦
    measureReal_mono ?_ (by finiteness)
  intro z hz
  change t + v < z at hz
  change t + u < z
  linarith

private theorem setOf_lt_posPart_sub_eq_Ioi_add
    (t u : ℝ) (hu : 0 < u) :
    {z : ℝ | u < (z - t)⁺} = Ioi (t + u) := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_Ioi, PosPart.posPart, lt_max_iff]
  constructor
  · rintro (hz | hz)
    · linarith
    · linarith
  · intro hz
    left
    linarith

private theorem integrableOn_upperTailFrom
    (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ)
    (hstop : Integrable (fun z : ℝ ↦ (z - t)⁺) ν) :
    IntegrableOn (fun u : ℝ ↦ ν.real (Ioi (t + u))) (Ioi 0) := by
  refine ⟨(measurable_upperTailFrom ν t).aestronglyMeasurable.restrict, ?_⟩
  change HasFiniteIntegral
    (fun u : ℝ ↦ ν.real (Ioi (t + u)))
    (volume.restrict (Ioi 0))
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ ↦ measureReal_nonneg)]
  have hkey := lintegral_eq_lintegral_meas_lt ν
    (ae_of_all _ fun z : ℝ ↦ posPart_nonneg (z - t))
    hstop.aemeasurable
  have hlt := hstop.lintegral_lt_top
  rw [hkey] at hlt
  calc
    (∫⁻ u : ℝ in Ioi 0,
        ENNReal.ofReal (ν.real (Ioi (t + u)))) =
        ∫⁻ u : ℝ in Ioi 0, ν {z : ℝ | u < (z - t)⁺} := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u hu
      calc
        ENNReal.ofReal (ν.real (Ioi (t + u))) =
            ν (Ioi (t + u)) :=
          ofReal_measureReal
        _ = ν {z : ℝ | u < (z - t)⁺} := by
          rw [setOf_lt_posPart_sub_eq_Ioi_add t u hu]
    _ < ∞ := hlt

private theorem integral_posPart_sub_eq_integral_upperTailFrom
    (ν : Measure ℝ) (t : ℝ)
    (hstop : Integrable (fun z : ℝ ↦ (z - t)⁺) ν) :
    (∫ z : ℝ, (z - t)⁺ ∂ν) =
      ∫ u : ℝ in Ioi 0, ν.real (Ioi (t + u)) := by
  rw [hstop.integral_eq_integral_meas_lt
    (ae_of_all _ fun z : ℝ ↦ posPart_nonneg (z - t))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change ν.real {a : ℝ | u < (a - t)⁺} =
    ν.real (Ioi (t + u))
  rw [setOf_lt_posPart_sub_eq_Ioi_add t u hu]

private theorem integral_Ioi_mul_exp_neg_sq_div_two :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-x ^ 2 / 2)) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert integral_mul_cexp_neg_mul_sq
    (b := (1 / 2 : ℂ)) (by norm_num) using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      change (↑(x * Real.exp (-x ^ 2 / 2)) : ℂ) =
        (x : ℂ) * Complex.exp (-(1 / 2) * (x : ℂ) ^ 2)
      have hexponent :
          (-(1 / 2) * (x : ℂ) ^ 2) =
            ((-x ^ 2 / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hexponent, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  · norm_num

private theorem integral_posPart_standardGaussian :
    (∫ x : ℝ, x⁺ ∂gaussianReal 0 1) = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  change (∫ x : ℝ, gaussianPDFReal 0 1 x * x⁺) =
    (Real.sqrt (2 * Real.pi))⁻¹
  calc
    (∫ x : ℝ, gaussianPDFReal 0 1 x * x⁺) =
        ∫ x : ℝ in Ioi 0, gaussianPDFReal 0 1 x * x := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · change 0 < x at hx
          simp [hx, hx.le, PosPart.posPart]
        · change ¬0 < x at hx
          have hx' : x ≤ 0 := le_of_not_gt hx
          simp [hx, hx', PosPart.posPart]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ in Ioi 0, x * Real.exp (-x ^ 2 / 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
        ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := by
      rw [integral_Ioi_mul_exp_neg_sq_div_two, mul_one]

private theorem two_mul_inv_sqrt_two_mul_pi :
    2 * (Real.sqrt (2 * Real.pi))⁻¹ =
      Real.sqrt (2 / Real.pi) := by
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2) Real.pi,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) Real.pi]
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem integral_abs_standardGaussian :
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) =
      Real.sqrt (2 / Real.pi) := by
  have hId : Integrable id (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (1 : ℝ≥0)).integrable (by norm_num)
  have habs := integral_abs_eq_two_mul_integral_posPart_sub_integral hId
  simp only [id_eq] at habs
  calc
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) =
        2 * (Real.sqrt (2 * Real.pi))⁻¹ - 0 := by
      rw [habs, integral_id_gaussianReal, integral_posPart_standardGaussian]
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ := sub_zero _
    _ = Real.sqrt (2 / Real.pi) := two_mul_inv_sqrt_two_mul_pi

private theorem absoluteTail_le_two_mul_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : HasSubgaussianMGF id 1 ν) {t : ℝ} (ht : 0 ≤ t) :
    absoluteTail ν t ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  calc
    absoluteTail ν t ≤ ν.real {x | t ≤ |id x|} := by
      exact measureReal_mono
        (fun x hx ↦ by
          change t < |x| at hx
          change t ≤ |id x|
          simpa only [id_eq] using hx.le)
        (by finiteness)
    _ ≤ 2 * Real.exp (-t ^ 2 / 2) :=
      measureReal_abs_ge_le_two_mul_exp hν ht

private noncomputable def truncatedTailBound (U T t : ℝ) : ℝ :=
  if t ≤ T then U else 4 * Real.exp (-t ^ 2 / 2)

private theorem integrableOn_truncatedTailBound
    (U T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (truncatedTailBound U T) (Ioi 0) := by
  have hsmall :
      IntegrableOn (truncatedTailBound U T) (Ioc 0 T) := by
    refine (integrableOn_const (μ := volume) (s := Ioc 0 T) (C := U)
      measure_Ioc_lt_top.ne).congr_fun ?_ measurableSet_Ioc
    intro t ht
    rw [truncatedTailBound, if_pos ht.2]
  have hdecay :
      Integrable (fun t : ℝ ↦ 4 * Real.exp (-t ^ 2 / 2)) := by
    have h := (integrable_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num)).const_mul 4
    convert h using 1
    funext t
    congr 2
    ring
  have hlarge :
      IntegrableOn (truncatedTailBound U T) (Ioi T) := by
    refine hdecay.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t ht
    rw [truncatedTailBound, if_neg (not_le.mpr ht)]
  rw [← Ioc_union_Ioi_eq_Ioi hT]
  exact hsmall.union hlarge

private theorem integral_truncatedTailBound_le
    {U T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Ioi 0, truncatedTailBound U T t) ≤
      U * T + 4 * Real.exp (-T ^ 2 / 2) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hB := integrableOn_truncatedTailBound U T hT0
  have hsmall : IntegrableOn (truncatedTailBound U T) (Ioc 0 T) :=
    hB.mono_set Ioc_subset_Ioi_self
  have hlarge : IntegrableOn (truncatedTailBound U T) (Ioi T) :=
    hB.mono_set (Ioi_subset_Ioi hT0)
  have hsmallIntegral :
      (∫ t in Ioc 0 T, truncatedTailBound U T t) = U * T := by
    calc
      (∫ t in Ioc 0 T, truncatedTailBound U T t) =
          ∫ _ in Ioc 0 T, U := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        rw [truncatedTailBound, if_pos ht.2]
      _ = U * T := by
        rw [integral_const]
        simp [Real.volume_real_Ioc_of_le hT0]
        ring
  have hdecay :
      IntegrableOn (fun t : ℝ ↦ 4 * Real.exp (-t ^ 2 / 2)) (Ioi T) := by
    have h := (integrable_exp_neg_mul_sq
      (b := (1 / 2 : ℝ)) (by norm_num)).const_mul 4
    convert h.integrableOn using 1
    funext t
    congr 2
    ring
  have hmajor :
      IntegrableOn
        (fun t : ℝ ↦
          4 * Real.exp (-T ^ 2 / 2) * Real.exp (T - t))
        (Ioi T) := by
    have h := (integrableOn_exp_mul_Ioi
      (a := (-1 : ℝ)) (by norm_num) T).const_mul
        (4 * Real.exp (-T ^ 2 / 2) * Real.exp T)
    simpa only [IntegrableOn, Real.exp_sub, Real.exp_neg,
      neg_one_mul, div_eq_mul_inv, mul_assoc] using h
  have hdecayLe :
      (∫ t in Ioi T, 4 * Real.exp (-t ^ 2 / 2)) ≤
        4 * Real.exp (-T ^ 2 / 2) := by
    calc
      (∫ t in Ioi T, 4 * Real.exp (-t ^ 2 / 2)) ≤
          ∫ t in Ioi T,
            4 * Real.exp (-T ^ 2 / 2) * Real.exp (T - t) := by
        apply integral_mono_ae hdecay hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hfactor₁ : 0 ≤ t - T := sub_nonneg.mpr ht.le
        have hfactor₂ : 0 ≤ t + T - 2 := by linarith
        have hproduct : 0 ≤ (t - T) * (t + T - 2) :=
          mul_nonneg hfactor₁ hfactor₂
        have hexponent :
            -t ^ 2 / 2 ≤ -T ^ 2 / 2 + (T - t) := by
          nlinarith
        calc
          4 * Real.exp (-t ^ 2 / 2) ≤
              4 * Real.exp (-T ^ 2 / 2 + (T - t)) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr hexponent) (by norm_num)
          _ = 4 * Real.exp (-T ^ 2 / 2) * Real.exp (T - t) := by
            rw [Real.exp_add]
            ring
      _ = 4 * Real.exp (-T ^ 2 / 2) := by
        rw [show (fun t : ℝ ↦
            4 * Real.exp (-T ^ 2 / 2) * Real.exp (T - t)) =
            fun t ↦
              (4 * Real.exp (-T ^ 2 / 2) * Real.exp T) *
                Real.exp ((-1) * t) by
          funext t
          rw [Real.exp_sub, neg_one_mul, Real.exp_neg]
          ring]
        rw [integral_const_mul,
          integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) T]
        norm_num
        calc
          4 * Real.exp (-T ^ 2 / 2) * Real.exp T * Real.exp (-T) =
              4 * Real.exp (-T ^ 2 / 2) *
                (Real.exp T * Real.exp (-T)) := by ring
          _ = 4 * Real.exp (-T ^ 2 / 2) := by
            rw [← Real.exp_add]
            simp
  have hlargeIntegral :
      (∫ t in Ioi T, truncatedTailBound U T t) =
        ∫ t in Ioi T, 4 * Real.exp (-t ^ 2 / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [truncatedTailBound, if_neg (not_le.mpr ht)]
  rw [← Ioc_union_Ioi_eq_Ioi hT0,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hlarge,
    hsmallIntegral, hlargeIntegral]
  exact add_le_add le_rfl hdecayLe

/-- O'Donnell, Exercise 5.31(d): the nonuniform Berry--Esseen theorem gives a
dimension-free linear bound for the absolute first moment of a regular
Rademacher sum. -/
theorem exercise5_31d :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (a : Fin n → ℝ) {ε : ℝ},
        (∑ i, a i ^ 2 = 1) →
        (∀ i, |a i| ≤ ε) →
        |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
            Real.sqrt (2 / Real.pi)| ≤ C * ε := by
  rcases nonuniformBerryEsseen with ⟨C, hC, hBE⟩
  refine ⟨8 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n a ε hnormalized hbound
  let μ : Measure {−1,1}^[n] := rademacherMeasure n
  let X : Fin n → {−1,1}^[n] → ℝ := rademacherSummand a
  let S : Measure ℝ := μ.map (sumX X)
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_of_finite (X i)
  letI : IsProbabilityMeasure S := by
    dsimp only [S]
    exact isProbabilityMeasure_map_sumX (μ := μ) (X := X)
      fun i ↦ (hXmeas i).aemeasurable
  have hXindep : iIndepFun X μ := by
    simpa only [X, μ] using rademacherSummands_iIndep a
  have hXmean : ∀ i, ∫ x, X i x ∂μ = 0 := by
    intro i
    simpa only [X, μ] using integral_rademacherSummand_eq_zero a i
  have hX3 : ∀ i, MemLp (X i) 3 μ := by
    intro i
    simpa only [X, μ] using rademacherSummand_memLp a i 3
  have hvar : ∑ i, ProbabilityTheory.variance (X i) μ = 1 := by
    simpa only [X, μ, variance_rademacherSummand] using hnormalized
  let γ : ℝ := ∑ i, ∫ x, |X i x| ^ 3 ∂μ
  have hγnonneg : 0 ≤ γ := by
    dsimp only [γ]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun x ↦ pow_nonneg (abs_nonneg (X i x)) 3
  have hγle : γ ≤ ε := by
    change thirdMomentSum X μ ≤ ε
    simpa only [X, μ] using
      thirdMomentSum_rademacherSummand_le a hnormalized hbound
  have hnonuniform (x : ℝ) :
      |cdf S x - cdf (gaussianReal 0 1) x| ≤
        C * γ / (1 + |x| ^ 3) := by
    change
      |cdf (μ.map (fun ω ↦ ∑ i, X i ω)) x -
          cdf (gaussianReal 0 1) x| ≤
        C * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) / (1 + |x| ^ 3)
    exact hBE μ X hXmeas hXindep hXmean hX3 hvar x
  have hsumIntegrable : Integrable (sumX X) μ := by
    change Integrable
      (fun x : {−1,1}^[n] ↦ ∑ i, rademacherSummand a i x)
      (rademacherMeasure n)
    apply (rademacherLinearForm_hasSubgaussianMGF a hnormalized).integrable.congr
    exact ae_of_all _ fun x ↦ (sum_rademacherSummand a x).symm
  have hSabs : Integrable (fun z : ℝ ↦ |z|) S := by
    change Integrable (fun z : ℝ ↦ |z|) (μ.map (sumX X))
    rw [integrable_map_measure (by fun_prop)
      (measurable_sumX hXmeas).aemeasurable]
    simpa only [Function.comp_def] using hsumIntegrable.abs
  have hGabs : Integrable (fun z : ℝ ↦ |z|) (gaussianReal 0 1) := by
    have hGid : Integrable id (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (1 : ℝ≥0)).integrable (by norm_num)
    simpa only [id_eq] using hGid.abs
  have hcomparison :
      |(∫ z, |z| ∂S) - ∫ z, |z| ∂gaussianReal 0 1| ≤
        8 * (C * γ) := by
    calc
      |(∫ z, |z| ∂S) - ∫ z, |z| ∂gaussianReal 0 1| ≤
          ∫ t in Ioi 0, 2 * (C * γ) / (1 + t ^ 3) :=
        abs_integral_abs_sub_le_of_absoluteTail S (gaussianReal 0 1)
          hSabs hGabs (fun t ↦ 2 * (C * γ) / (1 + t ^ 3))
          (integrableOn_nonuniformTailBound (C * γ))
          fun t ht ↦ absoluteTail_error_le_nonuniform S ht.le hnonuniform
      _ ≤ 8 * (C * γ) :=
        integral_nonuniformTailBound_le (mul_nonneg hC.le hγnonneg)
  have hSfirstMoment :
      (∫ z, |z| ∂S) =
        𝔼 x : {−1,1}^[n], |linearForm a x| := by
    change (∫ z, |z| ∂μ.map (sumX X)) = _
    rw [integral_map (measurable_sumX hXmeas).aemeasurable (by fun_prop)]
    rw [show (fun x ↦ |sumX X x|) =
        fun x ↦ |linearForm a x| by
      funext x
      change |∑ i, rademacherSummand a i x| = |linearForm a x|
      rw [sum_rademacherSummand]]
    change (∫ x, |linearForm a x| ∂rademacherMeasure n) = _
    rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  rw [hSfirstMoment, integral_abs_standardGaussian] at hcomparison
  calc
    |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
        Real.sqrt (2 / Real.pi)| ≤ 8 * (C * γ) := hcomparison
    _ = (8 * C) * γ := by ring
    _ ≤ (8 * C) * ε :=
      mul_le_mul_of_nonneg_left hγle (mul_nonneg (by norm_num) hC.le)

/-- The nonuniform Berry--Esseen theorem specialized to the stop-loss transform
of a normalized regular Rademacher linear form. The comparison is uniform over
nonnegative thresholds. -/
theorem exists_stopLoss_linearForm_sub_standardGaussian_le_of_regular :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (a : Fin n → ℝ) {ε t : ℝ},
        (∑ i, a i ^ 2 = 1) →
        (∀ i, |a i| ≤ ε) →
        0 ≤ t →
        |(𝔼 x : {−1,1}^[n], (linearForm a x - t)⁺) -
            ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1| ≤ C * ε := by
  rcases nonuniformBerryEsseen with ⟨C, hC, hBE⟩
  refine ⟨8 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n a ε t hnormalized hbound ht
  let μ : Measure {−1,1}^[n] := rademacherMeasure n
  let X : Fin n → {−1,1}^[n] → ℝ := rademacherSummand a
  let S : Measure ℝ := μ.map (sumX X)
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_of_finite (X i)
  letI : IsProbabilityMeasure S := by
    dsimp only [S]
    exact isProbabilityMeasure_map_sumX (μ := μ) (X := X)
      fun i ↦ (hXmeas i).aemeasurable
  have hXindep : iIndepFun X μ := by
    simpa only [X, μ] using rademacherSummands_iIndep a
  have hXmean : ∀ i, ∫ x, X i x ∂μ = 0 := by
    intro i
    simpa only [X, μ] using integral_rademacherSummand_eq_zero a i
  have hX3 : ∀ i, MemLp (X i) 3 μ := by
    intro i
    simpa only [X, μ] using rademacherSummand_memLp a i 3
  have hvar : ∑ i, ProbabilityTheory.variance (X i) μ = 1 := by
    simpa only [X, μ, variance_rademacherSummand] using hnormalized
  let γ : ℝ := ∑ i, ∫ x, |X i x| ^ 3 ∂μ
  have hγnonneg : 0 ≤ γ := by
    dsimp only [γ]
    exact Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun x ↦ pow_nonneg (abs_nonneg (X i x)) 3
  have hγle : γ ≤ ε := by
    change thirdMomentSum X μ ≤ ε
    simpa only [X, μ] using
      thirdMomentSum_rademacherSummand_le a hnormalized hbound
  have hnonuniform (x : ℝ) :
      |cdf S x - cdf (gaussianReal 0 1) x| ≤
        C * γ / (1 + |x| ^ 3) := by
    change
      |cdf (μ.map (fun ω ↦ ∑ i, X i ω)) x -
          cdf (gaussianReal 0 1) x| ≤
        C * (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) /
          (1 + |x| ^ 3)
    exact hBE μ X hXmeas hXindep hXmean hX3 hvar x
  have hsumIntegrable : Integrable (sumX X) μ := by
    change Integrable
      (fun x : {−1,1}^[n] ↦ ∑ i, rademacherSummand a i x)
      (rademacherMeasure n)
    apply (rademacherLinearForm_hasSubgaussianMGF a hnormalized).integrable.congr
    exact ae_of_all _ fun x ↦ (sum_rademacherSummand a x).symm
  have hSId : Integrable id S := by
    change Integrable id (μ.map (sumX X))
    rw [integrable_map_measure (by fun_prop)
      (measurable_sumX hXmeas).aemeasurable]
    simpa only [Function.comp_def, id_eq] using hsumIntegrable
  have hSstop : Integrable (fun z : ℝ ↦ (z - t)⁺) S := by
    simpa only [Pi.sub_apply, id_eq, PosPart.posPart] using
      (hSId.sub (integrable_const t)).pos_part
  have hGId : Integrable id (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (1 : ℝ≥0)).integrable (by norm_num)
  have hGstop :
      Integrable (fun z : ℝ ↦ (z - t)⁺) (gaussianReal 0 1) := by
    simpa only [Pi.sub_apply, id_eq, PosPart.posPart] using
      (hGId.sub (integrable_const t)).pos_part
  have hStail :
      IntegrableOn (fun u : ℝ ↦ S.real (Ioi (t + u))) (Ioi 0) :=
    integrableOn_upperTailFrom S t hSstop
  have hGtail :
      IntegrableOn
        (fun u : ℝ ↦ (gaussianReal 0 1).real (Ioi (t + u)))
        (Ioi 0) :=
    integrableOn_upperTailFrom (gaussianReal 0 1) t hGstop
  have hCγ : 0 ≤ C * γ := mul_nonneg hC.le hγnonneg
  have htail (u : ℝ) (hu : 0 < u) :
      |S.real (Ioi (t + u)) -
          (gaussianReal 0 1).real (Ioi (t + u))| ≤
        2 * (C * γ) / (1 + u ^ 3) := by
    have hpow :
        u ^ 3 ≤ (t + u) ^ 3 :=
      pow_le_pow_left₀ hu.le (by linarith) 3
    have hdenSmall : 0 < 1 + u ^ 3 := by positivity
    have hdenLarge : 0 < 1 + (t + u) ^ 3 := by positivity
    calc
      |S.real (Ioi (t + u)) -
          (gaussianReal 0 1).real (Ioi (t + u))| =
          |cdf S (t + u) -
            cdf (gaussianReal 0 1) (t + u)| := by
        rw [measureReal_Ioi_eq_one_sub_cdf,
          measureReal_Ioi_eq_one_sub_cdf]
        simp only [sub_sub_sub_cancel_left, abs_sub_comm]
      _ ≤ C * γ / (1 + |t + u| ^ 3) :=
        hnonuniform (t + u)
      _ = C * γ / (1 + (t + u) ^ 3) := by
        rw [abs_of_nonneg (by linarith)]
      _ ≤ C * γ / (1 + u ^ 3) := by
        apply (div_le_div_iff₀ hdenLarge hdenSmall).2
        have hden :
            1 + u ^ 3 ≤ 1 + (t + u) ^ 3 := by
          linarith
        exact mul_le_mul_of_nonneg_left hden hCγ
      _ ≤ 2 * (C * γ) / (1 + u ^ 3) := by
        apply (div_le_div_iff₀ hdenSmall hdenSmall).2
        nlinarith
  have hcomparison :
      |(∫ z : ℝ, (z - t)⁺ ∂S) -
          ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1| ≤
        8 * (C * γ) := by
    rw [integral_posPart_sub_eq_integral_upperTailFrom S t hSstop,
      integral_posPart_sub_eq_integral_upperTailFrom
        (gaussianReal 0 1) t hGstop,
      ← integral_sub hStail hGtail]
    calc
      |∫ u : ℝ in Ioi 0,
          S.real (Ioi (t + u)) -
            (gaussianReal 0 1).real (Ioi (t + u))| ≤
          ∫ u : ℝ in Ioi 0,
            |S.real (Ioi (t + u)) -
              (gaussianReal 0 1).real (Ioi (t + u))| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ in Ioi 0,
          2 * (C * γ) / (1 + u ^ 3) := by
        apply integral_mono_ae
        · exact (hStail.sub hGtail).abs
        · exact integrableOn_nonuniformTailBound (C * γ)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact htail u hu
      _ ≤ 8 * (C * γ) :=
        integral_nonuniformTailBound_le hCγ
  have hSstopLoss :
      (∫ z : ℝ, (z - t)⁺ ∂S) =
        𝔼 x : {−1,1}^[n], (linearForm a x - t)⁺ := by
    change (∫ z : ℝ, (z - t)⁺ ∂μ.map (sumX X)) = _
    rw [integral_map (measurable_sumX hXmeas).aemeasurable
      (by fun_prop)]
    rw [show (fun x ↦ (sumX X x - t)⁺) =
        fun x ↦ (linearForm a x - t)⁺ by
      funext x
      rw [show sumX X x = linearForm a x by
        change (∑ i, rademacherSummand a i x) = linearForm a x
        exact sum_rademacherSummand a x]]
    change (∫ x, (linearForm a x - t)⁺ ∂rademacherMeasure n) = _
    rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  rw [hSstopLoss] at hcomparison
  calc
    |(𝔼 x : {−1,1}^[n], (linearForm a x - t)⁺) -
        ∫ z : ℝ, (z - t)⁺ ∂gaussianReal 0 1| ≤
        8 * (C * γ) := hcomparison
    _ = (8 * C) * γ := by ring
    _ ≤ (8 * C) * ε :=
      mul_le_mul_of_nonneg_left hγle
        (mul_nonneg (by norm_num) hC.le)

/-- O'Donnell, Exercise 5.31(b): splitting the layer-cake integral at `T ≥ 1`
combines the uniform Berry--Esseen estimate below `T` with the subgaussian
tails above `T`. -/
theorem exercise5_31b
    (a : Fin n → ℝ) {ε T : ℝ}
    (hnormalized : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ ε)
    (hT : 1 ≤ T) :
    |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
        Real.sqrt (2 / Real.pi)| ≤
      2 * thirdMomentBerryEsseenConstant * ε * T +
        4 * Real.exp (-T ^ 2 / 2) := by
  let μ : Measure {−1,1}^[n] := rademacherMeasure n
  let X : Fin n → {−1,1}^[n] → ℝ := rademacherSummand a
  let S : Measure ℝ := μ.map (sumX X)
  have hXmeas : ∀ i, Measurable (X i) :=
    fun i ↦ measurable_of_finite (X i)
  letI : IsProbabilityMeasure S := by
    dsimp only [S]
    exact isProbabilityMeasure_map_sumX (μ := μ) (X := X)
      fun i ↦ (hXmeas i).aemeasurable
  have hXindep : iIndepFun X μ := by
    simpa only [X, μ] using rademacherSummands_iIndep a
  have hXmean : ∀ i, ∫ x, X i x ∂μ = 0 := by
    intro i
    simpa only [X, μ] using integral_rademacherSummand_eq_zero a i
  have hX2 : ∀ i, MemLp (X i) 2 μ := by
    intro i
    simpa only [X, μ] using rademacherSummand_memLp a i 2
  have hvar : ∑ i, ProbabilityTheory.variance (X i) μ = 1 := by
    simpa only [X, μ, variance_rademacherSummand] using hnormalized
  have hX3 : ∀ i, Integrable (fun x ↦ |X i x| ^ 3) μ := by
    intro i
    simpa only [X, μ, Real.norm_eq_abs] using
      (rademacherSummand_memLp a i 3).integrable_norm_pow
        (by decide : (3 : ℕ) ≠ 0)
  have hγnonneg : 0 ≤ thirdMomentSum X μ :=
    thirdMomentSum_nonneg hX3
  have hγle : thirdMomentSum X μ ≤ ε := by
    simpa only [X, μ] using
      thirdMomentSum_rademacherSummand_le a hnormalized hbound
  have hε : 0 ≤ ε := hγnonneg.trans hγle
  have hsumSG : HasSubgaussianMGF (sumX X) 1 μ := by
    change HasSubgaussianMGF
      (fun x : {−1,1}^[n] ↦ ∑ i, rademacherSummand a i x)
      1 (rademacherMeasure n)
    apply (rademacherLinearForm_hasSubgaussianMGF a hnormalized).congr
    exact ae_of_all _ fun x ↦ (sum_rademacherSummand a x).symm
  have hSId : HasSubgaussianMGF id 1 S := by
    change HasSubgaussianMGF id 1 (μ.map (sumX X))
    exact (HasSubgaussianMGF.id_map_iff
      (measurable_sumX hXmeas).aemeasurable).2 hsumSG
  have hsumIntegrable : Integrable (sumX X) μ := hsumSG.integrable
  have hSabs : Integrable (fun z : ℝ ↦ |z|) S := by
    change Integrable (fun z : ℝ ↦ |z|) (μ.map (sumX X))
    rw [integrable_map_measure (by fun_prop)
      (measurable_sumX hXmeas).aemeasurable]
    simpa only [Function.comp_def] using hsumIntegrable.abs
  have hGabs : Integrable (fun z : ℝ ↦ |z|) (gaussianReal 0 1) := by
    have hGid : Integrable id (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (1 : ℝ≥0)).integrable (by norm_num)
    simpa only [id_eq] using hGid.abs
  let U : ℝ := 2 * thirdMomentBerryEsseenConstant * ε
  have huniform (t : ℝ) (ht : 0 ≤ t) :
      |absoluteTail S t - absoluteTail (gaussianReal 0 1) t| ≤ U := by
    have hinterval := exercise5_16_interval hX2 hXmeas hXindep hXmean
      hvar hX3 (.bounded true true (-t) t)
    have htail :
        |absoluteTail S t - absoluteTail (gaussianReal 0 1) t| ≤
          2 * thirdMomentBerryEsseenConstant * thirdMomentSum X μ := by
      apply absoluteTail_error_le_of_interval_error S (gaussianReal 0 1) ht
      simpa only [S, RealInterval.toSet] using hinterval
    exact htail.trans <| by
      dsimp only [U]
      exact mul_le_mul_of_nonneg_left hγle
        (mul_nonneg (by norm_num) thirdMomentBerryEsseenConstant_pos.le)
  have hlarge (t : ℝ) (ht : 0 ≤ t) :
      |absoluteTail S t - absoluteTail (gaussianReal 0 1) t| ≤
        4 * Real.exp (-t ^ 2 / 2) := by
    have hS := absoluteTail_le_two_mul_exp S hSId ht
    have hG := absoluteTail_le_two_mul_exp
      (gaussianReal 0 1) standardGaussian_hasSubgaussianMGF ht
    have hSnonneg : 0 ≤ absoluteTail S t := measureReal_nonneg
    have hGnonneg : 0 ≤ absoluteTail (gaussianReal 0 1) t :=
      measureReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have htail (t : ℝ) (ht : 0 < t) :
      |absoluteTail S t - absoluteTail (gaussianReal 0 1) t| ≤
        truncatedTailBound U T t := by
    rw [truncatedTailBound]
    split_ifs with htT
    · exact huniform t ht.le
    · exact hlarge t ht.le
  have hcomparison :
      |(∫ z, |z| ∂S) - ∫ z, |z| ∂gaussianReal 0 1| ≤
        U * T + 4 * Real.exp (-T ^ 2 / 2) := by
    calc
      |(∫ z, |z| ∂S) - ∫ z, |z| ∂gaussianReal 0 1| ≤
          ∫ t in Ioi 0, truncatedTailBound U T t :=
        abs_integral_abs_sub_le_of_absoluteTail S (gaussianReal 0 1)
          hSabs hGabs (truncatedTailBound U T)
          (integrableOn_truncatedTailBound U T (zero_le_one.trans hT))
          htail
      _ ≤ U * T + 4 * Real.exp (-T ^ 2 / 2) :=
        integral_truncatedTailBound_le hT
  have hSfirstMoment :
      (∫ z, |z| ∂S) =
        𝔼 x : {−1,1}^[n], |linearForm a x| := by
    change (∫ z, |z| ∂μ.map (sumX X)) = _
    rw [integral_map (measurable_sumX hXmeas).aemeasurable (by fun_prop)]
    rw [show (fun x ↦ |sumX X x|) =
        fun x ↦ |linearForm a x| by
      funext x
      change |∑ i, rademacherSummand a i x| = |linearForm a x|
      rw [sum_rademacherSummand]]
    change (∫ x, |linearForm a x| ∂rademacherMeasure n) = _
    rw [rademacherMeasure, integral_uniformPMF_eq_expect]
  rw [hSfirstMoment, integral_abs_standardGaussian] at hcomparison
  simpa only [U] using hcomparison

/-- O'Donnell, Exercise 5.31(c): choosing
`T = sqrt (2 * log (1 / ε))` in part (b) gives the asserted
`O(ε sqrt (log (1 / ε)))` estimate. The bound is stated on the standard
small-`ε` range `ε ≤ exp (-1)`, which is the formal meaning of the
asymptotic `O` in the exercise. -/
theorem exercise5_31c
    (a : Fin n → ℝ) {ε : ℝ}
    (hnormalized : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ ε)
    (hεpos : 0 < ε)
    (hεsmall : ε ≤ Real.exp (-1)) :
    |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
        Real.sqrt (2 / Real.pi)| ≤
      4 * (thirdMomentBerryEsseenConstant + 1) * ε *
        Real.sqrt (Real.log (1 / ε)) := by
  let L : ℝ := Real.log (1 / ε)
  let T : ℝ := Real.sqrt (2 * L)
  have hinv : Real.exp 1 ≤ 1 / ε := by
    apply (le_div_iff₀ hεpos).2
    calc
      Real.exp 1 * ε ≤ Real.exp 1 * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hεsmall (Real.exp_pos 1).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hL : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hinv
    simpa only [L, Real.log_exp] using hlog
  have hT : 1 ≤ T := by
    dsimp only [T]
    rw [Real.one_le_sqrt]
    nlinarith
  have hTsq : T ^ 2 = 2 * L := by
    dsimp only [T]
    rw [Real.sq_sqrt]
    nlinarith
  have htail : Real.exp (-T ^ 2 / 2) = ε := by
    rw [hTsq]
    have hexpLog : Real.exp L = 1 / ε := by
      dsimp only [L]
      rw [Real.exp_log (div_pos zero_lt_one hεpos)]
    calc
      Real.exp (-(2 * L) / 2) = Real.exp (-L) := by ring_nf
      _ = (Real.exp L)⁻¹ := Real.exp_neg L
      _ = (1 / ε)⁻¹ := by rw [hexpLog]
      _ = ε := by
        rw [one_div, inv_inv]
  have hTle : T ≤ 2 * Real.sqrt L := by
    dsimp only [T]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsquare := Real.sq_sqrt (zero_le_one.trans hL)
      nlinarith
  have hsqrt : 1 ≤ Real.sqrt L := by
    rw [Real.one_le_sqrt]
    exact hL
  have hb := exercise5_31b a hnormalized hbound hT
  rw [htail] at hb
  have hterm₁ :
      2 * thirdMomentBerryEsseenConstant * ε * T ≤
        (2 * thirdMomentBerryEsseenConstant * ε) *
          (2 * Real.sqrt L) :=
    mul_le_mul_of_nonneg_left hTle <| by
      positivity [thirdMomentBerryEsseenConstant_pos, hεpos]
  have hterm₂ : 4 * ε ≤ (4 * ε) * Real.sqrt L := by
    calc
      4 * ε = (4 * ε) * 1 := by ring
      _ ≤ (4 * ε) * Real.sqrt L :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
  calc
    |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
        Real.sqrt (2 / Real.pi)| ≤
        2 * thirdMomentBerryEsseenConstant * ε * T + 4 * ε := hb
    _ ≤
        (2 * thirdMomentBerryEsseenConstant * ε) *
            (2 * Real.sqrt L) +
          (4 * ε) * Real.sqrt L :=
      add_le_add hterm₁ hterm₂
    _ = 4 * (thirdMomentBerryEsseenConstant + 1) * ε *
        Real.sqrt (Real.log (1 / ε)) := by
      rw [show Real.log (1 / ε) = L by rfl]
      ring

/-- O'Donnell, Theorem 5.16: the absolute first moment of a normalized regular
Rademacher sum is universally within `O(ε)` of its Gaussian limit. -/
theorem exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (a : Fin n → ℝ) {ε : ℝ},
        (∑ i, a i ^ 2 = 1) →
        (∀ i, |a i| ≤ ε) →
        |(𝔼 x : {−1,1}^[n], |linearForm a x|) -
            Real.sqrt (2 / Real.pi)| ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ := exercise5_31d
  refine ⟨C, hC, ?_⟩
  intro n a ε hnormalized hregular
  exact hbound a hnormalized hregular

end FABL
