/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import ProbabilityApproximation.ChenShao.UniformBerryEsseen

/-!
# Strict and interval forms of Berry--Esseen

Book item: Exercise 5.16.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace FABL

/-- A single classification of bounded and unbounded real intervals, with endpoint inclusion
recorded by the Boolean flags. -/
inductive RealInterval where
  | univ
  | below (closed : Bool) (upper : ℝ)
  | above (closed : Bool) (lower : ℝ)
  | bounded (leftClosed rightClosed : Bool) (lower upper : ℝ)

/-- The subset of `ℝ` represented by a `RealInterval`. -/
def RealInterval.toSet : RealInterval → Set ℝ
  | .univ => Set.univ
  | .below true upper => Iic upper
  | .below false upper => Iio upper
  | .above true lower => Ici lower
  | .above false lower => Ioi lower
  | .bounded true true lower upper => Icc lower upper
  | .bounded false true lower upper => Ioc lower upper
  | .bounded true false lower upper => Ico lower upper
  | .bounded false false lower upper => Ioo lower upper

private lemma measureReal_Iio_eq_leftLim_cdf
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Iio x) = Function.leftLim (cdf ν) x := by
  have hnonneg : 0 ≤ Function.leftLim (cdf ν) x := by
    exact (cdf_nonneg ν (x - 1)).trans ((monotone_cdf ν).le_leftLim (sub_one_lt x))
  calc
    ν.real (Iio x) = (cdf ν).measure.real (Iio x) := by rw [measure_cdf]
    _ = ENNReal.toReal (ENNReal.ofReal (Function.leftLim (cdf ν) x - 0)) := by
      rw [measureReal_def, StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot ν)]
    _ = Function.leftLim (cdf ν) x := by
      rw [sub_zero, ENNReal.toReal_ofReal hnonneg]

private lemma gaussianReal_cdf_leftLim (x : ℝ) :
    Function.leftLim (cdf (gaussianReal 0 1)) x = cdf (gaussianReal 0 1) x := by
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hzero : (cdf (gaussianReal 0 1)).measure {x} = 0 := by
    rw [measure_cdf]
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hzero
  exact le_antisymm ((monotone_cdf (gaussianReal 0 1)).leftLim_le le_rfl)
    (sub_nonpos.mp hzero)

private lemma strictCdfError_le_of_cdfError_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {B : ℝ}
    (h : ∀ y, |cdf ν y - cdf (gaussianReal 0 1) y| ≤ B) (x : ℝ) :
    |ν.real (Iio x) - (gaussianReal 0 1).real (Iio x)| ≤ B := by
  rw [measureReal_Iio_eq_leftLim_cdf ν x,
    measureReal_Iio_eq_leftLim_cdf (gaussianReal 0 1) x]
  have hlimit :
      |Function.leftLim (cdf ν) x -
          Function.leftLim (cdf (gaussianReal 0 1)) x| ≤ B := by
    refine le_of_tendsto
      ((((monotone_cdf ν).tendsto_leftLim x).sub
        ((monotone_cdf (gaussianReal 0 1)).tendsto_leftLim x)).abs) ?_
    exact Eventually.of_forall h
  rw [gaussianReal_cdf_leftLim] at hlimit
  rw [gaussianReal_cdf_leftLim]
  exact hlimit

private lemma abs_measureReal_sdiff_sub_le_two
    (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {s t : Set ℝ} {B : ℝ} (hts : t ⊆ s) (ht : MeasurableSet t)
    (hs : |ν₁.real s - ν₂.real s| ≤ B)
    (ht' : |ν₁.real t - ν₂.real t| ≤ B) :
    |ν₁.real (s \ t) - ν₂.real (s \ t)| ≤ 2 * B := by
  have hν₁ : ν₁.real (s \ t) = ν₁.real s - ν₁.real t :=
    measureReal_sdiff hts ht
  have hν₂ : ν₂.real (s \ t) = ν₂.real s - ν₂.real t :=
    measureReal_sdiff hts ht
  rw [hν₁, hν₂]
  calc
    |(ν₁.real s - ν₁.real t) - (ν₂.real s - ν₂.real t)| =
        |(ν₁.real s - ν₂.real s) - (ν₁.real t - ν₂.real t)| := by ring_nf
    _ ≤ |ν₁.real s - ν₂.real s| + |ν₁.real t - ν₂.real t| := by
      simpa using abs_sub (ν₁.real s - ν₂.real s) (ν₁.real t - ν₂.real t)
    _ ≤ B + B := add_le_add hs ht'
    _ = 2 * B := by ring_nf

/-- O'Donnell, Exercise 5.16(a): the uniform third-moment Berry--Esseen estimate also holds
for strict lower half-lines. -/
theorem exercise5_16_strict
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (x : ℝ) :
    |(μ.map (sumX X)).real (Iio x) - (gaussianReal 0 1).real (Iio x)| ≤
      thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ := by
  classical
  letI : IsProbabilityMeasure (μ.map (sumX X)) :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun k ↦ (hXmeas k).aemeasurable
  exact strictCdfError_le_of_cdfError_le (μ.map (sumX X))
    (fun y ↦ uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 y) x

/-- O'Donnell, Exercise 5.16(b): on every bounded or unbounded real interval, with either
choice of endpoint inclusion, the Berry--Esseen error is at most twice the half-line error. -/
theorem exercise5_16_interval
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 μ) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X μ) (h_mean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hvar : ∑ k, variance (X k) μ = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) μ)
    (I : RealInterval) :
    |(μ.map (sumX X)).real I.toSet - (gaussianReal 0 1).real I.toSet| ≤
      2 * thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ := by
  classical
  let S : Measure ℝ := μ.map (sumX X)
  let G : Measure ℝ := gaussianReal 0 1
  let B : ℝ := thirdMomentBerryEsseenConstant * thirdMomentSum (X := X) μ
  letI : IsProbabilityMeasure S :=
    isProbabilityMeasure_map_sumX (μ := μ) (X := X) fun k ↦ (hXmeas k).aemeasurable
  letI : IsProbabilityMeasure G := inferInstance
  have hB : 0 ≤ B :=
    mul_nonneg thirdMomentBerryEsseenConstant_pos.le (thirdMomentSum_nonneg h3)
  have hclosed (x : ℝ) : |S.real (Iic x) - G.real (Iic x)| ≤ B := by
    have hbe := uniformBerryEsseen_thirdMoment hX hXmeas h_indep h_mean hvar h3 x
    change |cdf S x - cdf G x| ≤ B at hbe
    simpa only [cdf_eq_real] using hbe
  have hopen (x : ℝ) : |S.real (Iio x) - G.real (Iio x)| ≤ B := by
    simpa only [S, G, B] using
      exercise5_16_strict hX hXmeas h_indep h_mean hvar h3 x
  have haboveClosed (x : ℝ) : |S.real (Ici x) - G.real (Ici x)| ≤ B := by
    calc
      |S.real (Ici x) - G.real (Ici x)| =
          |(1 - S.real (Iio x)) - (1 - G.real (Iio x))| := by
            rw [← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
              probReal_compl_eq_one_sub measurableSet_Iio]
      _ = |G.real (Iio x) - S.real (Iio x)| := by
        congr 1
        ring_nf
      _ = |S.real (Iio x) - G.real (Iio x)| := abs_sub_comm _ _
      _ ≤ B := hopen x
  have haboveOpen (x : ℝ) : |S.real (Ioi x) - G.real (Ioi x)| ≤ B := by
    calc
      |S.real (Ioi x) - G.real (Ioi x)| =
          |(1 - S.real (Iic x)) - (1 - G.real (Iic x))| := by
            rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
              probReal_compl_eq_one_sub measurableSet_Iic]
      _ = |G.real (Iic x) - S.real (Iic x)| := by
        congr 1
        ring_nf
      _ = |S.real (Iic x) - G.real (Iic x)| := abs_sub_comm _ _
      _ ≤ B := hclosed x
  have hdouble : B ≤ 2 * B := by linarith
  suffices
      |S.real I.toSet - G.real I.toSet| ≤ 2 * B by
    simpa only [S, G, B, mul_assoc] using this
  cases I with
  | univ =>
      simp [RealInterval.toSet, hB]
  | below closed upper =>
      cases closed with
      | false =>
          simpa only [RealInterval.toSet] using (hopen upper).trans hdouble
      | true =>
          simpa only [RealInterval.toSet] using (hclosed upper).trans hdouble
  | above closed lower =>
      cases closed with
      | false =>
          simpa only [RealInterval.toSet] using (haboveOpen lower).trans hdouble
      | true =>
          simpa only [RealInterval.toSet] using (haboveClosed lower).trans hdouble
  | bounded leftClosed rightClosed lower upper =>
      cases leftClosed <;> cases rightClosed
      · simp only [RealInterval.toSet]
        by_cases h : lower < upper
        · have hset : Iio upper \ Iic lower = Ioo lower upper := by
            ext x
            simp
          rw [← hset]
          exact abs_measureReal_sdiff_sub_le_two S G
            (fun _ hx ↦ lt_of_le_of_lt hx h) measurableSet_Iic
            (hopen upper) (hclosed lower)
        · simp [Ioo_eq_empty h, hB]
      · simp only [RealInterval.toSet]
        by_cases h : lower ≤ upper
        · have hset : Iic upper \ Iic lower = Ioc lower upper := by
            ext x
            simp
          rw [← hset]
          exact abs_measureReal_sdiff_sub_le_two S G
            (Iic_subset_Iic.mpr h) measurableSet_Iic (hclosed upper) (hclosed lower)
        · simp [Ioc_eq_empty (fun hlt ↦ h hlt.le), hB]
      · simp only [RealInterval.toSet]
        by_cases h : lower ≤ upper
        · have hset : Iio upper \ Iio lower = Ico lower upper := by
            ext x
            simp
          rw [← hset]
          exact abs_measureReal_sdiff_sub_le_two S G
            (Iio_subset_Iio h) measurableSet_Iio (hopen upper) (hopen lower)
        · simp [Ico_eq_empty (fun hlt ↦ h hlt.le), hB]
      · simp only [RealInterval.toSet]
        by_cases h : lower ≤ upper
        · have hset : Iic upper \ Iio lower = Icc lower upper := by
            ext x
            simp
          rw [← hset]
          exact abs_measureReal_sdiff_sub_le_two S G
            (fun _ hx ↦ hx.le.trans h) measurableSet_Iio (hclosed upper) (hopen lower)
        · simp [Icc_eq_empty h, hB]

end FABL
