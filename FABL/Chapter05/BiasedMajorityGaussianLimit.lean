/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter02.NoiseStability.NoiseOperator
import FABL.Chapter05.HammingBallLimit
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Gaussian limit for biased Majority

Book item: Exercise 5.32.
-/

open Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

namespace FABL

local instance biasedMajoritySignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance biasedMajoritySignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The strict upper-right quadrant above a common threshold. -/
def gaussianUpperRightQuadrant (t : ℝ) : Set CorrelationPlane :=
  {z | t < correlationFirstCoordinate z ∧
    t < correlationSecondCoordinate z}

/-- A strict common-threshold upper-right quadrant is open. -/
theorem isOpen_gaussianUpperRightQuadrant (t : ℝ) :
    IsOpen (gaussianUpperRightQuadrant t) := by
  exact (isOpen_lt continuous_const continuous_correlationFirstCoordinate).inter
    (isOpen_lt continuous_const continuous_correlationSecondCoordinate)

private theorem frontier_gaussianUpperRightQuadrant_subset
    (t : ℝ) :
    frontier (gaussianUpperRightQuadrant t) ⊆
      {z | correlationFirstCoordinate z = t} ∪
        {z | correlationSecondCoordinate z = t} := by
  let first : Set CorrelationPlane :=
    {z | t < correlationFirstCoordinate z}
  let second : Set CorrelationPlane :=
    {z | t < correlationSecondCoordinate z}
  have hfirst :
      frontier first ⊆ {z | correlationFirstCoordinate z = t} := by
    intro z hz
    exact (frontier_lt_subset_eq continuous_const
      continuous_correlationFirstCoordinate hz).symm
  have hsecond :
      frontier second ⊆ {z | correlationSecondCoordinate z = t} := by
    intro z hz
    exact (frontier_lt_subset_eq continuous_const
      continuous_correlationSecondCoordinate hz).symm
  rw [show gaussianUpperRightQuadrant t = first ∩ second by rfl]
  exact (frontier_inter_subset first second).trans <|
    (Set.union_subset_union inter_subset_left inter_subset_right).trans <|
      Set.union_subset_union hfirst hsecond

private theorem correlatedGaussianMeasure_coordinateThresholds_null
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      ({z | correlationFirstCoordinate z = t} ∪
        {z | correlationSecondCoordinate z = t}) = 0 := by
  apply measure_union_null
  · change (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (correlationFirstCoordinate ⁻¹' ({t} : Set ℝ)) = 0
    rw [← Measure.map_apply continuous_correlationFirstCoordinate.measurable
      (measurableSet_singleton t),
      correlatedGaussianMeasure_map_firstCoordinate]
    letI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton t
  · change (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (correlationSecondCoordinate ⁻¹' ({t} : Set ℝ)) = 0
    rw [← Measure.map_apply continuous_correlationSecondCoordinate.measurable
      (measurableSet_singleton t),
      correlatedGaussianMeasure_map_secondCoordinate ρ hρ]
    letI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton t

private theorem correlatedGaussianMeasure_frontier_upperRight_null
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (frontier (gaussianUpperRightQuadrant t)) = 0 :=
  measure_mono_null (frontier_gaussianUpperRightQuadrant_subset t)
    (correlatedGaussianMeasure_coordinateThresholds_null ρ hρ t)

private theorem normalizedCorrelatedSignSumMeasure_upperRight_tendsto
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    Tendsto
      (fun n ↦ normalizedCorrelatedSignSumMeasure ρ hρ n
        (gaussianUpperRightQuadrant t))
      atTop
      (𝓝 (correlatedGaussianMeasure ρ
        (gaussianUpperRightQuadrant t))) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian ρ hρ)
    (by simpa using
      correlatedGaussianMeasure_frontier_upperRight_null ρ hρ t)

/-- The Gaussian same-threshold quadrant probability
`Λ_ρ(β) = Pr[Z₁ > t_β, Z₂ > t_β]`, where
`\bar Φ(t_β) = β`. -/
noncomputable def gaussianQuadrantProbability
    (ρ : Ioo (-1 : ℝ) 1) (β : Ioo (0 : ℝ) 1) : ℝ :=
  (correlatedGaussianMeasure (ρ : ℝ) : Measure CorrelationPlane).real
    (gaussianUpperRightQuadrant (standardGaussianUpperQuantile β))

private theorem standardGaussianUpperQuantile_upperTailOpen_biasedMajority
    (t : ℝ) :
    standardGaussianUpperQuantile
        (standardGaussianUpperTailOpen (OrderDual.toDual t)) = t := by
  rw [show standardGaussianUpperTailOpen (OrderDual.toDual t) =
      ⟨standardGaussianUpperTail t,
        standardGaussianUpperTail_pos t,
        standardGaussianUpperTail_lt_one t⟩ by
    apply Subtype.ext
    rfl]
  exact standardGaussianUpperQuantile_upperTail t

private theorem
    correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
    (n : ℕ) (xy : {−1,1}^[n] × {−1,1}^[n]) :
    correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) =
      normalizedRademacherSum n xy.1 := by
  rw [correlationFirstCoordinate_normalizedCorrelatedPairSum]
  unfold normalizedRademacherSum linearForm
  rw [Finset.mul_sum]

private theorem
    correlationSecondCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
    (n : ℕ) (xy : {−1,1}^[n] × {−1,1}^[n]) :
    correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) =
      normalizedRademacherSum n xy.2 := by
  rw [correlationSecondCoordinate_normalizedCorrelatedPairSum]
  unfold normalizedRademacherSum linearForm
  rw [Finset.mul_sum]

private theorem
    coe_normalizedCorrelatedSignSumMeasure_upperRight_eq_noiseStability
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) (t : ℝ) (n : ℕ) :
    ((normalizedCorrelatedSignSumMeasure ρ hρ n
      (gaussianUpperRightQuadrant t) : NNReal) : ℝ) =
      noiseStability ρ hρ (hammingUpperTailIndicator t n) := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [← integral_indicator_one
    (isOpen_gaussianUpperRightQuadrant t).measurableSet]
  rw [normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF]
  change (∫ z : CorrelationPlane,
      (gaussianUpperRightQuadrant t).indicator
          (fun _ ↦ (1 : ℝ)) z
        ∂(correlatedPairPMF (n := n) ρ hρ).toMeasure.map
          (normalizedCorrelatedPairSum n)) = _
  rw [integral_map
    (measurable_of_finite (normalizedCorrelatedPairSum n)).aemeasurable
    (((measurable_const :
        Measurable (fun _ : CorrelationPlane ↦ (1 : ℝ))).indicator
      (isOpen_gaussianUpperRightQuadrant t).measurableSet).aestronglyMeasurable)]
  rw [← pmfExpectation_eq_integral]
  unfold noiseStability pmfExpectation
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hx : t < normalizedRademacherSum n xy.1 <;>
    by_cases hy : t < normalizedRademacherSum n xy.2
  · have hmem :
        normalizedCorrelatedPairSum n xy ∈
          gaussianUpperRightQuadrant t := by
      exact ⟨
        correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
          n xy ▸ hx,
        correlationSecondCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
          n xy ▸ hy⟩
    simp [Set.indicator_of_mem hmem, hammingUpperTailIndicator, hx, hy]
  · have hnotMem :
        normalizedCorrelatedPairSum n xy ∉
          gaussianUpperRightQuadrant t := by
      intro hmem
      exact hy
        (correlationSecondCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
          n xy ▸ hmem.2)
    simp [Set.indicator_of_notMem hnotMem, hammingUpperTailIndicator, hx, hy]
  · have hnotMem :
        normalizedCorrelatedPairSum n xy ∉
          gaussianUpperRightQuadrant t := by
      intro hmem
      exact hx
        (correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
          n xy ▸ hmem.1)
    simp [Set.indicator_of_notMem hnotMem, hammingUpperTailIndicator, hx, hy]
  · have hnotMem :
        normalizedCorrelatedPairSum n xy ∉
          gaussianUpperRightQuadrant t := by
      intro hmem
      exact hx
        (correlationFirstCoordinate_normalizedCorrelatedPairSum_eq_normalizedRademacherSum
          n xy ▸ hmem.1)
    simp [Set.indicator_of_notMem hnotMem, hammingUpperTailIndicator, hx, hy]

/-- Exercise 5.32: the noise stability of the strict biased-Majority
threshold converges to the correlated Gaussian quadrant probability with
the same Gaussian mass. -/
theorem tendsto_noiseStability_hammingUpperTailIndicator
    (t : ℝ) (ρ : Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n : ℕ ↦
        noiseStability (ρ : ℝ) ⟨ρ.2.1.le, ρ.2.2.le⟩
          (hammingUpperTailIndicator t n))
      atTop
      (𝓝 (gaussianQuadrantProbability ρ
        (standardGaussianUpperTailOpen (OrderDual.toDual t)))) := by
  let hρclosed : (ρ : ℝ) ∈ Icc (-1 : ℝ) 1 :=
    ⟨ρ.2.1.le, ρ.2.2.le⟩
  have hnn :=
    normalizedCorrelatedSignSumMeasure_upperRight_tendsto
      (ρ : ℝ) hρclosed t
  have hreal :
      Tendsto
        (fun n : ℕ ↦
          ((normalizedCorrelatedSignSumMeasure (ρ : ℝ) hρclosed n
            (gaussianUpperRightQuadrant t) : NNReal) : ℝ))
        atTop
        (𝓝 (((correlatedGaussianMeasure (ρ : ℝ)
          (gaussianUpperRightQuadrant t) : NNReal) : ℝ))) :=
    NNReal.tendsto_coe.2 hnn
  have hfun :
      (fun n : ℕ ↦
        ((normalizedCorrelatedSignSumMeasure (ρ : ℝ) hρclosed n
          (gaussianUpperRightQuadrant t) : NNReal) : ℝ)) =
        fun n ↦
          noiseStability (ρ : ℝ) hρclosed
            (hammingUpperTailIndicator t n) := by
    funext n
    exact
      coe_normalizedCorrelatedSignSumMeasure_upperRight_eq_noiseStability
        (ρ : ℝ) hρclosed t n
  rw [hfun] at hreal
  simpa only [gaussianQuadrantProbability,
    standardGaussianUpperQuantile_upperTailOpen_biasedMajority,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] using hreal

private theorem correlatedGaussianMeasure_map_neg_biasedMajority
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).map
        (fun z ↦ -z) =
      correlatedGaussianMeasure ρ := by
  apply Measure.ext_of_charFun
  funext t
  have hneg :
      (fun z : CorrelationPlane ↦ -z) = ((-1 : ℝ) • ·) := by
    funext z
    simp
  rw [hneg, charFun_map_smul,
    charFun_correlatedGaussianMeasure ρ hρ,
    charFun_correlatedGaussianMeasure ρ hρ]
  congr 2
  unfold correlationQuadraticForm
  simp

private theorem
    correlatedGaussianMeasure_upperRight_neg_eq_lowerLeft
    (ρ : ℝ) (hρ : ρ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).real
        (gaussianUpperRightQuadrant (-t)) =
      (correlatedGaussianMeasure ρ : Measure CorrelationPlane).real
        {z | correlationFirstCoordinate z ≤ t ∧
          correlationSecondCoordinate z ≤ t} := by
  classical
  let μ : Measure CorrelationPlane := correlatedGaussianMeasure ρ
  let lowerOpen : Set CorrelationPlane :=
    {z | correlationFirstCoordinate z < t ∧
      correlationSecondCoordinate z < t}
  let lowerClosed : Set CorrelationPlane :=
    {z | correlationFirstCoordinate z ≤ t ∧
      correlationSecondCoordinate z ≤ t}
  have hmap :
      μ.map (fun z ↦ -z) = μ := by
    simpa only [μ] using
      correlatedGaussianMeasure_map_neg_biasedMajority ρ hρ
  have happly := congrArg
    (fun ν : Measure CorrelationPlane ↦
      ν.real (gaussianUpperRightQuadrant (-t))) hmap
  rw [map_measureReal_apply (by fun_prop)
    (isOpen_gaussianUpperRightQuadrant (-t)).measurableSet] at happly
  have hpreimage :
      (fun z : CorrelationPlane ↦ -z) ⁻¹'
          gaussianUpperRightQuadrant (-t) =
        lowerOpen := by
    ext z
    simp [gaussianUpperRightQuadrant, lowerOpen,
      correlationFirstCoordinate, correlationSecondCoordinate]
  rw [hpreimage] at happly
  have hsubset : lowerOpen ⊆ lowerClosed := by
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hdiff :
      lowerClosed \ lowerOpen ⊆
        {z | correlationFirstCoordinate z = t} ∪
          {z | correlationSecondCoordinate z = t} := by
    intro z hz
    rcases hz with ⟨hzClosed, hzOpen⟩
    dsimp only [lowerClosed] at hzClosed
    dsimp only [lowerOpen] at hzOpen
    simp only [mem_setOf_eq] at hzClosed hzOpen
    rcases not_and_or.mp hzOpen with hx | hy
    · exact Or.inl (le_antisymm hzClosed.1 (le_of_not_gt hx))
    · exact Or.inr (le_antisymm hzClosed.2 (le_of_not_gt hy))
  have hdiffNull : μ (lowerClosed \ lowerOpen) = 0 := by
    apply measure_mono_null hdiff
    simpa only [μ] using
      correlatedGaussianMeasure_coordinateThresholds_null ρ hρ t
  have hAE : lowerOpen =ᵐ[μ] lowerClosed :=
    EventuallyLE.antisymm hsubset.eventuallyLE
      (ae_le_set.mpr hdiffNull)
  exact happly.symm.trans (measureReal_congr hAE)

/-- If `α = Φ(t) = 1 - \bar Φ(t)`, then the Gaussian quadrant
probability `Λ_ρ(α)` is the lower-left probability at threshold `t`. -/
theorem gaussianQuadrantProbability_one_sub_upperTail
    (ρ : Ioo (-1 : ℝ) 1) (t : ℝ) :
    gaussianQuadrantProbability ρ
        ⟨1 - (standardGaussianUpperTailOpen
            (OrderDual.toDual t) : ℝ),
          Set.Ioo.one_sub_mem
            (standardGaussianUpperTailOpen (OrderDual.toDual t)).2⟩ =
      (correlatedGaussianMeasure (ρ : ℝ) :
        Measure CorrelationPlane).real
        {z | correlationFirstCoordinate z ≤ t ∧
          correlationSecondCoordinate z ≤ t} := by
  unfold gaussianQuadrantProbability
  rw [standardGaussianUpperQuantile_one_sub
    (standardGaussianUpperTailOpen (OrderDual.toDual t))]
  rw [standardGaussianUpperQuantile_upperTailOpen_biasedMajority]
  exact correlatedGaussianMeasure_upperRight_neg_eq_lowerLeft
    (ρ : ℝ) ⟨ρ.2.1.le, ρ.2.2.le⟩ t

end FABL
