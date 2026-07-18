/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.GaussianDisagreement

/-!
# Gaussian thresholds

Book item: Sheppard's Formula in Section 5.2.
-/

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal RealInnerProductSpace

@[expose] public section

namespace FABL

private def gaussianLowerLeftQuadrant : Set CorrelationPlane :=
  {z | correlationFirstCoordinate z ≤ 0 ∧ correlationSecondCoordinate z ≤ 0}

private def gaussianUpperRightQuadrant : Set CorrelationPlane :=
  {z | 0 ≤ correlationFirstCoordinate z ∧ 0 ≤ correlationSecondCoordinate z}

private theorem measurableSet_gaussianLowerLeftQuadrant :
    MeasurableSet gaussianLowerLeftQuadrant := by
  exact ((isClosed_le continuous_correlationFirstCoordinate continuous_const).inter
    (isClosed_le continuous_correlationSecondCoordinate continuous_const)).measurableSet

private theorem measurableSet_gaussianUpperRightQuadrant :
    MeasurableSet gaussianUpperRightQuadrant := by
  exact ((isClosed_le continuous_const continuous_correlationFirstCoordinate).inter
    (isClosed_le continuous_const continuous_correlationSecondCoordinate)).measurableSet

private theorem correlatedGaussianMeasure_map_neg
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).map (fun z ↦ -z) =
      correlatedGaussianMeasure ρ := by
  apply Measure.ext_of_charFun
  funext t
  have hneg : (fun z : CorrelationPlane ↦ -z) = ((-1 : ℝ) • ·) := by
    funext z
    simp
  rw [hneg]
  rw [charFun_map_smul, charFun_correlatedGaussianMeasure ρ hρ,
    charFun_correlatedGaussianMeasure ρ hρ]
  congr 2
  unfold correlationQuadraticForm
  simp

private theorem correlatedGaussianMeasure_lowerLeft_eq_upperRight
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).real
        gaussianLowerLeftQuadrant =
      (correlatedGaussianMeasure ρ : Measure CorrelationPlane).real
        gaussianUpperRightQuadrant := by
  have hmap := correlatedGaussianMeasure_map_neg ρ hρ
  have happly := congrArg
    (fun μ : Measure CorrelationPlane ↦ μ gaussianLowerLeftQuadrant) hmap
  rw [Measure.map_apply (by fun_prop) measurableSet_gaussianLowerLeftQuadrant] at happly
  have hpreimage :
      (fun z : CorrelationPlane ↦ -z) ⁻¹' gaussianLowerLeftQuadrant =
        gaussianUpperRightQuadrant := by
    ext z
    simp only [gaussianLowerLeftQuadrant, gaussianUpperRightQuadrant, mem_preimage,
      mem_setOf_eq]
    simp [correlationFirstCoordinate, correlationSecondCoordinate]
  rw [hpreimage] at happly
  exact congrArg ENNReal.toReal happly.symm

/-- O'Donnell, Sheppard's Formula: the canonical correlated Gaussian law represents the
book's pair of standard Gaussian random variables with correlation `ρ`; its lower-left quadrant
has the stated probability. -/
theorem sheppardsFormula
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).real
        {z | correlationFirstCoordinate z ≤ 0 ∧ correlationSecondCoordinate z ≤ 0} =
      1 / 2 - (1 / 2) * (Real.arccos ρ / Real.pi) := by
  let μ : Measure CorrelationPlane := correlatedGaussianMeasure ρ
  letI : IsProbabilityMeasure μ := inferInstance
  have hAxes :
      μ ({z | correlationFirstCoordinate z = 0} ∪
        {z | correlationSecondCoordinate z = 0}) = 0 :=
    correlatedGaussianMeasure_coordinateAxes_null ρ hρ
  have hInter :
      μ (gaussianLowerLeftQuadrant ∩ gaussianUpperRightQuadrant) = 0 := by
    apply measure_mono_null _ hAxes
    intro z hz
    rcases hz with ⟨⟨hxle, _⟩, hxge, _⟩
    exact Or.inl (le_antisymm hxle hxge)
  have hInterReal :
      μ.real (gaussianLowerLeftQuadrant ∩ gaussianUpperRightQuadrant) = 0 := by
    simp [Measure.real, hInter]
  have hUnion :
      gaussianLowerLeftQuadrant ∪ gaussianUpperRightQuadrant =
        gaussianDisagreementRegionᶜ := by
    ext z
    simp only [gaussianLowerLeftQuadrant, gaussianUpperRightQuadrant,
      gaussianDisagreementRegion, mem_union, mem_setOf_eq, mem_compl_iff]
    rw [not_lt]
    exact (mul_nonneg_iff.trans or_comm).symm
  have hUnionReal :
      μ.real (gaussianLowerLeftQuadrant ∪ gaussianUpperRightQuadrant) =
        μ.real gaussianLowerLeftQuadrant + μ.real gaussianUpperRightQuadrant := by
    have h := measureReal_union_add_inter
      (μ := μ) (s := gaussianLowerLeftQuadrant)
      measurableSet_gaussianUpperRightQuadrant
    simpa only [hInterReal, add_zero] using h
  have hComplement :=
    measureReal_add_measureReal_compl
      (μ := μ) isOpen_gaussianDisagreementRegion.measurableSet
  rw [← hUnion] at hComplement
  have hTotal :
      μ.real gaussianDisagreementRegion +
          μ.real gaussianLowerLeftQuadrant +
          μ.real gaussianUpperRightQuadrant =
        1 := by
    calc
      μ.real gaussianDisagreementRegion +
            μ.real gaussianLowerLeftQuadrant +
            μ.real gaussianUpperRightQuadrant =
          μ.real gaussianDisagreementRegion +
            (μ.real gaussianLowerLeftQuadrant +
              μ.real gaussianUpperRightQuadrant) := by ring
      _ = μ.real gaussianDisagreementRegion +
          μ.real (gaussianLowerLeftQuadrant ∪ gaussianUpperRightQuadrant) := by
        rw [hUnionReal]
      _ = 1 := by simpa using hComplement
  have hSymmetry :
      μ.real gaussianLowerLeftQuadrant = μ.real gaussianUpperRightQuadrant :=
    correlatedGaussianMeasure_lowerLeft_eq_upperRight ρ hρ
  have hDisagreement :
      μ.real gaussianDisagreementRegion = Real.arccos ρ / Real.pi := by
    rw [Measure.real, correlatedGaussianMeasure_disagreement ρ hρ,
      ENNReal.toReal_ofReal]
    exact div_nonneg (Real.arccos_nonneg ρ) Real.pi_pos.le
  change μ.real gaussianLowerLeftQuadrant =
    1 / 2 - (1 / 2) * (Real.arccos ρ / Real.pi)
  rw [hDisagreement, ← hSymmetry] at hTotal
  linarith

end FABL
