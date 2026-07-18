/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# Consequences of the Berry--Esseen hypotheses

Book item: Remark 5.15.
-/

open Finset MeasureTheory
open scoped BigOperators ProbabilityTheory

@[expose] public section

namespace FABL

/-- O'Donnell, Remark 5.15: uniformly bounded centered summands whose total variance is one
have total third absolute moment at most the uniform bound. -/
theorem sum_integral_abs_cube_le_of_ae_abs_le
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (X : ι → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvariance : ∑ i, Var[X i; μ] = 1)
    {ε : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ ε) :
    ∑ i, ∫ ω, |X i ω| ^ 3 ∂μ ≤ ε := by
  have hpointwise (i : ι) :
      ∀ᵐ ω ∂μ, |X i ω| ^ 3 ≤ ε * (X i ω) ^ 2 := by
    filter_upwards [hbound i] with ω hω
    calc
      |X i ω| ^ 3 = |X i ω| * (X i ω) ^ 2 := by
        rw [show (X i ω) ^ 2 = |X i ω| ^ 2 by exact (sq_abs (X i ω)).symm]
        ring
      _ ≤ ε * (X i ω) ^ 2 := mul_le_mul_of_nonneg_right hω (sq_nonneg _)
  have hcubic (i : ι) : Integrable (fun ω ↦ |X i ω| ^ 3) μ := by
    refine ((hX i).integrable_sq.const_mul ε).mono'
      (by
        change AEStronglyMeasurable ((fun ω ↦ |X i ω|) ^ 3) μ
        simpa only [Real.norm_eq_abs] using (hX i).aestronglyMeasurable.norm.pow 3) ?_
    filter_upwards [hpointwise i] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hω
  have hthird (i : ι) :
      (∫ ω, |X i ω| ^ 3 ∂μ) ≤ ε * Var[X i; μ] := by
    calc
      (∫ ω, |X i ω| ^ 3 ∂μ) ≤ ∫ ω, ε * (X i ω) ^ 2 ∂μ := by
        exact integral_mono_ae (hcubic i) ((hX i).integrable_sq.const_mul ε) (hpointwise i)
      _ = ε * (∫ ω, (X i ω) ^ 2 ∂μ) := by
        rw [integral_const_mul]
      _ = ε * Var[X i; μ] := by
        rw [← ProbabilityTheory.variance_of_integral_eq_zero
          (hX i).aemeasurable (hmean i)]
  calc
    (∑ i, ∫ ω, |X i ω| ^ 3 ∂μ) ≤ ∑ i, ε * Var[X i; μ] :=
      sum_le_sum fun i _ ↦ hthird i
    _ = ε * ∑ i, Var[X i; μ] := by rw [mul_sum]
    _ = ε := by rw [hvariance, mul_one]

end FABL
