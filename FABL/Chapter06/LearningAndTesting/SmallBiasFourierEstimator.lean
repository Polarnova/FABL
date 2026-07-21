/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasGenerator
public import FABL.Chapter06.LearningAndTesting.DeterministicQuery
public import FABL.Chapter06.LearningAndTesting.FourierNorms

/-!
# Deterministic Fourier estimation from a small-bias sample

Mathematical and query-program core of O'Donnell, Proposition 6.40.

A finite sample map is kept separate from its construction algorithm.  The estimator enumerates
that map, issues exactly one real-valued oracle query per entry, and charges the finite arithmetic
work explicitly.  Its error theorem uses Lemma 6.38 and the fact that multiplication by a Walsh
monomial permutes Fourier coefficients.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n m : ℕ}

/-- The empirical Fourier coefficient obtained by enumerating a finite binary-cube sample map. -/
noncomputable def smallBiasFourierEstimate
    (f : {−1,1}^[n] → ℝ) (sample : Fin m → F₂Cube n)
    (U : Finset (Fin n)) : ℝ :=
  (∑ i : Fin m,
      f (binaryCubeSignEquiv n (sample i)) *
        monomial U (binaryCubeSignEquiv n (sample i))) / m

/-- Local arithmetic charged after collecting the sample's oracle answers. -/
def smallBiasFourierEstimatorWork (m : ℕ) (U : Finset (Fin n)) : ℕ :=
  m * (U.card + 2) + 1

/-- Exact constructor-derived cost of the finite-sample Fourier estimator. -/
def smallBiasFourierEstimatorCost (m : ℕ) (U : Finset (Fin n)) :
    LearningCost :=
  DeterministicQueryProgram.queryBatchCost m +
    ⟨0, 0, smallBiasFourierEstimatorWork m U⟩

/-- The real-valued deterministic query program that enumerates a finite sample map. -/
noncomputable def smallBiasFourierEstimatorProgram
    (sample : Fin m → F₂Cube n) (U : Finset (Fin n)) :
    DeterministicQueryProgram {−1,1}^[n] ℝ ℝ :=
  .queryBatch m
    (fun i ↦ binaryCubeSignEquiv n (sample i))
    (fun answers ↦
      .tick (smallBiasFourierEstimatorWork m U)
        (.pure
          ((∑ i : Fin m,
              answers i * monomial U (binaryCubeSignEquiv n (sample i))) / m)))

/-- The estimator program returns the empirical coefficient with its exact visible cost. -/
theorem DeterministicQueryProgram.runWithCost_smallBiasFourierEstimatorProgram
    (f : {−1,1}^[n] → ℝ) (sample : Fin m → F₂Cube n)
    (U : Finset (Fin n)) :
    DeterministicQueryProgram.runWithCost f
        (smallBiasFourierEstimatorProgram sample U) =
      (smallBiasFourierEstimate f sample U,
        smallBiasFourierEstimatorCost m U) := by
  rfl

/-- Multiplication by a Walsh monomial translates the Fourier frequency. -/
theorem fourierCoeff_pointwise_mul_monomial
    (f : {−1,1}^[n] → ℝ) (U S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f x * monomial U x) S =
      fourierCoeff f (U ∆ S) := by
  unfold fourierCoeff
  apply Finset.expect_congr rfl
  intro x _
  rw [mul_assoc, monomial_mul_monomial]

/-- Multiplication by a Walsh monomial preserves the Fourier `1`-norm. -/
theorem fourierOneNorm_pointwise_mul_monomial
    (f : {−1,1}^[n] → ℝ) (U : Finset (Fin n)) :
    fourierOneNorm (fun x ↦ f x * monomial U x) =
      fourierOneNorm f := by
  classical
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    { toFun := fun S ↦ U ∆ S
      invFun := fun S ↦ U ∆ S
      left_inv := by
        intro S
        ext i
        simp
      right_inv := by
        intro S
        ext i
        simp }
  unfold fourierOneNorm
  apply Fintype.sum_equiv e
  intro S
  rw [fourierCoeff_pointwise_mul_monomial]
  rfl

/-- The uniform mean of the modulated function is the requested Fourier coefficient. -/
theorem mean_pointwise_mul_monomial
    (f : {−1,1}^[n] → ℝ) (U : Finset (Fin n)) :
    mean (fun x ↦ f x * monomial U x) = fourierCoeff f U := by
  rw [mean_eq_fourierCoeff_empty, fourierCoeff_pointwise_mul_monomial]
  congr 1
  ext i
  simp [Finset.mem_symmDiff]

/-- The empirical coefficient is expectation under the sample's uniform pushforward density. -/
theorem smallBiasFourierEstimate_eq_uniformPushforward_expectation
    [NeZero m]
    (f : {−1,1}^[n] → ℝ) (sample : Fin m → F₂Cube n)
    (U : Finset (Fin n)) :
    smallBiasFourierEstimate f sample U =
      (ProbabilityDensity.uniformPushforward sample).expectation
        (fun x ↦
          f (binaryCubeSignEquiv n x) *
            monomial U (binaryCubeSignEquiv n x)) := by
  rw [ProbabilityDensity.expectation_uniformPushforward,
    Fintype.expect_eq_sum_div_card]
  simp [smallBiasFourierEstimate]

/-- A `δ`-biased finite sample estimates every Fourier coefficient to within
`‖f̂‖₁ δ`. -/
theorem abs_smallBiasFourierEstimate_sub_fourierCoeff_le
    [NeZero m]
    (f : {−1,1}^[n] → ℝ) (sample : Fin m → F₂Cube n)
    (U : Finset (Fin n)) {δ : ℝ}
    (hsample :
      (ProbabilityDensity.uniformPushforward sample).IsBiased δ)
    (hδ : 0 ≤ δ) :
    |smallBiasFourierEstimate f sample U - fourierCoeff f U| ≤
      fourierOneNorm f * δ := by
  rw [smallBiasFourierEstimate_eq_uniformPushforward_expectation,
    ← mean_pointwise_mul_monomial f U,
    ← fourierOneNorm_pointwise_mul_monomial f U]
  exact
    ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_mul
      (ProbabilityDensity.uniformPushforward sample)
      (fun x ↦ f x * monomial U x) hsample hδ

/-- Proposition 6.40's deterministic estimator guarantee, relative to a supplied
`(ε / s)`-biased finite sample.  The construction algorithm for that sample is the
separate Theorem 6.30 layer. -/
theorem abs_smallBiasFourierEstimate_sub_fourierCoeff_le_parameter
    [NeZero m]
    (f : {−1,1}^[n] → ℝ) (sample : Fin m → F₂Cube n)
    (U : Finset (Fin n)) {ε s : ℝ}
    (hε : 0 < ε) (_hεhalf : ε ≤ 1 / 2) (hs : 1 ≤ s)
    (hsample :
      (ProbabilityDensity.uniformPushforward sample).IsBiased (ε / s))
    (hf : fourierOneNorm f ≤ s) :
    |smallBiasFourierEstimate f sample U - fourierCoeff f U| ≤ ε := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hratio : 0 ≤ ε / s := div_nonneg hε.le hspos.le
  calc
    |smallBiasFourierEstimate f sample U - fourierCoeff f U| ≤
        fourierOneNorm f * (ε / s) :=
      abs_smallBiasFourierEstimate_sub_fourierCoeff_le
        f sample U hsample hratio
    _ ≤ s * (ε / s) :=
      mul_le_mul_of_nonneg_right hf hratio
    _ = ε := by field_simp [ne_of_gt hspos]

end FABL
