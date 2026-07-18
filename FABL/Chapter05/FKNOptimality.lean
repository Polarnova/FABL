/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter03.LowDegreeSpectralConcentration
import FABL.Chapter05.GaussianIsoperimetricAsymptotics
import FABL.Chapter05.HammingBallLimit

/-!
# Optimality of the improved FKN bound

Book item: Exercise 5.36.
-/

open Filter Finset ProbabilityTheory Set
open scoped BigOperators BooleanCube Topology

namespace FABL

/-- The Gaussian masses used to diagonalize Proposition 5.25. -/
noncomputable def fknOptimalityGaussianMass (q : ℕ) :
    Ioo (0 : ℝ) 1 :=
  ⟨1 / (((q + 2 : ℕ) : ℝ)), by positivity, by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (show 1 < q + 2 by omega)⟩

/-- The Gaussian quantile at the `q`-th target mass. -/
noncomputable def fknOptimalityThreshold (q : ℕ) : ℝ :=
  standardGaussianUpperQuantile (fknOptimalityGaussianMass q)

/-- The Gaussian isoperimetric boundary at the `q`-th target mass. -/
noncomputable def fknOptimalityGaussianBoundary (q : ℕ) : ℝ :=
  gaussianIsoperimetric
    ⟨(fknOptimalityGaussianMass q : ℝ),
      (fknOptimalityGaussianMass q).2.1.le,
      (fknOptimalityGaussianMass q).2.2.le⟩

@[simp] theorem standardGaussianUpperTail_fknOptimalityThreshold
    (q : ℕ) :
    standardGaussianUpperTail (fknOptimalityThreshold q) =
      (fknOptimalityGaussianMass q : ℝ) := by
  simpa only [fknOptimalityThreshold] using
    standardGaussianUpperTail_quantile
      (fknOptimalityGaussianMass q)

theorem fknOptimalityGaussianBoundary_eq_density (q : ℕ) :
    fknOptimalityGaussianBoundary q =
      gaussianPDFReal 0 1 (fknOptimalityThreshold q) := by
  simpa only [fknOptimalityGaussianBoundary,
    fknOptimalityThreshold] using
    gaussianIsoperimetric_apply_of_mem_Ioo
      (⟨(fknOptimalityGaussianMass q : ℝ),
        (fknOptimalityGaussianMass q).2.1.le,
        (fknOptimalityGaussianMass q).2.2.le⟩ : unitInterval)
      (fknOptimalityGaussianMass q).2

theorem fknOptimalityGaussianBoundary_pos (q : ℕ) :
    0 < fknOptimalityGaussianBoundary q := by
  rw [fknOptimalityGaussianBoundary_eq_density]
  exact gaussianPDFReal_pos 0 1 (fknOptimalityThreshold q)
    (by norm_num)

private theorem tendsto_fknOptimalityGaussianMass_zero :
    Tendsto
      (fun q : ℕ ↦ (fknOptimalityGaussianMass q : ℝ))
      atTop (𝓝 0) := by
  have h :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
  change Tendsto
    (fun q : ℕ ↦ (1 : ℝ) / (((q + 2 : ℕ) : ℝ)))
    atTop (𝓝 0) at h
  simpa only [fknOptimalityGaussianMass] using h

private theorem tendsto_fknOptimalityGaussianMass_atBot :
    Tendsto fknOptimalityGaussianMass
      atTop (atBot : Filter (Ioo (0 : ℝ) 1)) := by
  rw [tendsto_Ioo_atBot]
  exact tendsto_nhdsWithin_iff.2
    ⟨tendsto_fknOptimalityGaussianMass_zero,
      Eventually.of_forall fun q ↦
        (fknOptimalityGaussianMass q).2.1⟩

/-- The simultaneous mass and level-one approximation required at stage
`q` of the diagonal construction. -/
def IsFKNOptimalityApproximation (q r : ℕ) : Prop :=
  |(𝔼 x : {−1,1}^[r + 1],
      hammingUpperTailIndicator
        (fknOptimalityThreshold q) (r + 1) x) -
      (fknOptimalityGaussianMass q : ℝ)| <
        (fknOptimalityGaussianMass q : ℝ) / 2 ∧
    |fourierWeightAtLevel 1
        (hammingUpperTailIndicator
          (fknOptimalityThreshold q) (r + 1)) -
      fknOptimalityGaussianBoundary q ^ 2| <
        fknOptimalityGaussianBoundary q ^ 2 / 2

private theorem exists_fknOptimalityApproximation (q : ℕ) :
    ∃ r : ℕ, IsFKNOptimalityApproximation q r := by
  have hmass :=
    (proposition5_25 (fknOptimalityThreshold q)).1
  rw [standardGaussianUpperTail_fknOptimalityThreshold] at hmass
  have hweight :=
    (proposition5_25 (fknOptimalityThreshold q)).2
  rw [← fknOptimalityGaussianBoundary_eq_density] at hweight
  have hmassEventually :
      ∀ᶠ r : ℕ in atTop,
        |(𝔼 x : {−1,1}^[r + 1],
            hammingUpperTailIndicator
              (fknOptimalityThreshold q) (r + 1) x) -
          (fknOptimalityGaussianMass q : ℝ)| <
            (fknOptimalityGaussianMass q : ℝ) / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hmass.eventually
        (Metric.ball_mem_nhds
          (fknOptimalityGaussianMass q : ℝ)
          (half_pos (fknOptimalityGaussianMass q).2.1))
  have hweightEventually :
      ∀ᶠ r : ℕ in atTop,
        |fourierWeightAtLevel 1
            (hammingUpperTailIndicator
              (fknOptimalityThreshold q) (r + 1)) -
          fknOptimalityGaussianBoundary q ^ 2| <
            fknOptimalityGaussianBoundary q ^ 2 / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hweight.eventually
        (Metric.ball_mem_nhds
          (fknOptimalityGaussianBoundary q ^ 2)
          (half_pos
            (sq_pos_of_pos
              (fknOptimalityGaussianBoundary_pos q))))
  exact (hmassEventually.and hweightEventually).exists

/-- A dimension index at which both approximations for stage `q` hold. -/
noncomputable def fknOptimalityDimensionIndex (q : ℕ) : ℕ :=
  Classical.choose (exists_fknOptimalityApproximation q)

theorem fknOptimalityDimensionIndex_spec (q : ℕ) :
    IsFKNOptimalityApproximation q
      (fknOptimalityDimensionIndex q) :=
  Classical.choose_spec (exists_fknOptimalityApproximation q)

/-- The Hamming-tail dimension selected at stage `q`. -/
noncomputable def fknOptimalityTailDimension (q : ℕ) : ℕ :=
  fknOptimalityDimensionIndex q + 1

/-- The small Hamming upper-tail set selected at stage `q`. -/
noncomputable def fknOptimalitySmallSet (q : ℕ) :
    {−1,1}^[fknOptimalityTailDimension q] → ℝ :=
  hammingUpperTailIndicator
    (fknOptimalityThreshold q) (fknOptimalityTailDimension q)

/-- The uniform mass of the selected Hamming upper-tail set. -/
noncomputable def fknOptimalitySmallSetMass (q : ℕ) : ℝ :=
  𝔼 x : {−1,1}^[fknOptimalityTailDimension q],
    fknOptimalitySmallSet q x

theorem fknOptimalitySmallSetMass_approx (q : ℕ) :
    |fknOptimalitySmallSetMass q -
        (fknOptimalityGaussianMass q : ℝ)| <
      (fknOptimalityGaussianMass q : ℝ) / 2 := by
  change
    |(𝔼 x : {−1,1}^[fknOptimalityDimensionIndex q + 1],
        hammingUpperTailIndicator
          (fknOptimalityThreshold q)
          (fknOptimalityDimensionIndex q + 1) x) -
        (fknOptimalityGaussianMass q : ℝ)| <
      (fknOptimalityGaussianMass q : ℝ) / 2
  exact (fknOptimalityDimensionIndex_spec q).1

theorem fknOptimalitySmallSetWeight_approx (q : ℕ) :
    |fourierWeightAtLevel 1 (fknOptimalitySmallSet q) -
        fknOptimalityGaussianBoundary q ^ 2| <
      fknOptimalityGaussianBoundary q ^ 2 / 2 := by
  simpa only [IsFKNOptimalityApproximation,
    fknOptimalityTailDimension, fknOptimalitySmallSet] using
    (fknOptimalityDimensionIndex_spec q).2

theorem fknOptimalitySmallSetMass_pos (q : ℕ) :
    0 < fknOptimalitySmallSetMass q := by
  have hleft :=
    (abs_lt.mp (fknOptimalitySmallSetMass_approx q)).1
  nlinarith [(fknOptimalityGaussianMass q).2.1]

theorem fknOptimalityGaussianMass_lt_two_mul_smallSetMass
    (q : ℕ) :
    (fknOptimalityGaussianMass q : ℝ) <
      2 * fknOptimalitySmallSetMass q := by
  have hleft :=
    (abs_lt.mp (fknOptimalitySmallSetMass_approx q)).1
  linarith

theorem two_mul_fknOptimalitySmallSetMass_lt_three_mul_gaussianMass
    (q : ℕ) :
    2 * fknOptimalitySmallSetMass q <
      3 * (fknOptimalityGaussianMass q : ℝ) := by
  have hright :=
    (abs_lt.mp (fknOptimalitySmallSetMass_approx q)).2
  linarith

theorem fknOptimalitySmallSetWeight_gt_half_boundary_sq (q : ℕ) :
    fknOptimalityGaussianBoundary q ^ 2 / 2 <
      fourierWeightAtLevel 1 (fknOptimalitySmallSet q) := by
  have hleft :=
    (abs_lt.mp (fknOptimalitySmallSetWeight_approx q)).1
  nlinarith

/-- The closeness parameter forced by the exact distinguished Fourier
coefficient. -/
noncomputable def fknOptimalityDelta (q : ℕ) : ℝ :=
  2 * fknOptimalitySmallSetMass q

theorem fknOptimalityDelta_pos (q : ℕ) :
    0 < fknOptimalityDelta q := by
  exact mul_pos (by norm_num) (fknOptimalitySmallSetMass_pos q)

theorem fknOptimalityGaussianMass_lt_delta (q : ℕ) :
    (fknOptimalityGaussianMass q : ℝ) <
      fknOptimalityDelta q := by
  exact fknOptimalityGaussianMass_lt_two_mul_smallSetMass q

theorem fknOptimalityDelta_lt_three_mul_gaussianMass (q : ℕ) :
    fknOptimalityDelta q <
      3 * (fknOptimalityGaussianMass q : ℝ) := by
  exact
    two_mul_fknOptimalitySmallSetMass_lt_three_mul_gaussianMass q

theorem tendsto_fknOptimalityDelta :
    Tendsto fknOptimalityDelta atTop (𝓝 0) := by
  apply squeeze_zero
  · exact fun q ↦ (fknOptimalityDelta_pos q).le
  · exact fun q ↦
      (fknOptimalityDelta_lt_three_mul_gaussianMass q).le
  · simpa only [mul_zero] using
      tendsto_fknOptimalityGaussianMass_zero.const_mul 3

/-- The Boolean function obtained by changing a dictator only on the
selected Hamming set in its negative slice. -/
noncomputable def fknOptimalityFunction (q : ℕ) :
    BooleanFunction (fknOptimalityTailDimension q + 1) :=
  fun z ↦
    if fknOptimalitySmallSet q (Fin.tail z) = 1
    then 1
    else z 0

private theorem fknOptimalityFunction_toReal_cons_one
    (q : ℕ) (x : {−1,1}^[fknOptimalityTailDimension q]) :
    (fknOptimalityFunction q).toReal (Fin.cons 1 x) = 1 := by
  simp [fknOptimalityFunction, BooleanFunction.toReal]

private theorem fknOptimalityFunction_toReal_cons_neg_one
    (q : ℕ) (x : {−1,1}^[fknOptimalityTailDimension q]) :
    (fknOptimalityFunction q).toReal (Fin.cons (-1) x) =
      2 * fknOptimalitySmallSet q x - 1 := by
  by_cases h :
      fknOptimalityThreshold q <
        normalizedRademacherSum (fknOptimalityTailDimension q) x
  · simp [fknOptimalityFunction, fknOptimalitySmallSet,
      hammingUpperTailIndicator, h, BooleanFunction.toReal]
    norm_num
  · simp [fknOptimalityFunction, fknOptimalitySmallSet,
      hammingUpperTailIndicator, h, BooleanFunction.toReal]

private theorem firstCoordinateSlice_fknOptimalityFunction_one
    (q : ℕ) :
    firstCoordinateSlice (fknOptimalityFunction q).toReal 1 =
      fun _ ↦ 1 := by
  funext x
  exact fknOptimalityFunction_toReal_cons_one q x

private theorem firstCoordinateSlice_fknOptimalityFunction_neg_one
    (q : ℕ) :
    firstCoordinateSlice (fknOptimalityFunction q).toReal (-1) =
      fun x ↦ 2 * fknOptimalitySmallSet q x - 1 := by
  funext x
  exact fknOptimalityFunction_toReal_cons_neg_one q x

private theorem fourierCoeff_fknOptimalityLowerSlice_empty
    (q : ℕ) :
    fourierCoeff
        (fun x ↦ 2 * fknOptimalitySmallSet q x - 1)
        ∅ =
      2 * fknOptimalitySmallSetMass q - 1 := by
  unfold fourierCoeff
  simp only [monomial, Finset.prod_empty, mul_one]
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect]
  simp [fknOptimalitySmallSetMass]

private theorem fourierCoeff_fknOptimalityLowerSlice_singleton
    (q : ℕ) (i : Fin (fknOptimalityTailDimension q)) :
    fourierCoeff
        (fun x ↦ 2 * fknOptimalitySmallSet q x - 1)
        {i} =
      2 * fourierCoeff (fknOptimalitySmallSet q) {i} := by
  unfold fourierCoeff
  rw [show
      (fun x ↦
        (2 * fknOptimalitySmallSet q x - 1) * monomial {i} x) =
        fun x ↦
          2 * (fknOptimalitySmallSet q x * monomial {i} x) -
            monomial {i} x by
      funext x
      ring,
    Finset.expect_sub_distrib, ← Finset.mul_expect,
    expect_monomial]
  simp

/-- The distinguished singleton coefficient is exactly
`1 - δ / 2` at every stage. -/
theorem fourierCoeff_fknOptimalityFunction_zero (q : ℕ) :
    fourierCoeff (fknOptimalityFunction q).toReal
        {(0 : Fin (fknOptimalityTailDimension q + 1))} =
      1 - fknOptimalityDelta q / 2 := by
  have hfrequency :
      ({(0 : Fin (fknOptimalityTailDimension q + 1))} :
          Finset (Fin (fknOptimalityTailDimension q + 1))) =
        insert 0
          (tailFrequency
            (∅ : Finset (Fin (fknOptimalityTailDimension q)))) := by
    simp [tailFrequency]
  rw [hfrequency, fourierCoeff_insert_zero_tailFrequency,
    firstCoordinateSlice_fknOptimalityFunction_one,
    firstCoordinateSlice_fknOptimalityFunction_neg_one,
    fourierCoeff_fknOptimalityLowerSlice_empty]
  simp only [fourierCoeff, monomial, Finset.prod_empty, mul_one,
    Fintype.expect_const]
  simp [fknOptimalityDelta]
  ring

/-- Every tail singleton coefficient of the Boolean construction is the
corresponding singleton coefficient of its selected Hamming set. -/
theorem fourierCoeff_fknOptimalityFunction_succ
    (q : ℕ) (i : Fin (fknOptimalityTailDimension q)) :
    fourierCoeff (fknOptimalityFunction q).toReal {i.succ} =
      fourierCoeff (fknOptimalitySmallSet q) {i} := by
  have hfrequency :
      ({i.succ} :
          Finset (Fin (fknOptimalityTailDimension q + 1))) =
        tailFrequency ({i} :
          Finset (Fin (fknOptimalityTailDimension q))) := by
    simp [tailFrequency]
  rw [hfrequency, fourierCoeff_tailFrequency,
    firstCoordinateSlice_fknOptimalityFunction_one,
    firstCoordinateSlice_fknOptimalityFunction_neg_one,
    fourierCoeff_fknOptimalityLowerSlice_singleton]
  have hone :
      fourierCoeff
          (fun _ : {−1,1}^[fknOptimalityTailDimension q] ↦ (1 : ℝ))
          {i} = 0 := by
    simp [fourierCoeff, expect_monomial]
  rw [hone]
  ring

/-- The level-one weight splits into the squared distinguished
coefficient and the level-one weight of the selected Hamming set. -/
theorem fourierWeightAtLevel_one_fknOptimalityFunction (q : ℕ) :
    fourierWeightAtLevel 1 (fknOptimalityFunction q).toReal =
      (1 - fknOptimalitySmallSetMass q) ^ 2 +
        fourierWeightAtLevel 1 (fknOptimalitySmallSet q) := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton,
    Fin.sum_univ_succ,
    fourierCoeff_fknOptimalityFunction_zero]
  simp_rw [fourierCoeff_fknOptimalityFunction_succ]
  rw [← fourierWeightAtLevel_one_eq_sum_singleton]
  simp [fknOptimalityDelta]

/-- The exact level-one identity in terms of the closeness parameter. -/
theorem fourierWeightAtLevel_one_fknOptimalityFunction_eq_delta
    (q : ℕ) :
    fourierWeightAtLevel 1 (fknOptimalityFunction q).toReal =
      1 - fknOptimalityDelta q +
        fknOptimalityDelta q ^ 2 / 4 +
        fourierWeightAtLevel 1 (fknOptimalitySmallSet q) := by
  rw [fourierWeightAtLevel_one_fknOptimalityFunction]
  simp [fknOptimalityDelta]
  ring

/-- The principal asymptotic scale in Proposition 5.27 along the chosen
Gaussian masses. -/
noncomputable def fknOptimalityGaussianMain (q : ℕ) : ℝ :=
  (fknOptimalityGaussianMass q : ℝ) *
    Real.sqrt
      (2 * Real.log
        (1 / (fknOptimalityGaussianMass q : ℝ)))

private theorem one_lt_inv_fknOptimalityGaussianMass (q : ℕ) :
    1 < 1 / (fknOptimalityGaussianMass q : ℝ) := by
  apply (lt_div_iff₀ (fknOptimalityGaussianMass q).2.1).2
  simpa using (fknOptimalityGaussianMass q).2.2

private theorem fknOptimalityGaussianMain_pos (q : ℕ) :
    0 < fknOptimalityGaussianMain q := by
  unfold fknOptimalityGaussianMain
  exact mul_pos (fknOptimalityGaussianMass q).2.1 <|
    Real.sqrt_pos.2 <|
      mul_pos (by norm_num) <|
        Real.log_pos (one_lt_inv_fknOptimalityGaussianMass q)

private theorem fknOptimalityGaussianBoundary_isEquivalent_main :
    Asymptotics.IsEquivalent atTop
      fknOptimalityGaussianBoundary
      fknOptimalityGaussianMain := by
  exact gaussianIsoperimetric_isEquivalent_atBot.comp_tendsto
    tendsto_fknOptimalityGaussianMass_atBot

private theorem eventually_half_fknOptimalityGaussianMain_lt_boundary :
    ∀ᶠ q : ℕ in atTop,
      fknOptimalityGaussianMain q / 2 <
        fknOptimalityGaussianBoundary q := by
  have hmainNe :
      ∀ᶠ q : ℕ in atTop,
        fknOptimalityGaussianMain q ≠ 0 :=
    Eventually.of_forall fun q ↦
      (fknOptimalityGaussianMain_pos q).ne'
  have hratio :
      Tendsto
        (fun q ↦
          fknOptimalityGaussianBoundary q /
            fknOptimalityGaussianMain q)
        atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hmainNe).1
      fknOptimalityGaussianBoundary_isEquivalent_main
  have hhalf :
      ∀ᶠ q : ℕ in atTop,
        (1 / 2 : ℝ) <
          fknOptimalityGaussianBoundary q /
            fknOptimalityGaussianMain q :=
    hratio.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hhalf] with q hq
  have :=
    (lt_div_iff₀ (fknOptimalityGaussianMain_pos q)).1 hq
  nlinarith

private theorem fknOptimalityGaussianMain_sq (q : ℕ) :
    fknOptimalityGaussianMain q ^ 2 =
      2 * (fknOptimalityGaussianMass q : ℝ) ^ 2 *
        Real.log
          (1 / (fknOptimalityGaussianMass q : ℝ)) := by
  have hlog :
      0 ≤ Real.log
        (1 / (fknOptimalityGaussianMass q : ℝ)) :=
    (Real.log_pos
      (one_lt_inv_fknOptimalityGaussianMass q)).le
  rw [fknOptimalityGaussianMain, mul_pow,
    Real.sq_sqrt (mul_nonneg (by norm_num) hlog)]
  ring

private theorem eventually_gaussianMass_sq_log_div_two_lt_boundary_sq :
    ∀ᶠ q : ℕ in atTop,
      (fknOptimalityGaussianMass q : ℝ) ^ 2 *
          Real.log
            (1 / (fknOptimalityGaussianMass q : ℝ)) / 2 <
        fknOptimalityGaussianBoundary q ^ 2 := by
  filter_upwards
      [eventually_half_fknOptimalityGaussianMain_lt_boundary]
      with q hhalf
  have hsquare :
      (fknOptimalityGaussianMain q / 2) ^ 2 <
        fknOptimalityGaussianBoundary q ^ 2 :=
    (sq_lt_sq₀
      (div_nonneg (fknOptimalityGaussianMain_pos q).le
        (by norm_num))
      (fknOptimalityGaussianBoundary_pos q).le).2 hhalf
  nlinarith [fknOptimalityGaussianMain_sq q]

private theorem eventually_gaussianMass_sq_log_div_four_lt_smallSetWeight :
    ∀ᶠ q : ℕ in atTop,
      (fknOptimalityGaussianMass q : ℝ) ^ 2 *
          Real.log
            (1 / (fknOptimalityGaussianMass q : ℝ)) / 4 <
        fourierWeightAtLevel 1 (fknOptimalitySmallSet q) := by
  filter_upwards
      [eventually_gaussianMass_sq_log_div_two_lt_boundary_sq]
      with q hboundary
  have hselected :=
    fknOptimalitySmallSetWeight_gt_half_boundary_sq q
  linarith

private theorem fknOptimalityDelta_sq_log_le
    (q : ℕ) (hdelta : fknOptimalityDelta q < 1) :
    fknOptimalityDelta q ^ 2 *
        Real.log (1 / fknOptimalityDelta q) ≤
      9 * ((fknOptimalityGaussianMass q : ℝ) ^ 2 *
        Real.log
          (1 / (fknOptimalityGaussianMass q : ℝ))) := by
  have hαpos := (fknOptimalityGaussianMass q).2.1
  have hδpos := fknOptimalityDelta_pos q
  have hαδ :
      (fknOptimalityGaussianMass q : ℝ) ≤
        fknOptimalityDelta q :=
    (fknOptimalityGaussianMass_lt_delta q).le
  have hδα :
      fknOptimalityDelta q ≤
        3 * (fknOptimalityGaussianMass q : ℝ) :=
    (fknOptimalityDelta_lt_three_mul_gaussianMass q).le
  have hinv :
      1 / fknOptimalityDelta q ≤
        1 / (fknOptimalityGaussianMass q : ℝ) :=
    one_div_le_one_div_of_le hαpos hαδ
  have hlog :
      Real.log (1 / fknOptimalityDelta q) ≤
        Real.log
          (1 / (fknOptimalityGaussianMass q : ℝ)) :=
    (Real.strictMonoOn_log.le_iff_le
      (one_div_pos.mpr hδpos)
      (one_div_pos.mpr hαpos)).2 hinv
  have hlogDeltaNonneg :
      0 ≤ Real.log (1 / fknOptimalityDelta q) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hδpos).2 (by linarith)
  have hsquare :
      fknOptimalityDelta q ^ 2 ≤
        9 * (fknOptimalityGaussianMass q : ℝ) ^ 2 := by
    nlinarith
  calc
    fknOptimalityDelta q ^ 2 *
          Real.log (1 / fknOptimalityDelta q) ≤
        (9 * (fknOptimalityGaussianMass q : ℝ) ^ 2) *
          Real.log (1 / fknOptimalityDelta q) :=
      mul_le_mul_of_nonneg_right hsquare hlogDeltaNonneg
    _ ≤
        (9 * (fknOptimalityGaussianMass q : ℝ) ^ 2) *
          Real.log
            (1 / (fknOptimalityGaussianMass q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ =
        9 * ((fknOptimalityGaussianMass q : ℝ) ^ 2 *
          Real.log
            (1 / (fknOptimalityGaussianMass q : ℝ))) := by
      ring

private theorem eventually_fknOptimalityDelta_lt_one :
    ∀ᶠ q : ℕ in atTop, fknOptimalityDelta q < 1 :=
  tendsto_fknOptimalityDelta.eventually
    (Iio_mem_nhds (by norm_num))

private theorem eventually_fknOptimalityGain :
    ∀ᶠ q : ℕ in atTop,
      (1 / 36 : ℝ) * fknOptimalityDelta q ^ 2 *
          Real.log (1 / fknOptimalityDelta q) ≤
        fourierWeightAtLevel 1 (fknOptimalitySmallSet q) := by
  filter_upwards
      [eventually_fknOptimalityDelta_lt_one,
        eventually_gaussianMass_sq_log_div_four_lt_smallSetWeight]
      with q hdelta hweight
  have hcompare :=
    fknOptimalityDelta_sq_log_le q hdelta
  nlinarith

/-- Exercise 5.36's quantitative lower bound, with the universal
Omega constant `1 / 36`. -/
theorem eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower :
    ∀ᶠ q : ℕ in atTop,
      1 - fknOptimalityDelta q +
          (1 / 36 : ℝ) * fknOptimalityDelta q ^ 2 *
            Real.log (1 / fknOptimalityDelta q) ≤
        fourierWeightAtLevel 1 (fknOptimalityFunction q).toReal := by
  filter_upwards [eventually_fknOptimalityGain] with q hgain
  rw [fourierWeightAtLevel_one_fknOptimalityFunction_eq_delta]
  nlinarith [sq_nonneg (fknOptimalityDelta q)]

/-- Exercise 5.36: a full sequence of Boolean functions and positive
parameters tending to zero with exact distinguished coefficient and the
optimal second-order lower bound. -/
theorem exercise5_36 :
    ∃ dimensions : ℕ → ℕ,
      ∃ functions :
          (q : ℕ) → BooleanFunction (dimensions q + 1),
        ∃ delta : ℕ → ℝ,
          (∀ q, 0 < delta q) ∧
          Tendsto delta atTop (𝓝 0) ∧
          (∀ q,
            fourierCoeff (functions q).toReal
                {(0 : Fin (dimensions q + 1))} =
              1 - delta q / 2) ∧
          ∃ c : ℝ, 0 < c ∧
            ∀ᶠ q : ℕ in atTop,
              1 - delta q +
                  c * delta q ^ 2 *
                    Real.log (1 / delta q) ≤
                fourierWeightAtLevel 1 (functions q).toReal := by
  refine ⟨fknOptimalityTailDimension,
    fknOptimalityFunction, fknOptimalityDelta,
    fknOptimalityDelta_pos, tendsto_fknOptimalityDelta,
    fourierCoeff_fknOptimalityFunction_zero,
    (1 / 36 : ℝ), by norm_num, ?_⟩
  exact
    eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower

end FABL
