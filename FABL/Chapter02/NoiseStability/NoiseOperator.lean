/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.GaussianDisagreement

/-!
# Noise operator and stability

Book items: Definition 2.42, Definition 2.43, Definition 2.46, Fact 2.48, Proposition 2.47, Theorem
2.45.

The noise operator, noise stability, noise sensitivity, and the majority limit from Section 2.4
of O'Donnell's *Analysis of Boolean Functions*.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance noiseOperatorSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance noiseOperatorSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- O'Donnell, Definition 2.46: the Fourier multiplier form of the noise operator.  The
construction uses the Walsh basis to obtain linearity by construction. -/
noncomputable def noiseOperator (ρ : ℝ) :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) :=
  (walshBasis n).constr ℝ fun S ↦ ρ ^ S.card • monomial S

/-- O'Donnell, Proposition 2.47: each Walsh character is an eigenfunction of the noise
operator, with eigenvalue `ρ ^ |S|`. -/
@[simp] theorem noiseOperator_monomial (ρ : ℝ) (S : Finset (Fin n)) :
    noiseOperator ρ (monomial S) = ρ ^ S.card • monomial S := by
  rw [noiseOperator]
  have hbasis : walshBasis n S = monomial S := parity_orthonormal_basis.1 S
  simpa only [hbasis] using
    (Module.Basis.constr_basis (walshBasis n) ℝ
      (fun T : Finset (Fin n) ↦ ρ ^ T.card • monomial T) S)

/-- O'Donnell, Proposition 2.47: pointwise form of the Walsh-character eigenvalue identity. -/
theorem noiseOperator_monomial_apply (ρ : ℝ) (S : Finset (Fin n))
    (x : {−1,1}^[n]) :
    noiseOperator ρ (monomial S) x = ρ ^ S.card * monomial S x := by
  rw [noiseOperator_monomial]
  rfl

/-- The conditional-expectation realization of the noise operator. -/
private noncomputable def kernelNoiseOperator
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) where
  toFun f x := pmfExpectation (noiseKernel ρ hρ x) f
  map_add' f g := by
    funext x
    unfold pmfExpectation
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  map_smul' c f := by
    funext x
    unfold pmfExpectation
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

/-- The Fourier multiplier and conditional-expectation constructions of `Tρ` agree. -/
private theorem kernelNoiseOperator_eq_noiseOperator
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    kernelNoiseOperator ρ hρ = (noiseOperator ρ :
      ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ)) := by
  apply (walshBasis n).ext
  intro S
  funext x
  have hbasis : walshBasis n S = monomial S := parity_orthonormal_basis.1 S
  rw [hbasis, kernelNoiseOperator, noiseOperator_monomial_apply]
  exact pmfExpectation_noiseKernel_monomial ρ hρ x S

/-- O'Donnell, Definition 2.46: conditional expectation under `Nρ(x)` equals evaluation of
the Fourier-multiplier noise operator. -/
theorem noiseOperator_apply_eq_pmfExpectation
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    noiseOperator ρ f x = pmfExpectation (noiseKernel ρ hρ x) f := by
  rw [← kernelNoiseOperator_eq_noiseOperator ρ hρ]
  rfl

/-- O'Donnell, Definition 2.42: noise stability is the expected product over the honest
`ρ`-correlated pair distribution. -/
noncomputable def noiseStability (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) : ℝ :=
  pmfExpectation (correlatedPairPMF ρ hρ) fun xy ↦ f xy.1 * f xy.2

/-- O'Donnell, Definition 2.42: disagreement probability of a Boolean function on a
`ρ`-correlated pair. -/
noncomputable def correlatedDisagreementProbability
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) : ℝ :=
  pmfExpectation (correlatedPairPMF ρ hρ)
    fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0

/-- For odd arity, the CLT normalized-sum measure of the opposite-sign region is exactly the
correlated disagreement probability of majority. -/
theorem coe_normalizedCorrelatedSignSumMeasure_disagreement_eq_majority
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ} (hn : Odd n) :
    ((normalizedCorrelatedSignSumMeasure ρ hρ n gaussianDisagreementRegion : NNReal) : ℝ) =
      correlatedDisagreementProbability ρ hρ (majority n) := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [← integral_indicator_one isOpen_gaussianDisagreementRegion.measurableSet]
  rw [normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF]
  change (∫ x : CorrelationPlane,
      gaussianDisagreementRegion.indicator (fun _ ↦ (1 : ℝ)) x
        ∂(correlatedPairPMF (n := n) ρ hρ).toMeasure.map
          (normalizedCorrelatedPairSum n)) = _
  rw [integral_map (measurable_of_finite (normalizedCorrelatedPairSum n)).aemeasurable
    (((measurable_const : Measurable (fun _ : CorrelationPlane ↦ (1 : ℝ))).indicator
      isOpen_gaussianDisagreementRegion.measurableSet).aestronglyMeasurable)]
  rw [← pmfExpectation_eq_integral]
  unfold correlatedDisagreementProbability pmfExpectation
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hxy : majority n xy.1 ≠ majority n xy.2
  · have hmem : normalizedCorrelatedPairSum n xy ∈ gaussianDisagreementRegion :=
      (normalizedCorrelatedPairSum_mem_disagreement_iff_majority_ne hn xy).2 hxy
    simp [Set.indicator_of_mem hmem, hxy]
  · have hmem : normalizedCorrelatedPairSum n xy ∉ gaussianDisagreementRegion := by
      simpa only [normalizedCorrelatedPairSum_mem_disagreement_iff_majority_ne hn xy] using hxy
    simp [Set.indicator_of_notMem hmem, hxy]

/-- O'Donnell, Theorem 2.45, disagreement form: the disagreement probability of odd majority
converges to the Gaussian angle `arccos ρ / π`. -/
theorem tendsto_correlatedDisagreementProbability_majority_odd
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto
      (fun k ↦ correlatedDisagreementProbability ρ hρ (majority (2 * k + 1)))
      atTop (𝓝 (Real.arccos ρ / Real.pi)) := by
  have hindex : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  have hnn :=
    (normalizedCorrelatedSignSumMeasure_disagreement_tendsto ρ hρ).comp hindex
  have hreal :
      Tendsto
        (fun k ↦ ((normalizedCorrelatedSignSumMeasure ρ hρ (2 * k + 1)
          gaussianDisagreementRegion : NNReal) : ℝ))
        atTop
        (𝓝 (((correlatedGaussianMeasure ρ gaussianDisagreementRegion : NNReal) : ℝ))) :=
    NNReal.tendsto_coe.2 hnn
  have hlimit :
      ((correlatedGaussianMeasure ρ gaussianDisagreementRegion : NNReal) : ℝ) =
        Real.arccos ρ / Real.pi := by
    rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
    change ((correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      gaussianDisagreementRegion).toReal = _
    rw [correlatedGaussianMeasure_disagreement ρ hρ, ENNReal.toReal_ofReal]
    exact div_nonneg (Real.arccos_nonneg ρ) Real.pi_pos.le
  rw [hlimit] at hreal
  have hodd (k : ℕ) : Odd (2 * k + 1) := by
    refine ⟨k, ?_⟩
    omega
  have hfun :
      (fun k ↦ ((normalizedCorrelatedSignSumMeasure ρ hρ (2 * k + 1)
        gaussianDisagreementRegion : NNReal) : ℝ)) =
        fun k ↦ correlatedDisagreementProbability ρ hρ (majority (2 * k + 1)) := by
    funext k
    exact coe_normalizedCorrelatedSignSumMeasure_disagreement_eq_majority ρ hρ (hodd k)
  rw [hfun] at hreal
  exact hreal

/-- The two standard trigonometric forms of the majority-stability limit agree. -/
theorem two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos (ρ : ℝ) :
    2 / Real.pi * Real.arcsin ρ =
      1 - 2 / Real.pi * Real.arccos ρ := by
  rw [Real.arcsin_eq_pi_div_two_sub_arccos]
  field_simp [Real.pi_ne_zero]

/-- O'Donnell, Definition 2.42: agreement probability of a Boolean function on a
`ρ`-correlated pair. -/
noncomputable def correlatedAgreementProbability
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) : ℝ :=
  pmfExpectation (correlatedPairPMF ρ hρ)
    fun xy ↦ if f xy.1 = f xy.2 then 1 else 0

/-- O'Donnell, Definition 2.43: the interval proof converting a bit-flip probability to its
correlation parameter. -/
theorem one_sub_two_mul_mem_Icc (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    1 - 2 * δ ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor <;> linarith [hδ.1, hδ.2]

/-- O'Donnell, Definition 2.43: noise sensitivity is the probability that a Boolean function
changes under independent bit reversals of probability `δ`. -/
noncomputable def noiseSensitivity (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) : ℝ :=
  pmfExpectation
    (correlatedPairPMF (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ))
    fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0

/-- O'Donnell, Fact 2.48: stability is the normalized inner product with the noise operator. -/
theorem noiseStability_eq_uniformInner_noiseOperator
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) :
    noiseStability ρ hρ f = ⟪f, noiseOperator ρ f⟫ᵤ := by
  unfold noiseStability correlatedPairPMF
  rw [pmfExpectation_bind]
  simp_rw [pmfExpectation_map]
  rw [pmfExpectation_uniformPMF_eq_expect]
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect]
  apply Finset.expect_congr rfl
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  change pmfExpectation (noiseKernel ρ hρ x) (fun y ↦ f x * f y) =
    noiseOperator ρ f x * f x
  rw [pmfExpectation_const_mul, noiseOperator_apply_eq_pmfExpectation ρ hρ]
  ring

/-- PMF expectation preserves subtraction. -/
private theorem pmfExpectation_sub {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (f g : Ω → ℝ) :
    pmfExpectation p (fun x ↦ f x - g x) = pmfExpectation p f - pmfExpectation p g := by
  unfold pmfExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- PMF expectation preserves division by a scalar. -/
private theorem pmfExpectation_div {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (f : Ω → ℝ) (c : ℝ) :
    pmfExpectation p (fun x ↦ f x / c) = pmfExpectation p f / c := by
  unfold pmfExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Boolean disagreement is encoded by one half of one minus the product of the two signs. -/
private theorem boolean_disagreement_indicator (f : BooleanFunction n)
    (x y : {−1,1}^[n]) :
    (if f x ≠ f y then (1 : ℝ) else 0) =
      (1 - f.toReal x * f.toReal y) / 2 := by
  rcases Int.units_eq_one_or (f x) with hx | hx <;>
    rcases Int.units_eq_one_or (f y) with hy | hy <;>
    simp [BooleanFunction.toReal, hx, hy]

/-- O'Donnell, Definition 2.43: the equivalent relation between Boolean noise sensitivity
and noise stability. -/
theorem noiseSensitivity_eq_half_sub_half_noiseStability
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    noiseSensitivity δ hδ f =
      (1 - noiseStability (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ) f.toReal) / 2 := by
  let p : PMF ({−1,1}^[n] × {−1,1}^[n]) :=
    correlatedPairPMF (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ)
  unfold noiseSensitivity noiseStability
  change pmfExpectation p (fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0) = _
  rw [show pmfExpectation p (fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0) =
      pmfExpectation p (fun xy ↦ (1 - f.toReal xy.1 * f.toReal xy.2) / 2) by
    apply Finset.sum_congr rfl
    intro xy _
    simp only
    rw [boolean_disagreement_indicator]]
  rw [pmfExpectation_div, pmfExpectation_sub, pmfExpectation_const_one]

/-- O'Donnell, Definition 2.42: disagreement probability is one half minus one half of
Boolean noise stability. -/
theorem correlatedDisagreementProbability_eq
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    correlatedDisagreementProbability ρ hρ f =
      (1 - noiseStability ρ hρ f.toReal) / 2 := by
  let p : PMF ({−1,1}^[n] × {−1,1}^[n]) := correlatedPairPMF ρ hρ
  unfold correlatedDisagreementProbability noiseStability
  change pmfExpectation p (fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0) = _
  rw [show pmfExpectation p (fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0) =
      pmfExpectation p (fun xy ↦ (1 - f.toReal xy.1 * f.toReal xy.2) / 2) by
    apply Finset.sum_congr rfl
    intro xy _
    simp only
    rw [boolean_disagreement_indicator]]
  rw [pmfExpectation_div, pmfExpectation_sub, pmfExpectation_const_one]

/-- O'Donnell, Theorem 2.45: the noise stability of odd majority converges to the Gaussian
arcsine law. -/
theorem tendsto_noiseStability_majority_odd
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto
      (fun k ↦ noiseStability ρ hρ (majority (2 * k + 1)).toReal)
      atTop (𝓝 (2 / Real.pi * Real.arcsin ρ)) := by
  have hdis := tendsto_correlatedDisagreementProbability_majority_odd ρ hρ
  have hlimit :
      Tendsto
        (fun k ↦ 1 - 2 *
          correlatedDisagreementProbability ρ hρ (majority (2 * k + 1)))
        atTop (𝓝 (1 - 2 * (Real.arccos ρ / Real.pi))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hdis)
  have hfun :
      (fun k ↦ 1 - 2 *
        correlatedDisagreementProbability ρ hρ (majority (2 * k + 1))) =
        fun k ↦ noiseStability ρ hρ (majority (2 * k + 1)).toReal := by
    funext k
    rw [correlatedDisagreementProbability_eq]
    ring
  rw [hfun] at hlimit
  convert hlimit using 1
  rw [two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos]
  ring_nf

/-- O'Donnell, Theorem 2.45, equivalent inverse-cosine form of the odd-majority stability
limit. -/
theorem tendsto_noiseStability_majority_odd_arccos
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto
      (fun k ↦ noiseStability ρ hρ (majority (2 * k + 1)).toReal)
      atTop (𝓝 (1 - 2 / Real.pi * Real.arccos ρ)) := by
  rw [← two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos ρ]
  exact tendsto_noiseStability_majority_odd ρ hρ

/-- O'Donnell, Theorem 2.45, equivalent noise-sensitivity form: odd majority converges to the
Gaussian angle at correlation `1 - 2δ`. -/
theorem tendsto_noiseSensitivity_majority_odd
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto
      (fun k ↦ noiseSensitivity δ hδ (majority (2 * k + 1)))
      atTop (𝓝 (Real.arccos (1 - 2 * δ) / Real.pi)) := by
  simpa only [noiseSensitivity, correlatedDisagreementProbability] using
    tendsto_correlatedDisagreementProbability_majority_odd
      (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ)

/-- The half-angle identity underlying the small-noise expansion in Theorem 2.45. -/
theorem arccos_one_sub_two_mul_eq_two_mul_arcsin_sqrt
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    Real.arccos (1 - 2 * δ) = 2 * Real.arcsin (Real.sqrt δ) := by
  have hsqrt₀ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsqrt₁ : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.mpr hδ.2
  have hsin : Real.sin (Real.arcsin (Real.sqrt δ)) = Real.sqrt δ :=
    Real.sin_arcsin (by linarith) hsqrt₁
  calc
    Real.arccos (1 - 2 * δ) =
        Real.arccos (1 - 2 * Real.sin (Real.arcsin (Real.sqrt δ)) ^ 2) := by
      rw [hsin, Real.sq_sqrt hδ.1]
    _ = Real.arccos (Real.cos (2 * Real.arcsin (Real.sqrt δ))) := by
      rw [Real.cos_two_mul_eq_one_sub]
    _ = 2 * Real.arcsin (Real.sqrt δ) := by
      apply Real.arccos_cos
      · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hsqrt₀)
      · nlinarith [Real.arcsin_le_pi_div_two (Real.sqrt δ)]

/-- The exact inverse-sine value used to keep the cubic sine estimate in its valid range. -/
theorem arcsin_one_half : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
  apply Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
  constructor <;> nlinarith [Real.pi_pos]

/-- On `[0, 1/2]`, inverse sine differs from the identity by at most twice the cube. -/
theorem arcsin_sub_self_mem_Icc_two_mul_cube
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    Real.arcsin x - x ∈ Set.Icc (0 : ℝ) (2 * x ^ 3) := by
  have hx₁ : x ≤ 1 := hx.2.trans (by norm_num)
  have hxneg₁ : -1 ≤ x := by linarith [hx.1]
  have hsin : Real.sin (Real.arcsin x) = x :=
    Real.sin_arcsin hxneg₁ hx₁
  have hy₀ : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx.1
  have hx_le_y : x ≤ Real.arcsin x := by
    have h := Real.sin_le hy₀
    rw [hsin] at h
    exact h
  constructor
  · linarith
  · rcases hx.1.eq_or_lt with rfl | hxpos
    · simp
    · have hypos : 0 < Real.arcsin x := Real.arcsin_pos.mpr hxpos
      have hy_one : Real.arcsin x ≤ 1 := by
        calc
          Real.arcsin x ≤ Real.arcsin (1 / 2 : ℝ) :=
            Real.arcsin_le_arcsin hx.2
          _ = Real.pi / 6 := arcsin_one_half
          _ ≤ 1 := by nlinarith [Real.pi_lt_four]
      have hjordan : (2 / Real.pi) * Real.arcsin x ≤ x := by
        simpa [hsin] using
          Real.mul_le_sin hy₀ (Real.arcsin_le_pi_div_two x)
      have hy_le_two_mul : Real.arcsin x ≤ 2 * x := by
        have hdiv : (2 * Real.arcsin x) / Real.pi ≤ x := by
          calc
            (2 * Real.arcsin x) / Real.pi =
                (2 / Real.pi) * Real.arcsin x := by ring
            _ ≤ x := hjordan
        have htwo : 2 * Real.arcsin x ≤ x * Real.pi :=
          (div_le_iff₀ Real.pi_pos).mp hdiv
        have hpimul : x * Real.pi ≤ x * 4 :=
          mul_le_mul_of_nonneg_left Real.pi_lt_four.le hx.1
        linarith
      have hcubic := Real.sin_gt_sub_cube hypos hy_one
      rw [hsin] at hcubic
      calc
        Real.arcsin x - x ≤ Real.arcsin x ^ 3 / 4 := by linarith
        _ ≤ (2 * x) ^ 3 / 4 := by
          gcongr
        _ = 2 * x ^ 3 := by ring

/-- The cubic power of a square root is the real `3/2` power. -/
theorem sqrt_cube_eq_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x ^ 3 = x ^ (3 / 2 : ℝ) := by
  calc
    Real.sqrt x ^ 3 = x * Real.sqrt x := by
      rw [show Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x by ring,
        Real.sq_sqrt hx]
    _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) :=
      (Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)).symm
    _ = x ^ (3 / 2 : ℝ) := by ring_nf

/-- The inverse-cosine remainder in Theorem 2.45 is `O(δ^(3/2))` from the right at zero. -/
theorem arccos_one_sub_two_mul_sub_two_mul_sqrt_isBigO :
    (fun δ : ℝ ↦ Real.arccos (1 - 2 * δ) - 2 * Real.sqrt δ) =O[𝓝[≥] 0]
      (fun δ : ℝ ↦ δ ^ (3 / 2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < 1 / 4 by norm_num)] with δ hδ
  have hsqrt_half : Real.sqrt δ ≤ (1 / 2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [hδ.2]
  have hidentity := arccos_one_sub_two_mul_eq_two_mul_arcsin_sqrt δ
    ⟨hδ.1, hδ.2.trans (by norm_num)⟩
  have hremainder := arcsin_sub_self_mem_Icc_two_mul_cube (Real.sqrt δ)
    ⟨Real.sqrt_nonneg δ, hsqrt_half⟩
  have hrpow₀ : 0 ≤ δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hδ.1 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrpow₀]
  rw [hidentity]
  rw [show 2 * Real.arcsin (Real.sqrt δ) - 2 * Real.sqrt δ =
      2 * (Real.arcsin (Real.sqrt δ) - Real.sqrt δ) by ring]
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hremainder.1)]
  rw [sqrt_cube_eq_rpow_three_halves δ hδ.1] at hremainder
  nlinarith [hremainder.2]

/-- O'Donnell, Theorem 2.45, small-noise consequence: the limiting noise sensitivity of odd
majority is `(2 / π) √δ + O(δ^(3/2))`. -/
theorem majorityNoiseSensitivityLimit_sub_two_div_pi_mul_sqrt_isBigO :
    (fun δ : ℝ ↦ Real.arccos (1 - 2 * δ) / Real.pi -
      2 / Real.pi * Real.sqrt δ) =O[𝓝[≥] 0]
        (fun δ : ℝ ↦ δ ^ (3 / 2 : ℝ)) := by
  convert arccos_one_sub_two_mul_sub_two_mul_sqrt_isBigO.const_mul_left
    (1 / Real.pi) using 1
  funext δ
  ring

/-- O'Donnell, Definition 2.42: agreement and disagreement probabilities add to one. -/
theorem correlatedAgreementProbability_eq_one_sub_disagreement
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    correlatedAgreementProbability ρ hρ f =
      1 - correlatedDisagreementProbability ρ hρ f := by
  unfold correlatedAgreementProbability correlatedDisagreementProbability
  let p : PMF ({−1,1}^[n] × {−1,1}^[n]) := correlatedPairPMF ρ hρ
  change pmfExpectation p (fun xy ↦ if f xy.1 = f xy.2 then 1 else 0) = _
  rw [show pmfExpectation p (fun xy ↦ if f xy.1 = f xy.2 then 1 else 0) =
      pmfExpectation p (fun xy ↦ 1 - if f xy.1 ≠ f xy.2 then 1 else 0) by
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hxy : f xy.1 = f xy.2 <;> simp [hxy]]
  rw [pmfExpectation_sub, pmfExpectation_const_one]

/-- O'Donnell, Definition 2.42: Boolean stability is agreement minus disagreement. -/
theorem noiseStability_toReal_eq_agreement_sub_disagreement
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    noiseStability ρ hρ f.toReal =
      correlatedAgreementProbability ρ hρ f -
        correlatedDisagreementProbability ρ hρ f := by
  rw [correlatedAgreementProbability_eq_one_sub_disagreement,
    correlatedDisagreementProbability_eq]
  ring

/-- O'Donnell, Definition 2.42: Boolean stability is twice agreement probability minus one. -/
theorem noiseStability_toReal_eq_two_mul_agreement_sub_one
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    noiseStability ρ hρ f.toReal =
      2 * correlatedAgreementProbability ρ hρ f - 1 := by
  rw [correlatedAgreementProbability_eq_one_sub_disagreement,
    correlatedDisagreementProbability_eq]
  ring


end FABL
