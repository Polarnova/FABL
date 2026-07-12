/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.NoiseKernels
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Correlated Gaussian limit

Book item supported: Theorem 2.45.

The two-dimensional central-limit argument used for majority noise stability.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The real Hilbert plane used for the two-dimensional central-limit argument. -/
abbrev CorrelationPlane := WithLp 2 (ℝ × ℝ)

/-- A correlated pair of signs embedded as a vector in the real Hilbert plane. -/
def correlatedSignVector (xy : Sign × Sign) : CorrelationPlane :=
  toLp 2 (signValue xy.1, signValue xy.2)

/-- Projection of a correlated sign vector onto a direction in the real Hilbert plane. -/
def correlatedSignProjection (t : CorrelationPlane) (xy : Sign × Sign) : ℝ :=
  signValue xy.1 * (ofLp t).1 + signValue xy.2 * (ofLp t).2

/-- Projection is linear in its Hilbert-plane direction. -/
theorem correlatedSignProjection_smul (a : ℝ) (t : CorrelationPlane) (xy : Sign × Sign) :
    correlatedSignProjection (a • t) xy = a * correlatedSignProjection t xy := by
  unfold correlatedSignProjection
  simp
  ring

/-- The explicit coordinate projection agrees with the Hilbert-space inner product. -/
theorem correlatedSignProjection_eq_inner (t : CorrelationPlane) (xy : Sign × Sign) :
    correlatedSignProjection t xy = inner ℝ (correlatedSignVector xy) t := by
  rw [correlatedSignProjection, correlatedSignVector]
  simp [prod_inner_apply, RCLike.inner_apply, mul_comm]

/-- The covariance quadratic form of a pair of standard signs with correlation `ρ`. -/
def correlationQuadraticForm (ρ : ℝ) (t : CorrelationPlane) : ℝ :=
  (ofLp t).1 ^ 2 + 2 * ρ * (ofLp t).1 * (ofLp t).2 + (ofLp t).2 ^ 2

/-- Every projection of the one-coordinate correlated-sign vector is centered. -/
theorem correlatedSignProjection_expectation
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (t : CorrelationPlane) :
    pmfExpectation (correlatedSignPairPMF ρ hρ) (correlatedSignProjection t) = 0 := by
  unfold correlatedSignProjection
  rw [pmfExpectation_add, pmfExpectation_mul_const, pmfExpectation_mul_const,
    correlatedSignPairPMF_expect_signValue_fst,
    correlatedSignPairPMF_expect_signValue_snd]
  ring

/-- The second moment of every projection is its covariance quadratic form. -/
theorem correlatedSignProjection_secondMoment
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (t : CorrelationPlane) :
    pmfExpectation (correlatedSignPairPMF ρ hρ)
        (fun xy ↦ correlatedSignProjection t xy ^ 2) =
      correlationQuadraticForm ρ t := by
  let a := (ofLp t).1
  let b := (ofLp t).2
  have hsquare (xy : Sign × Sign) :
      correlatedSignProjection t xy ^ 2 =
        a ^ 2 + 2 * a * b * (signValue xy.1 * signValue xy.2) + b ^ 2 := by
    unfold correlatedSignProjection a b
    rcases signValue_eq_neg_one_or_one xy.1 with hx | hx <;>
      rcases signValue_eq_neg_one_or_one xy.2 with hy | hy <;>
      rw [hx, hy] <;> ring
  simp_rw [hsquare]
  rw [pmfExpectation_add, pmfExpectation_add,
    pmfExpectation_const, pmfExpectation_const_mul,
    correlatedSignPairPMF_expect_signValue_mul, pmfExpectation_const]
  unfold correlationQuadraticForm a b
  ring

local instance correlatedSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance correlatedSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The one-coordinate correlated-sign vector as a probability measure on the Hilbert plane. -/
noncomputable def correlatedSignVectorMeasure
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) : ProbabilityMeasure CorrelationPlane := by
  let p : ProbabilityMeasure (Sign × Sign) :=
    ⟨(correlatedSignPairPMF ρ hρ).toMeasure, inferInstance⟩
  exact p.map (measurable_of_finite correlatedSignVector).aemeasurable

/-- Characteristic functions of the planar vector law reduce to scalar projections. -/
theorem charFun_correlatedSignVectorMeasure_smul
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (a : ℝ) (t : CorrelationPlane) :
    charFun (correlatedSignVectorMeasure ρ hρ) (a • t) =
      charFun ((correlatedSignPairPMF ρ hρ).toMeasure.map
        (correlatedSignProjection t)) a := by
  rw [charFun_apply, charFun_apply]
  unfold correlatedSignVectorMeasure
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map, integral_map]
  · apply integral_congr_ae
    filter_upwards [] with xy
    rw [← correlatedSignProjection_eq_inner]
    rw [correlatedSignProjection_smul]
    rw [show inner ℝ (correlatedSignProjection t xy) a =
        correlatedSignProjection t xy * a by simp [RCLike.inner_apply, mul_comm]]
    push_cast
    ring_nf
  all_goals fun_prop

/-- A second-order characteristic-function expansion with an arbitrary finite second moment. -/
private theorem taylor_charFun_two_of_secondMoment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (h0 : P[X] = 0)
    (hmemX : MemLp X 2 P) (q : ℝ) (h2 : P[X ^ 2] = q) :
    (fun t ↦ charFun (P.map X) t - (1 - q * t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  have hmem : MemLp id 2 (P.map X) := by
    exact (memLp_map_measure_iff (g := id) (by fun_prop) hX).2 (by simpa using hmemX)
  have htaylor (t : ℝ) :
      taylorWithinEval (charFun (P.map X)) 2 Set.univ 0 t =
        1 - q * t ^ 2 / 2 := by
    rw [taylorWithinEval_charFun_two_zero hX hmem, h0, h2]
    simp
  simp_rw [← htaylor]
  convert! taylor_isLittleO_univ (contDiff_charFun hmem)
  simp

/-- Scalar central-limit characteristic-function convergence with an arbitrary second moment. -/
private theorem tendsto_charFun_inv_sqrt_mul_pow_of_secondMoment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (h0 : P[X] = 0)
    (hmemX : MemLp X 2 P) (q : ℝ) (h2 : P[X ^ 2] = q) :
    Tendsto (fun n : ℕ ↦ (charFun (P.map X) ((Real.sqrt n)⁻¹) ^ n))
      atTop (𝓝 (exp (-(q : ℂ) / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div (-(q : ℂ) / 2)
  suffices (fun n : ℕ ↦ charFun (P.map X) ((Real.sqrt n)⁻¹) -
      (1 + (-(q : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) ^ 2) / 2))) =o[atTop]
        fun n ↦ (((Real.sqrt n)⁻¹ : ℝ) ^ 2) by
    have hnorm : (fun n : ℕ ↦ ‖(1 / (n : ℂ))‖) =
        fun n : ℕ ↦ ‖(1 / (n : ℝ))‖ := by
      simp
    rw [← Asymptotics.isLittleO_norm_right, hnorm, Asymptotics.isLittleO_norm_right]
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have hsqrt : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  convert! (taylor_charFun_two_of_secondMoment hX h0 hmemX q h2).comp_tendsto hsqrt using 2
  all_goals simp
  all_goals ring

/-- The law of the normalized sum of `n` independent correlated-sign vectors. -/
noncomputable def normalizedCorrelatedSignSumMeasure
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) :
    ProbabilityMeasure CorrelationPlane :=
  ⟨(Measure.pi fun _ : Fin n ↦
      (correlatedSignVectorMeasure ρ hρ : Measure CorrelationPlane)).map
      (fun z ↦ (Real.sqrt n)⁻¹ • ∑ i, z i),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

/-- The normalized independent sum has the `n`th power of the one-coordinate characteristic
function at the rescaled argument. -/
theorem charFun_normalizedCorrelatedSignSumMeasure
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) (t : CorrelationPlane) :
    charFun (normalizedCorrelatedSignSumMeasure ρ hρ n) t =
      charFun (correlatedSignVectorMeasure ρ hρ) ((Real.sqrt n)⁻¹ • t) ^ n := by
  unfold normalizedCorrelatedSignSumMeasure
  change charFun
      ((Measure.pi fun _ : Fin n ↦
          (correlatedSignVectorMeasure ρ hρ : Measure CorrelationPlane)).map
        (fun z ↦ (Real.sqrt n)⁻¹ • ∑ i, z i)) t = _
  rw [show (fun z : Fin n → CorrelationPlane ↦ (Real.sqrt n)⁻¹ • ∑ i, z i) =
      ((Real.sqrt n)⁻¹ • ·) ∘ (fun z ↦ ∑ i, z i) from rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_smul]
  rw [congrFun (charFun_map_sum_pi_eq_prod
    (fun _ : Fin n ↦ (correlatedSignVectorMeasure ρ hρ : Measure CorrelationPlane)))
      ((Real.sqrt n)⁻¹ • t)]
  simp

/-- The linear construction of a pair of standard Gaussian variables with correlation `ρ`. -/
noncomputable def gaussianCorrelationMap (ρ : ℝ) (uv : ℝ × ℝ) : CorrelationPlane :=
  toLp 2 (uv.1, ρ * uv.1 + Real.sqrt (1 - ρ ^ 2) * uv.2)

/-- The Gaussian correlation construction is continuous. -/
theorem continuous_gaussianCorrelationMap (ρ : ℝ) : Continuous (gaussianCorrelationMap ρ) := by
  unfold gaussianCorrelationMap
  fun_prop

/-- The centered bivariate Gaussian law with unit marginal variances and correlation `ρ`. -/
noncomputable def correlatedGaussianMeasure (ρ : ℝ) : ProbabilityMeasure CorrelationPlane :=
  ⟨((gaussianReal 0 1).prod (gaussianReal 0 1)).map (gaussianCorrelationMap ρ),
    Measure.isProbabilityMeasure_map (continuous_gaussianCorrelationMap ρ).aemeasurable⟩

/-- Projection of the correlated Gaussian construction onto a planar direction. -/
theorem inner_gaussianCorrelationMap
    (ρ : ℝ) (uv : ℝ × ℝ) (t : CorrelationPlane) :
    inner ℝ (gaussianCorrelationMap ρ uv) t =
      inner ℝ uv.1 ((ofLp t).1 + ρ * (ofLp t).2) +
        inner ℝ uv.2 (Real.sqrt (1 - ρ ^ 2) * (ofLp t).2) := by
  unfold gaussianCorrelationMap
  simp [prod_inner_apply, RCLike.inner_apply]
  ring

/-- The correlated bivariate Gaussian has covariance quadratic form
`t₁² + 2 ρ t₁ t₂ + t₂²`. -/
theorem charFun_correlatedGaussianMeasure
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (t : CorrelationPlane) :
    charFun (correlatedGaussianMeasure ρ) t =
      exp (-(correlationQuadraticForm ρ t : ℂ) / 2) := by
  change charFun
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (gaussianCorrelationMap ρ)) t = _
  rw [charFun_apply, integral_map]
  · have hfactor :
        (fun uv : ℝ × ℝ ↦ exp (inner ℝ (gaussianCorrelationMap ρ uv) t * I)) =
          fun uv ↦
            exp (inner ℝ uv.1 ((ofLp t).1 + ρ * (ofLp t).2) * I) *
              exp (inner ℝ uv.2 (Real.sqrt (1 - ρ ^ 2) * (ofLp t).2) * I) := by
      funext uv
      rw [inner_gaussianCorrelationMap, ofReal_add, add_mul, exp_add]
    rw [hfactor]
    let a := (ofLp t).1 + ρ * (ofLp t).2
    let b := Real.sqrt (1 - ρ ^ 2) * (ofLp t).2
    let f : ℝ → ℂ := fun u ↦ exp (inner ℝ u a * I)
    let g : ℝ → ℂ := fun v ↦ exp (inner ℝ v b * I)
    change (∫ uv, f uv.1 * g uv.2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = _
    rw [integral_prod_mul f g]
    change charFun (gaussianReal 0 1) a * charFun (gaussianReal 0 1) b = _
    rw [charFun_gaussianReal, charFun_gaussianReal]
    simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, zero_sub]
    rw [← exp_add]
    congr 2
    have hnonneg : 0 ≤ 1 - ρ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ.2)
        (show 0 ≤ 1 + ρ by linarith [hρ.1])]
    have hsquareC : ((Real.sqrt (1 - ρ ^ 2) : ℝ) : ℂ) ^ 2 =
        1 - (ρ : ℂ) ^ 2 := by
      norm_cast
      exact Real.sq_sqrt hnonneg
    unfold correlationQuadraticForm
    dsimp [a, b]
    push_cast
    rw [mul_pow, hsquareC]
    ring
  all_goals first | exact (continuous_gaussianCorrelationMap ρ).aemeasurable | fun_prop

/-- The normalized sums of independent correlated-sign vectors converge weakly to the centered
bivariate Gaussian with the same covariance. -/
theorem normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto (normalizedCorrelatedSignSumMeasure ρ hρ) atTop
      (𝓝 (correlatedGaussianMeasure ρ)) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  rw [charFun_correlatedGaussianMeasure ρ hρ]
  simp_rw [charFun_normalizedCorrelatedSignSumMeasure,
    charFun_correlatedSignVectorMeasure_smul]
  let P : Measure (Sign × Sign) := (correlatedSignPairPMF ρ hρ).toMeasure
  let X : Sign × Sign → ℝ := correlatedSignProjection t
  let q : ℝ := correlationQuadraticForm ρ t
  have hX : AEMeasurable X P := by
    exact (measurable_of_finite X).aemeasurable
  have h0 : P[X] = 0 := by
    change ∫ xy, correlatedSignProjection t xy ∂(correlatedSignPairPMF ρ hρ).toMeasure = 0
    rw [← pmfExpectation_eq_integral]
    exact correlatedSignProjection_expectation ρ hρ t
  have h2 : P[X ^ 2] = q := by
    change ∫ xy, correlatedSignProjection t xy ^ 2
      ∂(correlatedSignPairPMF ρ hρ).toMeasure = correlationQuadraticForm ρ t
    rw [← pmfExpectation_eq_integral]
    exact correlatedSignProjection_secondMoment ρ hρ t
  have hbound (xy : Sign × Sign) :
      ‖X xy‖ ≤ |(ofLp t).1| + |(ofLp t).2| := by
    change |signValue xy.1 * (ofLp t).1 + signValue xy.2 * (ofLp t).2| ≤ _
    calc
      _ ≤ |signValue xy.1 * (ofLp t).1| + |signValue xy.2 * (ofLp t).2| :=
        abs_add_le _ _
      _ = _ := by
        rcases signValue_eq_neg_one_or_one xy.1 with hx | hx <;>
          rcases signValue_eq_neg_one_or_one xy.2 with hy | hy <;>
          rw [hx, hy] <;> simp
  have hmem : MemLp X 2 P :=
    MemLp.of_bound (by fun_prop) (|(ofLp t).1| + |(ofLp t).2|)
      (ae_of_all _ hbound)
  simpa [P, X, q] using
    tendsto_charFun_inv_sqrt_mul_pow_of_secondMoment hX h0 hmem q h2

/-- Pairing coordinates is an equivalence between two sign strings and a string of sign pairs. -/
def pairCoordinatesEquiv (n : ℕ) :
    ({−1,1}^[n] × {−1,1}^[n]) ≃ (Fin n → Sign × Sign) where
  toFun xy i := (xy.1 i, xy.2 i)
  invFun z := (fun i ↦ (z i).1, fun i ↦ (z i).2)
  left_inv xy := by
    ext i <;> rfl
  right_inv z := by
    ext i <;> rfl

/-- The coordinates of a correlated pair are independent copies of the one-coordinate
correlated-sign law. -/
theorem correlatedPairPMF_map_pairCoordinatesEquiv
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) :
    (correlatedPairPMF (n := n) ρ hρ).map (pairCoordinatesEquiv n) =
      independentProductPMF (fun _ : Fin n ↦ correlatedSignPairPMF ρ hρ) := by
  classical
  ext z
  rw [PMF.map_apply, tsum_eq_single ((pairCoordinatesEquiv n).symm z)]
  · rcases hxy : (pairCoordinatesEquiv n).symm z with ⟨x, y⟩
    have hz : z = pairCoordinatesEquiv n (x, y) := by
      calc
        z = pairCoordinatesEquiv n ((pairCoordinatesEquiv n).symm z) :=
          ((pairCoordinatesEquiv n).apply_symm_apply z).symm
        _ = pairCoordinatesEquiv n (x, y) := congrArg (pairCoordinatesEquiv n) hxy
    subst z
    rw [correlatedPairPMF_apply, independentProductPMF_apply]
    rw [if_pos rfl]
    change uniformPMF {−1,1}^[n] x * noiseKernel ρ hρ x y =
      ∏ i, correlatedSignPairPMF ρ hρ (x i, y i)
    simp_rw [correlatedSignPairPMF_apply]
    rw [Finset.prod_mul_distrib]
    unfold noiseKernel
    rw [independentProductPMF_apply]
    congr 1
    simp only [uniformPMF, PMF.uniformOfFintype_apply, Fintype.card_pi,
      Fintype.card_units_int, prod_const, card_univ, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.inv_pow
  · intro w hw
    have hne : z ≠ pairCoordinatesEquiv n w := by
      intro h
      apply hw
      apply (pairCoordinatesEquiv n).injective
      simpa using h.symm
    simp [hne]

/-- The measure attached to a finite independent-product PMF is Mathlib's product measure. -/
private theorem independentProductPMF_toMeasure {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] (p : ∀ i, PMF (α i)) :
    (independentProductPMF p).toMeasure = Measure.pi fun i ↦ (p i).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [(independentProductPMF p).toMeasure_apply_singleton x (measurableSet_singleton x),
    Measure.pi_singleton]
  simp only [independentProductPMF_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact ((p i).toMeasure_apply_singleton (x i) (measurableSet_singleton (x i))).symm

/-- The normalized planar sum associated to a string of correlated sign pairs. -/
noncomputable def normalizedCorrelatedSignVectorSum (n : ℕ)
    (z : Fin n → Sign × Sign) : CorrelationPlane :=
  (Real.sqrt n)⁻¹ • ∑ i, correlatedSignVector (z i)

/-- The normalized pair of vote margins associated to two sign strings. -/
noncomputable def normalizedCorrelatedPairSum (n : ℕ)
    (xy : {−1,1}^[n] × {−1,1}^[n]) : CorrelationPlane :=
  normalizedCorrelatedSignVectorSum n (pairCoordinatesEquiv n xy)

/-- The normalized-sum law used in the central limit theorem is the pushforward of the
correlated-pair law by the two normalized vote margins. -/
theorem normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) :
    (normalizedCorrelatedSignSumMeasure ρ hρ n : Measure CorrelationPlane) =
      (correlatedPairPMF (n := n) ρ hρ).toMeasure.map
        (normalizedCorrelatedPairSum n) := by
  change
    (Measure.pi fun _ : Fin n ↦
      (correlatedSignPairPMF ρ hρ).toMeasure.map correlatedSignVector).map
        (fun z ↦ (Real.sqrt n)⁻¹ • ∑ i, z i) = _
  rw [← Measure.pi_map_pi
    (μ := fun _ : Fin n ↦ (correlatedSignPairPMF ρ hρ).toMeasure)
    (f := fun _ : Fin n ↦ correlatedSignVector)
    (fun _ ↦ (measurable_of_finite correlatedSignVector).aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← independentProductPMF_toMeasure]
  rw [← correlatedPairPMF_map_pairCoordinatesEquiv ρ hρ n]
  rw [← PMF.toMeasure_map (correlatedPairPMF (n := n) ρ hρ)
    (f := pairCoordinatesEquiv n) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl


end FABL
