/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.StableInfluence
public import FABL.Chapter05.RandomBooleanFourierMaximum
public import FABL.Chapter06.Pseudorandomness.Regularity

/-!
# Random functions

Book items: Proposition 6.1, the first assertion of Example 6.4, Fact 6.8,
Exercises 6.1 and 6.2.

The biased random-function law is an explicit finite product PMF.  The concentration proof uses
Mathlib's sub-Gaussian Hoeffding inequality, while the stable-influence calculation uses the
uniform finite PMF on sign-valued functions.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance randomFunctionBoolMeasurableSpace : MeasurableSpace Bool := ⊤

local instance randomFunctionBoolMeasurableSingletonClass :
    MeasurableSingletonClass Bool where
  measurableSet_singleton _ := by simp

/-- A zero-one-valued function on the sign cube. -/
abbrev ZeroOneFunction (n : ℕ) := {−1,1}^[n] → Bool

/-- The real zero-one view of a Boolean bit. -/
def zeroOneValue (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Regard a zero-one-valued function as real-valued. -/
def ZeroOneFunction.toReal (f : ZeroOneFunction n) : {−1,1}^[n] → ℝ :=
  fun x ↦ zeroOneValue (f x)

/-- The Bernoulli PMF with success probability `p`, retaining the book's real parameter domain. -/
noncomputable def pBiasedBitPMF (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : PMF Bool :=
  let q : NNReal := ⟨p, hp.1⟩
  let hq : q ≤ 1 := by
    exact_mod_cast hp.2
  PMF.ofFintype (fun b : Bool ↦ cond b q (1 - q)) (by simp [hq])

/-- The expectation of a Bernoulli bit's zero-one view is its success probability. -/
theorem pmfExpectation_pBiasedBitPMF_zeroOneValue
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    pmfExpectation (pBiasedBitPMF p hp) zeroOneValue = p := by
  simp [pBiasedBitPMF, pmfExpectation, zeroOneValue]
  rfl

/-- The `p`-biased random-function law, with independent values at every cube input. -/
noncomputable def pBiasedRandomFunctionPMF
    (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    PMF (ZeroOneFunction n) :=
  independentProductPMF fun _ : {−1,1}^[n] ↦ pBiasedBitPMF p hp

/-- Evaluation of the `p`-biased random-function PMF factors over all cube inputs. -/
@[simp] theorem pBiasedRandomFunctionPMF_apply
    (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (f : ZeroOneFunction n) :
    pBiasedRandomFunctionPMF n p hp f =
      ∏ x, pBiasedBitPMF p hp (f x) := by
  rfl

/-- The `p`-biased random-function measure is the corresponding finite product measure. -/
theorem pBiasedRandomFunctionPMF_toMeasure
    (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure =
      Measure.pi fun _ : {−1,1}^[n] ↦ (pBiasedBitPMF p hp).toMeasure := by
  exact independentProductPMF_toMeasure _

private theorem integral_zeroOneValue_pBiasedBitPMF
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ b : Bool, zeroOneValue b ∂(pBiasedBitPMF p hp).toMeasure = p := by
  rw [← pmfExpectation_eq_integral]
  exact pmfExpectation_pBiasedBitPMF_zeroOneValue p hp

private theorem zeroOneValue_memLp_pBiasedBitPMF
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    MemLp zeroOneValue 2 (pBiasedBitPMF p hp).toMeasure := by
  refine MemLp.of_bound
    (measurable_of_finite zeroOneValue).aestronglyMeasurable 1
    (ae_of_all _ fun b ↦ ?_)
  cases b <;> simp [zeroOneValue]

private theorem variance_zeroOneValue_pBiasedBitPMF
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ProbabilityTheory.variance zeroOneValue
        (pBiasedBitPMF p hp).toMeasure =
      p * (1 - p) := by
  rw [variance_eq_sub (zeroOneValue_memLp_pBiasedBitPMF p hp)]
  have hsquare : (zeroOneValue ^ 2 : Bool → ℝ) = zeroOneValue := by
    funext b
    cases b <;> simp [zeroOneValue]
  rw [hsquare, integral_zeroOneValue_pBiasedBitPMF]
  ring

private theorem measure_abs_pBiasedWeightedSum_sub_mean_ge_le
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (w : {−1,1}^[n] → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          t ≤
            |∑ x, w x * (zeroOneValue (f x) - p)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ∑ x, w x ^ 2)) := by
  classical
  rw [pBiasedRandomFunctionPMF_toMeasure]
  let μ : Measure (ZeroOneFunction n) :=
    Measure.pi fun _ : {−1,1}^[n] ↦ (pBiasedBitPMF p hp).toMeasure
  let X : {−1,1}^[n] → ZeroOneFunction n → ℝ :=
    fun x f ↦ w x * (zeroOneValue (f x) - p)
  let c : {−1,1}^[n] → NNReal :=
    fun x ↦ ⟨w x ^ 2, sq_nonneg (w x)⟩
  have hbit (x : {−1,1}^[n]) :
      HasSubgaussianMGF
        (fun f : ZeroOneFunction n ↦ zeroOneValue (f x) - p) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := μ)
      (X := fun f : ZeroOneFunction n ↦ zeroOneValue (f x))
      (a := (-1 : ℝ)) (b := (1 : ℝ))
      (measurable_of_finite
        fun f : ZeroOneFunction n ↦ zeroOneValue (f x)).aemeasurable
      (ae_of_all _ fun f ↦ by
        cases f x <;> simp [zeroOneValue])
    have hmean :
        ∫ f : ZeroOneFunction n, zeroOneValue (f x) ∂μ = p := by
      rw [integral_comp_eval
        (μ := fun _ : {−1,1}^[n] ↦ (pBiasedBitPMF p hp).toMeasure)
        (i := x)
        (measurable_of_finite zeroOneValue).aestronglyMeasurable]
      exact integral_zeroOneValue_pBiasedBitPMF p hp
    rw [hmean] at h
    norm_num at h ⊢
    exact h
  have hcoordinate (x : {−1,1}^[n]) :
      HasSubgaussianMGF (X x) (c x) μ := by
    simpa only [X, c, NNReal.coe_mk, mul_one] using
      (hbit x).const_mul (w x)
  have hindep : iIndepFun X μ := by
    exact iIndepFun_pi fun x ↦
      (measurable_of_finite
        fun b : Bool ↦ w x * (zeroOneValue b - p)).aemeasurable
  have hsum :
      HasSubgaussianMGF
        (fun f : ZeroOneFunction n ↦
          ∑ x, w x * (zeroOneValue (f x) - p))
        (∑ x, c x) μ := by
    have h := HasSubgaussianMGF.sum_of_iIndepFun
      hindep (s := Finset.univ) (c := c)
        (fun x _ ↦ hcoordinate x)
    simpa only [X, Finset.sum_apply] using h
  have hupper := hsum.measure_ge_le ht
  have hlower := hsum.neg.measure_ge_le ht
  have hset :
      {f : ZeroOneFunction n |
          t ≤ |∑ x, w x * (zeroOneValue (f x) - p)|} =
        {f | t ≤ ∑ x, w x * (zeroOneValue (f x) - p)} ∪
          {f | t ≤ -(∑ x, w x * (zeroOneValue (f x) - p))} := by
    ext f
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
    μ.real
        ({f | t ≤ ∑ x, w x * (zeroOneValue (f x) - p)} ∪
          {f | t ≤ -(∑ x, w x * (zeroOneValue (f x) - p))}) ≤
        μ.real {f | t ≤ ∑ x, w x * (zeroOneValue (f x) - p)} +
          μ.real {f | t ≤ -(∑ x, w x * (zeroOneValue (f x) - p))} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (∑ x, c x : NNReal))) +
        Real.exp (-t ^ 2 / (2 * (∑ x, c x : NNReal))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ x, w x ^ 2)) := by
      have hc : ((∑ x, c x : NNReal) : ℝ) = ∑ x, w x ^ 2 := by
        rw [NNReal.coe_sum]
        rfl
      rw [hc]
      ring

private theorem fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum
    (p : ℝ) (S : Finset (Fin n)) (f : ZeroOneFunction n) :
    fourierCoeff f.toReal S - (if S = ∅ then p else 0) =
      ∑ x : {−1,1}^[n],
        (monomial S x / Fintype.card ({−1,1}^[n])) *
          (zeroOneValue (f x) - p) := by
  classical
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
    positivity
  have hmean :
      (if S = ∅ then p else 0) =
        p * (𝔼 x : {−1,1}^[n], monomial S x) := by
    rw [expect_monomial]
    split <;> simp_all
  rw [hmean, fourierCoeff, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  calc
    (∑ x, f.toReal x * monomial S x) /
          (Fintype.card ({−1,1}^[n]) : ℝ) -
        p * ((∑ x, monomial S x) /
          (Fintype.card ({−1,1}^[n]) : ℝ)) =
        (∑ x, (f.toReal x - p) * monomial S x) /
          (Fintype.card ({−1,1}^[n]) : ℝ) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      field_simp
    _ = ∑ x,
        (monomial S x / Fintype.card ({−1,1}^[n])) *
          (zeroOneValue (f x) - p) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ZeroOneFunction.toReal]
      ring

private theorem sum_sq_normalized_monomial
    (S : Finset (Fin n)) :
    ∑ x : {−1,1}^[n],
        (monomial S x / Fintype.card ({−1,1}^[n])) ^ 2 =
      1 / Fintype.card ({−1,1}^[n]) := by
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
    positivity
  simp_rw [div_pow, monomial_sq]
  simp
  field_simp

/-- Exercise 6.1: every Fourier coefficient of a `p`-biased random zero-one function has
variance `p(1-p) / 2ⁿ`. -/
theorem variance_pBiasedRandomFunction_fourierCoeff
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) :
    ProbabilityTheory.variance
        (fun f : ZeroOneFunction n ↦ fourierCoeff f.toReal S)
        (pBiasedRandomFunctionPMF n p hp).toMeasure =
      p * (1 - p) / (2 : ℝ) ^ n := by
  classical
  let w : {−1,1}^[n] → ℝ := fun x ↦
    monomial S x / Fintype.card ({−1,1}^[n])
  have hcoeff :
      (fun f : ZeroOneFunction n ↦ fourierCoeff f.toReal S) =
        fun f ↦
          (if S = ∅ then p else 0) +
            ∑ x, w x * (zeroOneValue (f x) - p) := by
    funext f
    have hcentered :=
      fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum p S f
    change fourierCoeff f.toReal S - (if S = ∅ then p else 0) =
      ∑ x, w x * (zeroOneValue (f x) - p) at hcentered
    linarith
  have hmem (x : {−1,1}^[n]) :
      MemLp (fun b : Bool ↦ w x * (zeroOneValue b - p)) 2
        (pBiasedBitPMF p hp).toMeasure := by
    obtain ⟨C, hC⟩ := Finite.exists_le
      (fun b : Bool ↦ ‖w x * (zeroOneValue b - p)‖)
    exact MemLp.of_bound
      (measurable_of_finite
        fun b : Bool ↦ w x * (zeroOneValue b - p)).aestronglyMeasurable
      C (ae_of_all _ hC)
  rw [hcoeff, pBiasedRandomFunctionPMF_toMeasure]
  rw [variance_const_add (measurable_of_finite _).aestronglyMeasurable]
  have hsumFunction :
      (fun f : ZeroOneFunction n ↦
        ∑ x, w x * (zeroOneValue (f x) - p)) =
        ∑ x, fun f ↦ w x * (zeroOneValue (f x) - p) := by
    funext f
    simp
  rw [hsumFunction]
  rw [variance_sum_pi hmem]
  simp_rw [variance_const_mul,
    variance_sub_const
      (measurable_of_finite zeroOneValue).aestronglyMeasurable,
    variance_zeroOneValue_pBiasedBitPMF]
  rw [← Finset.sum_mul]
  change
    (∑ x : {−1,1}^[n],
        (monomial S x / Fintype.card ({−1,1}^[n])) ^ 2) *
        (p * (1 - p)) = _
  rw [sum_sq_normalized_monomial]
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, Sign]
  rw [hcard]
  ring

private theorem measure_pBiasedRandomFunction_fourierCoeff_sub_mean_ge_le
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          t ≤
            |fourierCoeff f.toReal S -
              (if S = ∅ then p else 0)|} ≤
      2 * Real.exp
        (-(Fintype.card ({−1,1}^[n]) : ℝ) * t ^ 2 / 2) := by
  have h := measure_abs_pBiasedWeightedSum_sub_mean_ge_le
    p hp
      (fun x : {−1,1}^[n] ↦
        monomial S x / Fintype.card ({−1,1}^[n]))
      ht
  rw [sum_sq_normalized_monomial] at h
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
    positivity
  have hexponent :
      -t ^ 2 /
          (2 * (1 / (Fintype.card ({−1,1}^[n]) : ℝ))) =
        -(Fintype.card ({−1,1}^[n]) : ℝ) * t ^ 2 / 2 := by
    field_simp
  rw [hexponent] at h
  simpa only [fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum] using h

private theorem measure_pBiasedRandomFunction_fourierCoeff_atThreshold_ge_le
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          randomBooleanFourierThreshold n ≤
            |fourierCoeff f.toReal S -
              (if S = ∅ then p else 0)|} ≤
      2 * Real.exp (-(2 * (n : ℝ))) := by
  have h := measure_pBiasedRandomFunction_fourierCoeff_sub_mean_ge_le
    p hp S (randomBooleanFourierThreshold n)
      (randomBooleanFourierThreshold_nonneg n)
  rw [show
      -(Fintype.card ({−1,1}^[n]) : ℝ) *
            randomBooleanFourierThreshold n ^ 2 / 2 =
          -((Fintype.card ({−1,1}^[n]) : ℝ) *
            randomBooleanFourierThreshold n ^ 2 / 2) by ring,
    card_mul_randomBooleanFourierThreshold_sq_div_two] at h
  exact h

private theorem pBiasedFourierFailure_subset (n : ℕ) (p : ℝ) :
    {f : ZeroOneFunction n |
        randomBooleanFourierThreshold n <
            |fourierCoeff f.toReal ∅ - p| ∨
          ∃ S : Finset (Fin n), S.Nonempty ∧
            randomBooleanFourierThreshold n <
              |fourierCoeff f.toReal S|} ⊆
      ⋃ S : Finset (Fin n),
        {f : ZeroOneFunction n |
          randomBooleanFourierThreshold n ≤
            |fourierCoeff f.toReal S -
              (if S = ∅ then p else 0)|} := by
  intro f hf
  rcases hf with hf | ⟨S, hS, hf⟩
  · exact Set.mem_iUnion.2 ⟨∅, by simpa using hf.le⟩
  · exact Set.mem_iUnion.2
      ⟨S, by
        simpa [if_neg (Finset.nonempty_iff_ne_empty.mp hS)] using hf.le⟩

/-- O'Donnell, Proposition 6.1: for a `p`-biased random zero-one function in dimension
`n > 1`, the constant coefficient is close to `p` and every nonconstant coefficient is small,
simultaneously except with probability at most `2⁻ⁿ`. -/
theorem measure_pBiasedRandomFunction_fourierFailure_le
    (n : ℕ) (hn : 1 < n)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          randomBooleanFourierThreshold n <
              |fourierCoeff f.toReal ∅ - p| ∨
            ∃ S : Finset (Fin n), S.Nonempty ∧
              randomBooleanFourierThreshold n <
                |fourierCoeff f.toReal S|} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  have hcard :
      (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_finset]
  have hnTwo : 2 ≤ n := hn
  calc
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          randomBooleanFourierThreshold n <
              |fourierCoeff f.toReal ∅ - p| ∨
            ∃ S : Finset (Fin n), S.Nonempty ∧
              randomBooleanFourierThreshold n <
                |fourierCoeff f.toReal S|} ≤
        (pBiasedRandomFunctionPMF n p hp).toMeasure.real
          (⋃ S : Finset (Fin n),
            {f : ZeroOneFunction n |
              randomBooleanFourierThreshold n ≤
                |fourierCoeff f.toReal S -
                  (if S = ∅ then p else 0)|}) :=
      measureReal_mono (pBiasedFourierFailure_subset n p)
    _ ≤ ∑ S : Finset (Fin n),
        (pBiasedRandomFunctionPMF n p hp).toMeasure.real
          {f : ZeroOneFunction n |
            randomBooleanFourierThreshold n ≤
              |fourierCoeff f.toReal S -
                (if S = ∅ then p else 0)|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : Finset (Fin n),
        2 * Real.exp (-(2 * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_pBiasedRandomFunction_fourierCoeff_atThreshold_ge_le p hp S
    _ = (Fintype.card (Finset (Fin n)) : ℝ) *
        (2 * Real.exp (-(2 * (n : ℝ)))) := by
      simp [nsmul_eq_mul]
    _ = (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) := by
      rw [hcard]
    _ ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
      two_pow_mul_two_exp_neg_two_mul_le_rpow_neg hnTwo

/-- O'Donnell, Example 6.4 (first assertion): a `p`-biased random function fails
`2 √n · 2⁻ⁿᐟ²`-regularity with probability at most `2⁻ⁿ`. -/
theorem measure_pBiasedRandomFunction_not_isFourierRegular_le
    (n : ℕ) (hn : 1 < n)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (pBiasedRandomFunctionPMF n p hp).toMeasure.real
        {f |
          ¬ IsFourierRegular
            (randomBooleanFourierThreshold n) f.toReal} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  apply (measureReal_mono ?_).trans
    (measure_pBiasedRandomFunction_fourierFailure_le n hn p hp)
  intro f hf
  unfold IsFourierRegular at hf
  push Not at hf
  obtain ⟨S, hS, hf⟩ := hf
  exact Or.inr ⟨S, hS, hf⟩

private def randomBooleanParitySign
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : Sign :=
  ∏ i ∈ S, x i

private theorem signValue_randomBooleanParitySign
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    signValue (randomBooleanParitySign S x) = monomial S x := by
  simp [randomBooleanParitySign, monomial, signValue]

private def randomBooleanModulationEquiv
    (S : Finset (Fin n)) : BooleanFunction n ≃ BooleanFunction n :=
  Equiv.mulRight (randomBooleanParitySign S)

private theorem fourierCoeff_randomBooleanModulation_empty
    (S : Finset (Fin n)) (f : BooleanFunction n) :
    fourierCoeff (randomBooleanModulationEquiv S f).toReal ∅ =
      fourierCoeff f.toReal S := by
  rw [fourierCoeff, fourierCoeff]
  apply Finset.expect_congr rfl
  intro x _
  change
    signValue (f x * randomBooleanParitySign S x) * monomial ∅ x =
      signValue (f x) * monomial S x
  have hmul :
      signValue (f x * randomBooleanParitySign S x) =
        signValue (f x) * signValue (randomBooleanParitySign S x) := by
    simp [signValue]
  rw [hmul, signValue_randomBooleanParitySign]
  simp [monomial]

/-- Every squared Fourier coefficient has mean `2⁻ⁿ` for a uniformly random sign function. -/
theorem expect_sq_fourierCoeff_uniformBooleanFunction
    (S : Finset (Fin n)) :
    (𝔼 f : BooleanFunction n, fourierCoeff f.toReal S ^ 2) =
      1 / (2 : ℝ) ^ n := by
  classical
  let c : ℝ :=
    𝔼 f : BooleanFunction n, fourierCoeff f.toReal ∅ ^ 2
  have heq (T : Finset (Fin n)) :
      (𝔼 f : BooleanFunction n, fourierCoeff f.toReal T ^ 2) = c := by
    unfold c
    apply Fintype.expect_equiv (randomBooleanModulationEquiv T)
    intro f
    rw [fourierCoeff_randomBooleanModulation_empty]
  have hsum :
      ∑ T : Finset (Fin n),
          (𝔼 f : BooleanFunction n, fourierCoeff f.toReal T ^ 2) = 1 := by
    rw [← Finset.expect_sum_comm]
    calc
      (𝔼 f : BooleanFunction n,
          ∑ T : Finset (Fin n), fourierCoeff f.toReal T ^ 2) =
          𝔼 _f : BooleanFunction n, (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro f _
        exact sum_sq_fourierCoeff_eq_one f
      _ = 1 := Fintype.expect_const 1
  have hcard :
      (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_finset]
  have hc :
      (2 : ℝ) ^ n * c = 1 := by
    calc
      (2 : ℝ) ^ n * c =
          (Fintype.card (Finset (Fin n)) : ℝ) * c := by rw [hcard]
      _ = ∑ _T : Finset (Fin n), c := by simp [nsmul_eq_mul]
      _ = 1 := by simpa only [heq] using hsum
  rw [heq]
  exact (eq_div_iff (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))).2
    (by simpa [mul_comm] using hc)

private def randomFunctionEraseContainingEquiv (i : Fin n) :
    {S : Finset (Fin n) // i ∈ S} ≃
      {T : Finset (Fin n) // i ∉ T} where
  toFun S := ⟨S.1.erase i, by simp⟩
  invFun T := ⟨insert i T.1, by simp⟩
  left_inv S := by
    apply Subtype.ext
    simp [Finset.insert_erase S.2]
  right_inv T := by
    apply Subtype.ext
    simp [T.2]

/-- The subset weights in one stable influence sum to `(1 + ρ)ⁿ⁻¹`. -/
theorem sum_pow_card_sub_one_filter_mem
    (ρ : ℝ) (i : Fin n) :
    ∑ S : Finset (Fin n) with i ∈ S, ρ ^ (S.card - 1) =
      (1 + ρ) ^ (n - 1) := by
  classical
  have hleft :
      (∑ S : Finset (Fin n) with i ∈ S, ρ ^ (S.card - 1)) =
        ∑ S : {S : Finset (Fin n) // i ∈ S},
          ρ ^ (S.1.card - 1) := by
    symm
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Finset (Fin n))))
      (p := fun S : Finset (Fin n) ↦ i ∈ S)
      (fun S ↦ ρ ^ (S.card - 1)))
  have hright :
      (∑ T : Finset (Fin n) with i ∉ T, ρ ^ T.card) =
        ∑ T : {T : Finset (Fin n) // i ∉ T.1}, ρ ^ T.1.card := by
    exact Finset.sum_subtype
      ((Finset.univ : Finset (Finset (Fin n))).filter fun T ↦ i ∉ T)
      (by simp)
      (fun T ↦ ρ ^ T.card)
  rw [hleft, show
      (∑ S : {S : Finset (Fin n) // i ∈ S},
          ρ ^ (S.1.card - 1)) =
        ∑ T : {T : Finset (Fin n) // i ∉ T.1}, ρ ^ T.1.card by
      apply Fintype.sum_equiv (randomFunctionEraseContainingEquiv i)
      intro S
      change ρ ^ (S.1.card - 1) = ρ ^ (S.1.erase i).card
      rw [Finset.card_erase_of_mem S.2],
    ← hright]
  have hfilter :
      ((Finset.univ : Finset (Finset (Fin n))).filter fun T ↦ i ∉ T) =
        (Finset.univ.erase i).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset]
    constructor
    · intro hiT
      exact fun j hj ↦ by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro hji
        exact hiT (hji ▸ hj)
    · intro hT hiT
      exact (Finset.mem_erase.mp (hT hiT)).1 rfl
  change
    (∑ T ∈
      ((Finset.univ : Finset (Finset (Fin n))).filter fun T ↦ i ∉ T),
        ρ ^ T.card) = _
  rw [hfilter]
  calc
    (∑ T ∈ (Finset.univ.erase i).powerset, ρ ^ T.card) =
        ∑ T ∈ (Finset.univ.erase i).powerset,
          ρ ^ T.card * 1 ^ ((Finset.univ.erase i).card - T.card) := by
      apply Finset.sum_congr rfl
      intro T _
      simp
    _ = (ρ + 1) ^ (Finset.univ.erase i).card :=
      Finset.sum_pow_mul_eq_add_pow ρ 1 (Finset.univ.erase i)
    _ = (1 + ρ) ^ (n - 1) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [add_comm]

/-- Exercise 6.2: before substituting `ρ = 1 - δ`, the expected stable influence of a uniformly
random sign function is `(1 + ρ)ⁿ⁻¹ / 2ⁿ`. -/
theorem pmfExpectation_uniformBooleanFunction_stableInfluence
    (ρ : ℝ) (i : Fin n) :
    pmfExpectation (uniformPMF (BooleanFunction n))
        (fun f ↦ stableInfluence ρ f.toReal i) =
      (1 + ρ) ^ (n - 1) / (2 : ℝ) ^ n := by
  rw [pmfExpectation_uniformPMF_eq_expect]
  unfold stableInfluence
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect,
    expect_sq_fourierCoeff_uniformBooleanFunction]
  rw [← Finset.sum_mul]
  rw [sum_pow_card_sub_one_filter_mem]
  simp [div_eq_mul_inv]

/-- O'Donnell, Fact 6.8 and Exercise 6.2: for a uniformly random sign-valued function,
the expected `(1 - δ)`-stable influence of every coordinate is
`(1 - δ / 2)ⁿ / (2 - δ)`. -/
theorem pmfExpectation_uniformBooleanFunction_stableInfluence_one_sub
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    pmfExpectation (uniformPMF (BooleanFunction n))
        (fun f ↦ stableInfluence (1 - δ) f.toReal i) =
      (1 - δ / 2) ^ n / (2 - δ) := by
  rw [pmfExpectation_uniformBooleanFunction_stableInfluence]
  have hn : n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  have hden : (2 - δ : ℝ) ≠ 0 := by
    linarith [hδ.2]
  rw [show 1 + (1 - δ) = 2 - δ by ring,
    show 1 - δ / 2 = (2 - δ) / 2 by ring, div_pow]
  field_simp [hden]
  simpa [mul_comm] using pow_sub_one_mul hn (2 - δ)

end FABL
