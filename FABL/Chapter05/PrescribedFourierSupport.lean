/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.LowDegree
public import FABL.Chapter05.LinearThresholdFunctions

/-!
# Approximation on a prescribed Fourier support

Book item: Exercise 5.15(a)--(d).
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance prescribedFourierSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance prescribedFourierSignMeasurableSingletonClass :
    MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The projection of a point indicator onto a prescribed family of Fourier characters. -/
noncomputable def singletonIndicatorFourierProjection
    (𝓕 : Finset (Finset (Fin n))) (a : {−1,1}^[n]) :
    {−1,1}^[n] → ℝ :=
  fun x ↦ ∑ S ∈ 𝓕,
    fourierCoeff (indicatorPolynomial a) S * monomial S x

/-- The normalized point kernel `ψₐ` from Exercise 5.15. -/
noncomputable def prescribedFourierKernel
    (𝓕 : Finset (Finset (Fin n))) (a : {−1,1}^[n]) :
    {−1,1}^[n] → ℝ :=
  fun x ↦
    (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card *
      singletonIndicatorFourierProjection 𝓕 a x

private theorem fourierCoeff_indicatorPolynomial
    (a : {−1,1}^[n]) (S : Finset (Fin n)) :
    fourierCoeff (indicatorPolynomial a) S =
      (Fintype.card ({−1,1}^[n]) : ℝ)⁻¹ * monomial S a := by
  classical
  rw [fourierCoeff, Fintype.expect_eq_sum_div_card]
  simp [indicatorPolynomial_eq_ite, div_eq_inv_mul]

private theorem prescribedFourierKernel_apply
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (a x : {−1,1}^[n]) :
    prescribedFourierKernel 𝓕 a x =
      (𝓕.card : ℝ)⁻¹ *
        ∑ S ∈ 𝓕, monomial S a * monomial S x := by
  classical
  have hcardCube : (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard𝓕 : (𝓕.card : ℝ) ≠ 0 := by
    exact_mod_cast h𝓕.card_pos.ne'
  unfold prescribedFourierKernel singletonIndicatorFourierProjection
  simp_rw [fourierCoeff_indicatorPolynomial]
  rw [Finset.mul_sum]
  conv_rhs =>
    rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  field_simp

/-- Exercise 5.15(a): the normalized prescribed-support kernel equals one at its center. -/
theorem prescribedFourierKernel_apply_self
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (a : {−1,1}^[n]) :
    prescribedFourierKernel 𝓕 a a = 1 := by
  classical
  rw [prescribedFourierKernel_apply 𝓕 h𝓕]
  have hcard𝓕 : (𝓕.card : ℝ) ≠ 0 := by
    exact_mod_cast h𝓕.card_pos.ne'
  simp_rw [← pow_two, monomial_sq]
  simp [hcard𝓕]

private theorem fourierCoeff_prescribedFourierKernel
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (a : {−1,1}^[n]) (T : Finset (Fin n)) :
    fourierCoeff (prescribedFourierKernel 𝓕 a) T =
      if T ∈ 𝓕 then (𝓕.card : ℝ)⁻¹ * monomial T a else 0 := by
  classical
  rw [fourierCoeff]
  simp_rw [prescribedFourierKernel_apply 𝓕 h𝓕]
  rw [show
      (fun x : {−1,1}^[n] ↦
        ((𝓕.card : ℝ)⁻¹ * ∑ S ∈ 𝓕, monomial S a * monomial S x) *
          monomial T x) =
        fun x ↦ ∑ S ∈ 𝓕,
          ((𝓕.card : ℝ)⁻¹ * monomial S a) *
            (monomial S x * monomial T x) by
      funext x
      calc
        ((𝓕.card : ℝ)⁻¹ *
              ∑ S ∈ 𝓕, monomial S a * monomial S x) *
            monomial T x =
            (𝓕.card : ℝ)⁻¹ *
              ((∑ S ∈ 𝓕, monomial S a * monomial S x) *
                monomial T x) := by ring
        _ = (𝓕.card : ℝ)⁻¹ *
              ∑ S ∈ 𝓕,
                (monomial S a * monomial S x) * monomial T x := by
          rw [Finset.sum_mul]
        _ = ∑ S ∈ 𝓕,
              (𝓕.card : ℝ)⁻¹ *
                ((monomial S a * monomial S x) * monomial T x) := by
          rw [Finset.mul_sum]
        _ = ∑ S ∈ 𝓕,
              ((𝓕.card : ℝ)⁻¹ * monomial S a) *
                (monomial S x * monomial T x) := by
          apply Finset.sum_congr rfl
          intro S _
          ring]
  rw [Finset.expect_sum_comm]
  calc
    (∑ S ∈ 𝓕,
        𝔼 x : {−1,1}^[n],
          ((𝓕.card : ℝ)⁻¹ * monomial S a) *
            (monomial S x * monomial T x)) =
        ∑ S ∈ 𝓕,
          ((𝓕.card : ℝ)⁻¹ * monomial S a) *
            (if S = T then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.mul_expect, expect_monomial_mul]
    _ = if T ∈ 𝓕 then (𝓕.card : ℝ)⁻¹ * monomial T a else 0 := by
      by_cases hT : T ∈ 𝓕 <;> simp [hT]

/-- Exercise 5.15(a): the kernel has uniform second moment `1 / |𝓕|`. -/
theorem expect_sq_prescribedFourierKernel
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (a : {−1,1}^[n]) :
    (𝔼 x : {−1,1}^[n], prescribedFourierKernel 𝓕 a x ^ 2) =
      1 / 𝓕.card := by
  classical
  have hparseval := parseval (prescribedFourierKernel 𝓕 a)
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect] at hparseval
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial] at hparseval
  have hparseval' :
      (𝔼 x : {−1,1}^[n], prescribedFourierKernel 𝓕 a x ^ 2) =
        ∑ S, fourierCoeff (prescribedFourierKernel 𝓕 a) S ^ 2 := by
    simpa only [pow_two] using hparseval
  rw [hparseval']
  simp_rw [fourierCoeff_prescribedFourierKernel 𝓕 h𝓕]
  simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [mul_pow, monomial_sq]
  have hcard𝓕 : (𝓕.card : ℝ) ≠ 0 := by
    exact_mod_cast h𝓕.card_pos.ne'
  simp
  field_simp [hcard𝓕]

/-- Exercise 5.15(a): the prescribed-support kernel is symmetric in its two points. -/
theorem prescribedFourierKernel_comm
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (a x : {−1,1}^[n]) :
    prescribedFourierKernel 𝓕 a x =
      prescribedFourierKernel 𝓕 x a := by
  rw [prescribedFourierKernel_apply 𝓕 h𝓕,
    prescribedFourierKernel_apply 𝓕 h𝓕]
  apply congrArg ((𝓕.card : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Exercise 5.15(a): the squared off-center kernel mass has the stated exact value. -/
theorem sum_ne_sq_prescribedFourierKernel
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (x : {−1,1}^[n]) :
    (∑ a : {−1,1}^[n] with a ≠ x,
        prescribedFourierKernel 𝓕 a x ^ 2) =
      (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 := by
  classical
  have hmoment := expect_sq_prescribedFourierKernel 𝓕 h𝓕 x
  rw [Fintype.expect_eq_sum_div_card] at hmoment
  have hsum :
      (∑ a : {−1,1}^[n], prescribedFourierKernel 𝓕 a x ^ 2) =
        (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card := by
    calc
      (∑ a : {−1,1}^[n], prescribedFourierKernel 𝓕 a x ^ 2) =
          ∑ a : {−1,1}^[n], prescribedFourierKernel 𝓕 x a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [prescribedFourierKernel_comm 𝓕 h𝓕]
      _ = (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card := by
        have hcardCube : (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp [hcardCube] at hmoment ⊢
        exact hmoment
  rw [Finset.filter_ne']
  have hsplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset ({−1,1}^[n])))
      (f := fun a ↦ prescribedFourierKernel 𝓕 a x ^ 2)
      (Finset.mem_univ x)
  rw [prescribedFourierKernel_apply_self 𝓕 h𝓕 x] at hsplit
  simp only [one_pow] at hsplit
  linarith

/-- The off-center random sum in Exercise 5.15(b). -/
noncomputable def prescribedFourierOffCenterSum
    (𝓕 : Finset (Finset (Fin n))) (x : {−1,1}^[n])
    (f : BooleanFunction n) : ℝ :=
  ∑ a : {−1,1}^[n] with a ≠ x,
    signValue (f a) * prescribedFourierKernel 𝓕 a x

private theorem uniformBooleanFunction_toMeasure_eq_pi (n : ℕ) :
    (uniformPMF (BooleanFunction n)).toMeasure =
      Measure.pi fun _ : {−1,1}^[n] ↦ (uniformPMF Sign).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [(uniformPMF (BooleanFunction n)).toMeasure_apply_singleton f
    (measurableSet_singleton f), Measure.pi_singleton]
  have hf (x : {−1,1}^[n]) : f x = 1 ∨ f x = -1 :=
    Int.units_eq_one_or (f x)
  simp [uniformPMF, PMF.uniformOfFintype_apply, Fintype.card_pi,
    ENNReal.inv_pow, hf]

private theorem integral_signValue_uniformPMF :
    ∫ s : Sign, signValue s ∂(uniformPMF Sign).toMeasure = 0 := by
  rw [integral_uniformPMF_eq_expect, Fintype.expect_eq_sum_div_card]
  norm_num [Sign, signValue]

private theorem measure_abs_weightedBooleanSum_ge_le
    (w : {−1,1}^[n] → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | t ≤ |∑ a, w a * signValue (f a)|} ≤
      2 * Real.exp
        (-t ^ 2 / (2 * ∑ a, w a ^ 2)) := by
  classical
  rw [uniformBooleanFunction_toMeasure_eq_pi]
  let μ : Measure (BooleanFunction n) :=
    Measure.pi fun _ : {−1,1}^[n] ↦ (uniformPMF Sign).toMeasure
  let X : {−1,1}^[n] → BooleanFunction n → ℝ :=
    fun a f ↦ w a * signValue (f a)
  let c : {−1,1}^[n] → NNReal :=
    fun a ↦ ⟨w a ^ 2, sq_nonneg (w a)⟩
  have hsign (a : {−1,1}^[n]) :
      HasSubgaussianMGF
        (fun f : BooleanFunction n ↦ signValue (f a)) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ)
      (X := fun f : BooleanFunction n ↦ signValue (f a))
      (a := (-1 : ℝ)) (b := (1 : ℝ))
      (measurable_of_finite
        fun f : BooleanFunction n ↦ signValue (f a)).aemeasurable
      (ae_of_all _ fun f ↦ by
        rcases signValue_eq_neg_one_or_one (f a) with hf | hf <;>
          simp [hf])
      (by
        rw [integral_comp_eval
          (μ := fun _ : {−1,1}^[n] ↦ (uniformPMF Sign).toMeasure)
          (i := a)
          (measurable_of_finite signValue).aestronglyMeasurable]
        exact integral_signValue_uniformPMF)
    norm_num at h ⊢
    exact h
  have hcoordinate (a : {−1,1}^[n]) :
      HasSubgaussianMGF (X a) (c a) μ := by
    simpa only [X, c, NNReal.coe_mk, mul_one] using
      (hsign a).const_mul (w a)
  have hindep : iIndepFun X μ := by
    exact iIndepFun_pi fun a ↦
      (measurable_of_finite
        fun s : Sign ↦ w a * signValue s).aemeasurable
  have hsum :
      HasSubgaussianMGF
        (fun f : BooleanFunction n ↦ ∑ a, w a * signValue (f a))
        (∑ a, c a) μ := by
    have h := HasSubgaussianMGF.sum_of_iIndepFun
      hindep (s := Finset.univ) (c := c)
        (fun a _ ↦ hcoordinate a)
    simpa only [X, Finset.sum_apply] using h
  have hupper := hsum.measure_ge_le ht
  have hlower := hsum.neg.measure_ge_le ht
  have hset :
      {f : BooleanFunction n | t ≤ |∑ a, w a * signValue (f a)|} =
        {f | t ≤ ∑ a, w a * signValue (f a)} ∪
          {f | t ≤ -(∑ a, w a * signValue (f a))} := by
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
        ({f | t ≤ ∑ a, w a * signValue (f a)} ∪
          {f | t ≤ -(∑ a, w a * signValue (f a))}) ≤
        μ.real {f | t ≤ ∑ a, w a * signValue (f a)} +
          μ.real {f | t ≤ -(∑ a, w a * signValue (f a))} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (∑ a, c a : NNReal))) +
        Real.exp (-t ^ 2 / (2 * (∑ a, c a : NNReal))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ a, w a ^ 2)) := by
      have hc : ((∑ a, c a : NNReal) : ℝ) = ∑ a, w a ^ 2 := by
        rw [NNReal.coe_sum]
        rfl
      rw [hc]
      ring

private theorem prescribedFourierOffCenterSum_eq_weightedSum
    (𝓕 : Finset (Finset (Fin n))) (x : {−1,1}^[n])
    (f : BooleanFunction n) :
    prescribedFourierOffCenterSum 𝓕 x f =
      ∑ a : {−1,1}^[n],
        (if a = x then 0 else prescribedFourierKernel 𝓕 a x) *
          signValue (f a) := by
  classical
  unfold prescribedFourierOffCenterSum
  rw [Finset.filter_ne']
  calc
    (∑ a ∈ (Finset.univ.erase x),
        signValue (f a) * prescribedFourierKernel 𝓕 a x) =
        ∑ a ∈ (Finset.univ.erase x),
          prescribedFourierKernel 𝓕 a x * signValue (f a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a : {−1,1}^[n],
        (if a = x then 0 else prescribedFourierKernel 𝓕 a x) *
          signValue (f a) := by
      calc
        (∑ a ∈ (Finset.univ.erase x),
            prescribedFourierKernel 𝓕 a x * signValue (f a)) =
            ∑ a ∈ (Finset.univ.erase x),
              (if a = x then 0 else prescribedFourierKernel 𝓕 a x) *
                signValue (f a) := by
          apply Finset.sum_congr rfl
          intro a ha
          have hax : a ≠ x := Finset.ne_of_mem_erase ha
          simp [hax]
        _ = ∑ a : {−1,1}^[n],
            (if a = x then 0 else prescribedFourierKernel 𝓕 a x) *
              signValue (f a) := by
          apply Finset.sum_subset (Finset.erase_subset x Finset.univ)
          intro a _ ha
          have hax : a = x := by
            by_contra hne
            exact ha (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)
          simp [hax]

private theorem sum_sq_prescribedFourierOffCenterWeight
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (x : {−1,1}^[n]) :
    (∑ a : {−1,1}^[n],
        (if a = x then 0 else prescribedFourierKernel 𝓕 a x) ^ 2) =
      (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 := by
  classical
  calc
    (∑ a : {−1,1}^[n],
        (if a = x then 0 else prescribedFourierKernel 𝓕 a x) ^ 2) =
        ∑ a : {−1,1}^[n] with a ≠ x,
          prescribedFourierKernel 𝓕 a x ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hax : a = x <;> simp [hax]
    _ = (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 :=
      sum_ne_sq_prescribedFourierKernel 𝓕 h𝓕 x

private theorem prescribedFourierOffCenterVariance_le
    {n : ℕ} (hn : 0 < n)
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    {ε : ℝ} (hε : 0 < ε ∧ ε < 1)
    (hcard :
      (1 - ε ^ 2 / (6 * (n : ℝ))) *
          (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ)) :
    (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 ≤
      ε ^ 2 / (5 * (n : ℝ)) := by
  let z : ℝ := ε ^ 2 / (n : ℝ)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hεsqPos : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hzPos : 0 < z := div_pos hεsqPos hnReal
  have hεsqLt : ε ^ 2 < 1 := by nlinarith [sq_nonneg (ε - 1)]
  have hzLe : z ≤ 1 := by
    dsimp only [z]
    rw [div_le_one hnReal]
    exact hεsqLt.le.trans (by exact_mod_cast hn)
  have hproduct : 1 ≤ (1 - z / 6) * (1 + z / 5) := by
    have hzOne : 0 ≤ z * (1 - z) :=
      mul_nonneg hzPos.le (sub_nonneg.mpr hzLe)
    nlinarith
  have hfactor : 0 ≤ 1 + z / 5 := by positivity
  have hcard' :
      (1 - z / 6) * (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ) := by
    have hzSix : ε ^ 2 / (6 * (n : ℝ)) = z / 6 := by
      dsimp only [z]
      field_simp
    rwa [hzSix] at hcard
  have hcubePos :
      (0 : ℝ) < Fintype.card ({−1,1}^[n]) := by
    exact_mod_cast Fintype.card_pos
  have hscaled :=
    mul_le_mul_of_nonneg_right hcard' hfactor
  have hone :
      (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        ((1 - z / 6) * (Fintype.card ({−1,1}^[n]) : ℝ)) *
          (1 + z / 5) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by nlinarith [hzLe])) hcubePos.le]
  have hnumerator :
      (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ) * (1 + z / 5) := by
    exact hone.trans (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  have hcard𝓕 : (0 : ℝ) < 𝓕.card := by
    exact_mod_cast h𝓕.card_pos
  have hdiv :
      (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card ≤
        1 + z / 5 :=
    (div_le_iff₀ hcard𝓕).2 (by simpa [mul_comm] using hnumerator)
  have htarget :
      (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 ≤ z / 5 := by
    linarith
  convert htarget using 1
  dsimp only [z]
  field_simp

private theorem two_mul_exp_neg_five_halves_mul_le_four_pow_inv
    {n : ℕ} (hn : 0 < n) :
    2 * Real.exp (-(5 * (n : ℝ) / 2)) ≤
      1 / (4 : ℝ) ^ n := by
  have hexpOne : (8 / 3 : ℝ) < Real.exp 1 :=
    (by norm_num : (8 / 3 : ℝ) < 2.7182818283).trans
      Real.exp_one_gt_d9
  have hexpTwo : (64 / 9 : ℝ) < Real.exp 2 := by
    calc
      (64 / 9 : ℝ) = (8 / 3 : ℝ) ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 :=
        pow_lt_pow_left₀ hexpOne (by norm_num) (by norm_num)
      _ = Real.exp 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hexpHalf : (3 / 2 : ℝ) < Real.exp (1 / 2) := by
    convert Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1
    norm_num
  have hexpBase : (8 : ℝ) < Real.exp (5 / 2) := by
    calc
      (8 : ℝ) < (64 / 9 : ℝ) * (3 / 2 : ℝ) := by norm_num
      _ < Real.exp 2 * Real.exp (1 / 2) :=
        mul_lt_mul hexpTwo hexpHalf.le (by positivity) (by positivity)
      _ = Real.exp (5 / 2) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
  have hpower :
      (2 : ℝ) ^ (2 * n + 1) ≤ Real.exp (5 * (n : ℝ) / 2) := by
    calc
      (2 : ℝ) ^ (2 * n + 1) ≤ (2 : ℝ) ^ (3 * n) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      _ = (8 : ℝ) ^ n := by
        rw [show 3 * n = 3 * n by rfl, pow_mul]
        norm_num
      _ ≤ Real.exp (5 / 2) ^ n :=
        pow_le_pow_left₀ (by norm_num) hexpBase.le n
      _ = Real.exp (5 * (n : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  rw [Real.exp_neg]
  change 2 / Real.exp (5 * (n : ℝ) / 2) ≤ 1 / (4 : ℝ) ^ n
  apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos (by norm_num) _)).2
  rw [one_mul]
  calc
    2 * (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n + 1) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      calc
        2 * (2 : ℝ) ^ (2 * n) =
            (2 : ℝ) ^ 1 * (2 : ℝ) ^ (2 * n) := by norm_num
        _ = (2 : ℝ) ^ (1 + 2 * n) := by rw [pow_add]
        _ = (2 : ℝ) ^ (2 * n + 1) := by
          congr 1
          omega
    _ ≤ Real.exp (5 * (n : ℝ) / 2) := hpower

/-- Exercise 5.15(b): the prescribed off-center sum fails the `ε` bound at a fixed point
with probability at most `4⁻ⁿ`. -/
theorem measure_prescribedFourierOffCenterSum_abs_ge_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    {ε : ℝ} (hε : 0 < ε ∧ ε < 1)
    (hcard :
      (1 - ε ^ 2 / (6 * (n : ℝ))) *
          (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ))
    (x : {−1,1}^[n]) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} ≤
      1 / (4 : ℝ) ^ n := by
  classical
  by_cases hn : n = 0
  · subst n
    convert
      (measureReal_le_one :
        (uniformPMF (BooleanFunction 0)).toMeasure.real
          {f | ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} ≤ 1) using 1
    norm_num
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  let w : {−1,1}^[n] → ℝ :=
    fun a ↦ if a = x then 0 else prescribedFourierKernel 𝓕 a x
  have hoff (f : BooleanFunction n) :
      prescribedFourierOffCenterSum 𝓕 x f =
        ∑ a, w a * signValue (f a) := by
    simpa only [w] using
      prescribedFourierOffCenterSum_eq_weightedSum 𝓕 x f
  simp_rw [hoff]
  have hvariance :
      (∑ a : {−1,1}^[n], w a ^ 2) =
        (Fintype.card ({−1,1}^[n]) : ℝ) / 𝓕.card - 1 := by
    exact sum_sq_prescribedFourierOffCenterWeight 𝓕 h𝓕 x
  have hvarianceLe :
      (∑ a : {−1,1}^[n], w a ^ 2) ≤
        ε ^ 2 / (5 * (n : ℝ)) := by
    rw [hvariance]
    exact prescribedFourierOffCenterVariance_le hnPos 𝓕 h𝓕 hε hcard
  have hvarianceNonneg :
      0 ≤ ∑ a : {−1,1}^[n], w a ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  by_cases hvarianceZero : (∑ a : {−1,1}^[n], w a ^ 2) = 0
  · have hw (a : {−1,1}^[n]) : w a = 0 := by
      have ha :=
        (Finset.sum_eq_zero_iff_of_nonneg
          fun b _ ↦ sq_nonneg (w b)).mp hvarianceZero a (Finset.mem_univ a)
      nlinarith [sq_nonneg (w a)]
    simp [hw, not_le_of_gt hε.1]
  have hvariancePos :
      0 < ∑ a : {−1,1}^[n], w a ^ 2 :=
    lt_of_le_of_ne hvarianceNonneg (Ne.symm hvarianceZero)
  have htail :=
    measure_abs_weightedBooleanSum_ge_le w hε.1.le
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hfiveN : 0 < 5 * (n : ℝ) := by positivity
  have hmul :
      (5 * (n : ℝ)) * (∑ a : {−1,1}^[n], w a ^ 2) ≤ ε ^ 2 := by
    calc
      (5 * (n : ℝ)) * (∑ a : {−1,1}^[n], w a ^ 2) ≤
          (5 * (n : ℝ)) * (ε ^ 2 / (5 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hvarianceLe hfiveN.le
      _ = ε ^ 2 := by field_simp
  have hratio :
      5 * (n : ℝ) ≤ ε ^ 2 / (∑ a : {−1,1}^[n], w a ^ 2) :=
    (le_div_iff₀ hvariancePos).2 hmul
  have hexponent :
      -ε ^ 2 / (2 * ∑ a : {−1,1}^[n], w a ^ 2) ≤
        -(5 * (n : ℝ) / 2) := by
    have hvarianceNe :
        (∑ a : {−1,1}^[n], w a ^ 2) ≠ 0 :=
      ne_of_gt hvariancePos
    field_simp [hvarianceNe] at hratio ⊢
    nlinarith
  calc
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ε ≤ |∑ a, w a * signValue (f a)|} ≤
        2 * Real.exp
          (-ε ^ 2 / (2 * ∑ a : {−1,1}^[n], w a ^ 2)) :=
      htail
    _ ≤ 2 * Real.exp (-(5 * (n : ℝ) / 2)) := by
      gcongr
    _ ≤ 1 / (4 : ℝ) ^ n :=
      two_mul_exp_neg_five_halves_mul_le_four_pow_inv hnPos

/-- The prescribed-support polynomial used in Exercise 5.15(c). -/
noncomputable def prescribedFourierApproximation
    (𝓕 : Finset (Finset (Fin n))) (f : BooleanFunction n) :
    {−1,1}^[n] → ℝ :=
  fun x ↦ ∑ a : {−1,1}^[n],
    signValue (f a) * prescribedFourierKernel 𝓕 a x

/-- The explicit approximation has no Fourier coefficient outside the prescribed family. -/
theorem fourierCoeff_prescribedFourierApproximation_eq_zero
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (f : BooleanFunction n) (T : Finset (Fin n)) (hT : T ∉ 𝓕) :
    fourierCoeff (prescribedFourierApproximation 𝓕 f) T = 0 := by
  classical
  unfold fourierCoeff prescribedFourierApproximation
  rw [show
      (fun x : {−1,1}^[n] ↦
        (∑ a : {−1,1}^[n],
            signValue (f a) * prescribedFourierKernel 𝓕 a x) *
          monomial T x) =
        fun x ↦ ∑ a : {−1,1}^[n],
          signValue (f a) *
            (prescribedFourierKernel 𝓕 a x * monomial T x) by
      funext x
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  calc
    (𝔼 x : {−1,1}^[n],
        signValue (f a) *
          (prescribedFourierKernel 𝓕 a x * monomial T x)) =
        signValue (f a) *
          fourierCoeff (prescribedFourierKernel 𝓕 a) T := by
      rw [fourierCoeff, ← Finset.mul_expect]
    _ = 0 := by
      rw [fourierCoeff_prescribedFourierKernel 𝓕 h𝓕, if_neg hT, mul_zero]

private theorem prescribedFourierApproximation_apply
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    prescribedFourierApproximation 𝓕 f x =
      f.toReal x + prescribedFourierOffCenterSum 𝓕 x f := by
  classical
  unfold prescribedFourierApproximation prescribedFourierOffCenterSum
  rw [Finset.filter_ne']
  have hsplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset ({−1,1}^[n])))
      (f := fun a ↦
        signValue (f a) * prescribedFourierKernel 𝓕 a x)
      (Finset.mem_univ x)
  rw [prescribedFourierKernel_apply_self 𝓕 h𝓕 x] at hsplit
  simp only [mul_one] at hsplit
  rw [BooleanFunction.toReal]
  linarith

/-- A Boolean function has the prescribed-support uniform approximation required in
Exercise 5.15(c). -/
def HasPrescribedFourierUniformApproximation
    (𝓕 : Finset (Finset (Fin n))) (ε : ℝ) (f : BooleanFunction n) : Prop :=
  ∃ q : {−1,1}^[n] → ℝ,
    (∀ T : Finset (Fin n), T ∉ 𝓕 → fourierCoeff q T = 0) ∧
      ∀ x, |f.toReal x - q x| < ε

private theorem measure_exists_prescribedFourierOffCenterFailure_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    {ε : ℝ} (hε : 0 < ε ∧ ε < 1)
    (hcard :
      (1 - ε ^ 2 / (6 * (n : ℝ))) *
          (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ)) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ∃ x : {−1,1}^[n],
          ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} ≤
      1 / (2 : ℝ) ^ n := by
  have hset :
      {f : BooleanFunction n | ∃ x : {−1,1}^[n],
          ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} =
        ⋃ x : {−1,1}^[n],
          {f : BooleanFunction n |
            ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} := by
    ext f
    simp
  rw [hset]
  calc
    (uniformPMF (BooleanFunction n)).toMeasure.real
        (⋃ x : {−1,1}^[n],
          {f : BooleanFunction n |
            ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|}) ≤
        ∑ x : {−1,1}^[n],
          (uniformPMF (BooleanFunction n)).toMeasure.real
            {f : BooleanFunction n |
              ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : {−1,1}^[n], 1 / (4 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro x _
      exact
        measure_prescribedFourierOffCenterSum_abs_ge_le
          𝓕 h𝓕 hε hcard x
    _ = (Fintype.card ({−1,1}^[n]) : ℝ) * (1 / (4 : ℝ) ^ n) := by
      simp [nsmul_eq_mul]
    _ = (2 : ℝ) ^ n * (1 / (4 : ℝ) ^ n) := by
      congr 2
      norm_num [Fintype.card_pi, Sign]
    _ = 1 / (2 : ℝ) ^ n := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      field_simp
      calc
        ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ (n * 2) := by
          rw [pow_mul]
        _ = (2 : ℝ) ^ (2 * n) := by rw [Nat.mul_comm n 2]

/-- Exercise 5.15(c): all but a `2⁻ⁿ` fraction of Boolean functions have a uniformly
`ε`-close multilinear polynomial whose Fourier support lies in `𝓕`. -/
theorem measure_not_hasPrescribedFourierUniformApproximation_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty)
    {ε : ℝ} (hε : 0 < ε ∧ ε < 1)
    (hcard :
      (1 - ε ^ 2 / (6 * (n : ℝ))) *
          (Fintype.card ({−1,1}^[n]) : ℝ) ≤
        (𝓕.card : ℝ)) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ¬HasPrescribedFourierUniformApproximation 𝓕 ε f} ≤
      1 / (2 : ℝ) ^ n := by
  have hsubset :
      {f : BooleanFunction n |
        ¬HasPrescribedFourierUniformApproximation 𝓕 ε f} ⊆
        {f | ∃ x : {−1,1}^[n],
          ε ≤ |prescribedFourierOffCenterSum 𝓕 x f|} := by
    intro f hf
    by_contra hfailure
    apply hf
    refine ⟨prescribedFourierApproximation 𝓕 f, ?_, ?_⟩
    · intro T hT
      exact fourierCoeff_prescribedFourierApproximation_eq_zero
        𝓕 h𝓕 f T hT
    · intro x
      have hgood :
          |prescribedFourierOffCenterSum 𝓕 x f| < ε := by
        by_contra hx
        exact hfailure ⟨x, le_of_not_gt hx⟩
      rw [prescribedFourierApproximation_apply 𝓕 h𝓕]
      simpa only [sub_add_cancel_left, abs_neg] using hgood
  exact
    (measureReal_mono hsubset (by finiteness)).trans
      (measure_exists_prescribedFourierOffCenterFailure_le
        𝓕 h𝓕 hε hcard)

/-- The explicit Fourier-degree cutoff used for Exercise 5.15(d). -/
noncomputable def typicalPolynomialThresholdCutoff (n : ℕ) : ℕ :=
  Nat.floor
    ((n : ℝ) / 2 + (n : ℝ) / 2 *
      Real.sqrt (2 * Real.log ((48 : ℝ) * n) / (n : ℝ)))

private theorem log_48_mul_le_seven_log
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((48 : ℝ) * n) ≤ 7 * Real.log (n : ℝ) := by
  have hn6 : 48 ≤ n ^ 6 := by
    calc
      48 ≤ 2 ^ 6 := by norm_num
      _ ≤ n ^ 6 := Nat.pow_le_pow_left hn 6
  have hnat : 48 * n ≤ n ^ 7 := by
    rw [show n ^ 7 = n ^ 6 * n by ring]
    exact Nat.mul_le_mul_right n hn6
  have hreal : (48 : ℝ) * n ≤ (n : ℝ) ^ 7 := by
    exact_mod_cast hnat
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  calc
    Real.log ((48 : ℝ) * n) ≤ Real.log ((n : ℝ) ^ 7) :=
      Real.strictMonoOn_log.monotoneOn
        (mul_pos (by norm_num) hnReal) (pow_pos hnReal 7) hreal
    _ = 7 * Real.log (n : ℝ) := by
      rw [Real.log_pow]
      norm_num

/-- The explicit cutoff is at most `n / 2 + 2 * √(n log n)` for every `n ≥ 2`,
which realizes the `n / 2 + O(√(n log n))` bound in Exercise 5.15(d). -/
theorem typicalPolynomialThresholdCutoff_le
    {n : ℕ} (hn : 2 ≤ n) :
    (typicalPolynomialThresholdCutoff n : ℝ) ≤
      (n : ℝ) / 2 + 2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hnOneReal : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
  have hnTwoReal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg hnOneReal
  have hlog48n : 0 ≤ Real.log ((48 : ℝ) * n) :=
    Real.log_nonneg (by nlinarith)
  have hinside :
      0 ≤ 2 * Real.log ((48 : ℝ) * n) / (n : ℝ) := by
    positivity
  have hdeviationSq :
      Real.sqrt (2 * Real.log ((48 : ℝ) * n) / (n : ℝ)) ^ 2 =
        2 * Real.log ((48 : ℝ) * n) / (n : ℝ) :=
    Real.sq_sqrt hinside
  have hsqrtSq :
      Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ^ 2 =
        (n : ℝ) * Real.log (n : ℝ) :=
    Real.sq_sqrt (mul_nonneg hnReal.le hlogn)
  have hterm :
      (n : ℝ) / 2 *
          Real.sqrt (2 * Real.log ((48 : ℝ) * n) / (n : ℝ)) ≤
        2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply (sq_le_sq₀
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, hdeviationSq, mul_pow, hsqrtSq]
    have hlog := log_48_mul_le_seven_log hn
    rw [mul_comm (48 : ℝ)] at hlog
    field_simp
    nlinarith
  calc
    (typicalPolynomialThresholdCutoff n : ℝ) ≤
        (n : ℝ) / 2 + (n : ℝ) / 2 *
          Real.sqrt (2 * Real.log ((48 : ℝ) * n) / (n : ℝ)) := by
      apply Nat.floor_le
      exact add_nonneg (by positivity)
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    _ ≤ _ := by linarith

private theorem measure_uniformPMF_real_eq_ncard_div_card
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (A : Set Ω) :
    (uniformPMF Ω).toMeasure.real A =
      (A.ncard : ℝ) / Fintype.card Ω := by
  classical
  rw [Measure.real_def, PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.toReal_sum]
  · rw [Set.ncard_eq_toFinset_card' A]
    simp only [uniformPMF, Set.indicator_apply, PMF.uniformOfFintype_apply]
    calc
      (∑ x : Ω,
        (if x ∈ A then ((Fintype.card Ω : ℝ≥0∞)⁻¹) else 0).toReal) =
          ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ A),
            ((Fintype.card Ω : ℝ≥0∞)⁻¹).toReal := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ A <;> simp [hx]
      _ = ((Finset.univ.filter fun x : Ω ↦ x ∈ A).card : ℝ) *
          ((Fintype.card Ω : ℝ≥0∞)⁻¹).toReal := by
        simp [nsmul_eq_mul]
      _ = _ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
        simp [div_eq_mul_inv]
  · intro x _
    by_cases hx : x ∈ A <;> simp [hx, uniformPMF]

private theorem expect_signValue_prescribedFourierSupport :
    (𝔼 s : Sign, signValue s) = 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [Sign, signValue]

private theorem measure_positiveCoordinateCount_gt_typicalCutoff_le
    {n : ℕ} (hn : 0 < n) :
    (uniformPMF {−1,1}^[n]).toMeasure.real
        {x | typicalPolynomialThresholdCutoff n < positiveCoordinateCount x} ≤
      1 / (24 * (n : ℝ)) := by
  let δ : ℝ :=
    Real.sqrt (2 * Real.log ((48 : ℝ) * n) / (n : ℝ))
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hnOneReal : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hbasePos : (0 : ℝ) < 48 * n :=
    mul_pos (by norm_num) hnReal
  have hlogNonneg : 0 ≤ Real.log ((48 : ℝ) * n) :=
    Real.log_nonneg (by nlinarith)
  have hinside :
      0 ≤ 2 * Real.log ((48 : ℝ) * n) / (n : ℝ) := by
    positivity
  have hδnonneg : 0 ≤ δ := Real.sqrt_nonneg _
  have hconcentration :=
    measure_finiteUniformEmpiricalMean_sub_expect_ge_le
      signValue
      (fun s ↦ by
        rcases signValue_eq_neg_one_or_one s with hs | hs <;> simp [hs])
      (m := n) hn δ hδnonneg
  rw [expect_signValue_prescribedFourierSupport] at hconcentration
  simp only [sub_zero] at hconcentration
  have hsubset :
      {x : {−1,1}^[n] |
        typicalPolynomialThresholdCutoff n < positiveCoordinateCount x} ⊆
        {x | δ ≤ |finiteUniformEmpiricalMean signValue x|} := by
    intro x hx
    change typicalPolynomialThresholdCutoff n < positiveCoordinateCount x at hx
    have hargNonneg :
        0 ≤ (n : ℝ) / 2 + (n : ℝ) / 2 * δ :=
      add_nonneg (by positivity)
        (mul_nonneg (by positivity) hδnonneg)
    have hfloor :
        (n : ℝ) / 2 + (n : ℝ) / 2 * δ <
          positiveCoordinateCount x := by
      apply (Nat.floor_lt hargNonneg).mp
      simpa only [typicalPolynomialThresholdCutoff, δ] using hx
    have hmean :
        finiteUniformEmpiricalMean signValue x =
          (2 * (positiveCoordinateCount x : ℝ) - (n : ℝ)) / (n : ℝ) := by
      rw [finiteUniformEmpiricalMean,
        sum_signValue_eq_two_mul_positiveCoordinateCount_sub]
    have hδlt :
        δ < (2 * (positiveCoordinateCount x : ℝ) - (n : ℝ)) / (n : ℝ) := by
      apply (lt_div_iff₀ hnReal).2
      nlinarith
    change δ ≤ |finiteUniformEmpiricalMean signValue x|
    rw [hmean]
    exact hδlt.le.trans (le_abs_self _)
  calc
    (uniformPMF {−1,1}^[n]).toMeasure.real
        {x | typicalPolynomialThresholdCutoff n < positiveCoordinateCount x} ≤
        (uniformPMF {−1,1}^[n]).toMeasure.real
          {x | δ ≤ |finiteUniformEmpiricalMean signValue x|} :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ 2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2) := hconcentration
    _ = 2 * Real.exp (-Real.log ((48 : ℝ) * n)) := by
      have hδsq :
          δ ^ 2 = 2 * Real.log ((48 : ℝ) * n) / (n : ℝ) :=
        Real.sq_sqrt hinside
      rw [hδsq]
      congr 2
      field_simp
    _ = 1 / (24 * (n : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log hbasePos]
      field_simp
      ring

private theorem ncard_positiveCoordinateCount_gt_typicalCutoff
    (n : ℕ) :
    ({x : {−1,1}^[n] |
      typicalPolynomialThresholdCutoff n < positiveCoordinateCount x}).ncard =
      ({S : Finset (Fin n) |
        typicalPolynomialThresholdCutoff n < S.card}).ncard := by
  apply Set.ncard_congr
    (fun x _ ↦ signCubeEquivFinset n x)
  · intro x hx
    simpa using hx
  · intro x y _ _ hxy
    exact (signCubeEquivFinset n).injective hxy
  · intro S hS
    refine ⟨(signCubeEquivFinset n).symm S, ?_, ?_⟩
    · change typicalPolynomialThresholdCutoff n <
        positiveCoordinateCount ((signCubeEquivFinset n).symm S)
      rw [← signCubeEquivFinset_apply_card]
      simpa using hS
    · exact (signCubeEquivFinset n).apply_symm_apply S

private theorem card_lowDegreeFourierFamily_add_ncard_high
    (n : ℕ) :
    (lowDegreeFourierFamily n (typicalPolynomialThresholdCutoff n)).card +
        ({S : Finset (Fin n) |
          typicalPolynomialThresholdCutoff n < S.card}).ncard =
      2 ^ n := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin n))))
    (p := fun S ↦ S.card ≤ typicalPolynomialThresholdCutoff n)
  rw [Set.ncard_eq_toFinset_card']
  have hlow :
      lowDegreeFourierFamily n (typicalPolynomialThresholdCutoff n) =
        Finset.univ.filter
          (fun S : Finset (Fin n) ↦
            S.card ≤ typicalPolynomialThresholdCutoff n) := by
    ext S
    simp
  rw [hlow]
  convert hpartition using 1 <;> simp

/-- The low-degree family at the explicit cutoff meets the cardinality premise of
Exercise 5.15(c) with `ε = 1 / 2`. -/
theorem card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff
    (n : ℕ) :
    (1 - (1 / 2 : ℝ) ^ 2 / (6 * (n : ℝ))) *
        (Fintype.card ({−1,1}^[n]) : ℝ) ≤
      ((lowDegreeFourierFamily n
        (typicalPolynomialThresholdCutoff n)).card : ℝ) := by
  classical
  by_cases hnZero : n = 0
  · subst n
    norm_num [typicalPolynomialThresholdCutoff,
      lowDegreeFourierFamily]
  have hn : 0 < n := Nat.pos_of_ne_zero hnZero
  let highCube : Set {−1,1}^[n] :=
    {x | typicalPolynomialThresholdCutoff n < positiveCoordinateCount x}
  let highFrequency : Set (Finset (Fin n)) :=
    {S | typicalPolynomialThresholdCutoff n < S.card}
  have htail :=
    measure_positiveCoordinateCount_gt_typicalCutoff_le hn
  rw [measure_uniformPMF_real_eq_ncard_div_card] at htail
  have hhighNcard : highCube.ncard = highFrequency.ncard := by
    exact ncard_positiveCoordinateCount_gt_typicalCutoff n
  have hcubeCard :
      Fintype.card ({−1,1}^[n]) = 2 ^ n := by
    norm_num [Fintype.card_pi, Sign]
  have hdiv :
      (highFrequency.ncard : ℝ) / (2 : ℝ) ^ n ≤
        1 / (24 * (n : ℝ)) := by
    simpa only [highCube, highFrequency, hhighNcard, hcubeCard,
      Nat.cast_pow, Nat.cast_ofNat] using htail
  have hpartition :
      (lowDegreeFourierFamily n
          (typicalPolynomialThresholdCutoff n)).card +
        highFrequency.ncard = 2 ^ n := by
    exact card_lowDegreeFourierFamily_add_ncard_high n
  have hpowPos : (0 : ℝ) < 2 ^ n :=
    pow_pos (by norm_num) n
  have hhighLe :
      (highFrequency.ncard : ℝ) ≤
        (1 / (24 * (n : ℝ))) * (2 : ℝ) ^ n :=
    (div_le_iff₀ hpowPos).1 hdiv
  have hpartitionReal :
      ((lowDegreeFourierFamily n
          (typicalPolynomialThresholdCutoff n)).card : ℝ) +
        highFrequency.ncard = (2 : ℝ) ^ n := by
    exact_mod_cast hpartition
  have hfactor :
      (1 / 2 : ℝ) ^ 2 / (6 * (n : ℝ)) =
        1 / (24 * (n : ℝ)) := by
    field_simp
    ring
  have hpowCast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    norm_num
  rw [hfactor, hcubeCard, hpowCast]
  nlinarith

private theorem isPolynomialThreshold_of_hasLowDegreeUniformApproximation
    (f : BooleanFunction n)
    (happrox :
      HasPrescribedFourierUniformApproximation
        (lowDegreeFourierFamily n (typicalPolynomialThresholdCutoff n))
        (1 / 2 : ℝ) f) :
    IsPolynomialThreshold f (typicalPolynomialThresholdCutoff n) := by
  obtain ⟨q, hsupport, hclose⟩ := happrox
  refine ⟨q, ?_, ?_⟩
  · intro x
    rcases Int.units_eq_one_or (f x) with hfx | hfx
    · have hx :
          |(1 : ℝ) - q x| < 1 / 2 := by
        simpa [BooleanFunction.toReal, hfx] using hclose x
      have hq : 0 ≤ q x := by
        have := (abs_lt.mp hx).2
        linarith
      rw [hfx, thresholdSign_of_nonneg hq]
    · have hx :
          |(-1 : ℝ) - q x| < 1 / 2 := by
        simpa [BooleanFunction.toReal, hfx] using hclose x
      have hq : q x < 0 := by
        have := (abs_lt.mp hx).1
        linarith
      rw [hfx, thresholdSign_of_neg hq]
  · apply (fourierDegree_le_iff q
      (typicalPolynomialThresholdCutoff n)).2
    intro S hcard
    exact hsupport S (by simpa using hcard)

/-- Exercise 5.15(d): except for a `2⁻ⁿ` fraction, Boolean functions have a polynomial
threshold representation at the explicit `n / 2 + O(√(n log n))` cutoff. -/
theorem measure_not_isPolynomialThreshold_typicalPolynomialThresholdCutoff_le
    (n : ℕ) :
    (uniformPMF (BooleanFunction n)).toMeasure.real
        {f | ¬IsPolynomialThreshold f (typicalPolynomialThresholdCutoff n)} ≤
      1 / (2 : ℝ) ^ n := by
  have hsubset :
      {f : BooleanFunction n |
        ¬IsPolynomialThreshold f (typicalPolynomialThresholdCutoff n)} ⊆
        {f |
          ¬HasPrescribedFourierUniformApproximation
            (lowDegreeFourierFamily n (typicalPolynomialThresholdCutoff n))
            (1 / 2 : ℝ) f} := by
    intro f hthreshold happrox
    exact hthreshold
      (isPolynomialThreshold_of_hasLowDegreeUniformApproximation f happrox)
  exact
    (measureReal_mono hsubset (by finiteness)).trans
      (measure_not_hasPrescribedFourierUniformApproximation_le
        (lowDegreeFourierFamily n (typicalPolynomialThresholdCutoff n))
        (lowDegreeFourierFamily_nonempty n
          (typicalPolynomialThresholdCutoff n))
        (by norm_num)
        (card_lowDegreeFourierFamily_typicalPolynomialThresholdCutoff n))

end FABL
