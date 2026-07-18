/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions
import FABL.Chapter02.NoiseStability.CorrelatedGaussianLimit
import FABL.Chapter03.LearningTheory.FourierEstimation

/-!
# Sparse polynomial approximation

Book items: Theorem 5.12 and Corollary 5.13.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem fourierOneNorm_pos_of_ne_zero
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0) :
    0 < fourierOneNorm f := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  exact (abs_pos.mpr hx).trans_le (abs_apply_le_fourierOneNorm f x)

private theorem measure_finitePMFEmpiricalMean_sub_integral_ge_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (observation : Ω → ℝ)
    (hobservation : ∀ x, observation x ∈ Set.Icc (-1 : ℝ) 1)
    {m : ℕ} (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (independentProductPMF (fun _ : Fin m ↦ p)).toMeasure.real
        {samples |
          ε ≤
            |finiteUniformEmpiricalMean observation samples -
              ∫ x, observation x ∂p.toMeasure|} ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  rw [independentProductPMF_toMeasure]
  let mean : ℝ := ∫ x, observation x ∂p.toMeasure
  let centeredSum : (Fin m → Ω) → ℝ := fun samples ↦
    ∑ i, (observation (samples i) - mean)
  let empiricalError : (Fin m → Ω) → ℝ := fun samples ↦
    finiteUniformEmpiricalMean observation samples - mean
  let upper : Set (Fin m → Ω) :=
    {samples | (m : ℝ) * ε ≤ centeredSum samples}
  let lower : Set (Fin m → Ω) :=
    {samples | (m : ℝ) * ε ≤ -centeredSum samples}
  have hcoordinate (i : Fin m) :
      HasSubgaussianMGF
        (fun samples : Fin m → Ω ↦ observation (samples i) - mean) 1
        (Measure.pi fun _ : Fin m ↦ p.toMeasure) := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := Measure.pi fun _ : Fin m ↦ p.toMeasure)
      (X := fun samples : Fin m → Ω ↦ observation (samples i))
      (measurable_of_finite fun samples : Fin m → Ω ↦
        observation (samples i)).aemeasurable
      (ae_of_all _ fun samples ↦ hobservation (samples i))
    have hmean :
        ∫ samples : Fin m → Ω, observation (samples i)
          ∂(Measure.pi fun _ : Fin m ↦ p.toMeasure) = mean := by
      rw [integral_comp_eval
        (μ := fun _ : Fin m ↦ p.toMeasure) (i := i)
        (measurable_of_finite observation).aestronglyMeasurable]
    rw [hmean] at h
    norm_num at h ⊢
    exact h
  have hindep :
      iIndepFun
        (fun i (samples : Fin m → Ω) ↦ observation (samples i) - mean)
        (Measure.pi fun _ : Fin m ↦ p.toMeasure) := by
    exact iIndepFun_pi fun _ ↦
      (measurable_of_finite fun x : Ω ↦ observation x - mean).aemeasurable
  have hupper :
      (Measure.pi fun _ : Fin m ↦ p.toMeasure).real upper ≤
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
      (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
      (fun i _ ↦ hcoordinate i)
      (mul_nonneg (Nat.cast_nonneg m) hε)
    simpa [upper, centeredSum] using h
  have hlower :
      (Measure.pi fun _ : Fin m ↦ p.toMeasure).real lower ≤
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) := by
    have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
      (c := fun _ : Fin m ↦ (1 : NNReal)) (s := Finset.univ)
      (fun i _ ↦ hcoordinate i)
    have h := hsum.neg.measure_ge_le (mul_nonneg (Nat.cast_nonneg m) hε)
    simpa [lower, centeredSum] using h
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum (samples : Fin m → Ω) :
      centeredSum samples = (m : ℝ) * empiricalError samples := by
    unfold centeredSum empiricalError
    rw [Finset.sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold finiteUniformEmpiricalMean
    have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
    field_simp
  have hset : {samples | ε ≤ |empiricalError samples|} = upper ∪ lower := by
    ext samples
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro habs
      by_cases hnonneg : 0 ≤ empiricalError samples
      · left
        change (m : ℝ) * ε ≤ centeredSum samples
        rw [hsum]
        rw [abs_of_nonneg hnonneg] at habs
        exact mul_le_mul_of_nonneg_left habs hmReal.le
      · right
        change (m : ℝ) * ε ≤ -centeredSum samples
        rw [hsum]
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at habs
        nlinarith [mul_le_mul_of_nonneg_left habs hmReal.le]
    · rintro (hupper' | hlower')
      · change (m : ℝ) * ε ≤ centeredSum samples at hupper'
        rw [hsum] at hupper'
        have h : ε ≤ empiricalError samples := by nlinarith
        exact h.trans (le_abs_self _)
      · change (m : ℝ) * ε ≤ -centeredSum samples at hlower'
        rw [hsum] at hlower'
        have hneg : ε ≤ -empiricalError samples := by nlinarith
        exact hneg.trans (neg_le_abs _)
  rw [show {samples |
      ε ≤
        |finiteUniformEmpiricalMean observation samples -
          ∫ x, observation x ∂p.toMeasure|} =
      {samples | ε ≤ |empiricalError samples|} by rfl, hset]
  calc
    (Measure.pi fun _ : Fin m ↦ p.toMeasure).real (upper ∪ lower) ≤
        (Measure.pi fun _ : Fin m ↦ p.toMeasure).real upper +
          (Measure.pi fun _ : Fin m ↦ p.toMeasure).real lower :=
      measureReal_union_le upper lower
    _ ≤ Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) +
        Real.exp (-((m : ℝ) * ε) ^ 2 / (2 * (m : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
      have hmNe : (m : ℝ) ≠ 0 := ne_of_gt hmReal
      field_simp
      ring

private noncomputable def fourierAtomPMF
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0) :
    PMF (Finset (Fin n)) := by
  classical
  let L := fourierOneNorm f
  have hL : 0 < L := fourierOneNorm_pos_of_ne_zero f hf
  refine PMF.ofFintype
    (fun S ↦ ENNReal.ofReal (|fourierCoeff f S| / L)) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_div]
    apply congrArg ENNReal.ofReal
    rw [show (∑ S : Finset (Fin n), |fourierCoeff f S|) = L by
      rfl, div_self hL.ne']
  · intro S _
    exact div_nonneg (abs_nonneg _) hL.le

private noncomputable def signedFourierAtom
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℝ :=
  (SignType.sign (fourierCoeff f S) : ℝ) * monomial S x

private theorem signedFourierAtom_mem_Icc
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    signedFourierAtom f S x ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases lt_trichotomy (fourierCoeff f S) 0 with h | h | h <;>
    rcases sq_eq_one_iff.mp (monomial_sq S x) with hm | hm <;>
    simp [signedFourierAtom, sign_apply, h, hm]

private theorem integral_signedFourierAtom_fourierAtomPMF
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0) (x : {−1,1}^[n]) :
    ∫ S, signedFourierAtom f S x ∂(fourierAtomPMF f hf).toMeasure =
      f x / fourierOneNorm f := by
  classical
  have hL : 0 < fourierOneNorm f := fourierOneNorm_pos_of_ne_zero f hf
  rw [PMF.integral_eq_sum]
  simp only [fourierAtomPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hL.le), smul_eq_mul]
  calc
    (∑ S : Finset (Fin n),
        (|fourierCoeff f S| / fourierOneNorm f) *
          signedFourierAtom f S x) =
        (∑ S : Finset (Fin n), fourierCoeff f S * monomial S x) /
          fourierOneNorm f := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      rw [signedFourierAtom]
      field_simp [hL.ne']
      simp [mul_comm]
    _ = f x / fourierOneNorm f := by rw [fourier_expansion f x]

private noncomputable def sampledFourierFamily {s : ℕ}
    (samples : Fin s → Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image samples

private noncomputable def sampledFourierCoefficient {s : ℕ}
    (f : {−1,1}^[n] → ℝ) (samples : Fin s → Finset (Fin n))
    (T : Finset (Fin n)) : ℝ :=
  fourierOneNorm f / s *
    ∑ i : Fin s with samples i = T, (SignType.sign (fourierCoeff f T) : ℝ)

private noncomputable def sampledFourierPolynomial {s : ℕ}
    (f : {−1,1}^[n] → ℝ) (samples : Fin s → Finset (Fin n)) :
    {−1,1}^[n] → ℝ :=
  sparseFourierApproximation
    (sampledFourierFamily samples)
    (sampledFourierCoefficient f samples)

private theorem sampledFourierPolynomial_apply {s : ℕ}
    (f : {−1,1}^[n] → ℝ) (samples : Fin s → Finset (Fin n))
    (x : {−1,1}^[n]) :
    sampledFourierPolynomial f samples x =
      fourierOneNorm f *
        finiteUniformEmpiricalMean (fun T ↦ signedFourierAtom f T x) samples := by
  classical
  let 𝓕 := sampledFourierFamily samples
  have hmaps :
      ∀ i ∈ (Finset.univ : Finset (Fin s)), samples i ∈ 𝓕 := by
    intro i _
    exact Finset.mem_image_of_mem samples (Finset.mem_univ i)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin s))) (t := 𝓕) (g := samples)
      hmaps (fun i ↦ signedFourierAtom f (samples i) x)
  calc
    sampledFourierPolynomial f samples x =
        ∑ T ∈ 𝓕,
          (fourierOneNorm f / s *
              ∑ i : Fin s with samples i = T,
                (SignType.sign (fourierCoeff f T) : ℝ)) *
            monomial T x := by
      rfl
    _ = fourierOneNorm f / s *
        ∑ T ∈ 𝓕,
          ∑ i ∈ (Finset.univ : Finset (Fin s)) with samples i = T,
            signedFourierAtom f (samples i) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.mul_sum]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiT : samples i = T := (Finset.mem_filter.mp hi).2
      simp only [signedFourierAtom, hiT]
      ring
    _ = fourierOneNorm f / s *
        ∑ i : Fin s, signedFourierAtom f (samples i) x := by
      rw [hfiber]
    _ = fourierOneNorm f *
        finiteUniformEmpiricalMean (fun T ↦ signedFourierAtom f T x) samples := by
      simp only [finiteUniformEmpiricalMean]
      ring

private theorem polynomialSparsity_sampledFourierPolynomial_le {s : ℕ}
    (f : {−1,1}^[n] → ℝ) (samples : Fin s → Finset (Fin n)) :
    polynomialSparsity (sampledFourierPolynomial f samples) ≤ s := by
  classical
  have hsupport :
      fourierSupport (sampledFourierPolynomial f samples) ⊆
        sampledFourierFamily samples := by
    intro T hT
    rw [mem_fourierSupport] at hT
    rw [sampledFourierPolynomial,
      fourierCoeff_sparseFourierApproximation] at hT
    by_contra hnot
    simp [hnot] at hT
  rw [polynomialSparsity]
  exact (Finset.card_le_card hsupport).trans
    ((Finset.card_image_le :
      (Finset.univ.image samples).card ≤ (Finset.univ : Finset (Fin s)).card).trans_eq
        (by simp))

private theorem card_signCube_mul_hoeffding_bound_lt_one
    {n s : ℕ} (hn : 0 < n) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ)
    (hs : 4 * (n : ℝ) * L ^ 2 / δ ^ 2 ≤ (s : ℝ)) :
    (Fintype.card ({−1,1}^[n]) : ℝ) *
        (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) < 1 := by
  have hrate :
      2 * (n : ℝ) ≤ (s : ℝ) * (δ / L) ^ 2 / 2 := by
    calc
      2 * (n : ℝ) =
          (4 * (n : ℝ) * L ^ 2 / δ ^ 2) * ((δ / L) ^ 2 / 2) := by
            field_simp [hL.ne', hδ.ne']
            ring
      _ ≤ (s : ℝ) * ((δ / L) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = (s : ℝ) * (δ / L) ^ 2 / 2 := by ring
  have hexp :
      Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) ≤
        Real.exp (-(2 * (n : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow :
      (2 : ℝ) ^ (n + 1) < Real.exp (2 * (n : ℝ)) := by
    have hindex : n + 1 ≤ 2 * n := by omega
    have hbase :
        (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (2 * n) :=
      pow_le_pow_right₀ (by norm_num) hindex
    have hstrict :
        (2 : ℝ) ^ (2 * n) < (Real.exp 1) ^ (2 * n) :=
      pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by omega)
    have hexpPow :
        (Real.exp 1) ^ (2 * n) = Real.exp (2 * (n : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    exact hbase.trans_lt (hstrict.trans_eq hexpPow)
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, Sign]
  calc
    (Fintype.card ({−1,1}^[n]) : ℝ) *
          (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) ≤
        (2 : ℝ) ^ n * (2 * Real.exp (-(2 * (n : ℝ)))) := by
      rw [hcard]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by positivity)
    _ = (2 : ℝ) ^ (n + 1) / Real.exp (2 * (n : ℝ)) := by
      rw [Real.exp_neg, div_eq_mul_inv, pow_succ]
      ring
    _ < 1 := (div_lt_one (Real.exp_pos _)).2 hpow

private theorem exists_fourierAtomSamples_uniformApproximation
    {n s : ℕ} (hn : 0 < n)
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : 4 * (n : ℝ) * fourierOneNorm f ^ 2 / δ ^ 2 ≤ (s : ℝ)) :
    ∃ samples : Fin s → Finset (Fin n),
      (∀ i, fourierCoeff f (samples i) ≠ 0) ∧
        ∀ x, |f x - sampledFourierPolynomial f samples x| < δ := by
  classical
  let L := fourierOneNorm f
  have hL : 0 < L := fourierOneNorm_pos_of_ne_zero f hf
  have hsReal : 0 < (s : ℝ) := by
    have hbound :
        0 < 4 * (n : ℝ) * fourierOneNorm f ^ 2 / δ ^ 2 := by
      positivity
    exact hbound.trans_le hs
  have hsPos : 0 < s := by exact_mod_cast hsReal
  let sampleLaw : PMF (Fin s → Finset (Fin n)) :=
    independentProductPMF (fun _ : Fin s ↦ fourierAtomPMF f hf)
  let bad : {−1,1}^[n] → Set (Fin s → Finset (Fin n)) := fun x ↦
    {samples |
      δ / L ≤
        |finiteUniformEmpiricalMean
              (fun T ↦ signedFourierAtom f T x) samples -
            f x / L|}
  have hrow (x : {−1,1}^[n]) :
      sampleLaw.toMeasure.real (bad x) ≤
        2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) := by
    have hbound :=
      measure_finitePMFEmpiricalMean_sub_integral_ge_le
        (fourierAtomPMF f hf) (fun T ↦ signedFourierAtom f T x)
        (fun T ↦ signedFourierAtom_mem_Icc f T x)
        hsPos (δ / L) (by positivity)
    rw [integral_signedFourierAtom_fourierAtomPMF f hf x] at hbound
    exact hbound
  have hunion :
      sampleLaw.toMeasure.real (⋃ x : {−1,1}^[n], bad x) < 1 := by
    calc
      sampleLaw.toMeasure.real (⋃ x : {−1,1}^[n], bad x) ≤
          ∑ x : {−1,1}^[n], sampleLaw.toMeasure.real (bad x) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _x : {−1,1}^[n],
          2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro x _
        exact hrow x
      _ = (Fintype.card ({−1,1}^[n]) : ℝ) *
          (2 * Real.exp (-(s : ℝ) * (δ / L) ^ 2 / 2)) := by
        simp [nsmul_eq_mul]
      _ < 1 :=
        card_signCube_mul_hoeffding_bound_lt_one hn hL hδ (by
          simpa [L] using hs)
  have hsupportNotSubset :
      ¬sampleLaw.support ⊆ ⋃ x : {−1,1}^[n], bad x := by
    intro hsubset
    have hmeasure :
        sampleLaw.toMeasure (⋃ x : {−1,1}^[n], bad x) = 1 :=
      (sampleLaw.toMeasure_apply_eq_one_iff MeasurableSet.of_discrete).2 hsubset
    have hmeasureReal :
        sampleLaw.toMeasure.real (⋃ x : {−1,1}^[n], bad x) = 1 := by
      rw [Measure.real, hmeasure]
      norm_num
    rw [hmeasureReal] at hunion
    exact (lt_irrefl (1 : ℝ)) hunion
  obtain ⟨samples, hsamplesSupport, hsamples⟩ :=
    Set.not_subset.mp hsupportNotSubset
  refine ⟨samples, ?_, ?_⟩
  · intro i
    have hlaw : sampleLaw samples ≠ 0 :=
      (sampleLaw.mem_support_iff samples).mp hsamplesSupport
    simp only [sampleLaw, independentProductPMF_apply] at hlaw
    have hatom : fourierAtomPMF f hf (samples i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hlaw i (Finset.mem_univ i)
    intro hcoeff
    apply hatom
    simp [fourierAtomPMF, hcoeff]
  · intro x
    have hnotBad : samples ∉ bad x := by
      intro hx
      exact hsamples (Set.mem_iUnion.2 ⟨x, hx⟩)
    have herror :
        |finiteUniformEmpiricalMean
              (fun T ↦ signedFourierAtom f T x) samples -
            f x / L| < δ / L := by
      change ¬ δ / L ≤
        |finiteUniformEmpiricalMean
              (fun T ↦ signedFourierAtom f T x) samples -
            f x / L| at hnotBad
      exact lt_of_not_ge hnotBad
    calc
      |f x - sampledFourierPolynomial f samples x| =
          |L * (f x / L -
            finiteUniformEmpiricalMean
              (fun T ↦ signedFourierAtom f T x) samples)| := by
        rw [sampledFourierPolynomial_apply]
        congr 1
        field_simp [L, hL.ne']
        ring
      _ = L * |f x / L -
          finiteUniformEmpiricalMean
            (fun T ↦ signedFourierAtom f T x) samples| := by
        rw [abs_mul, abs_of_pos hL]
      _ = L * |finiteUniformEmpiricalMean
            (fun T ↦ signedFourierAtom f T x) samples -
          f x / L| := by
        rw [abs_sub_comm]
      _ < L * (δ / L) := mul_lt_mul_of_pos_left herror hL
      _ = δ := by field_simp [hL.ne']

private theorem exists_sparsePolynomial_uniformApproximation_of_ne_zero
    {n s : ℕ} (hn : 0 < n)
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : 4 * (n : ℝ) * fourierOneNorm f ^ 2 / δ ^ 2 ≤ (s : ℝ)) :
    ∃ q : {−1,1}^[n] → ℝ,
      polynomialSparsity q ≤ s ∧ ∀ x, |f x - q x| < δ := by
  obtain ⟨samples, _, happrox⟩ :=
    exists_fourierAtomSamples_uniformApproximation hn f hf hδ hs
  exact ⟨sampledFourierPolynomial f samples,
    polynomialSparsity_sampledFourierPolynomial_le f samples, happrox⟩

/-- O'Donnell, Theorem 5.12: a function on a positive-dimensional Boolean cube has a uniformly
close polynomial whose Fourier support has the stated cardinality bound. -/
theorem exists_sparsePolynomial_uniformApproximation
    {n s : ℕ} (hn : 0 < n)
    (f : {−1,1}^[n] → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : 4 * (n : ℝ) * fourierOneNorm f ^ 2 / δ ^ 2 ≤ (s : ℝ)) :
    ∃ q : {−1,1}^[n] → ℝ,
      polynomialSparsity q ≤ s ∧ ∀ x, |f x - q x| < δ := by
  classical
  by_cases hf : f = 0
  · subst f
    refine ⟨0, ?_, ?_⟩
    · simp [polynomialSparsity, fourierSupport, fourierCoeff]
    · intro x
      simpa using hδ
  · exact exists_sparsePolynomial_uniformApproximation_of_ne_zero
      hn f hf hδ hs

private theorem booleanFunction_toReal_ne_zero (f : BooleanFunction n) :
    f.toReal ≠ 0 := by
  intro hzero
  have hx := congrFun hzero (fun _ ↦ (1 : Sign))
  have hvalue := signValue_eq_neg_one_or_one (f fun _ ↦ (1 : Sign))
  simp only [BooleanFunction.toReal, Pi.zero_apply] at hx
  rcases hvalue with hvalue | hvalue <;> linarith

/-- O'Donnell, Corollary 5.13: every Boolean function on a positive-dimensional cube has a
polynomial threshold representation with sparsity at most the stated ceiling. -/
theorem exists_polynomialThresholdRepresentation_sparsity_le_ceil
    {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    ∃ p : {−1,1}^[n] → ℝ,
      IsPolynomialThresholdRepresentation f p ∧
        polynomialSparsity p ≤
          Nat.ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2) := by
  have hs :
      4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2 / (1 : ℝ) ^ 2 ≤
        (Nat.ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2) : ℝ) := by
    simpa using
      (Nat.le_ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2))
  obtain ⟨p, hsparsity, happrox⟩ :=
    exists_sparsePolynomial_uniformApproximation
      hn f.toReal (δ := 1) (by norm_num) hs
  refine ⟨p, ?_, hsparsity⟩
  intro x
  have hx := happrox x
  rcases Int.units_eq_one_or (f x) with hfx | hfx
  · have hp : 0 < p x := by
      simp only [BooleanFunction.toReal, hfx, signValue_one] at hx
      linarith [abs_lt.mp hx]
    rw [hfx, thresholdSign_of_nonneg hp.le]
  · have hp : p x < 0 := by
      simp only [BooleanFunction.toReal, hfx, signValue_neg_one] at hx
      linarith [abs_lt.mp hx]
    rw [hfx, thresholdSign_of_neg hp]

/-- O'Donnell, Corollary 5.13: every Boolean function on a positive-dimensional cube is the
majority of exactly the stated number of parity or negated-parity functions. Nonvanishing of each
sampled coefficient certifies that every displayed `SignType.sign` is `-1` or `1`. -/
theorem exists_parityMajorityRepresentation
    {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    ∃ samples :
        Fin (Nat.ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2)) →
          Finset (Fin n),
      (∀ i, fourierCoeff f.toReal (samples i) ≠ 0) ∧
        ∀ x,
          f x =
            thresholdSign
              (∑ i,
                (SignType.sign (fourierCoeff f.toReal (samples i)) : ℝ) *
                  monomial (samples i) x) := by
  let s := Nat.ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2)
  change
    ∃ samples : Fin s → Finset (Fin n),
      (∀ i, fourierCoeff f.toReal (samples i) ≠ 0) ∧
        ∀ x,
          f x =
            thresholdSign
              (∑ i,
                (SignType.sign (fourierCoeff f.toReal (samples i)) : ℝ) *
                  monomial (samples i) x)
  have hf : f.toReal ≠ 0 := booleanFunction_toReal_ne_zero f
  have hL : 0 < fourierOneNorm f.toReal :=
    fourierOneNorm_pos_of_ne_zero f.toReal hf
  have hs :
      4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2 / (1 : ℝ) ^ 2 ≤
        (s : ℝ) := by
    simpa [s] using
      (Nat.le_ceil (4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2))
  have hsReal : 0 < (s : ℝ) := by
    have hbound :
        0 < 4 * (n : ℝ) * fourierOneNorm f.toReal ^ 2 := by
      positivity
    exact hbound.trans_le (by simpa using hs)
  obtain ⟨samples, hcoeff, happrox⟩ :=
    exists_fourierAtomSamples_uniformApproximation
      (s := s) hn f.toReal hf (δ := 1) (by norm_num) hs
  have hscale : 0 < fourierOneNorm f.toReal / (s : ℝ) :=
    div_pos hL hsReal
  refine ⟨samples, hcoeff, ?_⟩
  intro x
  have hq :
      sampledFourierPolynomial f.toReal samples x =
        (fourierOneNorm f.toReal / (s : ℝ)) *
          ∑ i : Fin s,
            (SignType.sign (fourierCoeff f.toReal (samples i)) : ℝ) *
              monomial (samples i) x := by
    rw [sampledFourierPolynomial_apply]
    simp only [finiteUniformEmpiricalMean, signedFourierAtom]
    ring
  have hx := happrox x
  rcases Int.units_eq_one_or (f x) with hfx | hfx
  · have hqpos : 0 < sampledFourierPolynomial f.toReal samples x := by
      simp only [BooleanFunction.toReal, hfx, signValue_one] at hx
      linarith [abs_lt.mp hx]
    rw [hq] at hqpos
    have hsum :
        0 <
          ∑ i : Fin s,
            (SignType.sign (fourierCoeff f.toReal (samples i)) : ℝ) *
              monomial (samples i) x :=
      pos_of_mul_pos_right hqpos hscale.le
    rw [hfx, thresholdSign_of_nonneg hsum.le]
  · have hqneg : sampledFourierPolynomial f.toReal samples x < 0 := by
      simp only [BooleanFunction.toReal, hfx, signValue_neg_one] at hx
      linarith [abs_lt.mp hx]
    rw [hq] at hqneg
    have hsum :
        (∑ i : Fin s,
            (SignType.sign (fourierCoeff f.toReal (samples i)) : ℝ) *
              monomial (samples i) x) < 0 :=
      neg_of_mul_neg_right hqneg hscale.le
    rw [hfx, thresholdSign_of_neg hsum]

end FABL
