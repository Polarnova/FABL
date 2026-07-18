/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter05.GaussianIsoperimetricConcavity
import FABL.Chapter05.HammingBallLimit
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The signed counterexample to the printed Gaussian-sharp Level-1 bound

Book item: the false printed `[-1,1]` form of Exercise 5.44.
-/

open Filter Finset ProbabilityTheory Set
open scoped BigOperators BooleanCube Topology

namespace FABL

variable {n : ℕ}

/-- The difference of the two opposite strict Hamming tails at threshold `t`. -/
noncomputable def signedHammingTwoTail
    (t : ℝ) (n : ℕ) (x : {−1,1}^[n]) : ℝ :=
  hammingUpperTailIndicator t n x -
    hammingUpperTailIndicator t n (-x)

private theorem normalizedRademacherSum_neg_counterexample
    (x : {−1,1}^[n]) :
  normalizedRademacherSum n (-x) =
      -normalizedRademacherSum n x := by
  unfold normalizedRademacherSum linearForm
  have hsign (s : Sign) :
      signValue (-s) = -signValue s := by
    rcases Int.units_eq_one_or s with hs | hs <;>
      simp [hs, signValue]
  simp only [Pi.neg_apply, hsign, mul_neg, Finset.sum_neg_distrib]

private theorem monomial_neg_input_counterexample
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    monomial S (-x) =
      (-1 : ℝ) ^ S.card * monomial S x := by
  simp [monomial, signValue, Finset.prod_neg]

private theorem fourierCoeff_comp_neg_singleton
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    fourierCoeff (fun x ↦ f (-x)) {i} =
      -fourierCoeff f {i} := by
  unfold fourierCoeff
  rw [show
      (𝔼 x : {−1,1}^[n], f (-x) * monomial {i} x) =
        𝔼 x : {−1,1}^[n], f x * monomial {i} (-x) by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    simp]
  simp_rw [monomial_neg_input_counterexample]
  simp only [Finset.card_singleton, pow_one]
  rw [show
      (fun x : {−1,1}^[n] ↦
        f x * (-1 * monomial {i} x)) =
          fun x ↦ -(f x * monomial {i} x) by
    funext x
    ring]
  exact Finset.expect_neg_distrib
    (Finset.univ : Finset {−1,1}^[n])
    (fun x ↦ f x * monomial {i} x)

/-- Every singleton coefficient of the signed two-tail function is twice
the corresponding coefficient of its upper tail. -/
theorem fourierCoeff_signedHammingTwoTail_singleton
    (t : ℝ) (n : ℕ) (i : Fin n) :
    fourierCoeff (signedHammingTwoTail t n) {i} =
      2 * fourierCoeff (hammingUpperTailIndicator t n) {i} := by
  rw [show
      fourierCoeff (signedHammingTwoTail t n) {i} =
        fourierCoeff (hammingUpperTailIndicator t n) {i} -
          fourierCoeff
            (fun x ↦ hammingUpperTailIndicator t n (-x)) {i} by
    unfold signedHammingTwoTail fourierCoeff
    rw [show
        (fun x : {−1,1}^[n] ↦
          (hammingUpperTailIndicator t n x -
              hammingUpperTailIndicator t n (-x)) *
            monomial {i} x) =
          fun x ↦
            hammingUpperTailIndicator t n x * monomial {i} x -
              hammingUpperTailIndicator t n (-x) * monomial {i} x by
      funext x
      ring]
    exact Finset.expect_sub_distrib
      (Finset.univ : Finset {−1,1}^[n])
      (fun x ↦ hammingUpperTailIndicator t n x * monomial {i} x)
      (fun x ↦ hammingUpperTailIndicator t n (-x) * monomial {i} x)]
  rw [fourierCoeff_comp_neg_singleton]
  ring

private theorem abs_signedHammingTwoTail
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x : {−1,1}^[n]) :
    |signedHammingTwoTail t n x| =
      hammingUpperTailIndicator t n x +
        hammingUpperTailIndicator t n (-x) := by
  have hneg :
      normalizedRademacherSum n (-x) =
        -normalizedRademacherSum n x :=
    normalizedRademacherSum_neg_counterexample x
  by_cases hupper : t < normalizedRademacherSum n x
  · have hlower : ¬t < normalizedRademacherSum n (-x) := by
      rw [hneg]
      linarith
    simp [signedHammingTwoTail, hammingUpperTailIndicator,
      hupper, hlower]
  · by_cases hlower : t < normalizedRademacherSum n (-x)
    · simp [signedHammingTwoTail, hammingUpperTailIndicator,
        hupper, hlower]
    · simp [signedHammingTwoTail, hammingUpperTailIndicator,
        hupper, hlower]

/-- Every signed two-tail function takes values in `[-1,1]`. -/
theorem signedHammingTwoTail_mem_Icc
    (t : ℝ) (n : ℕ) (x : {−1,1}^[n]) :
    signedHammingTwoTail t n x ∈ Icc (-1 : ℝ) 1 := by
  have hupper :
      hammingUpperTailIndicator t n x = 0 ∨
        hammingUpperTailIndicator t n x = 1 := by
    unfold hammingUpperTailIndicator
    split <;> simp
  have hlower :
      hammingUpperTailIndicator t n (-x) = 0 ∨
        hammingUpperTailIndicator t n (-x) = 1 := by
    unfold hammingUpperTailIndicator
    split <;> simp
  rcases hupper with hupper | hupper <;>
    rcases hlower with hlower | hlower <;>
      simp [signedHammingTwoTail, hupper, hlower]

private theorem expect_hammingUpperTailIndicator_comp_neg
    (t : ℝ) (n : ℕ) :
    (𝔼 x : {−1,1}^[n], hammingUpperTailIndicator t n (-x)) =
      𝔼 x : {−1,1}^[n], hammingUpperTailIndicator t n x := by
  apply Fintype.expect_equiv (Equiv.neg _)
  intro x
  simp

/-- The absolute mean of a signed two-tail function is twice the mass of
one tail. -/
theorem expect_abs_signedHammingTwoTail
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (𝔼 x : {−1,1}^[n], |signedHammingTwoTail t n x|) =
      2 * (𝔼 x : {−1,1}^[n],
        hammingUpperTailIndicator t n x) := by
  rw [show
      (fun x : {−1,1}^[n] ↦ |signedHammingTwoTail t n x|) =
        fun x ↦
          hammingUpperTailIndicator t n x +
            hammingUpperTailIndicator t n (-x) by
    funext x
    exact abs_signedHammingTwoTail t ht n x,
    Finset.expect_add_distrib,
    expect_hammingUpperTailIndicator_comp_neg]
  ring

/-- The level-one weight of the signed two-tail function is four times
the level-one weight of one tail. -/
theorem fourierWeightAtLevel_one_signedHammingTwoTail
    (t : ℝ) (n : ℕ) :
    fourierWeightAtLevel 1 (signedHammingTwoTail t n) =
      4 * fourierWeightAtLevel 1
        (hammingUpperTailIndicator t n) := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton,
    fourierWeightAtLevel_one_eq_sum_singleton]
  simp_rw [fourierCoeff_signedHammingTwoTail_singleton]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The common singleton-coefficient bound used by the signed two-tail
sequence. -/
noncomputable def signedHammingTwoTailEpsilon
    (t : ℝ) (m : ℕ) : ℝ :=
  |2 * fourierCoeff
    (hammingUpperTailIndicator t (m + 1))
    {(0 : Fin (m + 1))}|

/-- Every singleton coefficient of the signed two-tail sequence has
magnitude exactly its chosen regularity parameter. -/
theorem abs_fourierCoeff_signedHammingTwoTail_eq_epsilon
    (t : ℝ) (m : ℕ) (i : Fin (m + 1)) :
    |fourierCoeff (signedHammingTwoTail t (m + 1)) {i}| =
      signedHammingTwoTailEpsilon t m := by
  rw [fourierCoeff_signedHammingTwoTail_singleton]
  unfold signedHammingTwoTailEpsilon
  rw [fourierCoeff_hammingUpperTailIndicator_singleton t m i,
    fourierCoeff_hammingUpperTailIndicator_singleton t m
      (0 : Fin (m + 1))]

private theorem tendsto_inv_sqrt_nat_succ :
    Tendsto
      (fun m : ℕ ↦
        (Real.sqrt (((m + 1 : ℕ) : ℝ)))⁻¹)
      atTop (𝓝 0) := by
  have hbase :
      Tendsto
        (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)
        atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact hbase.comp (tendsto_add_atTop_nat 1)

/-- The singleton-coefficient parameter of the signed two-tail sequence
converges to zero. -/
theorem tendsto_signedHammingTwoTailEpsilon (t : ℝ) :
    Tendsto (signedHammingTwoTailEpsilon t)
      atTop (𝓝 0) := by
  have hcoeff :
      Tendsto
        (fun m : ℕ ↦
          fourierCoeff
            (hammingUpperTailIndicator t (m + 1))
            {(0 : Fin (m + 1))})
        atTop (𝓝 0) := by
    have hproduct :=
      (tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum
        t).mul tendsto_inv_sqrt_nat_succ
    simpa only [
      fourierCoeff_hammingUpperTailIndicator_singleton,
      div_eq_mul_inv, mul_zero] using hproduct
  change Tendsto
    (fun m : ℕ ↦
      |2 * fourierCoeff
        (hammingUpperTailIndicator t (m + 1))
        {(0 : Fin (m + 1))}|)
    atTop (𝓝 0)
  simpa only [mul_zero, abs_zero] using (hcoeff.const_mul 2).abs

/-- The absolute means of the signed two-tail sequence converge to twice
the corresponding Gaussian upper-tail probability. -/
theorem tendsto_expect_abs_signedHammingTwoTail
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          |signedHammingTwoTail t (m + 1) x|)
      atTop (𝓝 (2 * standardGaussianUpperTail t)) := by
  rw [show
      (fun m : ℕ ↦
        𝔼 x : {−1,1}^[m + 1],
          |signedHammingTwoTail t (m + 1) x|) =
        fun m ↦
          2 * (𝔼 x : {−1,1}^[m + 1],
            hammingUpperTailIndicator t (m + 1) x) by
    funext m
    exact expect_abs_signedHammingTwoTail t ht (m + 1)]
  exact (tendsto_expect_hammingUpperTailIndicator t).const_mul 2

/-- The level-one weights of the signed two-tail sequence converge to four
times the squared Gaussian density at the threshold. -/
theorem tendsto_fourierWeightAtLevel_one_signedHammingTwoTail
    (t : ℝ) :
    Tendsto
      (fun m : ℕ ↦
        fourierWeightAtLevel 1
          (signedHammingTwoTail t (m + 1)))
      atTop (𝓝 (4 * gaussianPDFReal 0 1 t ^ 2)) := by
  rw [show
      (fun m : ℕ ↦
        fourierWeightAtLevel 1
          (signedHammingTwoTail t (m + 1))) =
        fun m ↦
          4 * fourierWeightAtLevel 1
            (hammingUpperTailIndicator t (m + 1)) by
    funext m
    exact fourierWeightAtLevel_one_signedHammingTwoTail t (m + 1)]
  exact (proposition5_25 t).2.const_mul 4

private theorem strictConcaveOn_gaussianIsoperimetricReal :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1)
      gaussianIsoperimetricReal := by
  apply strictConcaveOn_of_deriv2_neg
    (convex_Icc (0 : ℝ) 1)
    continuousOn_gaussianIsoperimetricReal
  intro α hα
  rw [interior_Icc] at hα
  rw [gaussianIsoperimetric_second_derivative hα]
  exact div_neg_of_neg_of_pos (by norm_num)
    (gaussianIsoperimetricReal_pos hα)

private theorem exists_signedHammingTwoTail_alpha :
    ∃ α : ℝ,
      1 / 4 < α ∧ α < 1 / 2 ∧
        gaussianIsoperimetricReal α <
          2 * gaussianIsoperimetricReal (1 / 8) := by
  have hmidpoint :=
    strictConcaveOn_gaussianIsoperimetricReal.2
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      (show (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      (show (0 : ℝ) ≠ 1 / 4 by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hstrict :
      gaussianIsoperimetricReal (1 / 4) <
        2 * gaussianIsoperimetricReal (1 / 8) := by
    norm_num [smul_eq_mul] at hmidpoint ⊢
    linarith
  have hcontinuous :
      ContinuousAt gaussianIsoperimetricReal (1 / 4) :=
    continuousOn_gaussianIsoperimetricReal.continuousAt
      (Icc_mem_nhds (by norm_num) (by norm_num))
  have hU :
      ∀ᶠ α in 𝓝 (1 / 4 : ℝ),
        gaussianIsoperimetricReal α <
          2 * gaussianIsoperimetricReal (1 / 8) :=
    hcontinuous.tendsto.eventually (Iio_mem_nhds hstrict)
  have hUright :
      ∀ᶠ α in 𝓝[>] (1 / 4 : ℝ),
        gaussianIsoperimetricReal α <
          2 * gaussianIsoperimetricReal (1 / 8) :=
    hU.filter_mono inf_le_left
  have hhalf :
      ∀ᶠ α in 𝓝[>] (1 / 4 : ℝ), α < 1 / 2 :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 / 4 : ℝ), α < 1 / 2 from
      Iio_mem_nhds (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).filter_mono
        inf_le_left
  have hcombined :
      ∀ᶠ α in 𝓝[>] (1 / 4 : ℝ),
        1 / 4 < α ∧ α < 1 / 2 ∧
          gaussianIsoperimetricReal α <
            2 * gaussianIsoperimetricReal (1 / 8) := by
    filter_upwards [self_mem_nhdsWithin, hhalf, hUright] with α hαgt hαhalf hαU
    exact ⟨hαgt, hαhalf, hαU⟩
  exact hcombined.exists

/-- The printed `[-1,1]` version of Exercise 5.44 is false. There is one
fixed `α ∈ (0,1/2)` for which every proposed error constant is defeated by
a signed two-tail function with arbitrarily small singleton coefficients. -/
theorem exercise5_44_printed_false :
    ∃ α : unitInterval, 0 < (α : ℝ) ∧ (α : ℝ) < 1 / 2 ∧
      ∀ Cα : ℝ,
        ∃ (n : ℕ) (f : {−1,1}^[n] → ℝ) (ε : ℝ),
          (∀ x, -1 ≤ f x) ∧
          (∀ x, f x ≤ 1) ∧
          (𝔼 x, |f x|) ≤ (α : ℝ) ∧
          (∀ i, |fourierCoeff f {i}| ≤ ε) ∧
          0 ≤ ε ∧
          gaussianIsoperimetric α ^ 2 + Cα * ε <
            fourierWeightAtLevel 1 f := by
  obtain ⟨α, hquarterα, hαhalf, hUα⟩ :=
    exists_signedHammingTwoTail_alpha
  have hαpos : 0 < α := by linarith
  let αUnit : unitInterval :=
    ⟨α, hαpos.le, by linarith⟩
  refine ⟨αUnit, hαpos, hαhalf, ?_⟩
  intro Cα
  let β : ℝ := 1 / 8
  have hβ : β ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [β]
    norm_num
  let βOpen : Ioo (0 : ℝ) 1 := ⟨β, hβ⟩
  let t : ℝ := standardGaussianUpperQuantile βOpen
  have htail : standardGaussianUpperTail t = β := by
    simpa only [t, βOpen] using
      standardGaussianUpperTail_quantile βOpen
  have htpos : 0 < t := by
    have htailZero : standardGaussianUpperTail 0 = 1 / 2 := by
      have hreflection := standardGaussianUpperTail_neg 0
      norm_num at hreflection ⊢
      linarith
    by_contra ht
    have htle : t ≤ 0 := le_of_not_gt ht
    have hanti :=
      standardGaussianUpperTail_strictAnti.antitone htle
    rw [htailZero, htail] at hanti
    dsimp only [β] at hanti
    norm_num at hanti
  have hpdf :
      gaussianPDFReal 0 1 t =
        gaussianIsoperimetricReal β := by
    rw [gaussianIsoperimetricReal_apply_of_mem_Ioo hβ]
  have hUα' :
      gaussianIsoperimetricReal α <
        2 * gaussianIsoperimetricReal β := by
    simpa only [β] using hUα
  have hUβpos : 0 < gaussianIsoperimetricReal β :=
    gaussianIsoperimetricReal_pos hβ
  have hUαpos : 0 < gaussianIsoperimetricReal α :=
    gaussianIsoperimetricReal_pos ⟨hαpos, by linarith⟩
  have hgap :
      gaussianIsoperimetricReal α ^ 2 <
        4 * gaussianPDFReal 0 1 t ^ 2 := by
    rw [hpdf]
    nlinarith
  have hmean :
      Tendsto
        (fun m : ℕ ↦
          𝔼 x : {−1,1}^[m + 1],
            |signedHammingTwoTail t (m + 1) x|)
        atTop (𝓝 (2 * β)) := by
    simpa only [htail] using
      tendsto_expect_abs_signedHammingTwoTail t htpos.le
  have hε :
      Tendsto (signedHammingTwoTailEpsilon t)
        atTop (𝓝 0) :=
    tendsto_signedHammingTwoTailEpsilon t
  have hweight :
      Tendsto
        (fun m : ℕ ↦
          fourierWeightAtLevel 1
            (signedHammingTwoTail t (m + 1)))
        atTop (𝓝 (4 * gaussianPDFReal 0 1 t ^ 2)) :=
    tendsto_fourierWeightAtLevel_one_signedHammingTwoTail t
  have hmeanEventually :
      ∀ᶠ m : ℕ in atTop,
        (𝔼 x : {−1,1}^[m + 1],
          |signedHammingTwoTail t (m + 1) x|) < α := by
    exact hmean.eventually <| Iio_mem_nhds <| by
      dsimp only [β]
      linarith
  have herror :
      Tendsto
        (fun m : ℕ ↦
          fourierWeightAtLevel 1
              (signedHammingTwoTail t (m + 1)) -
            Cα * signedHammingTwoTailEpsilon t m)
        atTop (𝓝 (4 * gaussianPDFReal 0 1 t ^ 2)) := by
    simpa only [mul_zero, sub_zero] using
      hweight.sub (hε.const_mul Cα)
  have hviolateEventually :
      ∀ᶠ m : ℕ in atTop,
        gaussianIsoperimetricReal α ^ 2 +
              Cα * signedHammingTwoTailEpsilon t m <
          fourierWeightAtLevel 1
            (signedHammingTwoTail t (m + 1)) := by
    have heventually :
        ∀ᶠ m : ℕ in atTop,
          gaussianIsoperimetricReal α ^ 2 <
            fourierWeightAtLevel 1
                (signedHammingTwoTail t (m + 1)) -
              Cα * signedHammingTwoTailEpsilon t m :=
      herror.eventually (Ioi_mem_nhds hgap)
    filter_upwards [heventually] with m hm
    linarith
  obtain ⟨m, hmMean, hmViolate⟩ :=
    (hmeanEventually.and hviolateEventually).exists
  let f : {−1,1}^[m + 1] → ℝ :=
    signedHammingTwoTail t (m + 1)
  let ε : ℝ := signedHammingTwoTailEpsilon t m
  refine ⟨m + 1, f, ε, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (signedHammingTwoTail_mem_Icc t (m + 1) x).1
  · intro x
    exact (signedHammingTwoTail_mem_Icc t (m + 1) x).2
  · exact hmMean.le
  · intro i
    rw [show f = signedHammingTwoTail t (m + 1) by rfl,
      abs_fourierCoeff_signedHammingTwoTail_eq_epsilon]
  · exact abs_nonneg _
  · rw [show f = signedHammingTwoTail t (m + 1) by rfl]
    rw [← gaussianIsoperimetricReal_eq_gaussianIsoperimetric αUnit]
    exact hmViolate

end FABL
