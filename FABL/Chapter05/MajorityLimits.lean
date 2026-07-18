/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Nat.Choose.Central

/-!
# Majority limits

This file formalizes O'Donnell, Exercise 5.18: the central-binomial power series
for the derivative of `Real.arcsin`, its termwise integral on the open unit
interval, and convergence of the integrated series at both endpoints.
-/

@[expose] public section

namespace FABL

open Filter Finset Set
open scoped Topology

/-- The coefficient of `z^(2j + 1)` in the central-binomial series for `Real.arcsin`. -/
noncomputable def arcsinSeriesCoefficient (j : ℕ) : ℝ :=
  (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) / (2 * j + 1)

/-- The coefficient of `z^k` in the odd-power presentation of the arcsine series. -/
noncomputable def arcsinOddPowerCoefficient (k : ℕ) : ℝ :=
  if Odd k then
    2 / ((k : ℝ) * (2 : ℝ) ^ k) * (Nat.choose (k - 1) ((k - 1) / 2) : ℝ)
  else
    0

@[simp]
theorem arcsinOddPowerCoefficient_two_mul_add_one (j : ℕ) :
    arcsinOddPowerCoefficient (2 * j + 1) = arcsinSeriesCoefficient j := by
  rw [arcsinOddPowerCoefficient, if_pos (odd_two_mul_add_one j)]
  unfold arcsinSeriesCoefficient
  rw [show 2 * j + 1 - 1 = 2 * j by omega, show 2 * j / 2 = j by omega]
  push_cast
  rw [pow_succ]
  field_simp

@[simp]
private lemma arcsinOddPowerCoefficient_two_mul (j : ℕ) :
    arcsinOddPowerCoefficient (2 * j) = 0 := by
  rw [arcsinOddPowerCoefficient, if_neg]
  exact Nat.not_odd_iff_even.2 (even_two_mul j)

@[simp]
private lemma arcsinOddPowerCoefficient_mul_two (j : ℕ) :
    arcsinOddPowerCoefficient (j * 2) = 0 := by
  simpa only [mul_comm] using arcsinOddPowerCoefficient_two_mul j

@[simp]
private lemma arcsinOddPowerCoefficient_mul_two_add_one (j : ℕ) :
    arcsinOddPowerCoefficient (j * 2 + 1) = arcsinSeriesCoefficient j := by
  simpa only [mul_comm] using arcsinOddPowerCoefficient_two_mul_add_one j

private lemma arcsinSeriesCoefficient_nonneg (j : ℕ) :
    0 ≤ arcsinSeriesCoefficient j := by
  unfold arcsinSeriesCoefficient
  positivity

private lemma multichoose_one_half_eq_centralBinom (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n =
      (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hfactorial :=
        Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) (n + 1)
      rw [ascPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_add,
        Polynomial.smeval_X, Polynomial.smeval_natCast] at hfactorial
      simp only [npow_one, npow_zero, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, mul_one] at hfactorial
      have hprevious :=
        Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
      simp only [nsmul_eq_mul] at hprevious
      rw [← hprevious] at hfactorial
      have hrec :
          (n + 1 : ℝ) * Ring.multichoose (1 / 2 : ℝ) (n + 1) =
            (n + 1 / 2 : ℝ) * Ring.multichoose (1 / 2 : ℝ) n := by
        have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hnfac
        calc
          (n.factorial : ℝ) *
                ((n + 1 : ℝ) * Ring.multichoose (1 / 2 : ℝ) (n + 1)) =
              (n + 1 : ℝ) * (n.factorial : ℝ) *
                Ring.multichoose (1 / 2 : ℝ) (n + 1) := by ring
          _ = (n.factorial : ℝ) * Ring.multichoose (1 / 2 : ℝ) n *
                (1 / 2 + n : ℝ) := hfactorial
          _ = (n.factorial : ℝ) *
                ((n + 1 / 2 : ℝ) * Ring.multichoose (1 / 2 : ℝ) n) := by ring
      rw [ih] at hrec
      have hcentral := Nat.succ_mul_centralBinom_succ n
      rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
      rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
      have hcentralR :
          (n + 1 : ℝ) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) =
            2 * (2 * n + 1 : ℝ) * (Nat.choose (2 * n) n : ℝ) := by
        exact_mod_cast hcentral
      have hpow :
          (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        norm_num
        ring
      field_simp at hrec
      have hnext :
          (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) =
            4 * Ring.multichoose (1 / 2 : ℝ) (n + 1) * (2 : ℝ) ^ (2 * n) := by
        apply mul_left_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)
        nlinarith [hcentralR]
      rw [hpow]
      field_simp
      nlinarith

/-- O'Donnell, Exercise 5.18(a): the generalized-binomial expansion of
`(1 - z²)⁻¹ᐟ²` on the open unit interval. -/
theorem exercise5_18a {z : ℝ} (hz : |z| < 1) :
    HasSum
      (fun j : ℕ ↦
        (Nat.choose (2 * j) j : ℝ) * z ^ (2 * j) / (2 : ℝ) ^ (2 * j))
      ((1 - z ^ 2) ^ (-1 / 2 : ℝ)) := by
  have hzsq_lt : z ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z).2 hz
  have hzsq : z ^ 2 ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero]
    exact (enorm_lt_coe (x := z ^ 2) (r := (1 : NNReal))).2 <| by
      rw [← NNReal.coe_lt_coe]
      simpa [Real.norm_of_nonneg (sq_nonneg z)] using hzsq_lt
  have h :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum hzsq
  have hterms :
      HasSum
        (fun j : ℕ ↦
          (Nat.choose (2 * j) j : ℝ) * z ^ (2 * j) / (2 : ℝ) ^ (2 * j))
        (1 / (1 - (0 + z ^ 2)) ^ (1 / 2 : ℝ)) := by
    apply h.congr_fun
    intro j
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    rw [← Ring.multichoose_eq, multichoose_one_half_eq_centralBinom, ← pow_mul]
    ring
  have h' :
      HasSum
        (fun j : ℕ ↦
          (Nat.choose (2 * j) j : ℝ) * z ^ (2 * j) / (2 : ℝ) ^ (2 * j))
        (1 / (1 - z ^ 2) ^ (1 / 2 : ℝ)) := by
    simpa only [zero_add] using hterms
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg (by linarith : 0 ≤ 1 - z ^ 2)]
  simpa only [one_div] using h'

private lemma centralBinomialRatio_nonneg (j : ℕ) :
    0 ≤ (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) := by
  positivity

private lemma centralBinomialRatio_le_one (j : ℕ) :
    (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) ≤ 1 := by
  have hnat := Nat.centralBinom_le_four_pow j
  rw [Nat.centralBinom_eq_two_mul_choose] at hnat
  have hcast :
      (Nat.choose (2 * j) j : ℝ) ≤ ((4 : ℕ) ^ j : ℝ) := by
    exact_mod_cast hnat
  have hpow : ((4 : ℕ) ^ j : ℝ) = (2 : ℝ) ^ (2 * j) := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
  rw [hpow] at hcast
  exact (div_le_one (by positivity)).2 hcast

private lemma hasDerivAt_arcsinSeriesTerm (j : ℕ) (z : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦ arcsinSeriesCoefficient j * y ^ (2 * j + 1))
      ((Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) * z ^ (2 * j)) z := by
  have hscalar :
      arcsinSeriesCoefficient j * (2 * j + 1 : ℕ) =
        (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) := by
    unfold arcsinSeriesCoefficient
    field_simp
    push_cast
    ring
  have h :=
    ((hasDerivAt_id z).pow (2 * j + 1)).const_mul (arcsinSeriesCoefficient j)
  simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one] at h
  rw [← mul_assoc, hscalar] at h
  exact h

private lemma arcsinSeries_summable_and_hasDerivAt {z : ℝ} (hz : |z| < 1) :
    Summable (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1)) ∧
      HasDerivAt
        (fun y : ℝ ↦ ∑' j : ℕ, arcsinSeriesCoefficient j * y ^ (2 * j + 1))
        ((1 - z ^ 2) ^ (-1 / 2 : ℝ)) z := by
  let r : ℝ := (|z| + 1) / 2
  have hr₀ : 0 < r := by
    dsimp [r]
    linarith [abs_nonneg z]
  have hr₁ : r < 1 := by
    dsimp [r]
    linarith
  have hzmem : z ∈ Ioo (-r) r := (abs_lt).1 <| by
    dsimp [r]
    linarith
  have hu : Summable (fun j : ℕ ↦ r ^ (2 * j)) := by
    have hrsq : ‖r ^ 2‖ < 1 := by
      rw [Real.norm_of_nonneg (sq_nonneg r)]
      nlinarith
    simpa only [pow_mul] using (summable_geometric_of_norm_lt_one hrsq)
  have hbound :
      ∀ (j : ℕ) (y : ℝ), y ∈ Ioo (-r) r →
        ‖(Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) * y ^ (2 * j)‖ ≤
          r ^ (2 * j) := by
    intro j y hy
    have hyabs : |y| < r := (abs_lt).2 hy
    rw [norm_mul, Real.norm_of_nonneg (centralBinomialRatio_nonneg j), norm_pow,
      Real.norm_eq_abs]
    calc
      ((Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j)) * |y| ^ (2 * j) ≤
          1 * |y| ^ (2 * j) := by
        gcongr
        exact centralBinomialRatio_le_one j
      _ ≤ 1 * r ^ (2 * j) := by
        gcongr
      _ = r ^ (2 * j) := one_mul _
  have hzero :
      Summable (fun j : ℕ ↦ arcsinSeriesCoefficient j * (0 : ℝ) ^ (2 * j + 1)) := by
    simp
  have hsummable :=
    summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun j y _ ↦ hasDerivAt_arcsinSeriesTerm j y) hbound
      (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith) hzero hzmem
  have hd :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun j y _ ↦ hasDerivAt_arcsinSeriesTerm j y) hbound
      (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
      hzero hzmem
  have hderivsum :
      HasSum
        (fun j : ℕ ↦
          (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) * z ^ (2 * j))
        ((1 - z ^ 2) ^ (-1 / 2 : ℝ)) := by
    apply (exercise5_18a hz).congr_fun
    intro j
    ring
  rw [hderivsum.tsum_eq] at hd
  exact ⟨hsummable, hd⟩

private lemma arcsinSeries_eq_arcsin_of_abs_lt_one {z : ℝ} (hz : |z| < 1) :
    (∑' j : ℕ, arcsinSeriesCoefficient j * z ^ (2 * j + 1)) = Real.arcsin z := by
  let series : ℝ → ℝ :=
    fun y ↦ ∑' j : ℕ, arcsinSeriesCoefficient j * y ^ (2 * j + 1)
  have hseries : DifferentiableOn ℝ series (Ioo (-1) 1) := by
    intro y hy
    exact (arcsinSeries_summable_and_hasDerivAt ((abs_lt).2 hy)).2.differentiableAt
      |>.differentiableWithinAt
  have harcsin : DifferentiableOn ℝ Real.arcsin (Ioo (-1) 1) := by
    intro y hy
    exact (Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])).differentiableAt
      |>.differentiableWithinAt
  have hderiv : EqOn (deriv series) (deriv Real.arcsin) (Ioo (-1) 1) := by
    intro y hy
    have hs := (arcsinSeries_summable_and_hasDerivAt ((abs_lt).2 hy)).2.deriv
    have hyneg : y ≠ -1 := ne_of_gt hy.1
    have hyone : y ≠ 1 := ne_of_lt hy.2
    have hysq : y ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one y).2 ((abs_lt).2 hy)
    have ha := (Real.hasDerivAt_arcsin hyneg hyone).deriv
    rw [hs, ha, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      Real.rpow_neg (by linarith : 0 ≤ 1 - y ^ 2)]
    simp only [one_div]
  have heq :=
    isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo hseries harcsin hderiv
      (show (0 : ℝ) ∈ Set.Ioo (-1) 1 by norm_num)
      (show series 0 = Real.arcsin 0 by simp [series])
  exact heq ((abs_lt).1 hz)

private lemma arcsinSeries_hasSum_of_abs_lt_one {z : ℝ} (hz : |z| < 1) :
    HasSum
      (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1))
      (Real.arcsin z) := by
  have h := (arcsinSeries_summable_and_hasDerivAt hz).1.hasSum
  rw [arcsinSeries_eq_arcsin_of_abs_lt_one hz] at h
  exact h

private lemma summable_arcsinSeriesCoefficient : Summable arcsinSeriesCoefficient := by
  apply summable_of_sum_range_le (c := Real.pi / 2) arcsinSeriesCoefficient_nonneg
  · intro n
    have hcontinuous :
        Continuous
          (fun x : ℝ ↦
            ∑ j ∈ range n, arcsinSeriesCoefficient j * x ^ (2 * j + 1)) := by
      fun_prop
    have hlimit :
        Tendsto
          (fun x : ℝ ↦
            ∑ j ∈ range n, arcsinSeriesCoefficient j * x ^ (2 * j + 1))
          (𝓝[<] (1 : ℝ))
          (𝓝 (∑ j ∈ range n, arcsinSeriesCoefficient j)) := by
      change
        Tendsto
          (fun x : ℝ ↦
            ∑ j ∈ range n, arcsinSeriesCoefficient j * x ^ (2 * j + 1))
          (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio 1))
          (𝓝 (∑ j ∈ range n, arcsinSeriesCoefficient j))
      simpa only [one_pow, mul_one] using
        (hcontinuous.tendsto 1).mono_left inf_le_left
    apply le_of_tendsto hlimit
    · have hpos : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioi 0 :=
        Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hpos] with x hxlt hxpos
      change x < 1 at hxlt
      change 0 < x at hxpos
      have hxabs : |x| < 1 := (abs_lt).2 ⟨by linarith, hxlt⟩
      have hsum := arcsinSeries_hasSum_of_abs_lt_one hxabs
      have hpartial :=
        hsum.summable.sum_le_tsum (range n)
          (fun j _ ↦
            mul_nonneg (arcsinSeriesCoefficient_nonneg j) (pow_nonneg hxpos.le _))
      rw [hsum.tsum_eq] at hpartial
      exact hpartial.trans (Real.arcsin_le_pi_div_two x)

private lemma tsum_arcsinSeriesCoefficient :
    ∑' j : ℕ, arcsinSeriesCoefficient j = Real.pi / 2 := by
  have hlimit :
      Tendsto
        (fun x : ℝ ↦
          ∑' j : ℕ, arcsinSeriesCoefficient j * x ^ (2 * j + 1))
        (𝓝[<] (1 : ℝ))
        (𝓝 (∑' j : ℕ, arcsinSeriesCoefficient j)) := by
    apply tendsto_tsum_of_dominated_convergence summable_arcsinSeriesCoefficient
    · intro j
      change
        Tendsto
          (fun x : ℝ ↦ arcsinSeriesCoefficient j * x ^ (2 * j + 1))
          (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio 1))
          (𝓝 (arcsinSeriesCoefficient j))
      have hc :
          Continuous (fun x : ℝ ↦ arcsinSeriesCoefficient j * x ^ (2 * j + 1)) :=
        continuous_const.mul (continuous_id.pow (2 * j + 1))
      simpa only [one_pow, mul_one] using
        (hc.tendsto 1).mono_left inf_le_left
    · have hpos : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioi 0 :=
        Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hpos] with x hxle hxpos
      change x < 1 at hxle
      change 0 < x at hxpos
      intro j
      rw [norm_mul, Real.norm_of_nonneg (arcsinSeriesCoefficient_nonneg j), norm_pow,
        Real.norm_eq_abs]
      have habs : |x| ≤ 1 := (abs_le).2 ⟨by linarith, hxle.le⟩
      exact mul_le_of_le_one_right (arcsinSeriesCoefficient_nonneg j)
        (pow_le_one₀ (abs_nonneg x) habs)
  have hpos : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioi 0 :=
    Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds zero_lt_one)
  have heq :
      (fun x : ℝ ↦
        ∑' j : ℕ, arcsinSeriesCoefficient j * x ^ (2 * j + 1)) =ᶠ[𝓝[<] (1 : ℝ)]
        Real.arcsin := by
    filter_upwards [self_mem_nhdsWithin, hpos] with x hxlt hxpos
    change x < 1 at hxlt
    change 0 < x at hxpos
    exact arcsinSeries_eq_arcsin_of_abs_lt_one ((abs_lt).2 ⟨by linarith, hxlt⟩)
  have harcsin :
      Tendsto Real.arcsin (𝓝[<] (1 : ℝ)) (𝓝 (Real.pi / 2)) := by
    change
      Tendsto Real.arcsin (𝓝 (1 : ℝ) ⊓ 𝓟 (Iio 1)) (𝓝 (Real.pi / 2))
    simpa only [Real.arcsin_one] using
      (Real.continuous_arcsin.tendsto 1).mono_left inf_le_left
  exact tendsto_nhds_unique hlimit (harcsin.congr' heq.symm)

private lemma arcsinSeries_hasSum_one :
    HasSum arcsinSeriesCoefficient (Real.pi / 2) := by
  rw [← tsum_arcsinSeriesCoefficient]
  exact summable_arcsinSeriesCoefficient.hasSum

private lemma arcsinSeries_hasSum_neg_one :
    HasSum
      (fun j : ℕ ↦ arcsinSeriesCoefficient j * (-1 : ℝ) ^ (2 * j + 1))
      (-(Real.pi / 2)) := by
  apply arcsinSeries_hasSum_one.neg.congr_fun
  intro j
  rw [Odd.neg_one_pow (n := 2 * j + 1) (by
    refine ⟨j, ?_⟩
    ring)]
  ring

private lemma arcsinOddPowerSeries_hasSum_of_arcsinSeries
    {z a : ℝ}
    (h : HasSum
      (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1)) a) :
    HasSum (fun k : ℕ ↦ arcsinOddPowerCoefficient k * z ^ k) a := by
  let g : ℕ → ℝ := fun k ↦ arcsinOddPowerCoefficient k * z ^ k
  let q : ℕ × Fin 2 → ℝ :=
    fun p ↦ g ((Nat.divModEquiv 2).symm p)
  have hfiber :
      ∀ j : ℕ,
        HasSum (fun r : Fin 2 ↦ q (j, r))
          (arcsinSeriesCoefficient j * z ^ (2 * j + 1)) := by
    intro j
    convert hasSum_fintype (fun r : Fin 2 ↦ q (j, r)) using 1
    rw [Fin.sum_univ_two]
    simp [q, g, Nat.divModEquiv_symm_apply, mul_comm]
  have hqnorm : Summable (fun p : ℕ × Fin 2 ↦ ‖q p‖) := by
    apply (summable_prod_of_nonneg fun _ ↦ norm_nonneg _).2
    constructor
    · intro j
      exact Summable.of_finite
    · have houter :
          (fun j : ℕ ↦ ∑' r : Fin 2, ‖q (j, r)‖) =
            fun j : ℕ ↦ ‖arcsinSeriesCoefficient j * z ^ (2 * j + 1)‖ := by
        funext j
        rw [tsum_fintype, Fin.sum_univ_two]
        simp [q, g, Nat.divModEquiv_symm_apply, mul_comm]
      rw [houter]
      exact h.summable.norm
  have hq : Summable q := hqnorm.of_norm
  have hpairs :
      HasSum q a := by
    have hcollapsed := hq.hasSum.prod_fiberwise hfiber
    have hsum : (∑' p : ℕ × Fin 2, q p) = a := hcollapsed.unique h
    rw [← hsum]
    exact hq.hasSum
  have hcomp :
      HasSum (g ∘ (Nat.divModEquiv 2).symm) a := by
    simpa [q, Function.comp_def] using hpairs
  simpa [g] using (Nat.divModEquiv 2).symm.hasSum_iff.mp hcomp

/-- O'Donnell, Exercise 5.18(b)--(c): both odd-power presentations of the
arcsine series converge on the closed unit interval, including its endpoints. -/
theorem exercise5_18_arcsinSeries (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) :
    HasSum
        (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1))
        (Real.arcsin z) ∧
      HasSum
        (fun k : ℕ ↦ arcsinOddPowerCoefficient k * z ^ k)
        (Real.arcsin z) := by
  have hfirst :
      HasSum
        (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1))
        (Real.arcsin z) := by
    by_cases hone : z = 1
    · subst z
      simpa only [one_pow, mul_one, Real.arcsin_one] using arcsinSeries_hasSum_one
    by_cases hneg : z = -1
    · subst z
      simpa only [Real.arcsin_neg_one] using arcsinSeries_hasSum_neg_one
    have hzlt : z < 1 := lt_of_le_of_ne hz.2 hone
    have hneglt : -1 < z := lt_of_le_of_ne hz.1 (Ne.symm hneg)
    exact arcsinSeries_hasSum_of_abs_lt_one ((abs_lt).2 ⟨hneglt, hzlt⟩)
  exact ⟨hfirst, arcsinOddPowerSeries_hasSum_of_arcsinSeries hfirst⟩

/-- O'Donnell, Exercise 5.18: the derivative series on `(-1, 1)`, both
integrated odd-power series on `[-1, 1]`, and their exact endpoint sums. -/
theorem exercise5_18 :
    (∀ z : ℝ, |z| < 1 →
      HasSum
        (fun j : ℕ ↦
          (Nat.choose (2 * j) j : ℝ) * z ^ (2 * j) / (2 : ℝ) ^ (2 * j))
        ((1 - z ^ 2) ^ (-1 / 2 : ℝ))) ∧
      (∀ z : ℝ, z ∈ Icc (-1 : ℝ) 1 →
        HasSum
            (fun j : ℕ ↦ arcsinSeriesCoefficient j * z ^ (2 * j + 1))
            (Real.arcsin z) ∧
          HasSum
            (fun k : ℕ ↦ arcsinOddPowerCoefficient k * z ^ k)
            (Real.arcsin z)) ∧
      ((HasSum
            (fun j : ℕ ↦ arcsinSeriesCoefficient j * (1 : ℝ) ^ (2 * j + 1))
            (Real.pi / 2) ∧
          HasSum
            (fun k : ℕ ↦ arcsinOddPowerCoefficient k * (1 : ℝ) ^ k)
            (Real.pi / 2)) ∧
        (HasSum
            (fun j : ℕ ↦ arcsinSeriesCoefficient j * (-1 : ℝ) ^ (2 * j + 1))
            (-(Real.pi / 2)) ∧
          HasSum
            (fun k : ℕ ↦ arcsinOddPowerCoefficient k * (-1 : ℝ) ^ k)
            (-(Real.pi / 2)))) := by
  refine ⟨fun z hz ↦ exercise5_18a hz, exercise5_18_arcsinSeries, ?_⟩
  have hone := exercise5_18_arcsinSeries 1 (by norm_num)
  have hneg := exercise5_18_arcsinSeries (-1) (by norm_num)
  exact ⟨by simpa only [Real.arcsin_one] using hone,
    by simpa only [Real.arcsin_neg_one] using hneg⟩

end FABL
