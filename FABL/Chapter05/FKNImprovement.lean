/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import FABL.Chapter02.FKN
public import FABL.Chapter03.LowDegreeSpectralConcentration

/-!
# The balanced FKN lift and numerical details for the improved bound

Book items: Exercise 2.49 and Exercise 5.38.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## The balanced lift from Exercise 2.49 -/

/-- O'Donnell, Exercise 2.49: the balanced lift
`g(x₀, x) = x₀ f(x₀ x)` of a Boolean function. -/
def balancedFKNLift (f : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun z ↦ z 0 * f (fun i ↦ z 0 * z i.succ)

@[simp] theorem balancedFKNLift_fin_cons_one
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    balancedFKNLift f (Fin.cons 1 x) = f x := by
  simp [balancedFKNLift]

@[simp] theorem balancedFKNLift_fin_cons_neg_one
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    balancedFKNLift f (Fin.cons (-1) x) = -f (-x) := by
  apply Units.ext
  norm_num [balancedFKNLift, Fin.cons]
  exact congrArg Units.val (congrArg f (by funext i; rfl))

private theorem balancedFKNLift_toReal_fin_cons_one
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    (balancedFKNLift f).toReal (Fin.cons 1 x) = f.toReal x := by
  rw [BooleanFunction.toReal, BooleanFunction.toReal,
    balancedFKNLift_fin_cons_one]

private theorem balancedFKNLift_toReal_fin_cons_neg_one
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    (balancedFKNLift f).toReal (Fin.cons (-1) x) = -f.toReal (-x) := by
  rw [BooleanFunction.toReal, BooleanFunction.toReal,
    balancedFKNLift_fin_cons_neg_one]
  rcases Int.units_eq_one_or (f (-x)) with h | h <;>
    simp [h, signValue]

/-- Exercise 2.49: the balanced lift has mean zero. -/
theorem mean_balancedFKNLift (f : BooleanFunction n) :
    mean (balancedFKNLift f).toReal = 0 := by
  rw [mean, expect_fin_cons]
  simp_rw [balancedFKNLift_toReal_fin_cons_one,
    balancedFKNLift_toReal_fin_cons_neg_one]
  have hneg :
      (𝔼 x : {−1,1}^[n], -f.toReal (-x)) =
        -(𝔼 x : {−1,1}^[n], f.toReal x) := by
    rw [Finset.expect_neg_distrib]
    congr 1
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    rfl
  rw [hneg]
  ring

private theorem fourierCoeff_negatedInput_toReal
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ -f.toReal (-x)) S =
      -((-1 : ℝ) ^ S.card * fourierCoeff f.toReal S) := by
  unfold fourierCoeff
  rw [show
      (𝔼 x : {−1,1}^[n], -f.toReal (-x) * monomial S x) =
        𝔼 x : {−1,1}^[n],
          -f.toReal x * monomial S (-x) by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    simp]
  have hmonomial (x : {−1,1}^[n]) :
      monomial S (-x) = (-1 : ℝ) ^ S.card * monomial S x := by
    simp [monomial, signValue, Finset.prod_neg]
  simp_rw [hmonomial]
  rw [show
      (fun x : {−1,1}^[n] ↦
        -f.toReal x * ((-1 : ℝ) ^ S.card * monomial S x)) =
      fun x ↦ -((-1 : ℝ) ^ S.card) * (f.toReal x * monomial S x) by
    funext x
    ring]
  rw [← Finset.mul_expect]
  ring

private theorem fourierCoeff_balancedFKNLift_zero (f : BooleanFunction n) :
    fourierCoeff (balancedFKNLift f).toReal {0} =
      fourierCoeff f.toReal ∅ := by
  rw [show ({0} : Finset (Fin (n + 1))) =
      insert 0 (tailFrequency (∅ : Finset (Fin n))) by
    simp [tailFrequency]]
  rw [fourierCoeff_insert_zero_tailFrequency]
  simp_rw [show firstCoordinateSlice (balancedFKNLift f).toReal 1 = f.toReal by
    funext x
    exact balancedFKNLift_toReal_fin_cons_one f x]
  rw [show firstCoordinateSlice (balancedFKNLift f).toReal (-1) =
      fun x ↦ -f.toReal (-x) by
    funext x
    exact balancedFKNLift_toReal_fin_cons_neg_one f x]
  rw [fourierCoeff_negatedInput_toReal]
  simp

private theorem fourierCoeff_balancedFKNLift_succ
    (f : BooleanFunction n) (i : Fin n) :
    fourierCoeff (balancedFKNLift f).toReal {i.succ} =
      fourierCoeff f.toReal {i} := by
  rw [show ({i.succ} : Finset (Fin (n + 1))) =
      tailFrequency ({i} : Finset (Fin n)) by
    simp [tailFrequency]]
  rw [fourierCoeff_tailFrequency]
  simp_rw [show firstCoordinateSlice (balancedFKNLift f).toReal 1 = f.toReal by
    funext x
    exact balancedFKNLift_toReal_fin_cons_one f x]
  rw [show firstCoordinateSlice (balancedFKNLift f).toReal (-1) =
      fun x ↦ -f.toReal (-x) by
    funext x
    exact balancedFKNLift_toReal_fin_cons_neg_one f x]
  rw [fourierCoeff_negatedInput_toReal]
  simp

/-- Exercise 2.49: the level-one Fourier weight of the balanced lift is the
degree-at-most-one Fourier weight of the original function. -/
theorem fourierWeightAtLevel_one_balancedFKNLift
    (f : BooleanFunction n) :
    fourierWeightAtLevel 1 (balancedFKNLift f).toReal =
      fourierWeightAtMost 1 f.toReal := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton, Fin.sum_univ_succ]
  simp_rw [fourierCoeff_balancedFKNLift_zero,
    fourierCoeff_balancedFKNLift_succ]
  rw [fourierWeightAtMost_one_eq_empty_add_sum_singleton]

private def balancedFKNProjection
    (i : Fin (n + 1)) (negated : Bool) : BooleanFunction n :=
  fun x ↦ signedDictator i negated (Fin.cons 1 x)

private theorem balancedFKNProjection_isKJunta_one
    (i : Fin (n + 1)) (negated : Bool) :
    IsKJunta (balancedFKNProjection i negated) 1 := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · refine ⟨∅, by simp, ?_⟩
    intro x y _
    cases negated <;> simp [balancedFKNProjection, signedDictator, dictator]
  · refine ⟨{j}, by simp, ?_⟩
    intro x y hxy
    have hxyj : x j = y j := hxy j (by simp)
    cases negated <;>
      simp [balancedFKNProjection, signedDictator, dictator, hxyj]

private theorem signedDictator_neg_input
    (i : Fin (n + 1)) (negated : Bool) (z : {−1,1}^[n + 1]) :
    signedDictator i negated (-z) = -signedDictator i negated z := by
  cases negated <;> simp [signedDictator, dictator]

private theorem signedDictator_fin_cons_neg_one
    (i : Fin (n + 1)) (negated : Bool) (x : {−1,1}^[n]) :
    signedDictator i negated (Fin.cons (-1) x) =
      -signedDictator i negated (Fin.cons 1 (-x)) := by
  rw [← signedDictator_neg_input]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp

private theorem relativeHammingDist_balancedFKNLift_signedDictator
    (f : BooleanFunction n) (i : Fin (n + 1)) (negated : Bool) :
    relativeHammingDist (balancedFKNLift f) (signedDictator i negated) =
      relativeHammingDist f (balancedFKNProjection i negated) := by
  rw [← uniformProbability_ne_eq_relativeHammingDist,
    ← uniformProbability_ne_eq_relativeHammingDist]
  unfold uniformProbability
  rw [expect_fin_cons]
  have hplus :
      (𝔼 x : {−1,1}^[n],
        if balancedFKNLift f (Fin.cons 1 x) ≠
            signedDictator i negated (Fin.cons 1 x)
          then (1 : ℝ) else 0) =
        𝔼 x : {−1,1}^[n],
          if f x ≠ balancedFKNProjection i negated x
            then (1 : ℝ) else 0 := by
    apply Finset.expect_congr rfl
    intro x _
    simp [balancedFKNProjection]
  have hminus :
      (𝔼 x : {−1,1}^[n],
        if balancedFKNLift f (Fin.cons (-1) x) ≠
            signedDictator i negated (Fin.cons (-1) x)
          then (1 : ℝ) else 0) =
        𝔼 x : {−1,1}^[n],
          if f x ≠ balancedFKNProjection i negated x
            then (1 : ℝ) else 0 := by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    rw [Equiv.neg_apply, balancedFKNLift_fin_cons_neg_one,
      signedDictator_fin_cons_neg_one]
    simp [balancedFKNProjection]
  rw [hplus, hminus]
  ring

/-- Exercise 2.49: applying FKN to the balanced lift transfers its unchanged
`1601 · δ` closeness bound to a one-junta for the original function. -/
theorem exists_isKJunta_one_relativeHammingDist_le_of_fourierWeightAtMost_one
    (f : BooleanFunction n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : 1 - δ ≤ fourierWeightAtMost 1 f.toReal) :
    ∃ g : BooleanFunction n,
      IsKJunta g 1 ∧ relativeHammingDist f g ≤ 1601 * δ := by
  have hweightLift :
      1 - δ ≤ fourierWeightAtLevel 1 (balancedFKNLift f).toReal := by
    rw [fourierWeightAtLevel_one_balancedFKNLift]
    exact hweight
  obtain ⟨i, negated, hdist⟩ :=
    fkn (balancedFKNLift f) δ hδ₀ hδ hweightLift
  refine ⟨balancedFKNProjection i negated,
    balancedFKNProjection_isKJunta_one i negated, ?_⟩
  rw [← relativeHammingDist_balancedFKNLift_signedDictator]
  exact hdist

/-! ## Numerical details for the improved FKN bound -/

/-- The second-order error term in O'Donnell's improved FKN argument. -/
noncomputable def fknImprovementEta (C δ : ℝ) : ℝ :=
  16 * C ^ 2 * δ ^ 2 *
    max (Real.logb 2 (1 / (C * δ))) 1

private theorem twentyFiveDivEight_lt_logb_two_nine :
    (25 : ℝ) / 8 < Real.logb 2 9 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNine : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.logb]
  apply (lt_div_iff₀ hlogTwo).2
  rw [hlogNine]
  nlinarith [Real.log_three_gt_d9, Real.log_two_lt_d9]

private theorem logb_two_eight :
    Real.logb 2 8 = 3 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

private theorem logb_two_four :
    Real.logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

private theorem mul_logb_two_inv_lt_one_third
    {x : ℝ} (hx : 0 < x) (hx_le : x ≤ 1 / 10) :
    x * Real.logb 2 (1 / x) < 1 / 3 := by
  have hten_le_inv : (10 : ℝ) ≤ 1 / x := by
    rw [le_div_iff₀ hx]
    nlinarith
  have hexp_le_ten : Real.exp 1 ≤ (10 : ℝ) :=
    (Real.exp_one_lt_three.trans (by norm_num)).le
  have hratio :
      Real.log (1 / x) / (1 / x) ≤ Real.log 10 / 10 :=
    Real.log_div_self_antitoneOn
      hexp_le_ten (hexp_le_ten.trans hten_le_inv) hten_le_inv
  have hratio_eq :
      Real.log (1 / x) / (1 / x) = x * Real.log (1 / x) := by
    field_simp
  have hlog_ratio : Real.log 10 / 10 < Real.log 2 / 3 := by
    rw [Real.log_ten_eq]
    nlinarith [Real.log_five_lt_d9, Real.log_two_gt_d9]
  have hnatural : x * Real.log (1 / x) < Real.log 2 / 3 := by
    rw [← hratio_eq]
    exact hratio.trans_lt hlog_ratio
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb]
  calc
    x * (Real.log (1 / x) / Real.log 2) =
        (x * Real.log (1 / x)) / Real.log 2 := by ring
    _ < 1 / 3 := (div_lt_iff₀ hlogTwo).2 (by
      nlinarith)

/-- O'Donnell, Exercise 5.38(a): outside the small-error regime, the proposed
degree-one lower bound is already negative. -/
theorem exercise5_38a
    {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hlarge : 1 / (10 * C) < δ) :
    1 - δ / 2 - 2 * fknImprovementEta C δ < 0 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let x := C * δ
  have hx : 0 < x := mul_pos hCpos hδ
  have hx_large : (1 : ℝ) / 10 < x := by
    have hden : 0 < 10 * C := mul_pos (by norm_num) hCpos
    have := (div_lt_iff₀ hden).1 hlarge
    dsimp [x]
    nlinarith
  let L := Real.logb 2 (1 / x)
  let M := max L 1
  have hM_one : 1 ≤ M := le_max_right _ _
  have hmain : 1 < 32 * x ^ 2 * M := by
    by_cases hx_ninth : x ≤ 1 / 9
    · have hnine_le_inv : (9 : ℝ) ≤ 1 / x := by
        rw [le_div_iff₀ hx]
        nlinarith
      have hlog : Real.logb 2 9 ≤ L := by
        dsimp [L]
        exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 9) hnine_le_inv
      have hM : (25 : ℝ) / 8 < M :=
        twentyFiveDivEight_lt_logb_two_nine.trans_le
          (hlog.trans (le_max_left _ _))
      have hxsq : (1 : ℝ) / 100 < x ^ 2 := by nlinarith [sq_nonneg x]
      have hfirst : (1 : ℝ) / 100 * M < x ^ 2 * M :=
        mul_lt_mul_of_pos_right hxsq (by positivity)
      have hsecond : (25 : ℝ) / 800 < (1 : ℝ) / 100 * M := by
        nlinarith
      nlinarith
    · have hx_ninth' : 1 / 9 < x := lt_of_not_ge hx_ninth
      by_cases hx_eighth : x ≤ 1 / 8
      · have height_le_inv : (8 : ℝ) ≤ 1 / x := by
          rw [le_div_iff₀ hx]
          nlinarith
        have hlog : (3 : ℝ) ≤ L := by
          rw [← logb_two_eight]
          dsimp [L]
          exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            (by norm_num : (0 : ℝ) < 8) height_le_inv
        have hM : (3 : ℝ) ≤ M := hlog.trans (le_max_left _ _)
        have hxsq : (1 : ℝ) / 81 < x ^ 2 := by nlinarith [sq_nonneg x]
        have hfirst : (1 : ℝ) / 81 * M < x ^ 2 * M :=
          mul_lt_mul_of_pos_right hxsq (by positivity)
        have hsecond : (1 : ℝ) / 27 ≤ (1 : ℝ) / 81 * M := by
          nlinarith
        nlinarith
      · have hx_eighth' : 1 / 8 < x := lt_of_not_ge hx_eighth
        by_cases hx_quarter : x ≤ 1 / 4
        · have hfour_le_inv : (4 : ℝ) ≤ 1 / x := by
            rw [le_div_iff₀ hx]
            nlinarith
          have hlog : (2 : ℝ) ≤ L := by
            rw [← logb_two_four]
            dsimp [L]
            exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
              (by norm_num : (0 : ℝ) < 4) hfour_le_inv
          have hM : (2 : ℝ) ≤ M := hlog.trans (le_max_left _ _)
          have hxsq : (1 : ℝ) / 64 < x ^ 2 := by nlinarith [sq_nonneg x]
          have hfirst : (1 : ℝ) / 64 * M < x ^ 2 * M :=
            mul_lt_mul_of_pos_right hxsq (by positivity)
          have hsecond : (1 : ℝ) / 32 ≤ (1 : ℝ) / 64 * M := by
            nlinarith
          nlinarith
        · have hx_quarter' : 1 / 4 < x := lt_of_not_ge hx_quarter
          have hxsq : (1 : ℝ) / 16 < x ^ 2 := by nlinarith [sq_nonneg x]
          have hfirst : (1 : ℝ) / 16 < x ^ 2 * M := by
            calc
              (1 : ℝ) / 16 < x ^ 2 := hxsq
              _ ≤ x ^ 2 * M := by
                nlinarith [sq_nonneg x]
          nlinarith
  dsimp [fknImprovementEta, x, L, M] at hmain ⊢
  nlinarith [hδ]

/-- O'Donnell, Exercise 5.38(b): the numerical square comparison in the
small-error regime. -/
theorem exercise5_38b
    {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (10 * C)) :
    1 - δ - 16 * C ^ 2 * δ ^ 2 * Real.logb 2 (1 / (C * δ)) ≥
      (1 - δ / 2 - 2 * fknImprovementEta C δ) ^ 2 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let x := C * δ
  let L := Real.logb 2 (1 / x)
  let η := 16 * x ^ 2 * L
  have hx : 0 < x := mul_pos hCpos hδ
  have hx_le : x ≤ (1 : ℝ) / 10 := by
    have hden : 0 < 10 * C := mul_pos (by norm_num) hCpos
    have := (le_div_iff₀ hden).1 hsmall
    dsimp [x]
    nlinarith
  have hδ_le_x : δ ≤ x := by
    dsimp [x]
    nlinarith
  have hδ_le : δ ≤ (1 : ℝ) / 10 := hδ_le_x.trans hx_le
  have htwo_le_inv : (2 : ℝ) ≤ 1 / x := by
    rw [le_div_iff₀ hx]
    nlinarith
  have hL_one : 1 ≤ L := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    dsimp [L]
    exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) htwo_le_inv
  have hmax : max L 1 = L := max_eq_left hL_one
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    positivity
  have hδsq : δ ^ 2 / 4 ≤ η / 64 := by
    dsimp [η, x]
    have hC_sq : 1 ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
    have hbase : δ ^ 2 ≤ C ^ 2 * δ ^ 2 := by
      nlinarith [sq_nonneg δ]
    have hlogbase : C ^ 2 * δ ^ 2 ≤ C ^ 2 * δ ^ 2 * L := by
      nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg δ)]
    nlinarith
  have hη_upper : η < (16 : ℝ) / 25 := by
    have hxL := mul_logb_two_inv_lt_one_third hx hx_le
    dsimp [η, L]
    have hrewrite :
        16 * x ^ 2 * Real.logb 2 (1 / x) =
          16 * x * (x * Real.logb 2 (1 / x)) := by ring
    rw [hrewrite]
    have hmul :
        16 * x * (x * Real.logb 2 (1 / x)) <
          16 * x * (1 / 3) := by
      exact mul_lt_mul_of_pos_left hxL (by positivity)
    nlinarith
  have hδ_eta : 2 * δ * η ≤ η / 5 := by
    nlinarith
  have hηsq : 4 * η ^ 2 ≤ (64 : ℝ) / 25 * η := by
    nlinarith
  have hnumeric :
      δ ^ 2 / 4 + 2 * δ * η + 4 * η ^ 2 ≤ 3 * η := by
    nlinarith
  dsimp [fknImprovementEta, x, L, η] at hmax hnumeric ⊢
  rw [hmax]
  nlinarith

/-- Exercise 5.38: a nonnegative quantity with square at least the numerical
left-hand side is at least the improved FKN target. -/
theorem exercise5_38_nonnegative_lower_bound
    {C δ z : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (10 * C)) (hz : 0 ≤ z)
    (hzsq :
      1 - δ - 16 * C ^ 2 * δ ^ 2 * Real.logb 2 (1 / (C * δ)) ≤ z ^ 2) :
    1 - δ / 2 - 2 * fknImprovementEta C δ ≤ z := by
  by_cases htarget : 1 - δ / 2 - 2 * fknImprovementEta C δ ≤ 0
  · exact htarget.trans hz
  · have htarget_nonneg :
        0 ≤ 1 - δ / 2 - 2 * fknImprovementEta C δ :=
      (not_le.mp htarget).le
    have hsquare :=
      (exercise5_38b hC hδ hsmall).trans hzsq
    exact (sq_le_sq₀ htarget_nonneg hz).mp hsquare

/-- Exercise 5.38: square-root form of the numerical lower bound used in
Theorem 5.33. -/
theorem exercise5_38_sqrt_lower_bound
    {C δ A : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (10 * C)) (hA : 0 ≤ A)
    (hbound :
      1 - δ - 16 * C ^ 2 * δ ^ 2 * Real.logb 2 (1 / (C * δ)) ≤ A) :
    1 - δ / 2 - 2 * fknImprovementEta C δ ≤ Real.sqrt A := by
  apply exercise5_38_nonnegative_lower_bound hC hδ hsmall (Real.sqrt_nonneg A)
  rw [Real.sq_sqrt hA]
  exact hbound

end FABL
