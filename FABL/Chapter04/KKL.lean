/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.FKN
public import FABL.Chapter03.LowDegreeSpectralConcentration
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Kahn--Kalai--Linial theorem

This module proves the KKL theorem stated after Proposition 4.13. The proof follows the
Edge-KKL argument deferred by the book to Section 9.6: the spectral Jensen lower bound for total
stable influence is combined with the `(2,4)` hypercontractive estimate.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

/-! ## Hypercontractive estimate for Edge-KKL -/


variable {n : ℕ}

private theorem fourier_ext {f g : {−1,1}^[n] → ℝ}
    (h : ∀ S, fourierCoeff f S = fourierCoeff g S) : f = g := by
  funext x
  rw [fourier_expansion f x, fourier_expansion g x]
  apply Finset.sum_congr rfl
  intro S _
  rw [h S]

/-- The noise operator multiplies the Fourier coefficient at `S` by `ρ^|S|`. -/
theorem fourierCoeff_noiseOperator (rho : ℝ) (f : {−1,1}^[n] → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff (noiseOperator rho f) S =
      rho ^ S.card * fourierCoeff f S := by
  rw [fourierCoeff]
  calc
    (𝔼 x, noiseOperator rho f x * monomial S x) =
        𝔼 x, (∑ T, rho ^ T.card * fourierCoeff f T * monomial T x) * monomial S x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [noiseOperator_fourier_expansion]
    _ = 𝔼 x, ∑ T,
        (rho ^ T.card * fourierCoeff f T) * (monomial T x * monomial S x) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = ∑ T, (rho ^ T.card * fourierCoeff f T) *
        (𝔼 x, monomial T x * monomial S x) := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.mul_expect]
    _ = rho ^ S.card * fourierCoeff f S := by
      simp_rw [expect_monomial_mul]
      simp

/-- Noise operators form a multiplicative semigroup. -/
theorem noiseOperator_comp (rho sigma : ℝ) (f : {−1,1}^[n] → ℝ) :
    noiseOperator rho (noiseOperator sigma f) = noiseOperator (rho * sigma) f := by
  apply fourier_ext
  intro S
  simp only [fourierCoeff_noiseOperator]
  rw [mul_pow]
  ring

/-- The noise operator is self-adjoint for the uniform inner product. -/
theorem uniformInner_noiseOperator_left (rho : ℝ)
    (f g : {−1,1}^[n] → ℝ) :
    ⟪noiseOperator rho f, g⟫ᵤ = ⟪f, noiseOperator rho g⟫ᵤ := by
  rw [plancherel, plancherel]
  simp_rw [fourierCoeff_noiseOperator]
  apply Finset.sum_congr rfl
  intro S _
  ring

private noncomputable def firstCoordinateOddPart
    (f : {−1,1}^[n + 1] → ℝ) : {−1,1}^[n] → ℝ :=
  fun x ↦ (firstCoordinateSlice f 1 x - firstCoordinateSlice f (-1) x) / 2

private noncomputable def firstCoordinateEvenPart
    (f : {−1,1}^[n + 1] → ℝ) : {−1,1}^[n] → ℝ :=
  fun x ↦ (firstCoordinateSlice f 1 x + firstCoordinateSlice f (-1) x) / 2

private theorem fourierCoeff_firstCoordinateOddPart
    (f : {−1,1}^[n + 1] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (firstCoordinateOddPart f) S =
      fourierCoeff f (insert 0 (tailFrequency S)) := by
  rw [fourierCoeff_insert_zero_tailFrequency]
  unfold firstCoordinateOddPart fourierCoeff
  rw [show (fun x ↦
      ((firstCoordinateSlice f 1 x - firstCoordinateSlice f (-1) x) / 2) * monomial S x) =
      fun x ↦
        (firstCoordinateSlice f 1 x * monomial S x -
          firstCoordinateSlice f (-1) x * monomial S x) / 2 by
    funext x
    ring]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]

private theorem fourierCoeff_firstCoordinateEvenPart
    (f : {−1,1}^[n + 1] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (firstCoordinateEvenPart f) S =
      fourierCoeff f (tailFrequency S) := by
  rw [fourierCoeff_tailFrequency]
  unfold firstCoordinateEvenPart fourierCoeff
  rw [show (fun x ↦
      ((firstCoordinateSlice f 1 x + firstCoordinateSlice f (-1) x) / 2) * monomial S x) =
      fun x ↦
        (firstCoordinateSlice f 1 x * monomial S x +
          firstCoordinateSlice f (-1) x * monomial S x) / 2 by
    funext x
    ring]
  rw [← Finset.expect_div, Finset.expect_add_distrib]

private theorem fourierCoeff_slice_eq_tail_add_sign_mul_insert
    (f : {−1,1}^[n + 1] → ℝ) (b : Sign) (S : Finset (Fin n)) :
    fourierCoeff (firstCoordinateSlice f b) S =
      fourierCoeff f (tailFrequency S) +
        signValue b * fourierCoeff f (insert 0 (tailFrequency S)) := by
  have hmean := fourierCoeff_tailFrequency f S
  have hdiff := fourierCoeff_insert_zero_tailFrequency f S
  rcases Int.units_eq_one_or b with rfl | rfl
  · simp only [signValue_one, one_mul]
    linarith
  · simp only [signValue_neg_one, neg_one_mul]
    linarith

private theorem noiseOperator_firstCoordinateSlice
    (rho : ℝ) (f : {−1,1}^[n + 1] → ℝ) (b : Sign) :
    firstCoordinateSlice (noiseOperator rho f) b =
      fun x ↦
        signValue b * rho * noiseOperator rho (firstCoordinateOddPart f) x +
          noiseOperator rho (firstCoordinateEvenPart f) x := by
  apply fourier_ext
  intro S
  rw [fourierCoeff_slice_eq_tail_add_sign_mul_insert,
    fourierCoeff_noiseOperator, fourierCoeff_noiseOperator,
    card_tailFrequency, Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency]
  unfold fourierCoeff
  rw [show (fun x ↦
      (signValue b * rho * noiseOperator rho (firstCoordinateOddPart f) x +
        noiseOperator rho (firstCoordinateEvenPart f) x) * monomial S x) =
      fun x ↦
        signValue b * rho *
            (noiseOperator rho (firstCoordinateOddPart f) x * monomial S x) +
          noiseOperator rho (firstCoordinateEvenPart f) x * monomial S x by
    funext x
    ring]
  rw [Finset.expect_add_distrib, ← Finset.mul_expect,
    ]
  change rho ^ S.card * fourierCoeff f (tailFrequency S) +
      signValue b * (rho ^ (S.card + 1) *
        fourierCoeff f (insert 0 (tailFrequency S))) =
    signValue b * rho *
        fourierCoeff (noiseOperator rho (firstCoordinateOddPart f)) S +
      fourierCoeff (noiseOperator rho (firstCoordinateEvenPart f)) S
  rw [fourierCoeff_noiseOperator, fourierCoeff_noiseOperator,
    fourierCoeff_firstCoordinateOddPart, fourierCoeff_firstCoordinateEvenPart,
    pow_succ]
  ring

private noncomputable def kklNoiseRoot : ℝ := Real.sqrt (1 / 3 : ℝ)

private theorem kklNoiseRoot_sq : kklNoiseRoot ^ 2 = (1 / 3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

private theorem expect_sq_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, f x ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem expect_fourth_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, f x ^ 4 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem expect_sq_mul_sq_nonneg (d e : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, d x ^ 2 * e x ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem fourthMoment_le_sq_of_slice
    (d e : {−1,1}^[n] → ℝ) (f : {−1,1}^[n + 1] → ℝ)
    (hf : ∀ b x, f (Fin.cons b x) = signValue b * d x + e x)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : (𝔼 x, d x ^ 4) ≤ A ^ 2 / 9)
    (he : (𝔼 x, e x ^ 4) ≤ B ^ 2) :
    (𝔼 x, f x ^ 4) ≤ (A + B) ^ 2 := by
  let D₄ := 𝔼 x, d x ^ 4
  let E₄ := 𝔼 x, e x ^ 4
  let C := 𝔼 x, d x ^ 2 * e x ^ 2
  have hD₄ : 0 ≤ D₄ := expect_fourth_nonneg d
  have hE₄ : 0 ≤ E₄ := expect_fourth_nonneg e
  have hC : 0 ≤ C := expect_sq_mul_sq_nonneg d e
  have hCSq : C ^ 2 ≤ D₄ * E₄ := expect_sq_mul_sq_sq_le d e
  have hProduct : D₄ * E₄ ≤ (A * B / 3) ^ 2 := by
    calc
      D₄ * E₄ ≤ (A ^ 2 / 9) * B ^ 2 :=
        mul_le_mul hd he hE₄ (div_nonneg (sq_nonneg A) (by norm_num))
      _ = (A * B / 3) ^ 2 := by ring
  have hCross : C ≤ A * B / 3 :=
    (sq_le_sq₀ hC (div_nonneg (mul_nonneg hA hB) (by norm_num))).mp
      (hCSq.trans hProduct)
  rw [expect_fourth_eq_expect_odd_even d e f hf]
  change D₄ + 6 * C + E₄ ≤ (A + B) ^ 2
  change D₄ ≤ A ^ 2 / 9 at hd
  change E₄ ≤ B ^ 2 at he
  nlinarith [sq_nonneg A]

private theorem expect_noiseOperator_kklNoiseRoot_fourth_le_sq_expect_sq
    (f : {−1,1}^[n] → ℝ) :
    (𝔼 x, noiseOperator kklNoiseRoot f x ^ 4) ≤ (𝔼 x, f x ^ 2) ^ 2 := by
  induction n with
  | zero =>
      have hnoise : noiseOperator kklNoiseRoot f = f := by
        apply fourier_ext
        intro S
        rw [fourierCoeff_noiseOperator]
        have hS : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i
          exact Fin.elim0 i
        subst S
        simp
      rw [hnoise]
      let x₀ : {−1,1}^[0] := fun i ↦ Fin.elim0 i
      have hf : f = fun _ ↦ f x₀ := by
        funext x
        rw [Subsingleton.elim x x₀]
      rw [hf]
      simp
      ring_nf
      exact le_rfl
  | succ n ih =>
      let d := firstCoordinateOddPart f
      let e := firstCoordinateEvenPart f
      let Td := noiseOperator kklNoiseRoot d
      let Te := noiseOperator kklNoiseRoot e
      have hslice (b : Sign) (x : {−1,1}^[n]) :
          noiseOperator kklNoiseRoot f (Fin.cons b x) =
            signValue b * (kklNoiseRoot * Td x) + Te x := by
        have h := congrFun (noiseOperator_firstCoordinateSlice kklNoiseRoot f b) x
        simpa [firstCoordinateSlice, d, e, Td, Te, mul_assoc] using h
      have hA : 0 ≤ 𝔼 x, d x ^ 2 := expect_sq_nonneg d
      have hB : 0 ≤ 𝔼 x, e x ^ 2 := expect_sq_nonneg e
      have hd : (𝔼 x, (kklNoiseRoot * Td x) ^ 4) ≤
          (𝔼 x, d x ^ 2) ^ 2 / 9 := by
        calc
          (𝔼 x, (kklNoiseRoot * Td x) ^ 4) =
              𝔼 x, kklNoiseRoot ^ 4 * Td x ^ 4 := by
            apply Finset.expect_congr rfl
            intro x _
            ring
          _ = kklNoiseRoot ^ 4 * (𝔼 x, Td x ^ 4) :=
            (Finset.mul_expect Finset.univ (fun x ↦ Td x ^ 4) (kklNoiseRoot ^ 4)).symm
          _ ≤ kklNoiseRoot ^ 4 * (𝔼 x, d x ^ 2) ^ 2 := by
            gcongr
            exact ih d
          _ = (𝔼 x, d x ^ 2) ^ 2 / 9 := by
            rw [show kklNoiseRoot ^ 4 = (kklNoiseRoot ^ 2) ^ 2 by ring,
              kklNoiseRoot_sq]
            ring
      have he : (𝔼 x, Te x ^ 4) ≤ (𝔼 x, e x ^ 2) ^ 2 := ih e
      apply (fourthMoment_le_sq_of_slice
        (fun x ↦ kklNoiseRoot * Td x) Te (noiseOperator kklNoiseRoot f)
        hslice (𝔼 x, d x ^ 2) (𝔼 x, e x ^ 2) hA hB hd he).trans_eq
      rw [expect_sq_eq_expect_odd_even d e f]
      intro b x
      dsimp [d, e, firstCoordinateOddPart, firstCoordinateEvenPart]
      rcases Int.units_eq_one_or b with rfl | rfl <;> simp <;> ring

private theorem expect_mul_fourth_le_expect_sq_cubed_mul_expect_fourth
    (g h : {−1,1}^[n] → ℝ)
    (hg3 : ∀ x, g x ^ 3 = g x) (hg4 : ∀ x, g x ^ 4 = g x ^ 2) :
    (𝔼 x, g x * h x) ^ 4 ≤
      (𝔼 x, g x ^ 2) ^ 3 * (𝔼 x, h x ^ 4) := by
  let alpha := 𝔼 x, g x ^ 2
  let B := 𝔼 x, g x ^ 2 * h x ^ 2
  let H₄ := 𝔼 x, h x ^ 4
  have halpha : 0 ≤ alpha := expect_sq_nonneg g
  have hB : 0 ≤ B := by
    dsimp [B]
    rw [Fintype.expect_eq_sum_div_card]
    positivity
  have hH₄ : 0 ≤ H₄ := expect_fourth_nonneg h
  have hfirst := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ({−1,1}^[n])) (fun x ↦ g x ^ 2) (fun x ↦ g x * h x)
  have hfirstB : (𝔼 x, g x * h x) ^ 2 ≤ alpha * B := by
    calc
      (𝔼 x, g x * h x) ^ 2 =
          (𝔼 x, g x ^ 2 * (g x * h x)) ^ 2 := by
        congr 1
        apply Finset.expect_congr rfl
        intro x _
        rw [show g x ^ 2 * (g x * h x) = g x ^ 3 * h x by ring, hg3]
      _ ≤ (𝔼 x, (g x ^ 2) ^ 2) * 𝔼 x, (g x * h x) ^ 2 := hfirst
      _ = alpha * B := by
        congr 1
        · apply Finset.expect_congr rfl
          intro x _
          calc
            (g x ^ 2) ^ 2 = g x ^ 4 := by ring
            _ = g x ^ 2 := hg4 x
        · apply Finset.expect_congr rfl
          intro x _
          ring
  have hsecond := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ({−1,1}^[n])) g (fun x ↦ g x * h x ^ 2)
  have hrestricted : (𝔼 x, g x ^ 2 * h x ^ 4) ≤ H₄ := by
    apply Finset.expect_le_expect
    intro x _
    have heq : (g x ^ 2) ^ 2 = g x ^ 2 := by
      calc
        (g x ^ 2) ^ 2 = g x ^ 4 := by ring
        _ = g x ^ 2 := hg4 x
    have hg2 : g x ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (g x ^ 2 - 1)]
    exact mul_le_of_le_one_left (by positivity) hg2
  have hsecond' : B ^ 2 ≤ alpha * H₄ := by
    calc
      B ^ 2 = (𝔼 x, g x * (g x * h x ^ 2)) ^ 2 := by
        congr 1
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ ≤ (𝔼 x, g x ^ 2) * 𝔼 x, (g x * h x ^ 2) ^ 2 := hsecond
      _ = alpha * (𝔼 x, g x ^ 2 * h x ^ 4) := by
        have hpoint :
            (fun x ↦ (g x * h x ^ 2) ^ 2) =
              (fun x ↦ g x ^ 2 * h x ^ 4) := by
          funext x
          ring
        change (𝔼 x, g x ^ 2) * (𝔼 x, (g x * h x ^ 2) ^ 2) =
          (𝔼 x, g x ^ 2) * (𝔼 x, g x ^ 2 * h x ^ 4)
        rw [hpoint]
      _ ≤ alpha * H₄ := mul_le_mul_of_nonneg_left hrestricted halpha
  calc
    (𝔼 x, g x * h x) ^ 4 = ((𝔼 x, g x * h x) ^ 2) ^ 2 := by ring
    _ ≤ (alpha * B) ^ 2 := by gcongr
    _ = alpha ^ 2 * B ^ 2 := by ring
    _ ≤ alpha ^ 2 * (alpha * H₄) := by gcongr
    _ = alpha ^ 3 * H₄ := by ring

private theorem discreteDerivative_toReal_cube (f : BooleanFunction n) (i : Fin n)
    (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x ^ 3 = discreteDerivative i f.toReal x := by
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

private theorem discreteDerivative_toReal_fourth (f : BooleanFunction n) (i : Fin n)
    (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x ^ 4 = discreteDerivative i f.toReal x ^ 2 := by
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

/-- Corollary 9.12 at `ρ = 1 / 3`, specialized to a Boolean discrete derivative. -/
theorem stableInfluence_one_third_sq_le_booleanInfluence_cube
    (f : BooleanFunction n) (i : Fin n) :
    stableInfluence (1 / 3 : ℝ) f.toReal i ^ 2 ≤ booleanInfluence f i ^ 3 := by
  let g := discreteDerivative i f.toReal
  let u := noiseOperator kklNoiseRoot g
  let h := noiseOperator kklNoiseRoot u
  let A := stableInfluence (1 / 3 : ℝ) f.toReal i
  let alpha := influence f.toReal i
  have hthird : (1 / 3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hthird' : (1 / 3 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hrootProduct : kklNoiseRoot * kklNoiseRoot = (1 / 3 : ℝ) := by
    nlinarith [kklNoiseRoot_sq]
  have hsemigroup : h = noiseOperator (1 / 3 : ℝ) g := by
    dsimp [h, u]
    rw [noiseOperator_comp, hrootProduct]
  have hAinner : A = ⟪g, noiseOperator (1 / 3 : ℝ) g⟫ᵤ := by
    dsimp [A, g]
    rw [stableInfluence_eq_noiseStability_discreteDerivative (1 / 3 : ℝ) hthird,
      noiseStability_eq_uniformInner_noiseOperator (1 / 3 : ℝ) hthird']
  have hAexpect : A = 𝔼 x, g x * h x := by
    rw [hAinner, ← hsemigroup]
    simp only [uniformInner, RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    apply Finset.expect_congr rfl
    intro x _
    ring
  have huSq : (𝔼 x, u x ^ 2) = A := by
    calc
      (𝔼 x, u x ^ 2) = ⟪u, u⟫ᵤ := by
        simp only [uniformInner, RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
          starRingEnd_apply, star_trivial]
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = ⟪g, h⟫ᵤ := by
        dsimp [u, h]
        exact uniformInner_noiseOperator_left kklNoiseRoot g
          (noiseOperator kklNoiseRoot g)
      _ = ⟪g, noiseOperator (1 / 3 : ℝ) g⟫ᵤ := by rw [← hsemigroup]
      _ = A := hAinner.symm
  have hhFourth : (𝔼 x, h x ^ 4) ≤ A ^ 2 := by
    calc
      (𝔼 x, h x ^ 4) ≤ (𝔼 x, u x ^ 2) ^ 2 := by
        exact expect_noiseOperator_kklNoiseRoot_fourth_le_sq_expect_sq u
      _ = A ^ 2 := by rw [huSq]
  have hA : 0 ≤ A := stableInfluence_nonneg (1 / 3 : ℝ) hthird f.toReal i
  have halpha : 0 ≤ alpha := influence_nonneg f.toReal i
  have hfourth : A ^ 4 ≤ alpha ^ 3 * A ^ 2 := by
    calc
      A ^ 4 = (𝔼 x, g x * h x) ^ 4 := by rw [hAexpect]
      _ ≤ (𝔼 x, g x ^ 2) ^ 3 * (𝔼 x, h x ^ 4) := by
        exact expect_mul_fourth_le_expect_sq_cubed_mul_expect_fourth g h
          (discreteDerivative_toReal_cube f i)
          (discreteDerivative_toReal_fourth f i)
      _ = alpha ^ 3 * (𝔼 x, h x ^ 4) := by rfl
      _ ≤ alpha ^ 3 * A ^ 2 := by gcongr
  have hresult : A ^ 2 ≤ alpha ^ 3 := by
    by_cases hAzero : A = 0
    · simpa [hAzero] using pow_nonneg halpha 3
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      have hA2pos : 0 < A ^ 2 := sq_pos_of_pos hApos
      by_contra hnot
      have hlt : alpha ^ 3 < A ^ 2 := lt_of_not_ge hnot
      have hmul : alpha ^ 3 * A ^ 2 < A ^ 2 * A ^ 2 :=
        mul_lt_mul_of_pos_right hlt hA2pos
      nlinarith [hfourth, hmul]
  simpa [A, alpha, booleanInfluence_eq_influence_toReal] using hresult


variable {n : ℕ}

/-- O'Donnell, Definition 9.26: the largest coordinate influence, with value zero in dimension
zero. -/
noncomputable def maximumInfluence (f : BooleanFunction n) : ℝ :=
  ↑(Finset.univ.sup fun i : Fin n ↦
    (⟨booleanInfluence f i,
      booleanInfluence_eq_influence_toReal f i ▸ influence_nonneg f.toReal i⟩ : NNReal))

/-- Maximum influence is nonnegative. -/
theorem maximumInfluence_nonneg (f : BooleanFunction n) :
    0 ≤ maximumInfluence f := by
  unfold maximumInfluence
  exact NNReal.coe_nonneg _

/-- Every coordinate influence is bounded by the maximum influence. -/
theorem booleanInfluence_le_maximumInfluence (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence f i ≤ maximumInfluence f := by
  unfold maximumInfluence
  exact_mod_cast Finset.le_sup (f := fun j : Fin n ↦
    (⟨booleanInfluence f j,
      booleanInfluence_eq_influence_toReal f j ▸ influence_nonneg f.toReal j⟩ : NNReal))
    (Finset.mem_univ i)

/-- In every positive dimension, some coordinate attains the maximum influence. -/
theorem exists_booleanInfluence_eq_maximumInfluence (f : BooleanFunction n) (hn : 0 < n) :
    ∃ i : Fin n, booleanInfluence f i = maximumInfluence f := by
  let influenceNN := fun i : Fin n ↦
    (⟨booleanInfluence f i,
      booleanInfluence_eq_influence_toReal f i ▸ influence_nonneg f.toReal i⟩ : NNReal)
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rcases Finset.exists_mem_eq_sup Finset.univ huniv influenceNN with ⟨i, _, hi⟩
  refine ⟨i, ?_⟩
  unfold maximumInfluence
  have hcast := congrArg (fun r : NNReal ↦ (r : ℝ)) hi.symm
  dsimp [influenceNN] at hcast
  exact hcast

/-- Total influence is at most dimension times maximum influence. -/
theorem totalInfluence_le_natCast_mul_maximumInfluence (f : BooleanFunction n) :
    totalInfluence f.toReal ≤ (n : ℝ) * maximumInfluence f := by
  rw [totalInfluence]
  calc
    (∑ i : Fin n, influence f.toReal i) = ∑ i : Fin n, booleanInfluence f i := by
      simp_rw [booleanInfluence_eq_influence_toReal]
    _ ≤ ∑ _i : Fin n, maximumInfluence f := by
      exact Finset.sum_le_sum fun i _ ↦ booleanInfluence_le_maximumInfluence f i
    _ = (n : ℝ) * maximumInfluence f := by simp

private theorem stableInfluence_one_third_le_sqrt_max_mul_influence
    (f : BooleanFunction n) (i : Fin n) :
    stableInfluence (1 / 3 : ℝ) f.toReal i ≤
      Real.sqrt (maximumInfluence f) * influence f.toReal i := by
  have hthird : (1 / 3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hstable : 0 ≤ stableInfluence (1 / 3 : ℝ) f.toReal i :=
    stableInfluence_nonneg (1 / 3 : ℝ) hthird f.toReal i
  have hinf : 0 ≤ influence f.toReal i := influence_nonneg f.toReal i
  have hmax : 0 ≤ maximumInfluence f := maximumInfluence_nonneg f
  have hcoord : influence f.toReal i ≤ maximumInfluence f := by
    rw [← booleanInfluence_eq_influence_toReal]
    exact booleanInfluence_le_maximumInfluence f i
  apply (sq_le_sq₀ hstable (mul_nonneg (Real.sqrt_nonneg _) hinf)).mp
  calc
    stableInfluence (1 / 3 : ℝ) f.toReal i ^ 2 ≤ booleanInfluence f i ^ 3 :=
      stableInfluence_one_third_sq_le_booleanInfluence_cube f i
    _ = influence f.toReal i ^ 3 := by rw [booleanInfluence_eq_influence_toReal]
    _ ≤ maximumInfluence f * influence f.toReal i ^ 2 := by
      nlinarith [sq_nonneg (influence f.toReal i)]
    _ = (Real.sqrt (maximumInfluence f) * influence f.toReal i) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hmax]

/-- The upper half of the Edge-KKL chain at correlation `1 / 3`. -/
theorem totalStableInfluence_one_third_sq_le_maximum_mul_totalInfluence_sq
    (f : BooleanFunction n) :
    totalStableInfluence (1 / 3 : ℝ) f.toReal ^ 2 ≤
      maximumInfluence f * totalInfluence f.toReal ^ 2 := by
  have hsum : totalStableInfluence (1 / 3 : ℝ) f.toReal ≤
      Real.sqrt (maximumInfluence f) * totalInfluence f.toReal := by
    rw [totalStableInfluence, totalInfluence, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      stableInfluence_one_third_le_sqrt_max_mul_influence f i
  have hthird : (1 / 3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hleft : 0 ≤ totalStableInfluence (1 / 3 : ℝ) f.toReal :=
    totalStableInfluence_nonneg (1 / 3 : ℝ) hthird f.toReal
  have hright : 0 ≤ Real.sqrt (maximumInfluence f) * totalInfluence f.toReal :=
    mul_nonneg (Real.sqrt_nonneg _) (totalInfluence_nonneg f.toReal)
  calc
    totalStableInfluence (1 / 3 : ℝ) f.toReal ^ 2 ≤
        (Real.sqrt (maximumInfluence f) * totalInfluence f.toReal) ^ 2 :=
      (sq_le_sq₀ hleft hright).mpr hsum
    _ = maximumInfluence f * totalInfluence f.toReal ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (maximumInfluence_nonneg f)]

/-- The spectral Jensen lower half of the Edge-KKL chain. -/
theorem three_mul_variance_mul_rpow_le_totalStableInfluence_one_third
    (f : BooleanFunction n) (hvar : 0 < variance f.toReal) :
    3 * variance f.toReal *
        Real.rpow (1 / 3 : ℝ) (totalInfluence f.toReal / variance f.toReal) ≤
      totalStableInfluence (1 / 3 : ℝ) f.toReal := by
  let V := variance f.toReal
  let I := totalInfluence f.toReal
  let frequencies := Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅
  let weight := fun S : Finset (Fin n) ↦ fourierCoeff f.toReal S ^ 2 / V
  have hV : 0 < V := hvar
  have hweight : ∀ S ∈ frequencies, 0 ≤ weight S := by
    intro S _
    exact div_nonneg (sq_nonneg _) hV.le
  have hweightSum : ∑ S ∈ frequencies, weight S = 1 := by
    calc
      (∑ S ∈ frequencies, weight S) =
          (∑ S ∈ frequencies, fourierCoeff f.toReal S ^ 2) / V := by
        simp only [weight, Finset.sum_div]
      _ = V / V := by
        rw [show (∑ S ∈ frequencies, fourierCoeff f.toReal S ^ 2) = V by
          simpa [frequencies, V] using (variance_eq_sum_sq_fourierCoeff f.toReal).2.symm]
      _ = 1 := div_self hV.ne'
  have hweightedCard :
      (∑ S ∈ frequencies, weight S * (S.card : ℝ)) = I / V := by
    calc
      (∑ S ∈ frequencies, weight S * (S.card : ℝ)) =
          (∑ S ∈ frequencies, (S.card : ℝ) * fourierCoeff f.toReal S ^ 2) / V := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro S _
        dsimp [weight]
        ring
      _ = (∑ S, (S.card : ℝ) * fourierCoeff f.toReal S ^ 2) / V := by
        congr 1
        rw [show frequencies = Finset.univ.filter
          (fun S : Finset (Fin n) ↦ S ≠ ∅) by rfl, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S = ∅
        · simp [hS]
        · simp [hS]
      _ = I / V := by rw [← totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  have hjensen :
      Real.rpow (1 / 3 : ℝ) (I / V) ≤
        ∑ S ∈ frequencies,
          weight S * Real.rpow (1 / 3 : ℝ) (S.card : ℝ) := by
    rw [← hweightedCard]
    convert
      (convexOn_rpow_left (by norm_num : (0 : ℝ) < 1 / 3)).map_sum_le
        hweight hweightSum (fun _ _ ↦ Set.mem_univ _) using 1 <;> try rfl
  rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]
  calc
    3 * variance f.toReal *
          Real.rpow (1 / 3 : ℝ) (totalInfluence f.toReal / variance f.toReal) =
        3 * V * Real.rpow (1 / 3 : ℝ) (I / V) := by rfl
    _ ≤ 3 * V * (∑ S ∈ frequencies,
          weight S * Real.rpow (1 / 3 : ℝ) (S.card : ℝ)) := by
      gcongr
    _ = ∑ S ∈ frequencies,
          3 * (1 / 3 : ℝ) ^ S.card * fourierCoeff f.toReal S ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      dsimp [weight]
      rw [Real.rpow_natCast]
      field_simp
    _ ≤ ∑ S ∈ frequencies,
          (S.card : ℝ) * (1 / 3 : ℝ) ^ (S.card - 1) *
            fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hSne : S ≠ ∅ := (Finset.mem_filter.mp hS).2
      have hcard : 1 ≤ S.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
      have hpow : (1 / 3 : ℝ) ^ S.card =
          (1 / 3 : ℝ) ^ (S.card - 1) * (1 / 3 : ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      have hpowNonneg : 0 ≤ (1 / 3 : ℝ) ^ (S.card - 1) := by positivity
      have hcardReal : (1 : ℝ) ≤ S.card := by exact_mod_cast hcard
      have htermNonneg :
          0 ≤ (1 / 3 : ℝ) ^ (S.card - 1) * fourierCoeff f.toReal S ^ 2 :=
        mul_nonneg hpowNonneg (sq_nonneg _)
      calc
        3 * ((1 / 3 : ℝ) ^ (S.card - 1) * (1 / 3)) *
              fourierCoeff f.toReal S ^ 2 =
            (1 / 3 : ℝ) ^ (S.card - 1) * fourierCoeff f.toReal S ^ 2 := by ring
        _ ≤ (S.card : ℝ) * (1 / 3 : ℝ) ^ (S.card - 1) *
              fourierCoeff f.toReal S ^ 2 := by nlinarith
    _ = ∑ S,
          (S.card : ℝ) * (1 / 3 : ℝ) ^ (S.card - 1) *
            fourierCoeff f.toReal S ^ 2 := by
      rw [show frequencies = Finset.univ.filter
        (fun S : Finset (Fin n) ↦ S ≠ ∅) by rfl, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S = ∅ <;> simp [hS]

/-- O'Donnell, Theorem 9.24 (Edge-KKL), in the book's `K = I[f] / Var[f]`
normalization. -/
theorem edgeKKL (f : BooleanFunction n) (hvar : 0 < variance f.toReal) :
    9 * Real.rpow 9 (-(totalInfluence f.toReal / variance f.toReal)) /
        (totalInfluence f.toReal / variance f.toReal) ^ 2 ≤
      maximumInfluence f := by
  let V := variance f.toReal
  let I := totalInfluence f.toReal
  let K := I / V
  let J := totalStableInfluence (1 / 3 : ℝ) f.toReal
  let M := maximumInfluence f
  have hV : 0 < V := hvar
  have hK : 1 ≤ K := by
    dsimp [K, I, V]
    exact (le_div_iff₀ hvar).2 (by
      simpa using variance_le_totalInfluence f.toReal)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hI : I = K * V := by
    dsimp [K]
    field_simp
  have hpowSq :
      ((1 / 3 : ℝ) ^ K) ^ 2 = (9 : ℝ) ^ (-K) := by
    calc
      ((1 / 3 : ℝ) ^ K) ^ 2 =
          (1 / 3 : ℝ) ^ K * (1 / 3 : ℝ) ^ K := by ring
      _ = ((1 / 3 : ℝ) * (1 / 3 : ℝ)) ^ K := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 3)
          (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      _ = (9⁻¹ : ℝ) ^ K := by norm_num
      _ = (9 : ℝ) ^ (-K) := (Real.rpow_neg_eq_inv_rpow 9 K).symm
  have hlower : 3 * V * Real.rpow (1 / 3 : ℝ) K ≤ J := by
    simpa [V, I, K, J] using
      three_mul_variance_mul_rpow_le_totalStableInfluence_one_third f hvar
  have hleftNonneg : 0 ≤ 3 * V * Real.rpow (1 / 3 : ℝ) K :=
    mul_nonneg (mul_nonneg (by norm_num) hV.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hthird : (1 / 3 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hJnonneg : 0 ≤ J := by
    exact totalStableInfluence_nonneg (1 / 3 : ℝ) hthird f.toReal
  have hsquared :
      (3 * V * Real.rpow (1 / 3 : ℝ) K) ^ 2 ≤ M * I ^ 2 := by
    exact ((sq_le_sq₀ hleftNonneg hJnonneg).mpr hlower).trans
      (totalStableInfluence_one_third_sq_le_maximum_mul_totalInfluence_sq f)
  have hnormalized : 9 * V ^ 2 * Real.rpow 9 (-K) ≤ M * K ^ 2 * V ^ 2 := by
    calc
      9 * V ^ 2 * Real.rpow 9 (-K) =
          (3 * V * Real.rpow (1 / 3 : ℝ) K) ^ 2 := by
        change 9 * V ^ 2 * (9 : ℝ) ^ (-K) =
          (3 * V * (1 / 3 : ℝ) ^ K) ^ 2
        rw [← hpowSq]
        ring
      _ ≤ M * I ^ 2 := hsquared
      _ = M * K ^ 2 * V ^ 2 := by rw [hI]; ring
  have hcanceled : 9 * Real.rpow 9 (-K) ≤ M * K ^ 2 := by
    by_contra hnot
    have hlt : M * K ^ 2 < 9 * Real.rpow 9 (-K) := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt (sq_pos_of_pos hV)
    nlinarith [hnormalized, hmul]
  change 9 * Real.rpow 9 (-K) / K ^ 2 ≤ M
  exact (div_le_iff₀ (sq_pos_of_pos hKpos)).2 hcanceled

/-- The Kahn--Kalai--Linial theorem with a dimension-independent explicit constant. This is the
book's `Var[f] * Ω(log n / n)` claim with natural logarithm; changing the logarithm base only
changes the constant. -/
theorem kkl (f : BooleanFunction n) :
    variance f.toReal * Real.log (n : ℝ) / (100 * (n : ℝ)) ≤
      maximumInfluence f := by
  by_cases hn : n ≤ 1
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simpa using maximumInfluence_nonneg f
  have hnTwo : 2 ≤ n := by omega
  let N : ℝ := n
  let L := Real.log N
  let V := variance f.toReal
  let I := totalInfluence f.toReal
  let K := I / V
  let M := maximumInfluence f
  have hNgtOne : 1 < N := by
    dsimp [N]
    exact_mod_cast hnTwo
  have hNpos : 0 < N := zero_lt_one.trans hNgtOne
  have hLpos : 0 < L := Real.log_pos hNgtOne
  have hLnonneg : 0 ≤ L := hLpos.le
  have hVnonneg : 0 ≤ V := by
    exact (variance_eq_four_mul_probabilities f).2.2.1
  by_cases hVpos : 0 < V
  · have hVle : V ≤ 1 := (variance_eq_four_mul_probabilities f).2.2.2
    have hK : 1 ≤ K := by
      dsimp [K, I, V]
      exact (le_div_iff₀ hVpos).2 (by
        simpa using variance_le_totalInfluence f.toReal)
    have hKpos : 0 < K := zero_lt_one.trans_le hK
    have hI : I = V * K := by
      dsimp [K]
      field_simp
    have haverage : V * K / N ≤ M := by
      apply (div_le_iff₀ hNpos).2
      rw [← hI]
      simpa [N, M, mul_comm] using totalInfluence_le_natCast_mul_maximumInfluence f
    by_cases hhigh : L / 100 ≤ K
    · calc
        variance f.toReal * Real.log (n : ℝ) / (100 * (n : ℝ)) =
            (V * (L / 100)) / N := by
          dsimp [V, L, N]
          ring
        _ ≤ (V * K) / N := by gcongr
        _ ≤ M := haverage
    · have hKlow : K < L / 100 := lt_of_not_ge hhigh
      have hlogNinePos : 0 < Real.log 9 := Real.log_pos (by norm_num)
      have hlogNineLe : Real.log 9 ≤ 8 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
        norm_num at h ⊢
        exact h
      have hdenominator : 4 * Real.log 9 ≤ 100 := by nlinarith
      have hthreshold : L / 100 ≤ L / (4 * Real.log 9) := by
        apply (div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num) hlogNinePos)).2
        exact mul_le_mul_of_nonneg_left hdenominator hLnonneg
      have hKthreshold : K ≤ L / (4 * Real.log 9) :=
        hKlow.le.trans hthreshold
      have hbaseIdentity :
          (9 : ℝ) ^ (-L / (4 * Real.log 9)) = N ^ (-(1 : ℝ) / 4) := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hNpos]
        congr 1
        dsimp [L]
        field_simp [ne_of_gt hlogNinePos]
      have hpower : N ^ (-(1 : ℝ) / 4) ≤ (9 : ℝ) ^ (-K) := by
        rw [← hbaseIdentity]
        have hexponent : -L / (4 * Real.log 9) ≤ -K := by
          calc
            -L / (4 * Real.log 9) = -(L / (4 * Real.log 9)) := by ring
            _ ≤ -K := neg_le_neg hKthreshold
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          hexponent
      have hlogBound : L ≤ 4 * N ^ ((1 : ℝ) / 4) := by
        calc
          L ≤ N ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) := by
            simpa [L, N] using
              Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)
          _ = 4 * N ^ ((1 : ℝ) / 4) := by ring
      have hlogCube : L ^ 3 ≤ 64 * N ^ ((3 : ℝ) / 4) := by
        calc
          L ^ 3 ≤ (4 * N ^ ((1 : ℝ) / 4)) ^ 3 := by gcongr
          _ = 64 * (N ^ ((1 : ℝ) / 4)) ^ 3 := by ring
          _ = 64 * N ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_mul_natCast hNpos.le ((1 : ℝ) / 4) 3]
            norm_num
      have hvarianceLogCube : V * L ^ 3 ≤ 64 * N ^ ((3 : ℝ) / 4) := by
        calc
          V * L ^ 3 ≤ 1 * L ^ 3 := by gcongr
          _ ≤ 64 * N ^ ((3 : ℝ) / 4) := by simpa using hlogCube
      have hpowerMul :
          N ^ (-(1 : ℝ) / 4) * N = N ^ ((3 : ℝ) / 4) := by
        calc
          N ^ (-(1 : ℝ) / 4) * N =
              N ^ (-(1 : ℝ) / 4) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = N ^ (-(1 : ℝ) / 4 + 1) :=
            (Real.rpow_add hNpos (-(1 : ℝ) / 4) 1).symm
          _ = N ^ ((3 : ℝ) / 4) := by norm_num
      have hanalytic :
          V * L / (100 * N) ≤
            9 * N ^ (-(1 : ℝ) / 4) / (L / 100) ^ 2 := by
        have hleftDen : 0 < 100 * N := mul_pos (by norm_num) hNpos
        have hrightDen : 0 < (L / 100) ^ 2 := sq_pos_of_pos (div_pos hLpos (by norm_num))
        apply (div_le_div_iff₀ hleftDen hrightDen).2
        calc
          V * L * (L / 100) ^ 2 = V * L ^ 3 / 10000 := by ring
          _ ≤ (64 * N ^ ((3 : ℝ) / 4)) / 10000 := by gcongr
          _ ≤ 900 * N ^ ((3 : ℝ) / 4) := by
            have := Real.rpow_nonneg hNpos.le ((3 : ℝ) / 4)
            nlinarith
          _ = 9 * N ^ (-(1 : ℝ) / 4) * (100 * N) := by
            rw [← hpowerMul]
            ring
      have hKsq : K ^ 2 ≤ (L / 100) ^ 2 := by gcongr
      have hKsqPos : 0 < K ^ 2 := sq_pos_of_pos hKpos
      have hLsqPos : 0 < (L / 100) ^ 2 := sq_pos_of_pos (div_pos hLpos (by norm_num))
      have hedge := edgeKKL f hVpos
      change 9 * Real.rpow 9 (-K) / K ^ 2 ≤ M at hedge
      calc
        variance f.toReal * Real.log (n : ℝ) / (100 * (n : ℝ)) =
            V * L / (100 * N) := by rfl
        _ ≤ 9 * N ^ (-(1 : ℝ) / 4) / (L / 100) ^ 2 := hanalytic
        _ ≤ 9 * (9 : ℝ) ^ (-K) / (L / 100) ^ 2 := by
          apply (div_le_div_iff₀ hLsqPos hLsqPos).2
          gcongr
        _ ≤ 9 * (9 : ℝ) ^ (-K) / K ^ 2 := by
          apply (div_le_div_iff₀ hLsqPos hKsqPos).2
          gcongr
        _ ≤ M := by simpa only [Real.rpow_eq_pow] using hedge
  · have hVzero : V = 0 := le_antisymm (not_lt.mp hVpos) hVnonneg
    simpa [V, hVzero] using maximumInfluence_nonneg f

end FABL
