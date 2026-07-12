/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.EvenMajority

/-!
# Laplacian and Poincare inequality

Book items: Definition 2.34, Definition 2.36, Example 2.30, Proposition 2.35, Proposition 2.37,
Poincare inequality, Theorem 2.38, Exercise 2.17.

The discrete gradient, Laplacian, spectral total-influence formulas, and Poincare equality cases
from Section 2.3 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 2.34: the discrete gradient, valued in Mathlib's Euclidean space. -/
noncomputable def discreteGradient (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ discreteDerivative i f x

/-- The squared Euclidean norm of the discrete gradient is the sum of the squared coordinate
derivatives. -/
theorem norm_discreteGradient_sq (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    ‖discreteGradient f x‖ ^ 2 = ∑ i, discreteDerivative i f x ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change |discreteDerivative i f x| ^ 2 = discreteDerivative i f x ^ 2
  rw [sq_abs]

/-- O'Donnell, Definition 2.34: for Boolean-valued functions, squared gradient norm equals
sensitivity. -/
theorem norm_discreteGradient_toReal_sq_eq_sensitivity (f : BooleanFunction n)
    (x : {−1,1}^[n]) :
    ‖discreteGradient f.toReal x‖ ^ 2 = sensitivity f x := by
  calc
    ‖discreteGradient f.toReal x‖ ^ 2 =
        ∑ i, discreteDerivative i f.toReal x ^ 2 := norm_discreteGradient_sq f.toReal x
    _ = ∑ i, pivotalIndicator f i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact sq_discreteDerivative_toReal_eq_pivotalIndicator f i x
    _ = sensitivity f x := (sensitivity_cast_eq_sum_pivotalIndicator f x).symm

/-- O'Donnell, Proposition 2.35: total influence is the expected squared Euclidean norm of the
discrete gradient. -/
theorem totalInfluence_eq_expect_norm_discreteGradient_sq
    (f : {−1,1}^[n] → ℝ) :
    totalInfluence f = 𝔼 x, ‖discreteGradient f x‖ ^ 2 := by
  rw [totalInfluence_eq_expect_sum_sq_discreteDerivative]
  apply Finset.expect_congr rfl
  intro x _
  exact (norm_discreteGradient_sq f x).symm

/-- O'Donnell, Definition 2.36: the Laplacian is the sum of the coordinate Laplacians. -/
noncomputable def laplacian :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) :=
  ∑ i, coordinateLaplacian i

/-- The Laplacian acts pointwise as the sum of the coordinate Laplacians. -/
@[simp] theorem laplacian_apply (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    laplacian f x = ∑ i, coordinateLaplacian i f x := by
  simp [laplacian]

/-- O'Donnell, Proposition 2.37(1): the Laplacian is half the sum of the differences across all
incident cube edges. -/
theorem laplacian_eq_sum_sub_flip_div_two (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    laplacian f x = ∑ i, (f x - f (flipCoordinate x i)) / 2 := by
  rw [laplacian_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact coordinateLaplacian_eq_sub_flip_div_two f i x

/-- O'Donnell, Proposition 2.37(1), average-neighbor form: the Laplacian is `n/2` times the
difference between the value at `x` and the average value at its neighbors. -/
theorem laplacian_eq_card_mul_sub_expect_flip (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    laplacian f x =
      (n : ℝ) / 2 * (f x - 𝔼 i : Fin n, f (flipCoordinate x i)) := by
  rw [laplacian_eq_sum_sub_flip_div_two, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_const, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- O'Donnell, Proposition 2.37(2): on a Boolean-valued function the Laplacian is the output
times the sensitivity. -/
theorem laplacian_toReal_eq_mul_sensitivity (f : BooleanFunction n)
    (x : {−1,1}^[n]) :
    laplacian f.toReal x = f.toReal x * sensitivity f x := by
  classical
  rw [laplacian_apply]
  calc
    (∑ i, coordinateLaplacian i f.toReal x) =
        ∑ i, f.toReal x * pivotalIndicator f i x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pivotalIndicator]
      by_cases hp : IsPivotal f i x
      · rw [if_pos hp, coordinateLaplacian_eq_sub_flip_div_two]
        rw [IsPivotal] at hp
        rcases Int.units_eq_one_or (f x) with hx | hx
        · rcases Int.units_eq_one_or (f (flipCoordinate x i)) with hflip | hflip
          · exact (hp (by rw [hx, hflip])).elim
          · norm_num [BooleanFunction.toReal, hx, hflip]
        · rcases Int.units_eq_one_or (f (flipCoordinate x i)) with hflip | hflip
          · norm_num [BooleanFunction.toReal, hx, hflip]
          · exact (hp (by rw [hx, hflip])).elim
      · rw [if_neg hp, coordinateLaplacian_eq_sub_flip_div_two]
        have heq : f x = f (flipCoordinate x i) := not_ne_iff.mp hp
        simp [BooleanFunction.toReal, heq]
    _ = f.toReal x * ∑ i, pivotalIndicator f i x := by rw [Finset.mul_sum]
    _ = f.toReal x * sensitivity f x := by
      rw [← sensitivity_cast_eq_sum_pivotalIndicator]

/-- O'Donnell, Proposition 2.37(3): the Fourier expansion of the Laplacian multiplies the
coefficient at `S` by `|S|`. -/
theorem laplacian_eq_fourier_sum (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    laplacian f x =
      ∑ S, (S.card : ℝ) * fourierCoeff f S * monomial S x := by
  classical
  rw [laplacian_apply]
  simp_rw [coordinateLaplacian_eq_fourier_sum]
  calc
    (∑ i, ∑ S with i ∈ S, fourierCoeff f S * monomial S x) =
        ∑ S, ∑ i with i ∈ S, fourierCoeff f S * monomial S x := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ S, (S.card : ℝ) * fourierCoeff f S * monomial S x := by
      apply Finset.sum_congr rfl
      intro S _
      simp [mul_assoc]

/-- O'Donnell, Proposition 2.37(4): pairing a function with its Laplacian gives total influence. -/
theorem uniformInner_laplacian_eq_totalInfluence (f : {−1,1}^[n] → ℝ) :
    ⟪f, laplacian f⟫ᵤ = totalInfluence f := by
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect, totalInfluence]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, laplacian_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa [uniformInner, RCLike.wInner_cWeight_eq_expect] using
    uniformInner_coordinateLaplacian_eq_influence f i

/-- O'Donnell, Theorem 2.38, first Fourier formula: total influence is Fourier weight weighted
by subset cardinality. -/
theorem totalInfluence_eq_sum_card_mul_sq_fourierCoeff
    (f : {−1,1}^[n] → ℝ) :
    totalInfluence f = ∑ S, (S.card : ℝ) * fourierCoeff f S ^ 2 := by
  classical
  rw [totalInfluence]
  simp_rw [influence_eq_sum_sq_fourierCoeff]
  calc
    (∑ i, ∑ S with i ∈ S, fourierCoeff f S ^ 2) =
        ∑ S, ∑ i with i ∈ S, fourierCoeff f S ^ 2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ S, (S.card : ℝ) * fourierCoeff f S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _
      simp

/-- O'Donnell, Theorem 2.38, second Fourier formula: regrouping by degree expresses total
influence as the degree-weighted sum of level Fourier weights. -/
theorem totalInfluence_eq_sum_level_mul_fourierWeight
    (f : {−1,1}^[n] → ℝ) :
    totalInfluence f =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * fourierWeightAtLevel k f := by
  rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  calc
    (∑ S, (S.card : ℝ) * fourierCoeff f S ^ 2) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k, (S.card : ℝ) * fourierCoeff f S ^ 2 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by
        simpa using Finset.card_le_univ S
      omega
    _ = ∑ k ∈ Finset.range (n + 1), (k : ℝ) * fourierWeightAtLevel k f := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierWeightAtLevel]
      simp only [Finset.sum_filter, fourierWeight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = k <;> simp [hcard]

/-- O'Donnell, Theorem 2.38, spectral-distribution form: total influence of a Boolean function
is the finite expectation of the spectral sample's cardinality. -/
theorem totalInfluence_toReal_eq_spectralSample_expectedCard (f : BooleanFunction n) :
    totalInfluence f.toReal =
      ∑ S, (spectralSample f S).toReal * (S.card : ℝ) := by
  rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  apply Finset.sum_congr rfl
  intro S _
  rw [spectralSample_apply_toReal]
  simp [fourierWeight, mul_comm]

/-- O'Donnell, Example 2.30: Boolean total influence lies between zero and `n`. -/
theorem totalInfluence_toReal_mem_Icc (f : BooleanFunction n) :
    totalInfluence f.toReal ∈ Set.Icc (0 : ℝ) n := by
  constructor
  · exact totalInfluence_nonneg f.toReal
  · rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
    calc
      (∑ S, (S.card : ℝ) * fourierCoeff f.toReal S ^ 2) ≤
          ∑ S, (n : ℝ) * fourierCoeff f.toReal S ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hcard : S.card ≤ n := by
          simpa using Finset.card_le_univ S
        exact_mod_cast hcard
      _ = (n : ℝ) * ∑ S, fourierCoeff f.toReal S ^ 2 := by
        rw [Finset.mul_sum]
      _ = n := by rw [sum_sq_fourierCoeff_eq_one, mul_one]

/-- The core Poincaré inequality in Section 2.3: variance is at most total influence. -/
theorem variance_le_totalInfluence (f : {−1,1}^[n] → ℝ) :
    variance f ≤ totalInfluence f := by
  classical
  rw [(variance_eq_sum_sq_fourierCoeff f).2,
    totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · have hcard : (1 : ℝ) ≤ S.card := by
      exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    rw [if_pos hS]
    nlinarith [sq_nonneg (fourierCoeff f S)]

/-- Equality in the Poincaré inequality is equivalent to vanishing of every Fourier coefficient
above degree one. -/
theorem variance_eq_totalInfluence_iff (f : {−1,1}^[n] → ℝ) :
    variance f = totalInfluence f ↔
      ∀ S : Finset (Fin n), 1 < S.card → fourierCoeff f S = 0 := by
  classical
  rw [(variance_eq_sum_sq_fourierCoeff f).2,
    totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  rw [Finset.sum_filter]
  let gap : Finset (Fin n) → ℝ := fun S ↦
    (S.card : ℝ) * fourierCoeff f S ^ 2 -
      (if S ≠ ∅ then fourierCoeff f S ^ 2 else 0)
  have hgap_nonneg (S : Finset (Fin n)) : 0 ≤ gap S := by
    dsimp [gap]
    by_cases hS : S = ∅
    · simp [hS]
    · have hcard : (1 : ℝ) ≤ S.card := by
        exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
      rw [if_pos hS]
      calc
        0 ≤ ((S.card : ℝ) - 1) * fourierCoeff f S ^ 2 :=
          mul_nonneg (sub_nonneg.mpr hcard) (sq_nonneg _)
        _ = (S.card : ℝ) * fourierCoeff f S ^ 2 - fourierCoeff f S ^ 2 := by ring
  have hsum_gap :
      (∑ S, gap S) =
        (∑ S, (S.card : ℝ) * fourierCoeff f S ^ 2) -
          ∑ S, if S ≠ ∅ then fourierCoeff f S ^ 2 else 0 := by
    simp [gap, Finset.sum_sub_distrib]
  constructor
  · intro h S hS
    have hsum_zero : ∑ S, gap S = 0 := by
      rw [hsum_gap, h]
      ring
    have hgap_zero : gap S = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦ hgap_nonneg T).mp hsum_zero S
        (Finset.mem_univ S)
    have hSne : S ≠ ∅ := by
      intro hEmpty
      simp [hEmpty] at hS
    dsimp [gap] at hgap_zero
    rw [if_pos hSne] at hgap_zero
    have hcard : (1 : ℝ) < S.card := by exact_mod_cast hS
    have hfactor : ((S.card : ℝ) - 1) * fourierCoeff f S ^ 2 = 0 := by
      calc
        ((S.card : ℝ) - 1) * fourierCoeff f S ^ 2 =
            (S.card : ℝ) * fourierCoeff f S ^ 2 - fourierCoeff f S ^ 2 := by ring
        _ = 0 := hgap_zero
    rcases mul_eq_zero.mp hfactor with hcardZero | hsquare
    · linarith
    · simpa using hsquare
  · intro h
    apply Finset.sum_congr rfl
    intro S _
    by_cases hcard : S.card ≤ 1
    · by_cases hS : S = ∅
      · simp [hS]
      · have hcardOne : S.card = 1 := by
          have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
          omega
        simp [hS, hcardOne]
    · have hzero : fourierCoeff f S = 0 := h S (Nat.lt_of_not_ge hcard)
      simp [hzero]

/-- The Poincaré equality condition in Fourier-weight notation: equality holds exactly when
there is no Fourier weight above degree one. -/
theorem variance_eq_totalInfluence_iff_fourierWeightAbove_one_eq_zero
    (f : {−1,1}^[n] → ℝ) :
    variance f = totalInfluence f ↔ fourierWeightAbove 1 f = 0 := by
  rw [variance_eq_totalInfluence_iff]
  constructor
  · intro h
    unfold fourierWeightAbove
    apply Finset.sum_eq_zero
    intro S hS
    have hcard : 1 < S.card := (Finset.mem_filter.mp hS).2
    simp [fourierWeight, h S hcard]
  · intro h S hcard
    unfold fourierWeightAbove at h
    have hmem : S ∈ (Finset.univ.filter fun T : Finset (Fin n) ↦ 1 < T.card) := by
      simp [hcard]
    have hsquare : fourierWeight f S = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun T _ ↦ by exact sq_nonneg (fourierCoeff f T))).mp h S hmem
    exact sq_eq_zero_iff.mp (by simpa [fourierWeight] using hsquare)

/-- The Poincaré equality condition in the book's `W^{≤1}` form: all second moment lies on
degrees zero and one. -/
theorem variance_eq_totalInfluence_iff_lowDegreeWeight_eq_secondMoment
    (f : {−1,1}^[n] → ℝ) :
    variance f = totalInfluence f ↔
      (∑ S with S.card ≤ 1, fourierCoeff f S ^ 2) = 𝔼 x, f x ^ 2 := by
  have hsecondMoment :
      (𝔼 x, f x ^ 2) = ∑ S, fourierCoeff f S ^ 2 := by
    calc
      (𝔼 x, f x ^ 2) = ⟪f, f⟫ᵤ := by
        simp [uniformInner, RCLike.wInner_cWeight_eq_expect, pow_two]
      _ = ∑ S, fourierCoeff f S ^ 2 := parseval f
  have hpartition :
      (∑ S with S.card ≤ 1, fourierCoeff f S ^ 2) + fourierWeightAbove 1 f =
        ∑ S, fourierCoeff f S ^ 2 := by
    simpa [fourierWeightAbove, fourierWeight, not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Finset (Fin n)))
        (fun S : Finset (Fin n) ↦ S.card ≤ 1)
        (fun S ↦ fourierCoeff f S ^ 2))
  rw [variance_eq_totalInfluence_iff_fourierWeightAbove_one_eq_zero,
    hsecondMoment]
  constructor <;> intro h <;> linarith

/-- A Boolean `1`-junta is either constant or a signed dictator. -/
theorem eq_const_or_signedDictator_of_isKJunta_one
    (f : BooleanFunction n) (hf : IsKJunta f 1) :
    f = (fun _ ↦ 1) ∨ f = (fun _ ↦ -1) ∨
      ∃ i : Fin n, f = dictator i ∨ f = -dictator i := by
  classical
  rcases hf with ⟨S, hcard, hdepends⟩
  by_cases hS : S = ∅
  · have hconstant (x y : {−1,1}^[n]) : f x = f y := by
      apply hdepends
      intro i hi
      simp [hS] at hi
    rcases Int.units_eq_one_or (f (fun _ ↦ 1)) with hvalue | hvalue
    · left
      funext x
      rw [hconstant x (fun _ ↦ 1), hvalue]
    · right
      left
      funext x
      rw [hconstant x (fun _ ↦ 1), hvalue]
  · have hcardOne : S.card = 1 := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcardOne
    let xPlus : {−1,1}^[n] := fun _ ↦ 1
    let xMinus : {−1,1}^[n] := fun _ ↦ -1
    have hplus (x : {−1,1}^[n]) (hx : x i = 1) : f x = f xPlus := by
      apply hdepends
      intro j hj
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hj
      subst j
      simpa [xPlus] using hx
    have hminus (x : {−1,1}^[n]) (hx : x i = -1) : f x = f xMinus := by
      apply hdepends
      intro j hj
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hj
      subst j
      simpa [xMinus] using hx
    rcases Int.units_eq_one_or (f xPlus) with hp | hp <;>
      rcases Int.units_eq_one_or (f xMinus) with hm | hm
    · left
      funext x
      rcases Int.units_eq_one_or (x i) with hx | hx
      · rw [hplus x hx, hp]
      · rw [hminus x hx, hm]
    · right
      right
      refine ⟨i, Or.inl ?_⟩
      funext x
      rcases Int.units_eq_one_or (x i) with hx | hx
      · rw [hplus x hx, hp]
        simp [dictator, hx]
      · rw [hminus x hx, hm]
        simp [dictator, hx]
    · right
      right
      refine ⟨i, Or.inr ?_⟩
      funext x
      rcases Int.units_eq_one_or (x i) with hx | hx
      · rw [hplus x hx, hp]
        simp [dictator, hx]
      · rw [hminus x hx, hm]
        simp [dictator, hx]
    · right
      left
      funext x
      rcases Int.units_eq_one_or (x i) with hx | hx
      · rw [hplus x hx, hp]
      · rw [hminus x hx, hm]

/-- Negating a real-valued function does not change its variance. -/
theorem variance_neg (f : {−1,1}^[n] → ℝ) : variance (-f) = variance f := by
  unfold variance mean
  simp only [Pi.neg_apply]
  rw [Finset.expect_neg_distrib]
  apply Finset.expect_congr rfl
  intro x _
  ring

/-- A dictator has variance one. -/
theorem variance_dictator (i : Fin n) : variance (dictator i).toReal = 1 := by
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  rw [hdictator, (variance_eq_sum_sq_fourierCoeff (monomial {i})).1]
  have hsecond : (𝔼 x, monomial {i} x ^ 2) = (1 : ℝ) := by
    calc
      (𝔼 x, monomial {i} x ^ 2) = 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        exact monomial_sq {i} x
      _ = 1 := Fintype.expect_const 1
  have hmean : mean (monomial {i}) = 0 := by
    simp [mean, expect_monomial]
  rw [hsecond, hmean]
  norm_num

/-- The Boolean equality classification in the Poincaré inequality: equality holds exactly for
the two constants and the signed dictators. -/
theorem variance_eq_totalInfluence_toReal_iff (f : BooleanFunction n) :
    variance f.toReal = totalInfluence f.toReal ↔
      f = (fun _ ↦ 1) ∨ f = (fun _ ↦ -1) ∨
        ∃ i : Fin n, f = dictator i ∨ f = -dictator i := by
  constructor
  · intro heq
    have hlow :=
      (variance_eq_totalInfluence_iff_lowDegreeWeight_eq_secondMoment f.toReal).mp heq
    have hsecond : (𝔼 x, f.toReal x ^ 2) = (1 : ℝ) := by
      calc
        (𝔼 x, f.toReal x ^ 2) = 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
          apply Finset.expect_congr rfl
          intro x _
          rcases Int.units_eq_one_or (f x) with hx | hx <;>
            simp [BooleanFunction.toReal, hx]
        _ = 1 := Fintype.expect_const 1
    have hweight : fourierWeightAtMost 1 f.toReal = 1 := by
      simpa [fourierWeightAtMost, fourierWeight] using hlow.trans hsecond
    exact eq_const_or_signedDictator_of_isKJunta_one f
      (isKJunta_one_of_fourierWeightAtMost_one_eq_one f hweight)
  · rintro (rfl | rfl | ⟨i, rfl | rfl⟩)
    · have hconst : BooleanFunction.toReal ((fun _ ↦ 1) : BooleanFunction n) =
          (fun _ ↦ (1 : ℝ)) := by
        funext x
        simp [BooleanFunction.toReal]
      rw [hconst, totalInfluence_const]
      simp [variance, mean]
    · have hconst : BooleanFunction.toReal ((fun _ ↦ -1) : BooleanFunction n) =
          (fun _ ↦ (-1 : ℝ)) := by
        funext x
        simp [BooleanFunction.toReal]
      rw [hconst, totalInfluence_const]
      simp [variance, mean]
    · rw [variance_dictator, totalInfluence_dictator]
    · have hneg : (-dictator i : BooleanFunction n).toReal = -(dictator i).toReal := by
        funext x
        change signValue (-dictator i x) = -signValue (dictator i x)
        rcases Int.units_eq_one_or (dictator i x) with hx | hx <;> simp [hx]
      rw [hneg, variance_neg, totalInfluence_neg, variance_dictator,
        totalInfluence_dictator]


end FABL
