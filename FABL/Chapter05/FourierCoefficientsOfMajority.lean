/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.StableInfluence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Fourier coefficients of majority

Book items: Exercise 1.8(c), the symmetric-coefficient consequence of Exercise 1.30,
the middle-layer calculation (5.12)--(5.14), Theorem 5.19, and Exercise 5.24, used in
Section 5.3.
-/

open Finset Polynomial Set
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem monomial_neg_input (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    monomial S (-x) = (-1 : ℝ) ^ S.card * monomial S x := by
  simp [monomial, signValue, Finset.prod_neg]

/-- Exercise 1.8(c): an odd function has zero Fourier coefficient on every
even-cardinality set. -/
theorem fourierCoeff_eq_zero_of_odd_of_even_card
    {f : {−1,1}^[n] → ℝ} (hf : Function.Odd f)
    (S : Finset (Fin n)) (hS : Even S.card) :
    fourierCoeff f S = 0 := by
  have hodd : Function.Odd (fun x ↦ f x * monomial S x) := by
    intro x
    change f (-x) * monomial S (-x) = -(f x * monomial S x)
    rw [hf x, monomial_neg_input, hS.neg_one_pow]
    ring
  unfold fourierCoeff
  rw [Fintype.expect_eq_sum_div_card, hodd.sum_eq_zero, zero_div]

/-- Exercise 1.30: Fourier coefficients of a symmetric function depend only on
the cardinality of their index set. -/
theorem fourierCoeff_eq_of_card_eq_of_isSymmetric
    {f : {−1,1}^[n] → ℝ} (hf : IsSymmetric f)
    {S T : Finset (Fin n)} (hcard : S.card = T.card) :
    fourierCoeff f S = fourierCoeff f T := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
  have hcomp : f ∘ permuteInput σ.symm = f := by
    funext x
    exact hf σ.symm x
  calc
    fourierCoeff f S =
        fourierCoeff (f ∘ permuteInput σ.symm) S := by rw [hcomp]
    _ = fourierCoeff f (permuteFinset σ S) := by
      simpa using fourierCoeff_comp_permuteInput σ.symm f S
    _ = fourierCoeff f T := by rw [permuteFinset, hσ]

/-- The real-valued indicator of the middle Hamming layer in the even-dimensional sign cube. -/
def middleLayerIndicator (m : ℕ) (x : {−1,1}^[2 * m]) : ℝ :=
  if positiveCoordinateCount x = m then 1 else 0

/-- On a `2m`-dimensional sign cube, the chosen positive-coordinate representation
is exactly the book's indicator of strings with `m` negative coordinates. -/
theorem middleLayerIndicator_eq_one_iff_negative_count
    (m : ℕ) (x : {−1,1}^[2 * m]) :
    middleLayerIndicator m x = 1 ↔
      ((Finset.univ : Finset (Fin (2 * m))).filter fun i ↦ x i = -1).card = m := by
  classical
  have hnegativeFilter :
      (Finset.univ.filter fun i : Fin (2 * m) ↦ ¬x i = 1) =
        Finset.univ.filter fun i : Fin (2 * m) ↦ x i = -1 := by
    ext i
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi]
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * m)))) (p := fun i ↦ x i = 1)
  rw [hnegativeFilter] at hpartition
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  unfold middleLayerIndicator positiveCoordinateCount positiveCoordinateSet
  by_cases hpositive :
      (Finset.univ.filter fun i : Fin (2 * m) ↦ x i = 1).card = m <;>
    simp [hpositive] <;>
    omega

/-- The first identity in O'Donnell's middle-layer calculation: the last discrete derivative
of odd-arity majority is the indicator of the middle layer on the remaining coordinates. -/
theorem discreteDerivative_majority_odd_last_eq_middleLayerIndicator
    (m : ℕ) (x : {−1,1}^[2 * m]) :
    discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal
        (Fin.snoc x 1) =
      middleLayerIndicator m x := by
  let c := positiveCoordinateCount x
  have hsum : (∑ i, signValue (x i)) = (2 : ℝ) * c - 2 * m := by
    simpa only [c, Nat.cast_mul, Nat.cast_ofNat] using
      sum_signValue_eq_two_mul_positiveCoordinateCount_sub x
  have hplus :
      (∑ i : Fin (2 * m + 1),
        signValue ((Fin.snoc x (1 : Sign) : Fin (2 * m + 1) → Sign) i)) =
        (2 : ℝ) * c - 2 * m + 1 := by
    rw [Fin.sum_univ_castSucc]
    simp [hsum]
  have hminus :
      (∑ i : Fin (2 * m + 1),
        signValue ((Fin.snoc x (-1 : Sign) : Fin (2 * m + 1) → Sign) i)) =
        (2 : ℝ) * c - 2 * m - 1 := by
    rw [Fin.sum_univ_castSucc]
    simp [hsum]
    ring
  rw [discreteDerivative_apply]
  rw [show setCoordinate (Fin.snoc x 1) (Fin.last (2 * m)) 1 =
      Fin.snoc x 1 by
    simp [setCoordinate, Fin.update_snoc_last]]
  rw [show setCoordinate (Fin.snoc x 1) (Fin.last (2 * m)) (-1) =
      Fin.snoc x (-1) by
    simp [setCoordinate, Fin.update_snoc_last]]
  change
    (signValue (majority (2 * m + 1) (Fin.snoc x 1)) -
        signValue (majority (2 * m + 1) (Fin.snoc x (-1)))) / 2 =
      middleLayerIndicator m x
  simp only [majority, signValue_thresholdSign]
  rw [hplus, hminus]
  unfold middleLayerIndicator
  by_cases hc : c = m
  · have hcx : positiveCoordinateCount x = m := by simpa only [c] using hc
    norm_num [hc, hcx]
  · rcases lt_or_gt_of_ne hc with hlt | hgt
    · have hltR : (c : ℝ) < m := by exact_mod_cast hlt
      have hp : ¬0 ≤ (2 : ℝ) * c - 2 * m + 1 := by
        have hstep : (c : ℝ) + 1 ≤ m := by exact_mod_cast hlt
        linarith
      have hm : ¬0 ≤ (2 : ℝ) * c - 2 * m - 1 := by linarith
      have hcx : ¬positiveCoordinateCount x = m := by simpa only [c] using hc
      simp [hcx, hp, hm]
    · have hgtR : (m : ℝ) < c := by exact_mod_cast hgt
      have hp : 0 ≤ (2 : ℝ) * c - 2 * m + 1 := by linarith
      have hm : 0 ≤ (2 : ℝ) * c - 2 * m - 1 := by
        have hstep : (m : ℝ) + 1 ≤ c := by exact_mod_cast hgt
        linarith
      have hcx : ¬positiveCoordinateCount x = m := by simpa only [c] using hc
      simp [hcx, hp, hm]

/-- The middle-layer indicator is invariant under every coordinate permutation. -/
theorem middleLayerIndicator_isSymmetric (m : ℕ) :
    IsSymmetric (middleLayerIndicator m) := by
  intro π x
  unfold middleLayerIndicator
  rw [positiveCoordinateCount_permuteInput]

private theorem sum_bool_filter_true_middleLayer (p : ENNReal) :
    (∑ b ∈ ({true, false} : Finset Bool) with b = true,
      bif b then p else 1 - p) = p := by
  norm_num [Finset.sum_filter]

private theorem sum_bool_filter_false_middleLayer (p : ENNReal) :
    (∑ b ∈ ({true, false} : Finset Bool) with b = false,
      bif b then p else 1 - p) = 1 - p := by
  norm_num [Finset.sum_filter]

private theorem coordinateNoisePMF_apply_self_middleLayer
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Sign) :
    coordinateNoisePMF ρ hρ x x =
      (correlationKeepProbability ρ hρ : ENNReal) := by
  classical
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    simp [coordinateNoisePMF, sum_bool_filter_true_middleLayer]

private theorem coordinateNoisePMF_apply_neg_middleLayer
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Sign) :
    coordinateNoisePMF ρ hρ x (-x) =
      1 - (correlationKeepProbability ρ hρ : ENNReal) := by
  classical
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    simp [coordinateNoisePMF, sum_bool_filter_false_middleLayer]

private theorem coordinateNoisePMF_one_toReal
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (y : Sign) :
    (coordinateNoisePMF ρ hρ 1 y).toReal =
      if y = 1 then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  rcases Int.units_eq_one_or y with rfl | rfl
  · rw [coordinateNoisePMF_apply_self_middleLayer]
    rfl
  · rw [coordinateNoisePMF_apply_neg_middleLayer]
    rw [ENNReal.toReal_sub_of_le
      (by exact_mod_cast correlationKeepProbability_le_one ρ hρ)
      ENNReal.one_ne_top]
    change 1 - (1 + ρ) / 2 = (1 - ρ) / 2
    ring

private theorem noiseKernel_allOne_middleLayer_mass_toReal
    (m : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (y : {−1,1}^[2 * m]) (hy : positiveCoordinateCount y = m) :
    (noiseKernel ρ hρ (fun _ ↦ 1) y).toReal =
      ((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m := by
  classical
  have hpositive :
      ((Finset.univ : Finset (Fin (2 * m))).filter fun i ↦ y i = 1).card = m := by
    simpa [positiveCoordinateCount, positiveCoordinateSet] using hy
  have hnegative :
      ((Finset.univ : Finset (Fin (2 * m))).filter fun i ↦ ¬y i = 1).card = m := by
    have hmiddle : middleLayerIndicator m y = 1 := by
      simp [middleLayerIndicator, hy]
    have hnegativeValue :=
      (middleLayerIndicator_eq_one_iff_negative_count m y).mp hmiddle
    have hnegativeFilter :
        (Finset.univ.filter fun i : Fin (2 * m) ↦ ¬y i = 1) =
          Finset.univ.filter fun i : Fin (2 * m) ↦ y i = -1 := by
      ext i
      rcases Int.units_eq_one_or (y i) with hi | hi <;> simp [hi]
    rw [hnegativeFilter]
    exact hnegativeValue
  rw [noiseKernel, independentProductPMF_apply, ENNReal.toReal_prod]
  simp_rw [coordinateNoisePMF_one_toReal]
  rw [Finset.prod_ite]
  simp [Finset.prod_const, hpositive, hnegative, div_pow]

private theorem sum_middleLayerIndicator (m : ℕ) :
    ∑ x : {−1,1}^[2 * m], middleLayerIndicator m x =
      (Nat.choose (2 * m) m : ℝ) := by
  classical
  calc
    (∑ x : {−1,1}^[2 * m], middleLayerIndicator m x) =
        ∑ S : Finset (Fin (2 * m)), if S.card = m then (1 : ℝ) else 0 := by
      apply Fintype.sum_equiv (signCubeEquivFinset (2 * m))
      intro x
      simp [middleLayerIndicator, signCubeEquivFinset_apply_card]
    _ = (Nat.choose (2 * m) m : ℝ) := by
      rw [Finset.sum_boole]
      have hfilter :
          (Finset.univ.filter fun S : Finset (Fin (2 * m)) ↦ S.card = m) =
            Finset.univ.powersetCard m := by
        ext S
        simp
      rw [hfilter, Finset.card_powersetCard]
      simp

/-- Equation (5.13), first line: the noise operator at the all-ones input is the
middle-layer probability under independent coordinate noise. -/
theorem noiseOperator_middleLayerIndicator_allOne_eq_product
    (m : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    noiseOperator ρ (middleLayerIndicator m) (fun _ ↦ 1) =
      (Nat.choose (2 * m) m : ℝ) *
        ((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m := by
  rw [noiseOperator_apply_eq_pmfExpectation ρ hρ]
  unfold pmfExpectation
  calc
    (∑ y : {−1,1}^[2 * m],
        (noiseKernel ρ hρ (fun _ ↦ 1) y).toReal * middleLayerIndicator m y) =
        ∑ y : {−1,1}^[2 * m],
          (((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m) *
            middleLayerIndicator m y := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : positiveCoordinateCount y = m
      · rw [noiseKernel_allOne_middleLayer_mass_toReal m ρ hρ y hy]
      · simp [middleLayerIndicator, hy]
    _ = (((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m) *
        ∑ y : {−1,1}^[2 * m], middleLayerIndicator m y := by
      rw [Finset.mul_sum]
    _ = (Nat.choose (2 * m) m : ℝ) *
        ((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m := by
      rw [sum_middleLayerIndicator]
      ring

/-- Equation (5.13), second line: the middle-layer noise probability in its
polynomial form. -/
theorem noiseOperator_middleLayerIndicator_allOne_eq
    (m : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    noiseOperator ρ (middleLayerIndicator m) (fun _ ↦ 1) =
      (Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m) *
        (1 - ρ ^ 2) ^ m := by
  rw [noiseOperator_middleLayerIndicator_allOne_eq_product m ρ hρ]
  have hfactor :
      ((1 + ρ) / 2) * ((1 - ρ) / 2) = (1 - ρ ^ 2) / 4 := by
    ring
  have hfour : (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
  calc
    (Nat.choose (2 * m) m : ℝ) *
          ((1 + ρ) / 2) ^ m * ((1 - ρ) / 2) ^ m =
        (Nat.choose (2 * m) m : ℝ) *
          (((1 + ρ) / 2) * ((1 - ρ) / 2)) ^ m := by
      rw [mul_pow]
      ring
    _ = (Nat.choose (2 * m) m : ℝ) *
        ((1 - ρ ^ 2) / 4) ^ m := by rw [hfactor]
    _ = (Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m) *
        (1 - ρ ^ 2) ^ m := by
      rw [div_pow, hfour]
      ring

/-- Equation (5.14), first equality: evaluation at the all-ones input turns every
Walsh character into one. -/
theorem noiseOperator_middleLayerIndicator_allOne_eq_fourierSum
    (m : ℕ) (ρ : ℝ) :
    noiseOperator ρ (middleLayerIndicator m) (fun _ ↦ 1) =
      ∑ U : Finset (Fin (2 * m)),
        fourierCoeff (middleLayerIndicator m) U * ρ ^ U.card := by
  rw [noiseOperator_fourier_expansion]
  apply Finset.sum_congr rfl
  intro U _
  simp [monomial]
  ring

/-- Equation (5.14), grouped by cardinality: any representative of each Fourier
level may be used because the middle-layer indicator is symmetric. -/
theorem noiseOperator_middleLayerIndicator_allOne_eq_groupedFourierSum
    (m : ℕ) (ρ : ℝ)
    (T : ℕ → Finset (Fin (2 * m)))
    (hT : ∀ i, i ≤ 2 * m → (T i).card = i) :
    noiseOperator ρ (middleLayerIndicator m) (fun _ ↦ 1) =
      ∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℝ) *
          fourierCoeff (middleLayerIndicator m) (T i) * ρ ^ i := by
  rw [noiseOperator_middleLayerIndicator_allOne_eq_fourierSum]
  calc
    (∑ U : Finset (Fin (2 * m)),
        fourierCoeff (middleLayerIndicator m) U * ρ ^ U.card) =
        ∑ i ∈ Finset.range (2 * m + 1),
          ∑ U with U.card = i,
            fourierCoeff (middleLayerIndicator m) U * ρ ^ U.card := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro U _
      rw [Finset.mem_range]
      have hcard : U.card ≤ 2 * m := by simpa using Finset.card_le_univ U
      omega
    _ = ∑ i ∈ Finset.range (2 * m + 1),
        (Nat.choose (2 * m) i : ℝ) *
          fourierCoeff (middleLayerIndicator m) (T i) * ρ ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ 2 * m := by simpa using Finset.mem_range.mp hi
      have hTi : (T i).card = i := hT i hi_le
      calc
        (∑ U with U.card = i,
            fourierCoeff (middleLayerIndicator m) U * ρ ^ U.card) =
            ∑ _U ∈ (Finset.univ : Finset (Fin (2 * m))).powersetCard i,
              fourierCoeff (middleLayerIndicator m) (T i) * ρ ^ i := by
          apply Finset.sum_congr
          · ext U
            simp
          · intro U hU
            have hUcard : U.card = i := (Finset.mem_powersetCard.mp hU).2
            rw [hUcard]
            rw [fourierCoeff_eq_of_card_eq_of_isSymmetric
              (middleLayerIndicator_isSymmetric m) (hUcard.trans hTi.symm)]
        _ = (Nat.choose (2 * m) i : ℝ) *
            fourierCoeff (middleLayerIndicator m) (T i) * ρ ^ i := by
          rw [Finset.sum_const, Finset.card_powersetCard]
          simp [nsmul_eq_mul]
          ring

private noncomputable def middleLayerFourierPolynomial (m : ℕ) : ℝ[X] :=
  ∑ U : Finset (Fin (2 * m)),
    Polynomial.C (fourierCoeff (middleLayerIndicator m) U) * Polynomial.X ^ U.card

private noncomputable def middleLayerBinomialPolynomial (m : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (m + 1),
    Polynomial.C ((-1 : ℝ) ^ j * (Nat.choose m j : ℝ)) *
      Polynomial.X ^ (2 * j)

private theorem eval_middleLayerFourierPolynomial (m : ℕ) (ρ : ℝ) :
    Polynomial.eval ρ (middleLayerFourierPolynomial m) =
      ∑ U : Finset (Fin (2 * m)),
        fourierCoeff (middleLayerIndicator m) U * ρ ^ U.card := by
  rw [middleLayerFourierPolynomial, Polynomial.eval_finsetSum]
  simp

private theorem eval_middleLayerBinomialPolynomial (m : ℕ) (ρ : ℝ) :
    Polynomial.eval ρ (middleLayerBinomialPolynomial m) = (1 - ρ ^ 2) ^ m := by
  rw [middleLayerBinomialPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show 1 - ρ ^ 2 = -(ρ ^ 2) + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_pow, pow_mul]
  simp only [one_pow, mul_one]
  ring

private theorem middleLayerFourierPolynomial_eq (m : ℕ) :
    middleLayerFourierPolynomial m =
      Polynomial.C ((Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m)) *
        middleLayerBinomialPolynomial m := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Icc_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
  intro ρ hρ
  simp only [Set.mem_setOf_eq]
  rw [eval_middleLayerFourierPolynomial,
    ← noiseOperator_middleLayerIndicator_allOne_eq_fourierSum]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    eval_middleLayerBinomialPolynomial]
  exact noiseOperator_middleLayerIndicator_allOne_eq m ρ hρ

private theorem coeff_middleLayerFourierPolynomial
    (m k : ℕ) (T : Finset (Fin (2 * m))) (hT : T.card = k) :
    (middleLayerFourierPolynomial m).coeff k =
      (Nat.choose (2 * m) k : ℝ) *
        fourierCoeff (middleLayerIndicator m) T := by
  rw [middleLayerFourierPolynomial, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  calc
    (∑ U : Finset (Fin (2 * m)),
        if k = U.card then fourierCoeff (middleLayerIndicator m) U else 0) =
        ∑ U with U.card = k, fourierCoeff (middleLayerIndicator m) U := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro U _
      by_cases hUk : U.card = k
      · simp [hUk]
      · have hkU : ¬k = U.card := Ne.symm hUk
        simp [hUk, hkU]
    _ =
        ∑ U ∈ (Finset.univ : Finset (Fin (2 * m))).powersetCard k,
          fourierCoeff (middleLayerIndicator m) T := by
      apply Finset.sum_congr
      · ext U
        simp [eq_comm]
      · intro U hU
        have hUcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
        exact fourierCoeff_eq_of_card_eq_of_isSymmetric
          (middleLayerIndicator_isSymmetric m) (hUcard.trans hT.symm)
    _ = (Nat.choose (2 * m) k : ℝ) *
        fourierCoeff (middleLayerIndicator m) T := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [nsmul_eq_mul]

private theorem coeff_middleLayerBinomialPolynomial
    (m j : ℕ) (hj : j ≤ m) :
    (middleLayerBinomialPolynomial m).coeff (2 * j) =
      (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) := by
  rw [middleLayerBinomialPolynomial, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hne : 2 * j ≠ 2 * i := by omega
    simp [hne]
  · simp [hj]

/-- Equation (5.12): the exact Fourier coefficient of the middle Hamming layer
on an even-dimensional sign cube. -/
theorem fourierCoeff_middleLayerIndicator
    (m j : ℕ) (hj : j ≤ m)
    (T : Finset (Fin (2 * m))) (hT : T.card = 2 * j) :
    fourierCoeff (middleLayerIndicator m) T =
      (-1 : ℝ) ^ j *
        (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
        (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) := by
  have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff (2 * j))
    (middleLayerFourierPolynomial_eq m)
  rw [coeff_middleLayerFourierPolynomial m (2 * j) T hT,
    Polynomial.coeff_C_mul,
    coeff_middleLayerBinomialPolynomial m j hj] at hcoeff
  have hchooseNat : 0 < Nat.choose (2 * m) (2 * j) :=
    Nat.choose_pos (by omega)
  have hchoose : (Nat.choose (2 * m) (2 * j) : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  rw [show
      (-1 : ℝ) ^ j *
          (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
          (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) =
        (((Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m)) *
          ((-1 : ℝ) ^ j * (Nat.choose m j : ℝ))) /
            (Nat.choose (2 * m) (2 * j) : ℝ) by
      field_simp [hchoose]]
  apply (eq_div_iff hchoose).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcoeff

private theorem monomial_map_castSucc_snoc
    {k : ℕ} (T : Finset (Fin k)) (x : {−1,1}^[k]) (b : Sign) :
    monomial (T.map Fin.castSuccEmb) (Fin.snoc x b) = monomial T x := by
  simp [monomial]

private theorem fourierCoeff_lift_init
    {k : ℕ} (g : {−1,1}^[k] → ℝ) (T : Finset (Fin k)) :
    fourierCoeff (fun y : {−1,1}^[k + 1] ↦ g (Fin.init y))
        (T.map Fin.castSuccEmb) =
      fourierCoeff g T := by
  unfold fourierCoeff
  calc
    (𝔼 y : {−1,1}^[k + 1],
        g (Fin.init y) * monomial (T.map Fin.castSuccEmb) y) =
        𝔼 p : Sign × {−1,1}^[k],
          g p.2 * monomial (T.map Fin.castSuccEmb) (Fin.snoc p.2 p.1) := by
      apply Fintype.expect_equiv
        (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Sign)).symm
      intro y
      simp
    _ = 𝔼 b : Sign, 𝔼 x : {−1,1}^[k],
        g x * monomial (T.map Fin.castSuccEmb) (Fin.snoc x b) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 x : {−1,1}^[k], g x * monomial T x := by
      simp_rw [monomial_map_castSucc_snoc]
      exact Fintype.expect_const _

private theorem discreteDerivative_majority_odd_eq_middleLayerIndicator_init
    (m : ℕ) :
    discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal =
      fun y ↦ middleLayerIndicator m (Fin.init y) := by
  funext y
  have hcoordinate :
      setCoordinate y (Fin.last (2 * m)) 1 =
        Fin.snoc (Fin.init y) 1 := by
    calc
      setCoordinate y (Fin.last (2 * m)) 1 =
          setCoordinate
            (Fin.snoc (Fin.init y) (y (Fin.last (2 * m))))
            (Fin.last (2 * m)) 1 := by
        rw [Fin.snoc_init_self]
      _ = Fin.snoc (Fin.init y) 1 := by
        simp only [setCoordinate, Fin.update_snoc_last]
  calc
    discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal y =
        discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal
          (setCoordinate y (Fin.last (2 * m)) 1) := by
      symm
      exact discreteDerivative_setCoordinate
        (Fin.last (2 * m)) (majority (2 * m + 1)).toReal y 1
    _ = discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal
          (Fin.snoc (Fin.init y) 1) := by
      rw [hcoordinate]
    _ = middleLayerIndicator m (Fin.init y) :=
      discreteDerivative_majority_odd_last_eq_middleLayerIndicator m (Fin.init y)

/-- The derivative step in Theorem 5.19: adjoining the last coordinate to a
Fourier set of the middle layer gives the corresponding majority coefficient. -/
theorem fourierCoeff_majority_odd_insert_last
    (m : ℕ) (T : Finset (Fin (2 * m))) :
    fourierCoeff (majority (2 * m + 1)).toReal
        (insert (Fin.last (2 * m)) (T.map Fin.castSuccEmb)) =
      fourierCoeff (middleLayerIndicator m) T := by
  have hlast : Fin.last (2 * m) ∉ T.map Fin.castSuccEmb := by simp
  calc
    fourierCoeff (majority (2 * m + 1)).toReal
        (insert (Fin.last (2 * m)) (T.map Fin.castSuccEmb)) =
        fourierCoeff
          (discreteDerivative (Fin.last (2 * m)) (majority (2 * m + 1)).toReal)
          (T.map Fin.castSuccEmb) := by
      symm
      rw [fourierCoeff_discreteDerivative, if_neg hlast]
    _ = fourierCoeff
        (fun y : {−1,1}^[2 * m + 1] ↦ middleLayerIndicator m (Fin.init y))
        (T.map Fin.castSuccEmb) := by
      rw [discreteDerivative_majority_odd_eq_middleLayerIndicator_init]
    _ = fourierCoeff (middleLayerIndicator m) T :=
      fourierCoeff_lift_init (middleLayerIndicator m) T

private theorem majority_toReal_isSymmetric (n : ℕ) :
    IsSymmetric (majority n).toReal := by
  intro π x
  change signValue (majority n (permuteInput π x)) = signValue (majority n x)
  rw [majority_symmetric]

private theorem majority_toReal_odd (hn : Odd n) :
    Function.Odd (majority n).toReal := by
  intro x
  rw [BooleanFunction.toReal, BooleanFunction.toReal, majority_odd hn x]
  rcases Int.units_eq_one_or (majority n x) with h | h <;> simp [h]

/-- Theorem 5.19, even-cardinality case. -/
theorem fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
    (hn : Odd n) (S : Finset (Fin n)) (hS : Even S.card) :
    fourierCoeff (majority n).toReal S = 0 :=
  fourierCoeff_eq_zero_of_odd_of_even_card (majority_toReal_odd hn) S hS

/-- Theorem 5.19 in the equivalent parametrization `n = 2m+1`,
`|S| = 2j+1`. -/
theorem fourierCoeff_majority_two_mul_add_one
    (m j : ℕ) (S : Finset (Fin (2 * m + 1)))
    (hS : S.card = 2 * j + 1) :
    fourierCoeff (majority (2 * m + 1)).toReal S =
      (-1 : ℝ) ^ j *
        (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
        (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) := by
  have hcard_le : S.card ≤ 2 * m + 1 := by
    simpa using Finset.card_le_univ S
  have hj : j ≤ m := by omega
  obtain ⟨T, _, hT⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin (2 * m)))) (n := 2 * j) (by simp; omega)
  let U : Finset (Fin (2 * m + 1)) :=
    insert (Fin.last (2 * m)) (T.map Fin.castSuccEmb)
  have hUcard : U.card = 2 * j + 1 := by
    simp [U, hT]
  calc
    fourierCoeff (majority (2 * m + 1)).toReal S =
        fourierCoeff (majority (2 * m + 1)).toReal U :=
      fourierCoeff_eq_of_card_eq_of_isSymmetric
        (majority_toReal_isSymmetric (2 * m + 1)) (hS.trans hUcard.symm)
    _ = fourierCoeff (middleLayerIndicator m) T := by
      exact fourierCoeff_majority_odd_insert_last m T
    _ = (-1 : ℝ) ^ j *
        (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
        (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ) :=
      fourierCoeff_middleLayerIndicator m j hj T hT

/-- Theorem 5.19, odd-cardinality case, in the book's `n,k` notation. -/
theorem fourierCoeff_majority_of_odd_arity_of_card_eq_odd
    {k : ℕ} (hn : Odd n) (hk : Odd k)
    (S : Finset (Fin n)) (hS : S.card = k) :
    fourierCoeff (majority n).toReal S =
      (-1 : ℝ) ^ ((k - 1) / 2) *
        (Nat.choose ((n - 1) / 2) ((k - 1) / 2) : ℝ) /
          (Nat.choose (n - 1) (k - 1) : ℝ) *
        (2 / (2 : ℝ) ^ n) *
          (Nat.choose (n - 1) ((n - 1) / 2) : ℝ) := by
  rcases hn with ⟨m, rfl⟩
  rcases hk with ⟨j, rfl⟩
  have hspecial :=
    fourierCoeff_majority_two_mul_add_one m j S hS
  have hnPred : 2 * m + 1 - 1 = 2 * m := by omega
  have hkPred : 2 * j + 1 - 1 = 2 * j := by omega
  have hnHalf : (2 * m + 1 - 1) / 2 = m := by omega
  have hkHalf : (2 * j + 1 - 1) / 2 = j := by omega
  have hscale :
      (2 : ℝ) / (2 : ℝ) ^ (2 * m + 1) =
        1 / (2 : ℝ) ^ (2 * m) := by
    rw [pow_succ]
    ring
  rw [hnHalf, hkHalf, hnPred, hkPred, hscale]
  exact hspecial

/-- Exercise 5.24: the elementary estimate used in the monotonicity of
majority's fixed-level Fourier weights. -/
theorem exercise5_24 (k n : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((1 : ℝ) - ((k + 1 : ℕ) : ℝ) / (n : ℝ) +
        (k : ℝ) / (n : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) ≤
      1 + 2 * (k : ℝ) / (n : ℝ) := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  let x : ℝ := (k : ℝ) / (n : ℝ)
  let y : ℝ := 1 / (n : ℝ)
  let A : ℝ := (1 - x) * (1 - y)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy_le_x : y ≤ x := by
    dsimp [x, y]
    exact (div_le_div_iff_of_pos_right hn_pos).2 (by exact_mod_cast hk)
  have hx_le_half : x ≤ (1 : ℝ) / 2 := by
    dsimp [x]
    rw [div_le_iff₀ hn_pos]
    have hkn_real : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
    linarith
  have hx_lt_one : x < 1 := hx_le_half.trans_lt (by norm_num)
  have hy_lt_one : y < 1 := hy_le_x.trans_lt hx_lt_one
  have hx_compl_pos : 0 < 1 - x := sub_pos.mpr hx_lt_one
  have hy_compl_pos : 0 < 1 - y := sub_pos.mpr hy_lt_one
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hx_compl_pos hy_compl_pos
  have hsq : (1 - x) ^ 2 ≤ A := by
    dsimp [A]
    calc
      (1 - x) ^ 2 = (1 - x) * (1 - x) := by ring
      _ ≤ (1 - x) * (1 - y) :=
        mul_le_mul_of_nonneg_left (by linarith [hy_le_x]) hx_compl_pos.le
  have hsqrt_lower : 1 - x ≤ Real.sqrt A :=
    Real.le_sqrt_of_sq_le hsq
  have hsqrt_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hinv_sqrt : (Real.sqrt A)⁻¹ ≤ (1 - x)⁻¹ :=
    (inv_le_inv₀ hsqrt_pos hx_compl_pos).2 hsqrt_lower
  have hinv_linear : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hx_compl_pos]
    have hproduct : 0 ≤ x * (1 - 2 * x) :=
      mul_nonneg hx_nonneg (by linarith [hx_le_half])
    nlinarith
  have hfactor :
      (1 : ℝ) - ((k + 1 : ℕ) : ℝ) / (n : ℝ) +
          (k : ℝ) / (n : ℝ) ^ 2 = A := by
    dsimp [A, x, y]
    push_cast
    field_simp [hn_ne]
    ring
  rw [hfactor]
  calc
    A ^ (-(1 / 2 : ℝ)) = (Real.sqrt A)⁻¹ := by
      rw [Real.rpow_neg hA_pos.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1 + 2 * x := hinv_sqrt.trans hinv_linear
    _ = 1 + 2 * (k : ℝ) / (n : ℝ) := by
      dsimp [x]
      ring

end FABL
