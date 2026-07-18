/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.GoldreichLevin.RestrictedWeights
public import FABL.Chapter05.MajorityLargestFourierCoefficient
public import Mathlib.Probability.Distributions.Binomial

/-!
# The Fourier one-norm of majority

Book item: Exercise 5.26.
-/

open Filter
open scoped Asymptotics BigOperators BooleanCube ProbabilityTheory Real Topology unitInterval

@[expose] public section

namespace FABL

private theorem fourierOneNorm_degreePart_eq_sum_level
    {n k : ℕ} (f : {−1,1}^[n] → ℝ) :
    fourierOneNorm (degreePart k f) =
      ∑ S with S.card = k, |fourierCoeff f S| := by
  classical
  unfold fourierOneNorm
  simp only [fourierCoeff_degreePart, abs_ite, abs_zero]
  rw [← Finset.sum_filter]

private theorem fourierOneNorm_eq_sum_degreeParts
    {n : ℕ} (f : {−1,1}^[n] → ℝ) :
    fourierOneNorm f =
      ∑ k ∈ Finset.range (n + 1), fourierOneNorm (degreePart k f) := by
  classical
  simp_rw [fourierOneNorm_degreePart_eq_sum_level]
  unfold fourierOneNorm
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro S _
  rw [Finset.mem_range]
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  omega

/-- Exercise 5.26(a): the Fourier one-norm of the level-`2j+1` part of
majority on `2m+1` variables. -/
theorem fourierOneNorm_degreePart_majority_odd
    (m j : ℕ) (hj : j ≤ m) :
    fourierOneNorm
        (degreePart (2 * j + 1) (majority (2 * m + 1)).toReal) =
      (Nat.choose m j : ℝ) * (1 / (((2 * j + 1 : ℕ) : ℝ))) *
        ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 * m)) *
          (Nat.choose (2 * m) m : ℝ) := by
  classical
  rw [fourierOneNorm_degreePart_eq_sum_level]
  let c : ℝ :=
    (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
      (1 / (2 : ℝ) ^ (2 * m)) * (Nat.choose (2 * m) m : ℝ)
  have habs (S : Finset (Fin (2 * m + 1))) (hS : S.card = 2 * j + 1) :
      |fourierCoeff (majority (2 * m + 1)).toReal S| = c := by
    rw [fourierCoeff_majority_two_mul_add_one m j S hS]
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    rw [show
      (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) /
            (Nat.choose (2 * m) (2 * j) : ℝ) *
            (1 / (2 : ℝ) ^ (2 * m)) *
            (Nat.choose (2 * m) m : ℝ) =
          (-1 : ℝ) ^ j * c by
        dsimp [c]
        ring]
    simp [hc]
  calc
    (∑ S with S.card = 2 * j + 1,
        |fourierCoeff (majority (2 * m + 1)).toReal S|) =
        ∑ _S ∈ (Finset.univ : Finset (Fin (2 * m + 1))).powersetCard
          (2 * j + 1), c := by
      apply Finset.sum_congr
      · ext S
        simp
      · intro S hS
        exact habs S (Finset.mem_powersetCard.mp hS).2
    _ = (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) * c := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [nsmul_eq_mul]
    _ = (Nat.choose m j : ℝ) * (1 / (((2 * j + 1 : ℕ) : ℝ))) *
        ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 * m)) *
          (Nat.choose (2 * m) m : ℝ) := by
      have hsmall : (Nat.choose (2 * m) (2 * j) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hlevel : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hchoose :=
        Nat.add_one_mul_choose_eq (2 * m) (2 * j)
      have hchooseR :
          (((2 * m + 1 : ℕ) : ℝ)) *
              (Nat.choose (2 * m) (2 * j) : ℝ) =
            (Nat.choose (2 * m + 1) (2 * j + 1) : ℝ) *
              (((2 * j + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hchoose
      dsimp [c]
      field_simp [hsmall, hlevel]
      linear_combination
        -((Nat.choose m j : ℝ) * (Nat.choose (2 * m) m : ℝ)) * hchooseR

private theorem fourierOneNorm_degreePart_majority_odd_eq_zero_of_even
    (m k : ℕ) (hk : Even k) :
    fourierOneNorm (degreePart k (majority (2 * m + 1)).toReal) = 0 := by
  classical
  rw [fourierOneNorm_degreePart_eq_sum_level]
  apply Finset.sum_eq_zero
  intro S hS
  have hScard : S.card = k := (Finset.mem_filter.mp hS).2
  rw [fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
    ⟨m, rfl⟩ S (hScard.symm ▸ hk)]
  simp

private theorem sum_range_eq_sum_odd_of_even_eq_zero
    (a : ℕ → ℝ) (heven : ∀ j, a (2 * j) = 0) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2), a k =
      ∑ j ∈ Finset.range (m + 1), a (2 * j + 1) := by
  induction m with
  | zero =>
      rw [show 2 * 0 + 2 = 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, heven 0]
      simp
  | succ m ih =>
      have hevenNext : a (2 * m + 2) = 0 := by
        simpa [mul_add] using heven (m + 1)
      calc
        (∑ k ∈ Finset.range (2 * (m + 1) + 2), a k) =
            (∑ k ∈ Finset.range (2 * m + 2), a k) +
              a (2 * m + 2) + a (2 * m + 3) := by
          rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ j ∈ Finset.range (m + 1), a (2 * j + 1)) +
              a (2 * m + 3) := by
          rw [ih, hevenNext, add_zero]
        _ = (∑ j ∈ Finset.range (m + 1), a (2 * j + 1)) +
              a (2 * (m + 1) + 1) := by
          rw [show 2 * m + 3 = 2 * (m + 1) + 1 by omega]
        _ = ∑ j ∈ Finset.range (m + 1 + 1), a (2 * j + 1) :=
          (Finset.sum_range_succ _ _).symm

/-- The expectation of `(2X+1)⁻¹` for `X ∼ Binomial(m, 1/2)`. -/
noncomputable def binomialHalfOddReciprocalExpectation (m : ℕ) : ℝ :=
  ∫ j : ℕ, (1 : ℝ) / (2 * (j : ℝ) + 1) ∂
    ProbabilityTheory.binomial m
      ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

private theorem binomialHalfOddReciprocalExpectation_eq_sum (m : ℕ) :
    binomialHalfOddReciprocalExpectation m =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
          (1 / (2 * (j : ℝ) + 1)) := by
  unfold binomialHalfOddReciprocalExpectation
  rw [ProbabilityTheory.integral_binomial]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j hj
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    norm_num only [one_div, smul_eq_mul]
    have hpow :
        ((1 / 2 : ℝ) ^ j) * (1 / 2 : ℝ) ^ (m - j) =
          1 / (2 : ℝ) ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hjm]
      simp [one_div]
    calc
      (Nat.choose m j : ℝ) * (1 / 2) ^ j * (1 / 2) ^ (m - j) *
          (2 * (j : ℝ) + 1)⁻¹ =
          (Nat.choose m j : ℝ) *
            ((1 / 2) ^ j * (1 / 2) ^ (m - j)) *
              (2 * (j : ℝ) + 1)⁻¹ := by ring
      _ = (Nat.choose m j : ℝ) * (1 / (2 : ℝ) ^ m) *
            (2 * (j : ℝ) + 1)⁻¹ := by rw [hpow]
      _ = (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
            (2 * (j : ℝ) + 1)⁻¹ := by ring

/-- Exercise 5.26(b): the complete Fourier one-norm of odd majority, expressed
using `X ∼ Binomial(m, 1/2)`. -/
theorem fourierOneNorm_majority_odd_eq_binomialExpectation (m : ℕ) :
    fourierOneNorm (majority (2 * m + 1)).toReal =
      binomialHalfOddReciprocalExpectation m *
        ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ m) *
          (Nat.choose (2 * m) m : ℝ) := by
  rw [fourierOneNorm_eq_sum_degreeParts]
  rw [sum_range_eq_sum_odd_of_even_eq_zero
    (fun k ↦ fourierOneNorm (degreePart k (majority (2 * m + 1)).toReal)
      )
    (fun j ↦ fourierOneNorm_degreePart_majority_odd_eq_zero_of_even
      m (2 * j) ⟨j, by omega⟩) m]
  calc
    (∑ j ∈ Finset.range (m + 1),
        fourierOneNorm
          (degreePart (2 * j + 1) (majority (2 * m + 1)).toReal)) =
        ∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) * (1 / (((2 * j + 1 : ℕ) : ℝ))) *
            ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 * m)) *
              (Nat.choose (2 * m) m : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact fourierOneNorm_degreePart_majority_odd m j (by
        have := Finset.mem_range.mp hj
        omega)
    _ = binomialHalfOddReciprocalExpectation m *
        ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ m) *
          (Nat.choose (2 * m) m : ℝ) := by
      rw [binomialHalfOddReciprocalExpectation_eq_sum]
      calc
        (∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) * (1 / (((2 * j + 1 : ℕ) : ℝ))) *
              ((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (2 * m)) *
                (Nat.choose (2 * m) m : ℝ)) =
            ∑ j ∈ Finset.range (m + 1),
              ((Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
                (1 / (2 * (j : ℝ) + 1))) *
              (((((2 * m + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ m) *
                (Nat.choose (2 * m) m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j _
          field_simp
          push_cast
          ring
        _ = (∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
                (1 / (2 * (j : ℝ) + 1))) *
              (((2 * m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m *
                (Nat.choose (2 * m) m : ℝ)) := by
          rw [Finset.sum_mul]
        _ = (∑ j ∈ Finset.range (m + 1),
              (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
                (1 / (2 * (j : ℝ) + 1))) *
              (((2 * m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m) *
                (Nat.choose (2 * m) m : ℝ) := by ring

private theorem cast_choose_div_succ (n k : ℕ) :
    (Nat.choose n k : ℝ) / (((k + 1 : ℕ) : ℝ)) =
      (Nat.choose (n + 1) (k + 1) : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  have hchoose := Nat.add_one_mul_choose_eq n k
  exact_mod_cast (by simpa [mul_comm] using hchoose)

private theorem sum_cast_choose_div_succ (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℝ) / (((j + 1 : ℕ) : ℝ))) =
        ((2 : ℝ) ^ (m + 1) - 1) / (((m + 1 : ℕ) : ℝ)) := by
  calc
    (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) / (((j + 1 : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (j + 1) : ℝ) /
            (((m + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact cast_choose_div_succ m j
    _ = (∑ j ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (j + 1) : ℝ)) /
            (((m + 1 : ℕ) : ℝ)) := by
      rw [Finset.sum_div]
    _ = ((2 : ℝ) ^ (m + 1) - 1) /
        (((m + 1 : ℕ) : ℝ)) := by
      congr 1
      have hsumNat := Nat.sum_range_choose (m + 1)
      have hsum :
          (∑ j ∈ Finset.range (m + 2),
            (Nat.choose (m + 1) j : ℝ)) = (2 : ℝ) ^ (m + 1) := by
        exact_mod_cast hsumNat
      rw [Finset.sum_range_succ'] at hsum
      norm_num at hsum
      linarith

private theorem binomialHalfEvenReciprocalSum_eq (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
        (1 / (2 * (j : ℝ) + 2))) =
      (1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) := by
  calc
    (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
          (1 / (2 * (j : ℝ) + 2))) =
        (1 / (2 : ℝ) ^ (m + 1)) *
          ∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) / (((j + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      push_cast
      ring
    _ = (1 - 1 / (2 : ℝ) ^ (m + 1)) /
        (((m + 1 : ℕ) : ℝ)) := by
      rw [sum_cast_choose_div_succ]
      field_simp

private theorem cast_choose_div_two_succs (m j : ℕ) :
    (Nat.choose m j : ℝ) /
        ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) =
      (Nat.choose (m + 2) (j + 2) : ℝ) /
        ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by
  calc
    (Nat.choose m j : ℝ) /
          ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))) =
        ((Nat.choose m j : ℝ) / (((j + 1 : ℕ) : ℝ))) /
          (((j + 2 : ℕ) : ℝ)) := by ring
    _ = ((Nat.choose (m + 1) (j + 1) : ℝ) /
          (((m + 1 : ℕ) : ℝ))) / (((j + 2 : ℕ) : ℝ)) := by
      rw [cast_choose_div_succ]
    _ = ((Nat.choose (m + 1) (j + 1) : ℝ) /
          (((j + 2 : ℕ) : ℝ))) / (((m + 1 : ℕ) : ℝ)) := by ring
    _ = ((Nat.choose (m + 2) (j + 2) : ℝ) /
          (((m + 2 : ℕ) : ℝ))) / (((m + 1 : ℕ) : ℝ)) := by
      rw [cast_choose_div_succ]
    _ = (Nat.choose (m + 2) (j + 2) : ℝ) /
        ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by ring

private theorem sum_shifted_choose_le_pow (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (Nat.choose (m + 2) (j + 2) : ℝ)) ≤ (2 : ℝ) ^ (m + 2) := by
  have hsumNat := Nat.sum_range_choose (m + 2)
  have hsum :
      (∑ j ∈ Finset.range (m + 3),
        (Nat.choose (m + 2) j : ℝ)) = (2 : ℝ) ^ (m + 2) := by
    exact_mod_cast hsumNat
  rw [Finset.sum_range_succ'] at hsum
  rw [Finset.sum_range_succ'] at hsum
  norm_num at hsum
  have hzero : 0 ≤ ((m + 2 : ℕ) : ℝ) := by positivity
  linarith

private theorem binomialHalfTwoSuccReciprocalSum_le (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
        (1 / ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))))) ≤
      4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by
  have hden : 0 <
      (2 : ℝ) ^ m * (((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)) := by
    positivity
  calc
    (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
          (1 / ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ))))) =
        (∑ j ∈ Finset.range (m + 1),
          (Nat.choose (m + 2) (j + 2) : ℝ)) /
            ((2 : ℝ) ^ m * (((m + 1 : ℕ) : ℝ)) *
              (((m + 2 : ℕ) : ℝ))) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      calc
        (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
            (1 / ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) =
          ((Nat.choose m j : ℝ) /
            ((((j + 1 : ℕ) : ℝ)) * (((j + 2 : ℕ) : ℝ)))) /
              (2 : ℝ) ^ m := by ring
        _ = ((Nat.choose (m + 2) (j + 2) : ℝ) /
            ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) /
              (2 : ℝ) ^ m := by
          rw [cast_choose_div_two_succs]
        _ = (Nat.choose (m + 2) (j + 2) : ℝ) /
            ((2 : ℝ) ^ m * (((m + 1 : ℕ) : ℝ)) *
              (((m + 2 : ℕ) : ℝ))) := by ring
    _ ≤ (2 : ℝ) ^ (m + 2) /
        ((2 : ℝ) ^ m * (((m + 1 : ℕ) : ℝ)) *
          (((m + 2 : ℕ) : ℝ))) := by
      exact div_le_div_of_nonneg_right (sum_shifted_choose_le_pow m) hden.le
    _ = 4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by
      rw [show m + 2 = m + 2 by rfl, pow_add]
      norm_num
      field_simp

private theorem binomialHalfOddReciprocalExpectation_bounds (m : ℕ) :
    (1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) ≤
        binomialHalfOddReciprocalExpectation m ∧
      binomialHalfOddReciprocalExpectation m ≤
        (1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) +
          4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by
  rw [binomialHalfOddReciprocalExpectation_eq_sum]
  constructor
  · rw [← binomialHalfEvenReciprocalSum_eq]
    apply Finset.sum_le_sum
    intro j _
    have hweight : 0 ≤ (Nat.choose m j : ℝ) / (2 : ℝ) ^ m := by positivity
    apply mul_le_mul_of_nonneg_left _ hweight
    have hleft : 0 < 2 * (j : ℝ) + 1 := by positivity
    have hright : 0 < 2 * (j : ℝ) + 2 := by positivity
    exact one_div_le_one_div_of_le hleft (by linarith)
  · calc
      (∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
            (1 / (2 * (j : ℝ) + 1))) ≤
          ∑ j ∈ Finset.range (m + 1),
            ((Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
              (1 / (2 * (j : ℝ) + 2)) +
            (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
              (1 / ((((j + 1 : ℕ) : ℝ)) *
                (((j + 2 : ℕ) : ℝ))))) := by
        apply Finset.sum_le_sum
        intro j _
        have hweight : 0 ≤ (Nat.choose m j : ℝ) / (2 : ℝ) ^ m := by
          positivity
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ hweight
        field_simp
        push_cast
        nlinarith [sq_nonneg (j : ℝ)]
      _ = (∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
            (1 / (2 * (j : ℝ) + 2))) +
          ∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) / (2 : ℝ) ^ m *
              (1 / ((((j + 1 : ℕ) : ℝ)) *
                (((j + 2 : ℕ) : ℝ)))) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) +
          4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ))) := by
        rw [binomialHalfEvenReciprocalSum_eq]
        exact add_le_add_right (binomialHalfTwoSuccReciprocalSum_le m) _

private theorem
    tendsto_binomialHalfOddReciprocalExpectation_mul_oddArity_div_two :
    Tendsto
      (fun m : ℕ ↦
        binomialHalfOddReciprocalExpectation m *
          (((2 * m + 1 : ℕ) : ℝ)) / 2)
      atTop (𝓝 1) := by
  have hinvSucc :
      Tendsto (fun m : ℕ ↦ (1 : ℝ) / (((m + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hoddRatio :
      Tendsto
        (fun m : ℕ ↦
          (((2 * m + 1 : ℕ) : ℝ)) /
            (2 * (((m + 1 : ℕ) : ℝ))))
        atTop (𝓝 1) := by
    have hhalf :
        Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    have hsmall :
        Tendsto
          (fun m : ℕ ↦ (1 / 2 : ℝ) *
            (1 / (((m + 1 : ℕ) : ℝ))))
          atTop (𝓝 0) := by
      simpa using hhalf.mul hinvSucc
    have hone :
        Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have h :=
      hone.sub hsmall
    have h' :
        Tendsto
          (fun m : ℕ ↦ (1 : ℝ) -
            (1 / 2 : ℝ) * (1 / (((m + 1 : ℕ) : ℝ))))
          atTop (𝓝 1) := by
      simpa using h
    convert h' using 1
    funext m
    push_cast
    field_simp
    ring
  have hgeom :
      Tendsto
        (fun m : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ (m + 1))
        atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hpowSucc := (tendsto_add_atTop_iff_nat 1).2 hpow
    simpa only [one_div, inv_pow] using hpowSucc
  have hlower :
      Tendsto
        (fun m : ℕ ↦
          ((1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ))) *
            (((2 * m + 1 : ℕ) : ℝ)) / 2)
        atTop (𝓝 1) := by
    have hone :
        Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have honeSub :
        Tendsto
          (fun m : ℕ ↦ (1 : ℝ) - 1 / (2 : ℝ) ^ (m + 1))
          atTop (𝓝 1) := by
      simpa using hone.sub hgeom
    have hproduct := honeSub.mul hoddRatio
    have hproduct' :
        Tendsto
          (fun m : ℕ ↦
            (1 - 1 / (2 : ℝ) ^ (m + 1)) *
              ((((2 * m + 1 : ℕ) : ℝ)) /
                (2 * (((m + 1 : ℕ) : ℝ)))))
          atTop (𝓝 1) := by
      simpa using hproduct
    convert hproduct' using 1
    funext m
    field_simp
  have hinvAddTwo :
      Tendsto (fun m : ℕ ↦ (1 : ℝ) / (((m + 2 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 2).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hoddOverSucc :
      Tendsto
        (fun m : ℕ ↦
          (((2 * m + 1 : ℕ) : ℝ)) / (((m + 1 : ℕ) : ℝ)))
        atTop (𝓝 2) := by
    have htwo :
        Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have h :
        Tendsto
          (fun m : ℕ ↦ (2 : ℝ) -
            1 / (((m + 1 : ℕ) : ℝ)))
          atTop (𝓝 2) := by
      simpa using htwo.sub hinvSucc
    convert h using 1
    funext m
    push_cast
    field_simp
    ring
  have herror :
      Tendsto
        (fun m : ℕ ↦
          (4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
            (((2 * m + 1 : ℕ) : ℝ)) / 2)
        atTop (𝓝 0) := by
    have htwo :
        Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    have htwodiv :
        Tendsto
          (fun m : ℕ ↦ (2 : ℝ) *
            (1 / (((m + 2 : ℕ) : ℝ))))
          atTop (𝓝 0) := by
      simpa using htwo.mul hinvAddTwo
    have hproduct :
        Tendsto
          (fun m : ℕ ↦
            ((((2 * m + 1 : ℕ) : ℝ)) / (((m + 1 : ℕ) : ℝ))) *
              ((2 : ℝ) * (1 / (((m + 2 : ℕ) : ℝ)))))
          atTop (𝓝 0) := by
      simpa using hoddOverSucc.mul htwodiv
    convert hproduct using 1
    funext m
    field_simp
    ring
  have hupper :
      Tendsto
        (fun m : ℕ ↦
          ((1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ))) *
              (((2 * m + 1 : ℕ) : ℝ)) / 2 +
            (4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
              (((2 * m + 1 : ℕ) : ℝ)) / 2)
        atTop (𝓝 1) := by
    simpa using hlower.add herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · intro m
    have hmul := mul_le_mul_of_nonneg_right
      (binomialHalfOddReciprocalExpectation_bounds m).1
      (show 0 ≤ (((2 * m + 1 : ℕ) : ℝ)) / 2 by positivity)
    convert hmul using 1 <;> ring
  · intro m
    calc
      binomialHalfOddReciprocalExpectation m *
            (((2 * m + 1 : ℕ) : ℝ)) / 2 ≤
          ((1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ)) +
            4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
              (((2 * m + 1 : ℕ) : ℝ)) / 2 :=
        by
          calc
            binomialHalfOddReciprocalExpectation m *
                  (((2 * m + 1 : ℕ) : ℝ)) / 2 =
                binomialHalfOddReciprocalExpectation m *
                  ((((2 * m + 1 : ℕ) : ℝ)) / 2) := by ring
            _ ≤ ((1 - 1 / (2 : ℝ) ^ (m + 1)) /
                    (((m + 1 : ℕ) : ℝ)) +
                  4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
                ((((2 * m + 1 : ℕ) : ℝ)) / 2) :=
              mul_le_mul_of_nonneg_right
                (binomialHalfOddReciprocalExpectation_bounds m).2
                (by positivity)
            _ = ((1 - 1 / (2 : ℝ) ^ (m + 1)) /
                    (((m + 1 : ℕ) : ℝ)) +
                  4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
                (((2 * m + 1 : ℕ) : ℝ)) / 2 := by ring
      _ = ((1 - 1 / (2 : ℝ) ^ (m + 1)) / (((m + 1 : ℕ) : ℝ))) *
            (((2 * m + 1 : ℕ) : ℝ)) / 2 +
          (4 / ((((m + 1 : ℕ) : ℝ)) * (((m + 2 : ℕ) : ℝ)))) *
            (((2 * m + 1 : ℕ) : ℝ)) / 2 := by ring

private theorem fourierOneNorm_majority_odd_eq_expectation_mul_influence
    (m : ℕ) :
    fourierOneNorm (majority (2 * m + 1)).toReal =
      binomialHalfOddReciprocalExpectation m *
        (((2 * m + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ m *
          oddMajorityInfluence m := by
  rw [fourierOneNorm_majority_odd_eq_binomialExpectation]
  unfold oddMajorityInfluence
  field_simp
  ring

private theorem majorityFourierOneNormMain_eq_bookMain (m : ℕ) :
    2 * (2 : ℝ) ^ m * oddMajorityInfluenceMain m =
      (2 / Real.sqrt Real.pi) *
        (1 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ))) *
          (2 : ℝ) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2) := by
  have hrpow :
      (2 : ℝ) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2) =
        (2 : ℝ) ^ m * Real.sqrt 2 := by
    calc
      (2 : ℝ) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2) =
          (2 : ℝ) ^ ((m : ℝ) + 1 / 2) := by
        congr 1
        push_cast
        ring
      _ = (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_add (by norm_num) _ _
      _ = (2 : ℝ) ^ m * Real.sqrt 2 := by
        rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hsqrt :
      oddMajorityInfluenceMain m =
        Real.sqrt 2 / Real.sqrt Real.pi /
          Real.sqrt (((2 * m + 1 : ℕ) : ℝ)) := by
    unfold oddMajorityInfluenceMain
    rw [show
      2 / (Real.pi * (((2 * m + 1 : ℕ) : ℝ))) =
        (2 / Real.pi) / (((2 * m + 1 : ℕ) : ℝ)) by ring,
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 / Real.pi),
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2)]
  rw [hsqrt, hrpow]
  ring

/-- Exercise 5.26(c): as the positive odd arity tends to infinity, the
Fourier one-norm of majority is asymptotic to
`(2 / √π) n⁻¹ᐟ² 2^(n/2)`. -/
theorem fourierOneNorm_majority_odd_isEquivalent :
    (fun m : ℕ ↦ fourierOneNorm (majority (2 * m + 1)).toReal) ~[atTop]
      (fun m : ℕ ↦
        (2 / Real.sqrt Real.pi) *
          (1 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ))) *
            (2 : ℝ) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2)) := by
  have hproduct :=
    tendsto_binomialHalfOddReciprocalExpectation_mul_oddArity_div_two.mul
      tendsto_oddMajorityInfluence_div_main
  have hratio :
      Tendsto
        (fun m : ℕ ↦
          fourierOneNorm (majority (2 * m + 1)).toReal /
            (2 * (2 : ℝ) ^ m * oddMajorityInfluenceMain m))
        atTop (𝓝 1) := by
    have hproduct' :
        Tendsto
          (fun m : ℕ ↦
            (binomialHalfOddReciprocalExpectation m *
                (((2 * m + 1 : ℕ) : ℝ)) / 2) *
              (oddMajorityInfluence m / oddMajorityInfluenceMain m))
          atTop (𝓝 1) := by
      simpa using hproduct
    convert hproduct' using 1
    funext m
    rw [fourierOneNorm_majority_odd_eq_expectation_mul_influence]
    have hmain : oddMajorityInfluenceMain m ≠ 0 := by
      unfold oddMajorityInfluenceMain
      positivity
    field_simp [hmain]
  apply Asymptotics.isEquivalent_of_tendsto_one
  change Tendsto
    (fun m : ℕ ↦
      fourierOneNorm (majority (2 * m + 1)).toReal /
        ((2 / Real.sqrt Real.pi) *
          (1 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ))) *
            (2 : ℝ) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2)))
    atTop (𝓝 1)
  simpa only [majorityFourierOneNormMain_eq_bookMain] using hratio

end FABL
