/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.CorrelationImmunity

/-!
# Bounds for correlation-immune functions

Book items: Exercise 6.14, Theorem 6.25.

The Fourier coefficient of a pointwise product is the symmetric-difference convolution of the
two Fourier transforms. This makes the high-support obstruction in Exercise 6.14 explicit.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Fourier coefficients turn pointwise multiplication into symmetric-difference convolution. -/
theorem fourierCoeff_pointwise_mul
    (f g : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f x * g x) S =
      ∑ T, fourierCoeff f (T ∆ S) * fourierCoeff g T := by
  classical
  rw [fourierCoeff]
  calc
    (𝔼 x, (f x * g x) * monomial S x) =
        𝔼 x, (f x * (∑ T, fourierCoeff g T * monomial T x)) *
          monomial S x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← fourier_expansion g x]
    _ = 𝔼 x, ∑ T,
          fourierCoeff g T *
            (f x * monomial (T ∆ S) x) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      rw [← monomial_mul_monomial T S]
      ring
    _ = ∑ T, 𝔼 x,
          fourierCoeff g T *
            (f x * monomial (T ∆ S) x) := by
      rw [Finset.expect_sum_comm]
    _ = ∑ T, fourierCoeff f (T ∆ S) * fourierCoeff g T := by
      apply Finset.sum_congr rfl
      intro T _
      calc
        (𝔼 x, fourierCoeff g T *
            (f x * monomial (T ∆ S) x)) =
            fourierCoeff g T *
              (𝔼 x, f x * monomial (T ∆ S) x) := by
          exact (Finset.mul_expect Finset.univ
            (fun x ↦ f x * monomial (T ∆ S) x)
            (fourierCoeff g T)).symm
        _ = fourierCoeff f (T ∆ S) * fourierCoeff g T := by
          rw [← fourierCoeff]
          ring

/-- Three finite subsets related by symmetric difference have total cardinality at most twice
the ambient dimension. -/
theorem card_add_card_add_card_symmDiff_le_two_mul_dimension
    (S T : Finset (Fin n)) :
    S.card + T.card + (S ∆ T).card ≤ 2 * n := by
  classical
  have hdisjoint : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact (Finset.mem_sdiff.mp hiS).2 (Finset.mem_sdiff.mp hiT).1
  have hsymmDiff :
      (S ∆ T).card = (S \ T).card + (T \ S).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisjoint]
  have hS := Finset.card_sdiff_add_card_inter S T
  have hT := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hT
  have hunion := Finset.card_union_add_card_inter S T
  have hunion_le : (S ∪ T).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (S ∪ T))
  omega

/-- Three sets all larger than two thirds of the ambient dimension cannot have one equal to
the symmetric difference of the other two. -/
theorem not_three_large_of_eq_symmDiff
    (S T U : Finset (Fin n)) (hSTU : S = T ∆ U)
    (hS : 2 * n < 3 * S.card)
    (hT : 2 * n < 3 * T.card)
    (hU : 2 * n < 3 * U.card) :
    False := by
  have hcard :=
    card_add_card_add_card_symmDiff_le_two_mul_dimension T U
  rw [← hSTU] at hcard
  omega

/-- Exercise 6.14(a), in Fourier-coefficient form: when every nonconstant supported
monomial has degree greater than `2n/3`, the coefficient indexed by such an `S` in the
multilinear reduction of `p²` is exactly `2 c_∅ c_S`. -/
theorem fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hScoeff : fourierCoeff f S ≠ 0)
    (hlarge :
      ∀ T : Finset (Fin n), T.Nonempty → fourierCoeff f T ≠ 0 →
        2 * n < 3 * T.card) :
    fourierCoeff (fun x ↦ f x * f x) S =
      2 * fourierCoeff f ∅ * fourierCoeff f S := by
  classical
  rw [fourierCoeff_pointwise_mul]
  let term : Finset (Fin n) → ℝ := fun T ↦
    fourierCoeff f (T ∆ S) * fourierCoeff f T
  have hS_ne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hS
  have hterm_other (T : Finset (Fin n)) (hT0 : T ≠ ∅) (hTS : T ≠ S) :
      term T = 0 := by
    by_cases hTcoeff : fourierCoeff f T = 0
    · simp [term, hTcoeff]
    by_cases hdiffcoeff : fourierCoeff f (T ∆ S) = 0
    · simp [term, hdiffcoeff]
    exfalso
    have hTnonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT0
    have hdiffnonempty : (T ∆ S).Nonempty := by
      rw [Finset.symmDiff_nonempty]
      exact hTS
    have hrelation : S = T ∆ (T ∆ S) := by
      ext i
      simp
    exact not_three_large_of_eq_symmDiff S T (T ∆ S) hrelation
      (hlarge S hS hScoeff)
      (hlarge T hTnonempty hTcoeff)
      (hlarge (T ∆ S) hdiffnonempty hdiffcoeff)
  calc
    (∑ T, fourierCoeff f (T ∆ S) * fourierCoeff f T) =
        ∑ T, if T = ∅ then term ∅ else if T = S then term S else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      change term T = _
      by_cases hT0 : T = ∅
      · simp [hT0]
      by_cases hTS : T = S
      · subst T
        simp [hS_ne]
      · simp [hT0, hTS, hterm_other T hT0 hTS]
    _ = term ∅ + term S := by
      have hsplit (T : Finset (Fin n)) :
          (if T = ∅ then term ∅ else if T = S then term S else 0) =
            (if T = ∅ then term ∅ else 0) +
              (if T = S then term S else 0) := by
        by_cases hT0 : T = ∅
        · subst T
          have h0S : (∅ : Finset (Fin n)) ≠ S := Ne.symm hS_ne
          simp [h0S]
        · simp [hT0]
      simp_rw [hsplit, Finset.sum_add_distrib]
      simp
    _ = 2 * fourierCoeff f ∅ * fourierCoeff f S := by
      change
        fourierCoeff f (∅ ∆ S) * fourierCoeff f ∅ +
            fourierCoeff f (S ∆ S) * fourierCoeff f S =
          2 * fourierCoeff f ∅ * fourierCoeff f S
      have h0S : (∅ : Finset (Fin n)) ∆ S = S := by
        ext i
        simp [Finset.mem_symmDiff]
      have hSS : S ∆ S = (∅ : Finset (Fin n)) :=
        Finset.symmDiff_eq_empty.mpr rfl
      rw [h0S, hSS]
      ring

/-- O'Donnell, Theorem 6.25, with the necessary nonconstant hypothesis restored:
a biased nonconstant correlation-immune Boolean function satisfies
`3(k+1) ≤ 2n`. -/
theorem correlationImmune_not_resilient_three_mul_succ_le_two_mul_dimension
    (f : BooleanFunction n) (k : ℕ)
    (himmune : IsCorrelationImmune k f)
    (hnotResilient : ¬ IsResilient k f)
    (hnonconstant : ¬ ∃ c : ℝ, f.toReal = fun _ ↦ c) :
    3 * (k + 1) ≤ 2 * n := by
  classical
  by_contra hbound
  have hthreshold : 2 * n < 3 * (k + 1) := by omega
  have hmean : fourierCoeff f.toReal ∅ ≠ 0 := by
    rw [← mean_eq_fourierCoeff_empty]
    intro hzero
    apply hnotResilient
    exact ⟨himmune, hzero⟩
  have hexists :
      ∃ S : Finset (Fin n), S.Nonempty ∧ fourierCoeff f.toReal S ≠ 0 := by
    by_contra h
    push Not at h
    apply hnonconstant
    exact (isFourierRegular_zero_iff_exists_const f.toReal).1
      (fun S hS ↦ by simp [h S hS])
  obtain ⟨S, hS, hScoeff⟩ := hexists
  have hlarge :
      ∀ T : Finset (Fin n), T.Nonempty → fourierCoeff f.toReal T ≠ 0 →
        2 * n < 3 * T.card := by
    intro T hT hTcoeff
    have hkT : k < T.card := by
      by_contra hk
      have hzero := himmune T hT (by omega)
      have habs :
          |fourierCoeff f.toReal T| = 0 :=
        le_antisymm hzero (abs_nonneg _)
      exact hTcoeff (abs_eq_zero.mp habs)
    have hkSucc : k + 1 ≤ T.card := by omega
    omega
  have hsquare :=
    fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support
      f.toReal S hS hScoeff hlarge
  have hsquareZero :
      fourierCoeff (fun x ↦ f.toReal x * f.toReal x) S = 0 := by
    rw [fourierCoeff]
    calc
      (𝔼 x, (f.toReal x * f.toReal x) * monomial S x) =
          𝔼 x, monomial S x := by
        apply Finset.expect_congr rfl
        intro x _
        rcases Int.units_eq_one_or (f x) with hx | hx <;>
          simp [BooleanFunction.toReal, hx]
      _ = 0 := by
        rw [expect_monomial, if_neg
          (Finset.nonempty_iff_ne_empty.mp hS)]
  rw [hsquareZero] at hsquare
  have hproduct :
      2 * fourierCoeff f.toReal ∅ * fourierCoeff f.toReal S ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) hmean) hScoeff
  exact hproduct hsquare.symm

end FABL
