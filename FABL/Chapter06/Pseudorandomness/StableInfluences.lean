/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.StableInfluence

/-!
# Small stable influences

Book items: Definition 6.9 and the constant and parity cases of Example 6.10.

The chapter predicate is a direct bounded-coordinate wrapper around the stable-influence
definition from Chapter 2.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A function has `(ε, δ)`-small stable influences when every coordinate has stable influence
at correlation `1 - δ` at most `ε`. -/
def HasSmallStableInfluences (ε δ : ℝ) (f : {−1,1}^[n] → ℝ) : Prop :=
  ∀ i, stableInfluence (1 - δ) f i ≤ ε

/-- The specialization called `ε`-small influences in the book. -/
def HasSmallInfluences (ε : ℝ) (f : {−1,1}^[n] → ℝ) : Prop :=
  HasSmallStableInfluences ε 0 f

/-- At correlation one, stable influence is ordinary influence. -/
theorem stableInfluence_one_eq_influence
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    stableInfluence 1 f i = influence f i := by
  rw [stableInfluence, influence_eq_sum_sq_fourierCoeff]
  apply Finset.sum_congr rfl
  intro S _
  simp

/-- Small influences are exactly coordinatewise bounds on ordinary influences. -/
theorem hasSmallInfluences_iff
    (ε : ℝ) (f : {−1,1}^[n] → ℝ) :
    HasSmallInfluences ε f ↔ ∀ i, influence f i ≤ ε := by
  simp only [HasSmallInfluences, HasSmallStableInfluences, sub_zero,
    stableInfluence_one_eq_influence]

/-- The stable influence of a Walsh monomial is supported exactly on its variables. -/
theorem stableInfluence_monomial
    (ρ : ℝ) (S : Finset (Fin n)) (i : Fin n) :
    stableInfluence ρ (monomial S) i =
      if i ∈ S then ρ ^ (S.card - 1) else 0 := by
  rw [stableInfluence]
  simp_rw [fourierCoeff_monomial]
  by_cases hi : i ∈ S
  · rw [if_pos hi, Finset.sum_eq_single S]
    · simp
    · intro T hT hTS
      simp [hTS.symm]
    · simp [hi]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro T hT
    simp only [Finset.mem_filter] at hT
    have hST : S ≠ T := by
      intro h
      subst T
      exact hi hT.2
    simp [hST]

/-- A parity on `S` has the stable-influence profile stated in Example 6.10. -/
theorem monomial_hasSmallStableInfluences_of_card
    (S : Finset (Fin n)) (ε δ : ℝ)
    (hε : 0 ≤ ε)
    (hbound : (1 - δ) ^ (S.card - 1) ≤ ε) :
    HasSmallStableInfluences ε δ (monomial S) := by
  intro i
  rw [stableInfluence_monomial]
  split_ifs
  · exact hbound
  · exact hε

/-- Constant functions have `(0, 0)`-small stable influences. -/
theorem const_hasSmallStableInfluences_zero_zero (c : ℝ) :
    HasSmallStableInfluences (n := n) 0 0 (fun _ ↦ c) := by
  intro i
  rw [stableInfluence]
  have hsum :
      (∑ S with i ∈ S,
        (1 - 0) ^ (S.card - 1) *
          fourierCoeff (fun _ : {−1,1}^[n] ↦ c) S ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hnonempty : S ≠ ∅ := by
      intro h
      subst S
      simp at hS
    have hcoeff : fourierCoeff (fun _ : {−1,1}^[n] ↦ c) S = 0 := by
      rw [fourierCoeff]
      calc
        (𝔼 _x : {−1,1}^[n], c * monomial S _x) =
            c * (𝔼 x : {−1,1}^[n], monomial S x) := by
          rw [Finset.mul_expect]
        _ = 0 := by rw [expect_monomial, if_neg hnonempty, mul_zero]
    simp [hcoeff]
  rw [hsum]

end FABL
