/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.BasicFourierFormulas

/-!
# Social choice function definitions

Book items: Exercise 1.30(a), Definition 2.1, Definition 2.2, Definition 2.3, Definition 2.4,
Definition 2.5, Definition 2.6, Definition 2.7, Exercise 2.3.

Basic definitions and examples from Section 2.1 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The book's sign convention: `sgn(t) = 1` for `t ≥ 0` and `-1` otherwise. -/
noncomputable def thresholdSign (t : ℝ) : Sign :=
  if 0 ≤ t then 1 else -1

@[simp] theorem thresholdSign_of_nonneg {t : ℝ} (ht : 0 ≤ t) : thresholdSign t = 1 := by
  simp [thresholdSign, ht]

@[simp] theorem thresholdSign_of_neg {t : ℝ} (ht : t < 0) : thresholdSign t = -1 := by
  simp [thresholdSign, not_le.mpr ht]

/-- The real value of `thresholdSign t` is the usual two-valued sign convention. -/
theorem signValue_thresholdSign (t : ℝ) :
    signValue (thresholdSign t) = if 0 ≤ t then 1 else -1 := by
  by_cases ht : 0 ≤ t <;> simp [thresholdSign, ht]

/-- The real encoding of a sign, split into its two possible values. -/
theorem signValue_eq_ite (s : Sign) :
    signValue s = if s = 1 then 1 else -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [signValue]

/-- The real encoding distinguishes the two signs. -/
theorem signValue_injective : Function.Injective signValue := by
  intro a b hab
  apply Units.ext
  change (((a : ℤ) : ℝ) = ((b : ℤ) : ℝ)) at hab
  exact_mod_cast hab

/-- The real encoding preserves the order on signs. -/
theorem monotone_signValue : Monotone signValue := by
  intro a b hab
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl
  · norm_num
  · change (1 : ℤ) ≤ -1 at hab
    omega
  · norm_num
  · norm_num

/-- `-1` is the least sign. -/
theorem neg_one_le_sign (s : Sign) : (-1 : Sign) ≤ s := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · change (-1 : ℤ) ≤ 1
    omega
  · exact le_rfl

/-- `1` is the greatest sign. -/
theorem sign_le_one (s : Sign) : s ≤ (1 : Sign) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact le_rfl
  · change (-1 : ℤ) ≤ 1
    omega

/-- A sign below `-1` is `-1`. -/
theorem sign_eq_neg_one_of_le_neg_one (s : Sign) (h : s ≤ -1) : s = -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · change (1 : ℤ) ≤ -1 at h
    omega
  · rfl

/-- A sign above `1` is `1`. -/
theorem sign_eq_one_of_one_le (s : Sign) (h : 1 ≤ s) : s = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rfl
  · change (1 : ℤ) ≤ -1 at h
    omega

/-- The book's two-valued sign convention is monotone. -/
theorem monotone_thresholdSign : Monotone thresholdSign := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    simp [thresholdSign, ha, hb]
  · by_cases hb : 0 ≤ b
    · simp only [thresholdSign, if_false, ha, if_true, hb]
      change (-1 : ℤ) ≤ 1
      omega
    · simp [thresholdSign, ha, hb]

/-- Away from zero, the book's sign convention commutes with negation. -/
theorem thresholdSign_neg (t : ℝ) (ht : t ≠ 0) :
    thresholdSign (-t) = -thresholdSign t := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hnt : 0 < -t := neg_pos.mpr ht
    rw [thresholdSign_of_nonneg hnt.le, thresholdSign_of_neg ht]
    norm_num
  · have hnt : -t < 0 := neg_neg_of_pos ht
    rw [thresholdSign_of_neg hnt, thresholdSign_of_nonneg ht.le]

/-- The coordinates equal to `+1` in a sign-cube input. -/
def positiveCoordinateSet (x : {−1,1}^[n]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 1

/-- The number of `+1` coordinates in a sign-cube input. -/
def positiveCoordinateCount (x : {−1,1}^[n]) : ℕ :=
  (positiveCoordinateSet x).card

/-- The positive-coordinate count is at most the dimension of the cube. -/
theorem positiveCoordinateCount_le (x : {−1,1}^[n]) : positiveCoordinateCount x ≤ n := by
  calc
    positiveCoordinateCount x ≤ (Finset.univ : Finset (Fin n)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Fintype.card_fin n

/-- The canonical input whose first `k` coordinates are positive. -/
def canonicalCountInput (n k : ℕ) : {−1,1}^[n] :=
  fun i ↦ if (i : ℕ) < k then 1 else -1

/-- The canonical input has `min n k` positive coordinates. -/
theorem positiveCoordinateCount_canonicalCountInput (n k : ℕ) :
    positiveCoordinateCount (canonicalCountInput n k) = min n k := by
  simp [positiveCoordinateCount, positiveCoordinateSet, canonicalCountInput,
    Fin.card_filter_val_lt]

/-- Canonical count inputs are ordered by their number of positive coordinates. -/
theorem canonicalCountInput_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    canonicalCountInput n k ≤ canonicalCountInput n l := by
  intro i
  simp only [canonicalCountInput]
  by_cases hik : (i : ℕ) < k
  · have hil : (i : ℕ) < l := lt_of_lt_of_le hik hkl
    simp [hik, hil]
  · split_ifs
    · exact neg_one_le_sign _
    · exact le_rfl

/-- Express the coordinate sum in terms of the number of positive coordinates. -/
theorem sum_signValue_eq_two_mul_positiveCoordinateCount_sub (x : {−1,1}^[n]) :
    (∑ i, signValue (x i)) = 2 * positiveCoordinateCount x - n := by
  classical
  simp_rw [signValue_eq_ite]
  simp_rw [show ∀ i : Fin n,
      (if x i = 1 then (1 : ℝ) else -1) =
        2 * (if x i = 1 then (1 : ℝ) else 0) - 1 by
    intro i
    split <;> norm_num]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [positiveCoordinateCount, positiveCoordinateSet]

/-- An odd number of signs cannot have zero sum. -/
theorem sum_signValue_ne_zero_of_odd (hn : Odd n) (x : {−1,1}^[n]) :
    (∑ i, signValue (x i)) ≠ 0 := by
  rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub x]
  intro h
  have heqR : (2 : ℝ) * positiveCoordinateCount x = n := by
    linarith
  have heqN : 2 * positiveCoordinateCount x = n := by
    exact_mod_cast heqR
  rcases hn with ⟨k, hk⟩
  omega

/-- O'Donnell, Definition 2.1: the majority function, with ties resolved as `+1`. -/
noncomputable def majority (n : ℕ) : BooleanFunction n :=
  fun x ↦ thresholdSign (∑ i, signValue (x i))

/-- O'Donnell, Definition 2.1: a Boolean rule is a majority function when it agrees with the
sign of the vote margin away from tied profiles. -/
def IsMajorityFunction (f : BooleanFunction n) : Prop :=
  ∀ x, (∑ i, signValue (x i)) ≠ 0 →
    f x = thresholdSign (∑ i, signValue (x i))

/-- The canonical tie-to-`+1` majority rule is a majority function. -/
theorem majority_isMajorityFunction (n : ℕ) : IsMajorityFunction (majority n) := by
  intro x _
  rfl

/-- O'Donnell, Definition 2.2: Boolean AND in the book's `-1 = True` convention. -/
def andFunction (n : ℕ) : BooleanFunction n :=
  fun x ↦ if ∀ i, x i = -1 then -1 else 1

/-- O'Donnell, Definition 2.2: Boolean OR in the book's `-1 = True` convention. -/
def orFunction (n : ℕ) : BooleanFunction n :=
  fun x ↦ if ∀ i, x i = 1 then 1 else -1

/-- O'Donnell, Definition 2.3: the `i`th dictator function. -/
def dictator (i : Fin n) : BooleanFunction n :=
  fun x ↦ x i

/-- The real encoding of a dictator is the singleton monomial from Chapter 1. -/
theorem dictator_toReal_eq_monomial_singleton (i : Fin n) (x : {−1,1}^[n]) :
    (dictator i).toReal x = monomial {i} x := by
  simp [dictator, BooleanFunction.toReal, monomial]

/-- O'Donnell, Definition 2.4: a function is a `k`-junta when it depends on a set of at most
`k` coordinates. The dependence predicate is Mathlib's `DependsOn`. -/
def IsKJunta {β : Type*} (f : {−1,1}^[n] → β) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧ DependsOn f (S : Set (Fin n))

/-- Mathlib's factorization characterization of coordinate dependence, specialized to juntas. -/
theorem isKJunta_iff_exists_factorization {β : Type*} [Nonempty β]
    (f : {−1,1}^[n] → β) (k : ℕ) :
    IsKJunta f k ↔ ∃ S : Finset (Fin n), S.card ≤ k ∧
      ∃ g : ((i : (S : Set (Fin n))) → Sign) → β,
        f = g ∘ (S : Set (Fin n)).restrict := by
  constructor
  · rintro ⟨S, hS, hf⟩
    exact ⟨S, hS, dependsOn_iff_exists_comp.mp hf⟩
  · rintro ⟨S, hS, g, rfl⟩
    exact ⟨S, hS, dependsOn_iff_exists_comp.mpr ⟨g, rfl⟩⟩

/-- A dictator is a `1`-junta. -/
theorem dictator_isKJunta (i : Fin n) : IsKJunta (dictator i) 1 := by
  refine ⟨{i}, by simp, ?_⟩
  intro x y hxy
  exact hxy i (by simp)

/-- O'Donnell, Definition 2.5: a Boolean linear threshold function. -/
def IsLinearThreshold (f : BooleanFunction n) : Prop :=
  ∃ (a₀ : ℝ) (a : Fin n → ℝ),
    ∀ x, f x = thresholdSign (a₀ + ∑ i, a i * signValue (x i))

/-- A weighted-majority representation whose nonconstant weights are all one. -/
def IsEqualWeightThreshold (f : BooleanFunction n) : Prop :=
  ∃ a₀ : ℝ, ∀ x, f x = thresholdSign (a₀ + ∑ i, signValue (x i))

/-- Majority is a linear threshold function with all coordinate weights equal to one. -/
theorem majority_isLinearThreshold (n : ℕ) : IsLinearThreshold (majority n) := by
  refine ⟨0, fun _ ↦ 1, ?_⟩
  intro x
  simp [majority]

/-- Every dictator is a linear threshold function. -/
theorem dictator_isLinearThreshold (i : Fin n) : IsLinearThreshold (dictator i) := by
  refine ⟨0, fun j ↦ if j = i then 1 else 0, ?_⟩
  intro x
  have hsum : (∑ j, (if j = i then (1 : ℝ) else 0) * signValue (x j)) =
      signValue (x i) := by
    simp
  rw [hsum]
  rcases Int.units_eq_one_or (x i) with hi | hi <;>
    simp [dictator, hi, thresholdSign]

/-- View a flat input of length `s * w` as `s` consecutive blocks of width `w`. -/
def inputBlock {s w : ℕ} (x : {−1,1}^[s * w]) (i : Fin s) : {−1,1}^[w] :=
  fun j ↦ x (finProdFinEquiv (i, j))

/-- View an input of length `n ^ (d + 1)` as `n` blocks of length `n ^ d`. -/
def recursiveInputBlock {n d : ℕ} (x : {−1,1}^[n ^ (d + 1)])
    (i : Fin n) : {−1,1}^[n ^ d] :=
  fun j ↦ x (Fin.cast (by rw [pow_succ, Nat.mul_comm]) (finProdFinEquiv (i, j)))

/-- O'Donnell, Definition 2.6: the depth-`d` recursive majority of arity `n`.

At depth zero this is the identity on the unique input coordinate; the book starts the indexing at
depth one. -/
noncomputable def recursiveMajority (n : ℕ) : (d : ℕ) → BooleanFunction (n ^ d)
  | 0 => fun x ↦ x 0
  | d + 1 => fun x ↦ majority n (fun i ↦ recursiveMajority n d (recursiveInputBlock x i))

@[simp] theorem recursiveMajority_zero (n : ℕ) (x : {−1,1}^[n ^ 0]) :
    recursiveMajority n 0 x = x 0 := rfl

@[simp] theorem recursiveMajority_succ (n d : ℕ) (x : {−1,1}^[n ^ (d + 1)]) :
    recursiveMajority n (d + 1) x =
      majority n (fun i ↦ recursiveMajority n d (recursiveInputBlock x i)) := rfl

/-- The depth-one recursive majority is majority, after the canonical index cast. -/
theorem recursiveMajority_one (n : ℕ) (x : {−1,1}^[n ^ 1]) :
    recursiveMajority n 1 x = majority n (fun i ↦ x (Fin.cast (by simp) i)) := by
  simp only [recursiveMajority_succ, recursiveMajority_zero]
  congr 1
  funext i
  simp only [recursiveInputBlock]
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast]
  rw [finProdFinEquiv_apply_val]
  simp

/-- O'Donnell, Definition 2.7: OR of `s` width-`w` AND blocks. -/
def tribes (w s : ℕ) : BooleanFunction (s * w) :=
  fun x ↦ orFunction s (fun i ↦ andFunction w (inputBlock x i))

/-- Negate every coordinate of a sign-cube input. -/
def negateInput (x : {−1,1}^[n]) : {−1,1}^[n] :=
  fun i ↦ -x i

/-- Negation exchanges positive and negative coordinates. -/
theorem positiveCoordinateCount_negateInput (x : {−1,1}^[n]) :
    positiveCoordinateCount (negateInput x) = n - positiveCoordinateCount x := by
  have hsum : (∑ i, signValue (negateInput x i)) = -(∑ i, signValue (x i)) := by
    simp [negateInput, signValue]
  rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub,
    sum_signValue_eq_two_mul_positiveCoordinateCount_sub] at hsum
  have hcountR : (positiveCoordinateCount x : ℝ) ≤ n := by
    exact_mod_cast positiveCoordinateCount_le x
  have heqR : (positiveCoordinateCount (negateInput x) : ℝ) +
      positiveCoordinateCount x = n := by
    linarith
  have heqN : positiveCoordinateCount (negateInput x) +
      positiveCoordinateCount x = n := by
    exact_mod_cast heqR
  omega

/-- Reindex a sign-cube input by a coordinate permutation. -/
def permuteInput (π : Equiv.Perm (Fin n)) (x : {−1,1}^[n]) : {−1,1}^[n] :=
  fun i ↦ x (π i)

/-- Coordinate permutation as an equivalence of sign-cube inputs. -/
def permuteInputEquiv (π : Equiv.Perm (Fin n)) : {−1,1}^[n] ≃ {−1,1}^[n] where
  toFun := permuteInput π
  invFun := permuteInput π.symm
  left_inv x := by
    funext i
    simp [permuteInput]
  right_inv x := by
    funext i
    simp [permuteInput]

/-- Image of a Fourier index under a coordinate permutation. -/
def permuteFinset (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.map π.toEmbedding

/-- Permuting an input reindexes a monomial by the same permutation. -/
theorem monomial_permuteInput (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (x : {−1,1}^[n]) :
    monomial S (permuteInput π x) = monomial (permuteFinset π S) x := by
  simp [monomial, permuteInput, permuteFinset]

@[simp] theorem permuteFinset_symm (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    permuteFinset π (permuteFinset π.symm S) = S := by
  simp [permuteFinset, Finset.map_map]

/-- O'Donnell, Exercise 1.30(a): Fourier coefficients reindex under coordinate permutations. -/
theorem fourierCoeff_comp_permuteInput (π : Equiv.Perm (Fin n))
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (f ∘ permuteInput π) S =
      fourierCoeff f (permuteFinset π.symm S) := by
  apply Fintype.expect_equiv (permuteInputEquiv π)
  intro x
  change f (permuteInput π x) * monomial S x =
    f (permuteInput π x) * monomial (permuteFinset π.symm S) (permuteInput π x)
  congr 1
  rw [monomial_permuteInput, permuteFinset_symm]


end FABL
