/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.SocialChoiceFunctions.Definitions

/-!
# May's theorem

Book items: Definition 2.8, Exercise 2.3.

Symmetry, monotonicity, unanimity, and May's theorem from Section 2.1 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The unanimity property from O'Donnell, Definition 2.8. -/
def IsUnanimous (f : BooleanFunction n) : Prop :=
  f (fun _ ↦ 1) = 1 ∧ f (fun _ ↦ -1) = -1

/-- The symmetry property from O'Donnell, Definition 2.8. -/
def IsSymmetric {β : Type*} (f : {−1,1}^[n] → β) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : {−1,1}^[n]), f (permuteInput π x) = f x

/-- A coordinate permutation preserves the number of positive coordinates. -/
theorem positiveCoordinateCount_permuteInput (π : Equiv.Perm (Fin n))
    (x : {−1,1}^[n]) :
    positiveCoordinateCount (permuteInput π x) = positiveCoordinateCount x := by
  have hsum : (∑ i, signValue (permuteInput π x i)) = ∑ i, signValue (x i) := by
    exact Equiv.sum_comp π (fun i ↦ signValue (x i))
  rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub,
    sum_signValue_eq_two_mul_positiveCoordinateCount_sub] at hsum
  exact_mod_cast (by linarith :
    (positiveCoordinateCount (permuteInput π x) : ℝ) = positiveCoordinateCount x)

/-- Two sign-cube inputs with the same number of positive coordinates differ by a permutation. -/
theorem exists_permuteInput_eq_of_positiveCoordinateCount_eq (x y : {−1,1}^[n])
    (hcount : positiveCoordinateCount x = positiveCoordinateCount y) :
    ∃ π : Equiv.Perm (Fin n), permuteInput π x = y := by
  have hcard : (positiveCoordinateSet y).card = (positiveCoordinateSet x).card := by
    simpa [positiveCoordinateCount] using hcount.symm
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq
    (positiveCoordinateSet y) (positiveCoordinateSet x) hcard
  refine ⟨π, ?_⟩
  funext i
  have hmem : x (π i) = 1 ↔ y i = 1 := by
    have : π i ∈ positiveCoordinateSet x ↔ i ∈ positiveCoordinateSet y := by
      rw [← hπ]
      simp
    simpa [positiveCoordinateSet] using this
  rcases Int.units_eq_one_or (x (π i)) with hx | hx <;>
    rcases Int.units_eq_one_or (y i) with hy | hy <;>
      simp_all [permuteInput]

/-- O'Donnell, Definition 2.8: symmetry is equivalently dependence only on the number of `+1`
coordinates. -/
theorem isSymmetric_iff_eq_of_positiveCoordinateCount_eq {β : Type*}
    (f : {−1,1}^[n] → β) :
    IsSymmetric f ↔
      ∀ x y, positiveCoordinateCount x = positiveCoordinateCount y → f x = f y := by
  constructor
  · intro hf x y hcount
    obtain ⟨π, hπ⟩ := exists_permuteInput_eq_of_positiveCoordinateCount_eq x y hcount
    rw [← hπ]
    exact (hf π x).symm
  · intro hf π x
    apply hf
    exact positiveCoordinateCount_permuteInput π x

/-- An equal-weight threshold function is symmetric and monotone. -/
theorem IsEqualWeightThreshold.symmetric_and_monotone {f : BooleanFunction n}
    (hf : IsEqualWeightThreshold f) : IsSymmetric f ∧ Monotone f := by
  rcases hf with ⟨a₀, hf⟩
  constructor
  · intro π x
    rw [hf, hf]
    congr 1
    congr 1
    exact Equiv.sum_comp π (fun i ↦ signValue (x i))
  · intro x y hxy
    rw [hf, hf]
    apply monotone_thresholdSign
    gcongr with i
    exact monotone_signValue (hxy i)

/-- May's Theorem, Exercise 2.3(a), forward direction: every symmetric monotone Boolean function
has an equal-weight threshold representation. -/
theorem isEqualWeightThreshold_of_symmetric_monotone (f : BooleanFunction n)
    (hsym : IsSymmetric f) (hmono : Monotone f) :
    IsEqualWeightThreshold f := by
  classical
  have hcanonCount (x : {−1,1}^[n]) :
      positiveCoordinateCount (canonicalCountInput n (positiveCoordinateCount x)) =
        positiveCoordinateCount x := by
    rw [positiveCoordinateCount_canonicalCountInput, min_eq_right]
    exact positiveCoordinateCount_le x
  have hcanonEq (x : {−1,1}^[n]) :
      f (canonicalCountInput n (positiveCoordinateCount x)) = f x :=
    (isSymmetric_iff_eq_of_positiveCoordinateCount_eq f).mp hsym _ _ (hcanonCount x)
  let good : Finset ℕ := (Finset.range (n + 1)).filter
    fun k ↦ f (canonicalCountInput n k) = 1
  by_cases hgood : good.Nonempty
  · let k := good.min' hgood
    have hkGood : k ∈ good := Finset.min'_mem good hgood
    have hkval : f (canonicalCountInput n k) = 1 := (Finset.mem_filter.mp hkGood).2
    have hkmin {l : ℕ} (hl : l ∈ good) : k ≤ l := Finset.min'_le good l hl
    have hvalue (x : {−1,1}^[n]) :
        f x = 1 ↔ k ≤ positiveCoordinateCount x := by
      constructor
      · intro hx
        apply hkmin
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_range.mpr
          exact Nat.lt_succ_of_le (positiveCoordinateCount_le x)
        · rw [hcanonEq x]
          exact hx
      · intro hkx
        have hle := hmono (canonicalCountInput_mono n hkx)
        rw [hkval] at hle
        have hone := sign_eq_one_of_one_le _ hle
        rwa [hcanonEq x] at hone
    refine ⟨(n : ℝ) - 2 * k, ?_⟩
    intro x
    by_cases hkx : k ≤ positiveCoordinateCount x
    · rw [(hvalue x).2 hkx]
      symm
      apply thresholdSign_of_nonneg
      rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub]
      have hkxR : (k : ℝ) ≤ positiveCoordinateCount x := by
        exact_mod_cast hkx
      linarith
    · have hne : f x ≠ 1 := by
        intro hx
        exact hkx ((hvalue x).1 hx)
      have hxneg : f x = -1 := by
        rcases Int.units_eq_one_or (f x) with hx | hx
        · exact (hne hx).elim
        · exact hx
      rw [hxneg]
      symm
      apply thresholdSign_of_neg
      rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub]
      have hkxR : (positiveCoordinateCount x : ℝ) < k := by
        exact_mod_cast Nat.lt_of_not_ge hkx
      linarith
  · refine ⟨-(n : ℝ) - 1, ?_⟩
    intro x
    have hne : f x ≠ 1 := by
      intro hx
      apply hgood
      refine ⟨positiveCoordinateCount x, ?_⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        exact Nat.lt_succ_of_le (positiveCoordinateCount_le x)
      · rwa [hcanonEq x]
    have hxneg : f x = -1 := by
      rcases Int.units_eq_one_or (f x) with hx | hx
      · exact (hne hx).elim
      · exact hx
    rw [hxneg]
    symm
    apply thresholdSign_of_neg
    rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub]
    have hcountR : (positiveCoordinateCount x : ℝ) ≤ n := by
      exact_mod_cast positiveCoordinateCount_le x
    linarith

/-- May's Theorem, Exercise 2.3(a): symmetric monotone Boolean functions are exactly the
equal-weight threshold functions. -/
theorem symmetric_and_monotone_iff_isEqualWeightThreshold (f : BooleanFunction n) :
    IsSymmetric f ∧ Monotone f ↔ IsEqualWeightThreshold f := by
  constructor
  · rintro ⟨hsym, hmono⟩
    exact isEqualWeightThreshold_of_symmetric_monotone f hsym hmono
  · exact fun hf ↦ hf.symmetric_and_monotone

/-- May's Theorem, Exercise 2.3(b): a symmetric, monotone, odd Boolean function has odd arity
and is majority. -/
theorem may_theorem (f : BooleanFunction n) (hsym : IsSymmetric f) (hmono : Monotone f)
    (hodd : Function.Odd f) : Odd n ∧ f = majority n := by
  have hnOdd : Odd n := by
    rcases Nat.even_or_odd n with hnEven | hnOdd
    · rcases hnEven with ⟨k, hk⟩
      let x := canonicalCountInput n k
      have hk_le : k ≤ n := by omega
      have hcountx : positiveCoordinateCount x = k := by
        simp [x, positiveCoordinateCount_canonicalCountInput, min_eq_right hk_le]
      have hcountneg : positiveCoordinateCount (negateInput x) = k := by
        rw [positiveCoordinateCount_negateInput, hcountx, hk]
        omega
      have hsame : f (negateInput x) = f x :=
        (isSymmetric_iff_eq_of_positiveCoordinateCount_eq f).mp hsym _ _
          (hcountneg.trans hcountx.symm)
      have hoddx := hodd x
      change f (negateInput x) = -f x at hoddx
      rw [hoddx] at hsame
      rcases Int.units_eq_one_or (f x) with hx | hx <;> simp [hx] at hsame
    · exact hnOdd
  refine ⟨hnOdd, ?_⟩
  have hcanonCount (x : {−1,1}^[n]) :
      positiveCoordinateCount (canonicalCountInput n (positiveCoordinateCount x)) =
        positiveCoordinateCount x := by
    rw [positiveCoordinateCount_canonicalCountInput, min_eq_right]
    exact positiveCoordinateCount_le x
  have hcanonEq (x : {−1,1}^[n]) :
      f (canonicalCountInput n (positiveCoordinateCount x)) = f x :=
    (isSymmetric_iff_eq_of_positiveCoordinateCount_eq f).mp hsym _ _ (hcanonCount x)
  have hpositive (z : {−1,1}^[n]) (hz : 0 < ∑ i, signValue (z i)) : f z = 1 := by
    have hzR : (n : ℝ) < 2 * positiveCoordinateCount z := by
      rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub] at hz
      linarith
    have hzN : n < 2 * positiveCoordinateCount z := by
      exact_mod_cast hzR
    have hcz : n - positiveCoordinateCount z ≤ positiveCoordinateCount z := by
      omega
    have hle := hmono (canonicalCountInput_mono n hcz)
    have hlower : f (canonicalCountInput n (n - positiveCoordinateCount z)) =
        f (negateInput z) := by
      rw [← positiveCoordinateCount_negateInput z]
      exact hcanonEq (negateInput z)
    rw [hlower, hcanonEq z] at hle
    have hoddz := hodd z
    change f (negateInput z) = -f z at hoddz
    rw [hoddz] at hle
    rcases Int.units_eq_one_or (f z) with hz1 | hzneg
    · exact hz1
    · rw [hzneg] at hle
      change (1 : ℤ) ≤ -1 at hle
      omega
  funext x
  change f x = thresholdSign (∑ i, signValue (x i))
  have hsumne := sum_signValue_ne_zero_of_odd hnOdd x
  by_cases hsumpos : 0 < ∑ i, signValue (x i)
  · rw [hpositive x hsumpos]
    exact (thresholdSign_of_nonneg hsumpos.le).symm
  · have hsumneg : (∑ i, signValue (x i)) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hsumpos) hsumne
    have hnegpos : 0 < ∑ i, signValue ((-x) i) := by
      rw [show (∑ i, signValue ((-x) i)) = -(∑ i, signValue (x i)) by
        simp [signValue]]
      exact neg_pos.mpr hsumneg
    have hfn := hpositive (-x) hnegpos
    have hoddx := hodd x
    rw [hoddx] at hfn
    have hxneg : f x = -1 := by
      rcases Int.units_eq_one_or (f x) with hx | hx
      · simp [hx] at hfn
      · exact hx
    rw [hxneg]
    exact (thresholdSign_of_neg hsumneg).symm


end FABL
