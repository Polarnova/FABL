/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.InfluencesAndDerivatives.DiscreteDerivatives

/-!
# Degree-one Boolean rigidity

Book items: Exercise 1.19(a,b).

The degree-one rigidity results closing Section 2.2 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Degree-one Boolean rigidity -/

/-- Under full level-one Fourier weight, every coefficient off level one vanishes. -/
theorem fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1)
    (S : Finset (Fin n)) (hS : S.card ≠ 1) :
    fourierCoeff f.toReal S = 0 := by
  classical
  have htotal := sum_sq_fourierCoeff_eq_one f
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun T ↦ T.card = 1)
    (fun T ↦ fourierCoeff f.toReal T ^ 2)
  have hlevel :
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) ↦ T.card = 1),
        fourierCoeff f.toReal T ^ 2 = 1 := by
    simpa [fourierWeightAtLevel, fourierWeight] using hweight
  have hrest :
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) ↦ ¬T.card = 1),
        fourierCoeff f.toReal T ^ 2 = 0 := by
    linarith
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun T _ ↦ sq_nonneg (fourierCoeff f.toReal T))).mp hrest S
      (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)
  exact sq_eq_zero_iff.mp hsq

/-- A Boolean function with all Fourier weight at level one is its singleton Fourier sum. -/
theorem toReal_eq_sum_singleton_of_fourierWeightAtLevel_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1)
    (x : {−1,1}^[n]) :
    f.toReal x = ∑ i, fourierCoeff f.toReal {i} * signValue (x i) := by
  classical
  rw [fourier_expansion f.toReal x]
  calc
    (∑ S, fourierCoeff f.toReal S * monomial S x) =
        ∑ S with S.card = 1, fourierCoeff f.toReal S * monomial S x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = 1
      · simp [hS]
      · rw [if_neg hS,
          fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one f hweight S hS]
        simp
    _ = ∑ i, fourierCoeff f.toReal {i} * signValue (x i) := by
      rw [Finset.sum_bij (fun i _ ↦ ({i} : Finset (Fin n)))]
      · intro i _
        simp
      · intro i _ j _
        simp
      · intro S hS
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
        exact ⟨i, Finset.mem_univ i, rfl⟩
      · intro i _
        simp [monomial]

/-- With full level-one Fourier weight, the `i`th derivative is the singleton coefficient. -/
theorem discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtLevel_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1)
    (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x = fourierCoeff f.toReal {i} := by
  classical
  rw [discreteDerivative_eq_fourier_sum, Finset.sum_filter]
  rw [Finset.sum_eq_single {i}]
  · simp [monomial]
  · intro S _ hne
    by_cases hiS : i ∈ S
    · have hcard : S.card ≠ 1 := by
        intro hcard
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
        simp only [Finset.mem_singleton] at hiS
        subst j
        exact hne rfl
      rw [if_pos hiS,
        fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one f hweight S hcard]
      simp
    · simp [hiS]
  · simp

/-- Level-one Fourier weight is the sum of squared singleton coefficients. -/
theorem fourierWeightAtLevel_one_eq_sum_singleton (f : {−1,1}^[n] → ℝ) :
    fourierWeightAtLevel 1 f = ∑ i, fourierCoeff f {i} ^ 2 := by
  classical
  unfold fourierWeightAtLevel fourierWeight
  rw [Finset.sum_bij (fun i _ ↦ ({i} : Finset (Fin n)))]
  · intro i _
    simp
  · intro i _ j _
    simp
  · intro S hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    rfl

/-- Under full level-one weight, each singleton coefficient has square zero or one. -/
theorem singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtLevel_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1)
    (i : Fin n) :
    fourierCoeff f.toReal {i} ^ 2 = 0 ∨ fourierCoeff f.toReal {i} ^ 2 = 1 := by
  let x : {−1,1}^[n] := fun _ ↦ 1
  have h := sq_discreteDerivative_toReal_eq_pivotalIndicator f i x
  rw [discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtLevel_one_eq_one
    f hweight i x] at h
  classical
  by_cases hp : IsPivotal f i x
  · right
    simpa [pivotalIndicator, hp] using h
  · left
    simpa [pivotalIndicator, hp] using h

/-- Exactly one singleton coefficient has square one when all Fourier weight is at level one. -/
theorem exists_unique_singletonCoeff_sq_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1) :
    ∃ i : Fin n, fourierCoeff f.toReal {i} ^ 2 = 1 ∧
      ∀ j : Fin n, j ≠ i → fourierCoeff f.toReal {j} = 0 := by
  have hsum : (∑ i, fourierCoeff f.toReal {i} ^ 2) = 1 := by
    rw [← fourierWeightAtLevel_one_eq_sum_singleton]
    exact hweight
  have hexists : ∃ i : Fin n, fourierCoeff f.toReal {i} ^ 2 = 1 := by
    by_contra h
    push Not at h
    have hall (i : Fin n) : fourierCoeff f.toReal {i} ^ 2 = 0 :=
      (singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtLevel_one_eq_one
        f hweight i).resolve_right (h i)
    have : (∑ i, fourierCoeff f.toReal {i} ^ 2) = 0 := by
      simp [hall]
    linarith
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, hi, ?_⟩
  have hrest :
      ∑ j ∈ (Finset.univ.erase i), fourierCoeff f.toReal {j} ^ 2 = 0 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun j ↦ fourierCoeff f.toReal {j} ^ 2) (Finset.mem_univ i)
    linarith
  intro j hji
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ sq_nonneg (fourierCoeff f.toReal {k}))).mp hrest j (by simp [hji])
  exact sq_eq_zero_iff.mp hsq

/-- O'Donnell, Exercise 1.19(a): a Boolean function with all Fourier weight at level one is a
signed dictator. -/
theorem eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtLevel 1 f.toReal = 1) :
    ∃ i : Fin n, f = dictator i ∨ f = -dictator i := by
  obtain ⟨i, hi, hother⟩ := exists_unique_singletonCoeff_sq_eq_one f hweight
  have hai : fourierCoeff f.toReal {i} = 1 ∨ fourierCoeff f.toReal {i} = -1 :=
    sq_eq_one_iff.mp hi
  have hrepr (x : {−1,1}^[n]) :
      f.toReal x = fourierCoeff f.toReal {i} * signValue (x i) := by
    rw [toReal_eq_sum_singleton_of_fourierWeightAtLevel_one_eq_one f hweight x]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hother j hji]
      simp
    · simp
  refine ⟨i, ?_⟩
  rcases hai with hai | hai
  · left
    funext x
    apply signValue_injective
    change f.toReal x = signValue (x i)
    rw [hrepr, hai]
    ring
  · right
    funext x
    apply signValue_injective
    change f.toReal x = signValue (-x i)
    rw [hrepr, hai]
    simp [signValue]

/-- Under full Fourier weight through level one, every coefficient above level one vanishes. -/
theorem fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtMost 1 f.toReal = 1)
    (S : Finset (Fin n)) (hS : ¬S.card ≤ 1) :
    fourierCoeff f.toReal S = 0 := by
  classical
  have htotal := sum_sq_fourierCoeff_eq_one f
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun T ↦ T.card ≤ 1)
    (fun T ↦ fourierCoeff f.toReal T ^ 2)
  have hlevel :
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) ↦ T.card ≤ 1),
        fourierCoeff f.toReal T ^ 2 = 1 := by
    simpa [fourierWeightAtMost, fourierWeight] using hweight
  have hrest :
      ∑ T ∈ (Finset.univ.filter fun T : Finset (Fin n) ↦ ¬T.card ≤ 1),
        fourierCoeff f.toReal T ^ 2 = 0 := by
    linarith
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun T _ ↦ sq_nonneg (fourierCoeff f.toReal T))).mp hrest S
      (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)
  exact sq_eq_zero_iff.mp hsq

/-- Under full degree-at-most-one weight, the derivative is the singleton coefficient. -/
theorem discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtMost_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtMost 1 f.toReal = 1)
    (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x = fourierCoeff f.toReal {i} := by
  classical
  rw [discreteDerivative_eq_fourier_sum, Finset.sum_filter]
  rw [Finset.sum_eq_single {i}]
  · simp [monomial]
  · intro S _ hne
    by_cases hiS : i ∈ S
    · have hcard : ¬S.card ≤ 1 := by
        intro hcard
        have hnonempty : S.Nonempty := ⟨i, hiS⟩
        have hpos : 0 < S.card := Finset.card_pos.mpr hnonempty
        have hone : S.card = 1 := by omega
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hone
        simp only [Finset.mem_singleton] at hiS
        subst j
        exact hne rfl
      rw [if_pos hiS,
        fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one f hweight S hcard]
      simp
    · simp [hiS]
  · simp

/-- Under full weight through level one, every singleton coefficient has square zero or one. -/
theorem singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtMost_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtMost 1 f.toReal = 1)
    (i : Fin n) :
    fourierCoeff f.toReal {i} ^ 2 = 0 ∨ fourierCoeff f.toReal {i} ^ 2 = 1 := by
  let x : {−1,1}^[n] := fun _ ↦ 1
  have h := sq_discreteDerivative_toReal_eq_pivotalIndicator f i x
  rw [discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtMost_one_eq_one
    f hweight i x] at h
  classical
  by_cases hp : IsPivotal f i x
  · right
    simpa [pivotalIndicator, hp] using h
  · left
    simpa [pivotalIndicator, hp] using h

/-- O'Donnell, Exercise 1.19(b): a Boolean function with all Fourier weight through level one
depends on at most one coordinate. -/
theorem isKJunta_one_of_fourierWeightAtMost_one_eq_one
    (f : BooleanFunction n) (hweight : fourierWeightAtMost 1 f.toReal = 1) :
    IsKJunta f 1 := by
  classical
  by_cases hexists : ∃ i : Fin n, fourierCoeff f.toReal {i} ^ 2 = 1
  · obtain ⟨i, hi⟩ := hexists
    have htotal := sum_sq_fourierCoeff_eq_one f
    have hrest :
        ∑ S ∈ (Finset.univ.erase ({i} : Finset (Fin n))),
          fourierCoeff f.toReal S ^ 2 = 0 := by
      have hsplit := Finset.sum_erase_add
        (Finset.univ : Finset (Finset (Fin n)))
        (fun S ↦ fourierCoeff f.toReal S ^ 2) (Finset.mem_univ {i})
      linarith
    have hother (S : Finset (Fin n)) (hSi : S ≠ {i}) :
        fourierCoeff f.toReal S = 0 := by
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg
        (fun T _ ↦ sq_nonneg (fourierCoeff f.toReal T))).mp hrest S (by simp [hSi])
      exact sq_eq_zero_iff.mp hsq
    have hlevel : fourierWeightAtLevel 1 f.toReal = 1 := by
      rw [fourierWeightAtLevel_one_eq_sum_singleton]
      rw [Finset.sum_eq_single i]
      · exact hi
      · intro j _ hji
        rw [hother {j} (by simpa using hji)]
        simp
      · simp
    obtain ⟨j, hj⟩ :=
      eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one f hlevel
    refine ⟨{j}, by simp, ?_⟩
    rcases hj with rfl | rfl
    · intro x y hxy
      exact hxy j (by simp)
    · intro x y hxy
      simp only [Pi.neg_apply, dictator]
      rw [hxy j (by simp)]
  · push Not at hexists
    have hsingle (i : Fin n) : fourierCoeff f.toReal {i} = 0 := by
      have hsq := (singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtMost_one_eq_one
        f hweight i).resolve_right (hexists i)
      exact sq_eq_zero_iff.mp hsq
    have hnonempty (S : Finset (Fin n)) (hS : S ≠ ∅) :
        fourierCoeff f.toReal S = 0 := by
      by_cases hcard : S.card ≤ 1
      · have hpos : 0 < S.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
        have hone : S.card = 1 := by omega
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
        exact hsingle i
      · exact fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one
          f hweight S hcard
    have hconstant (x : {−1,1}^[n]) :
        f.toReal x = fourierCoeff f.toReal ∅ := by
      rw [fourier_expansion f.toReal x]
      rw [Finset.sum_eq_single ∅]
      · simp [monomial]
      · intro S _ hS
        rw [hnonempty S hS]
        simp
      · simp
    refine ⟨∅, by simp, ?_⟩
    intro x y _
    apply signValue_injective
    change f.toReal x = f.toReal y
    rw [hconstant x, hconstant y]


end FABL
