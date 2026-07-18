/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.SocialChoiceFunctions.MayTheorem
public import FABL.Chapter05.LinearThresholdFunctions
public import Mathlib.Algebra.BigOperators.Sym

/-!
# Threshold circuits

Book item: Exercise 5.12.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A real-valued Boolean function is a constant plus a list of linear threshold functions. -/
def IsRealSumOfLinearThresholds
    (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ (g : Fin s → BooleanFunction n) (c : ℝ),
    (∀ i, IsLinearThreshold (g i)) ∧
      ∀ x, f.toReal x = c + ∑ i, (g i).toReal x

/-- A real-valued Boolean function is a constant plus at most `s` linear threshold functions. -/
def HasRealSumOfLinearThresholdsSizeAtMost
    (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ t ≤ s, IsRealSumOfLinearThresholds f t

/-- An outer affine threshold gate applied to a list of linear threshold functions. -/
def IsThresholdOfThresholds
    (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ (g : Fin s → BooleanFunction n),
    (∀ i, IsLinearThreshold (g i)) ∧
      ∃ (a₀ : ℝ) (a : Fin s → ℝ),
        ∀ x, f x =
          thresholdSign (a₀ + ∑ i, a i * signValue (g i x))

/-- A threshold-of-thresholds circuit with at most `s` inner gates. -/
def HasThresholdOfThresholdsSizeAtMost
    (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ t ≤ s, IsThresholdOfThresholds f t

/-- A threshold-of-parities circuit is exactly a polynomial threshold representation whose
Fourier support has the stated cardinality bound. -/
def IsThresholdOfParities
    (f : BooleanFunction n) (s : ℕ) : Prop :=
  ∃ p : {−1,1}^[n] → ℝ,
    IsPolynomialThresholdRepresentation f p ∧ polynomialSparsity p ≤ s

private def positiveCoordinateCountOn
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℕ :=
  (S.filter fun i ↦ x i = 1).card

private theorem positiveCoordinateCountOn_le
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    positiveCoordinateCountOn S x ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

private theorem sum_signValue_on_eq
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    (∑ i ∈ S, signValue (x i)) =
      2 * positiveCoordinateCountOn S x - S.card := by
  classical
  simp_rw [signValue_eq_ite]
  simp_rw [show ∀ i : Fin n,
      (if x i = 1 then (1 : ℝ) else -1) =
        2 * (if x i = 1 then (1 : ℝ) else 0) - 1 by
    intro i
    split <;> norm_num]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [positiveCoordinateCountOn]

private def countThresholdGate
    (S : Finset (Fin n)) (k : ℕ) : BooleanFunction n :=
  fun x ↦ if k ≤ positiveCoordinateCountOn S x then 1 else -1

private theorem countThresholdGate_isLinearThreshold
    (S : Finset (Fin n)) (k : ℕ) :
    IsLinearThreshold (countThresholdGate S k) := by
  refine ⟨(S.card : ℝ) - 2 * k + 1,
    fun i ↦ if i ∈ S then 1 else 0, ?_⟩
  intro x
  have hsum :
      (∑ i : Fin n, (if i ∈ S then (1 : ℝ) else 0) * signValue (x i)) =
        ∑ i ∈ S, signValue (x i) := by
    simp
  rw [hsum, sum_signValue_on_eq]
  by_cases hk : k ≤ positiveCoordinateCountOn S x
  · rw [countThresholdGate, if_pos hk]
    symm
    apply thresholdSign_of_nonneg
    have hkR : (k : ℝ) ≤ positiveCoordinateCountOn S x := by
      exact_mod_cast hk
    linarith
  · rw [countThresholdGate, if_neg hk]
    symm
    apply thresholdSign_of_neg
    have hkSucc : positiveCoordinateCountOn S x + 1 ≤ k :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hk)
    have hkSuccR :
        (positiveCoordinateCountOn S x : ℝ) + 1 ≤ k := by
      exact_mod_cast hkSucc
    linarith

private def negCountThresholdGate
    (S : Finset (Fin n)) (k : ℕ) : BooleanFunction n :=
  fun x ↦ if k ≤ positiveCoordinateCountOn S x then -1 else 1

private theorem negCountThresholdGate_isLinearThreshold
    (S : Finset (Fin n)) (k : ℕ) :
    IsLinearThreshold (negCountThresholdGate S k) := by
  refine ⟨-((S.card : ℝ) - 2 * k + 1),
    fun i ↦ if i ∈ S then -1 else 0, ?_⟩
  intro x
  have hsum :
      (∑ i : Fin n, (if i ∈ S then (-1 : ℝ) else 0) * signValue (x i)) =
        -(∑ i ∈ S, signValue (x i)) := by
    simp [Finset.sum_neg_distrib]
  rw [hsum, sum_signValue_on_eq]
  by_cases hk : k ≤ positiveCoordinateCountOn S x
  · rw [negCountThresholdGate, if_pos hk]
    symm
    apply thresholdSign_of_neg
    have hkR : (k : ℝ) ≤ positiveCoordinateCountOn S x := by
      exact_mod_cast hk
    linarith
  · rw [negCountThresholdGate, if_neg hk]
    symm
    apply thresholdSign_of_nonneg
    have hkSucc : positiveCoordinateCountOn S x + 1 ≤ k :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hk)
    have hkSuccR :
        (positiveCoordinateCountOn S x : ℝ) + 1 ≤ k := by
      exact_mod_cast hkSucc
    linarith

private def constantThresholdGate (b : Sign) : BooleanFunction n :=
  fun _ ↦ b

private theorem constantThresholdGate_isLinearThreshold
    (b : Sign) :
    IsLinearThreshold (constantThresholdGate (n := n) b) := by
  rcases Int.units_eq_one_or b with rfl | rfl
  · refine ⟨1, fun _ ↦ 0, ?_⟩
    intro x
    simp [constantThresholdGate]
  · refine ⟨-1, fun _ ↦ 0, ?_⟩
    intro x
    simp [constantThresholdGate]

private def profileMainGate
    (S : Finset (Fin n)) (a : ℕ → Sign) (i : Fin n) :
    BooleanFunction n :=
  if a (i + 1) = a i then constantThresholdGate 1
  else if a (i + 1) = 1 then countThresholdGate S (i + 1)
  else negCountThresholdGate S (i + 1)

private def profileCorrectionGate
    (a : ℕ → Sign) (i : Fin n) :
    BooleanFunction n :=
  if a (i + 1) = a i then constantThresholdGate (-1)
  else constantThresholdGate (a (i + 1))

private theorem profileMainGate_isLinearThreshold
    (S : Finset (Fin n)) (a : ℕ → Sign) (i : Fin n) :
    IsLinearThreshold (profileMainGate S a i) := by
  rw [profileMainGate]
  split
  · exact constantThresholdGate_isLinearThreshold 1
  · split
    · exact countThresholdGate_isLinearThreshold S (i + 1)
    · exact negCountThresholdGate_isLinearThreshold S (i + 1)

private theorem profileCorrectionGate_isLinearThreshold
    (a : ℕ → Sign) (i : Fin n) :
    IsLinearThreshold (profileCorrectionGate (n := n) a i) := by
  rw [profileCorrectionGate]
  split
  · exact constantThresholdGate_isLinearThreshold (-1)
  · exact constantThresholdGate_isLinearThreshold _

private theorem profileGate_pair_value
    (S : Finset (Fin n)) (a : ℕ → Sign) (i : Fin n)
    (x : {−1,1}^[n]) :
    (profileMainGate S a i).toReal x +
        (profileCorrectionGate a i).toReal x =
      if (i : ℕ) < positiveCoordinateCountOn S x then
        signValue (a (i + 1)) - signValue (a i)
      else 0 := by
  by_cases heq : a (i + 1) = a i
  · rw [profileMainGate, if_pos heq, profileCorrectionGate, if_pos heq]
    simp [constantThresholdGate, BooleanFunction.toReal, heq]
  · rw [profileMainGate, if_neg heq, profileCorrectionGate, if_neg heq]
    by_cases hj : a (i + 1) = 1
    · have hi : a i = -1 := by
        rcases Int.units_eq_one_or (a i) with hi | hi
        · exact (heq (hj.trans hi.symm)).elim
        · exact hi
      rw [if_pos hj]
      simp only [BooleanFunction.toReal]
      by_cases hcount : (i : ℕ) < positiveCoordinateCountOn S x
      · have hle : (i : ℕ) + 1 ≤ positiveCoordinateCountOn S x :=
          Nat.lt_iff_add_one_le.mp hcount
        rw [countThresholdGate, if_pos hle]
        norm_num [constantThresholdGate, hi, hj, hcount]
      · have hle : ¬(i : ℕ) + 1 ≤ positiveCoordinateCountOn S x := by
          simpa only [Nat.lt_iff_add_one_le] using hcount
        rw [countThresholdGate, if_neg hle]
        norm_num [constantThresholdGate, hj, hcount]
    · have hj' : a (i + 1) = -1 := by
        rcases Int.units_eq_one_or (a (i + 1)) with h | h
        · exact (hj h).elim
        · exact h
      have hi : a i = 1 := by
        rcases Int.units_eq_one_or (a i) with h | h
        · exact h
        · exact (heq (hj'.trans h.symm)).elim
      rw [if_neg hj]
      simp only [BooleanFunction.toReal]
      by_cases hcount : (i : ℕ) < positiveCoordinateCountOn S x
      · have hle : (i : ℕ) + 1 ≤ positiveCoordinateCountOn S x :=
          Nat.lt_iff_add_one_le.mp hcount
        rw [negCountThresholdGate, if_pos hle]
        norm_num [constantThresholdGate, hi, hj', hcount]
      · have hle : ¬(i : ℕ) + 1 ≤ positiveCoordinateCountOn S x := by
          simpa only [Nat.lt_iff_add_one_le] using hcount
        rw [negCountThresholdGate, if_neg hle]
        norm_num [constantThresholdGate, hj', hcount]

private theorem sum_profileGate_pair
    (S : Finset (Fin n)) (a : ℕ → Sign)
    (x : {−1,1}^[n]) :
    (∑ i : Fin n,
        ((profileMainGate S a i).toReal x +
          (profileCorrectionGate a i).toReal x)) =
      signValue (a (positiveCoordinateCountOn S x)) - signValue (a 0) := by
  simp_rw [profileGate_pair_value]
  let r := positiveCoordinateCountOn S x
  have hfin :
      (∑ i : Fin n,
          if (i : ℕ) < r then
            signValue (a ((i : ℕ) + 1)) - signValue (a (i : ℕ))
          else 0) =
        ∑ i ∈ Finset.range n,
          if i < r then signValue (a (i + 1)) - signValue (a i) else 0 :=
    by
      simpa only using
        (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦
            if i < r then signValue (a (i + 1)) - signValue (a i) else 0) n)
  rw [hfin]
  have hScard : S.card ≤ n := by
    simpa using S.card_le_univ
  have hr : r ≤ n :=
    (positiveCoordinateCountOn_le S x).trans hScard
  have hfilter :
      (Finset.range n).filter (fun i ↦ i < r) = Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  exact Finset.sum_range_sub (fun k ↦ signValue (a k)) r

private def profileDecompositionGates
    (S : Finset (Fin n)) (a : ℕ → Sign) :
    Fin (n * 2) → BooleanFunction n :=
  fun j ↦
    let ij := (finProdFinEquiv (m := n) (n := 2)).symm j
    if ij.2 = 0 then profileMainGate S a ij.1
    else profileCorrectionGate a ij.1

private theorem sum_profileDecompositionGates
    (S : Finset (Fin n)) (a : ℕ → Sign)
    (x : {−1,1}^[n]) :
    (∑ j : Fin (n * 2), (profileDecompositionGates S a j).toReal x) =
      signValue (a (positiveCoordinateCountOn S x)) - signValue (a 0) := by
  rw [show (∑ j : Fin (n * 2), (profileDecompositionGates S a j).toReal x) =
      ∑ ij : Fin n × Fin 2,
        (profileDecompositionGates S a (finProdFinEquiv ij)).toReal x by
    symm
    exact Equiv.sum_comp finProdFinEquiv
      (fun j ↦ (profileDecompositionGates S a j).toReal x)]
  rw [Fintype.sum_prod_type]
  simpa [profileDecompositionGates, Fin.sum_univ_two] using
    sum_profileGate_pair S a x

private theorem profileDecompositionGates_isLinearThreshold
    (S : Finset (Fin n)) (a : ℕ → Sign) (j : Fin (n * 2)) :
    IsLinearThreshold (profileDecompositionGates S a j) := by
  let ij := (finProdFinEquiv (m := n) (n := 2)).symm j
  rw [profileDecompositionGates]
  split
  · exact profileMainGate_isLinearThreshold S a ij.1
  · exact profileCorrectionGate_isLinearThreshold a ij.1

private theorem isRealSumOfLinearThresholds_of_count_profile
    (S : Finset (Fin n)) (a : ℕ → Sign) (f : BooleanFunction n)
    (hf : ∀ x, f x = a (positiveCoordinateCountOn S x)) :
    IsRealSumOfLinearThresholds f (n * 2) := by
  refine ⟨profileDecompositionGates S a, signValue (a 0),
    profileDecompositionGates_isLinearThreshold S a, ?_⟩
  intro x
  rw [sum_profileDecompositionGates]
  change signValue (f x) =
    signValue (a 0) +
      (signValue (a (positiveCoordinateCountOn S x)) - signValue (a 0))
  rw [hf]
  ring

/-- Exercise 5.12(a): a symmetric Boolean function is, as a real-valued function, a constant
plus at most `2n` linear threshold functions. -/
theorem symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul
    (f : BooleanFunction n) (hf : IsSymmetric f) :
    HasRealSumOfLinearThresholdsSizeAtMost f (2 * n) := by
  let a : ℕ → Sign := fun k ↦ f (canonicalCountInput n k)
  have hprofile (x : {−1,1}^[n]) :
      f x = a (positiveCoordinateCountOn Finset.univ x) := by
    apply (isSymmetric_iff_eq_of_positiveCoordinateCount_eq f).mp hf
    change positiveCoordinateCount x =
      positiveCoordinateCount
        (canonicalCountInput n (positiveCoordinateCount x))
    rw [positiveCoordinateCount_canonicalCountInput, min_eq_right]
    exact positiveCoordinateCount_le x
  refine ⟨n * 2, by omega, ?_⟩
  exact isRealSumOfLinearThresholds_of_count_profile Finset.univ a f hprofile

private theorem isThresholdOfThresholds_of_isRealSumOfLinearThresholds
    (f : BooleanFunction n) (s : ℕ)
    (h : IsRealSumOfLinearThresholds f s) :
    IsThresholdOfThresholds f s := by
  rcases h with ⟨g, c, hg, hsum⟩
  refine ⟨g, hg, c, fun _ ↦ 1, ?_⟩
  intro x
  have hx := hsum x
  simp only [BooleanFunction.toReal, one_mul] at hx ⊢
  rw [← hx]
  rcases Int.units_eq_one_or (f x) with hfx | hfx <;>
    simp [hfx]

private def negativeCoordinateCountOn
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : ℕ :=
  (S.filter fun i ↦ x i = -1).card

private theorem positiveCoordinateCountOn_add_negativeCoordinateCountOn
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    positiveCoordinateCountOn S x + negativeCoordinateCountOn S x = S.card := by
  rw [positiveCoordinateCountOn, negativeCoordinateCountOn]
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := S) (fun i ↦ x i = 1)
  have hfilter :
      S.filter (fun i ↦ ¬x i = 1) =
        S.filter (fun i ↦ x i = -1) := by
    ext i
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi]
  rw [← hfilter]
  exact hpartition

private theorem parityFunction_eq_neg_one_pow_negativeCoordinateCountOn
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    parityFunction S x =
      (-1 : Sign) ^ negativeCoordinateCountOn S x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [parityFunction, negativeCoordinateCountOn]
  | @insert i S hi ih =>
      rcases Int.units_eq_one_or (x i) with hxi | hxi
      · rw [parityFunction, Finset.prod_insert hi]
        change x i * parityFunction S x =
          (-1 : Sign) ^ negativeCoordinateCountOn (insert i S) x
        rw [ih, hxi, one_mul]
        congr 1
        have hnot : x i ≠ -1 := by
          rw [hxi]
          norm_num
        simp only [negativeCoordinateCountOn, Finset.filter_insert,
          if_neg hnot]
      · rw [parityFunction, Finset.prod_insert hi]
        change x i * parityFunction S x =
          (-1 : Sign) ^ negativeCoordinateCountOn (insert i S) x
        rw [ih, hxi]
        have hcount :
            negativeCoordinateCountOn (insert i S) x =
              negativeCoordinateCountOn S x + 1 := by
          have hiFilter :
              i ∉ S.filter fun j ↦ x j = -1 := by
            intro hi'
            exact hi (Finset.filter_subset _ _ hi')
          simp only [negativeCoordinateCountOn, Finset.filter_insert,
            if_pos hxi, Finset.card_insert_of_notMem hiFilter]
        rw [hcount]
        change (-1 : Sign) * (-1 : Sign) ^ negativeCoordinateCountOn S x =
          (-1 : Sign) ^ Nat.succ (negativeCoordinateCountOn S x)
        calc
          (-1 : Sign) * (-1 : Sign) ^ negativeCoordinateCountOn S x =
              (-1 : Sign) ^ negativeCoordinateCountOn S x * (-1 : Sign) :=
            mul_comm _ _
          _ = (-1 : Sign) ^ Nat.succ (negativeCoordinateCountOn S x) := by
            exact (pow_succ (-1 : Sign)
              (negativeCoordinateCountOn S x)).symm

private def parityCountProfile
    (S : Finset (Fin n)) (k : ℕ) : Sign :=
  (-1 : Sign) ^ (S.card - k)

private theorem parityFunction_eq_parityCountProfile
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    parityFunction S x =
      parityCountProfile S (positiveCoordinateCountOn S x) := by
  rw [parityFunction_eq_neg_one_pow_negativeCoordinateCountOn]
  have hcount :=
    positiveCoordinateCountOn_add_negativeCoordinateCountOn S x
  have hnegative :
      negativeCoordinateCountOn S x =
        S.card - positiveCoordinateCountOn S x := by
    omega
  rw [hnegative]
  rfl

/-- Every parity has the real LTF-sum decomposition used in Exercise 5.12(b). -/
theorem parityFunction_isRealSumOfLinearThresholds
    (S : Finset (Fin n)) :
    IsRealSumOfLinearThresholds (parityFunction S) (n * 2) :=
  isRealSumOfLinearThresholds_of_count_profile
    S (parityCountProfile S) (parityFunction S)
    (parityFunction_eq_parityCountProfile S)

private theorem fourier_expansion_over_support
    (p : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    (∑ S : ↥(fourierSupport p),
        fourierCoeff p S.1 * monomial S.1 x) = p x := by
  classical
  calc
    (∑ S : ↥(fourierSupport p),
        fourierCoeff p S.1 * monomial S.1 x) =
        ∑ S ∈ fourierSupport p,
          fourierCoeff p S * monomial S x := by
      symm
      exact Finset.sum_subtype (fourierSupport p)
        (fun S ↦ Iff.rfl) (fun S ↦ fourierCoeff p S * monomial S x)
    _ = ∑ S : Finset (Fin n), fourierCoeff p S * monomial S x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hzero : fourierCoeff p S = 0 := by
        by_contra hne
        exact hS ((mem_fourierSupport p S).2 hne)
      simp [hzero]
    _ = p x := (fourier_expansion p x).symm

private theorem polynomialThresholdRepresentation_isThresholdOfThresholds
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p) :
    IsThresholdOfThresholds f
      ((fourierSupport p).card * (n * 2)) := by
  classical
  let e :
      (↥(fourierSupport p) × Fin (n * 2)) ≃
        Fin ((fourierSupport p).card * (n * 2)) :=
    Fintype.equivFinOfCardEq (by
      simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin])
  let g :
      Fin ((fourierSupport p).card * (n * 2)) → BooleanFunction n :=
    fun j ↦
      let Sj := e.symm j
      profileDecompositionGates Sj.1.1 (parityCountProfile Sj.1.1) Sj.2
  let a :
      Fin ((fourierSupport p).card * (n * 2)) → ℝ :=
    fun j ↦ fourierCoeff p (e.symm j).1.1
  refine ⟨g, ?_, ∑ S : ↥(fourierSupport p),
      fourierCoeff p S.1 * signValue (parityCountProfile S.1 0), a, ?_⟩
  · intro j
    exact profileDecompositionGates_isLinearThreshold
      (e.symm j).1.1 (parityCountProfile (e.symm j).1.1) (e.symm j).2
  · intro x
    rw [hrep x]
    congr 1
    have hgateReindex :
        (∑ j : Fin ((fourierSupport p).card * (n * 2)),
            a j * signValue (g j x)) =
          ∑ Sj : ↥(fourierSupport p) × Fin (n * 2),
            fourierCoeff p Sj.1.1 *
              signValue
                (profileDecompositionGates Sj.1.1
                  (parityCountProfile Sj.1.1) Sj.2 x) := by
      symm
      simpa only [a, g, Equiv.symm_apply_apply] using
        (Equiv.sum_comp e
          (fun j ↦ a j * signValue (g j x)))
    rw [hgateReindex, Fintype.sum_prod_type]
    symm
    calc
      (∑ S : ↥(fourierSupport p),
            fourierCoeff p S.1 *
              signValue (parityCountProfile S.1 0)) +
          ∑ S : ↥(fourierSupport p),
            ∑ j : Fin (n * 2),
              fourierCoeff p S.1 *
                signValue
                  (profileDecompositionGates S.1
                    (parityCountProfile S.1) j x) =
          ∑ S : ↥(fourierSupport p),
            fourierCoeff p S.1 *
              (signValue (parityCountProfile S.1 0) +
                ∑ j : Fin (n * 2),
                  signValue
                    (profileDecompositionGates S.1
                      (parityCountProfile S.1) j x)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro S _
        rw [← Finset.mul_sum]
        ring
      _ = ∑ S : ↥(fourierSupport p),
          fourierCoeff p S.1 * monomial S.1 x := by
        apply Finset.sum_congr rfl
        intro S _
        congr 1
        change signValue (parityCountProfile S.1 0) +
            ∑ j : Fin (n * 2),
              (profileDecompositionGates S.1
                (parityCountProfile S.1) j).toReal x =
          monomial S.1 x
        rw [sum_profileDecompositionGates]
        have hparity :=
          congrArg signValue (parityFunction_eq_parityCountProfile S.1 x)
        have hmonomial := congrFun (parityFunction_toReal S.1) x
        simp only [BooleanFunction.toReal] at hmonomial
        rw [← hmonomial, hparity]
        ring
      _ = p x := fourier_expansion_over_support p x

/-- Exercise 5.12(b): a polynomial threshold representation with sparsity `s` gives a
threshold-of-thresholds circuit of size at most `2ns`. -/
theorem polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p) :
    HasThresholdOfThresholdsSizeAtMost f
      (2 * n * polynomialSparsity p) := by
  refine ⟨(fourierSupport p).card * (n * 2), ?_, ?_⟩
  · simp only [polynomialSparsity]
    simp [Nat.mul_left_comm, Nat.mul_comm]
  · exact polynomialThresholdRepresentation_isThresholdOfThresholds f p hrep

/-- Exercise 5.12(b), in circuit language. -/
theorem thresholdOfParities_hasThresholdOfThresholdsSizeAtMost
    (f : BooleanFunction n) (s : ℕ)
    (h : IsThresholdOfParities f s) :
    HasThresholdOfThresholdsSizeAtMost f (2 * n * s) := by
  rcases h with ⟨p, hrep, hs⟩
  rcases polynomialThresholdRepresentation_hasThresholdOfThresholdsSizeAtMost
    f p hrep with ⟨t, ht, hcircuit⟩
  exact ⟨t, ht.trans (Nat.mul_le_mul_left (2 * n) hs), hcircuit⟩

/-- The quadratic form underlying the complete quadratic function. -/
def completeQuadraticBit (x : 𝔽₂^[n]) : 𝔽₂ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * x j

private def completeQuadraticPolar (x z : 𝔽₂^[n]) : 𝔽₂ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (x i * z j + z i * x j)

private theorem completeQuadraticBit_add (x z : 𝔽₂^[n]) :
    completeQuadraticBit (x + z) =
      completeQuadraticBit x + completeQuadraticBit z + completeQuadraticPolar x z := by
  simp only [completeQuadraticBit, completeQuadraticPolar, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

private def completeQuadraticPolarFrequency (z : 𝔽₂^[n]) : 𝔽₂^[n] :=
  fun i ↦ ∑ j ∈ ({i} : Finset (Fin n))ᶜ, z j

private theorem completeQuadraticPolar_eq_dotProduct
    (x z : 𝔽₂^[n]) :
    completeQuadraticPolar x z =
      f₂DotProduct (completeQuadraticPolarFrequency z) x := by
  classical
  rw [completeQuadraticPolar, f₂DotProduct, dotProduct]
  simp only [completeQuadraticPolarFrequency, Finset.sum_add_distrib]
  have hfirst :
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * z j) =
        ∑ i : Fin n, (∑ j ∈ Finset.Ioi i, z j) * x i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    ring
  have hsecond :
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, z i * x j) =
        ∑ j : Fin n, (∑ i ∈ Finset.Iio j, z i) * x j := by
    calc
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, z i * x j) =
          ∑ i : Fin n, ∑ j : Fin n, if i < j then z i * x j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _
          rfl
      _ = ∑ j : Fin n, ∑ i : Fin n, if i < j then z i * x j else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (∑ i ∈ Finset.Iio j, z i) * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_filter]
        have hfilter :
            (Finset.univ.filter fun i : Fin n ↦ i < j) = Finset.Iio j := by
          ext i
          simp
        rw [hfilter, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * z j) +
          ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, z i * x j =
        ∑ i : Fin n,
          ((∑ j ∈ Finset.Ioi i, z j) + ∑ j ∈ Finset.Iio i, z j) * x i := by
      rw [hfirst, hsecond, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin n, (∑ j ∈ ({i} : Finset (Fin n))ᶜ, z j) * x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_disjUnion (Finset.disjoint_Ioi_Iio i),
        Finset.Ioi_disjUnion_Iio]

private theorem completeQuadraticPolarFrequency_eq_zero_of_even
    (hn : Even n) {z : 𝔽₂^[n]}
    (hz : completeQuadraticPolarFrequency z = 0) :
    z = 0 := by
  classical
  let total : 𝔽₂ := ∑ i, z i
  have hzTotal (i : Fin n) : z i = total := by
    have hi := congrFun hz i
    change (∑ j ∈ ({i} : Finset (Fin n))ᶜ, z j) = 0 at hi
    have huniv :
        (∑ j : Fin n, z j) =
          z i + ∑ j ∈ ({i} : Finset (Fin n))ᶜ, z j := by
      rw [← Finset.sum_add_sum_compl ({i} : Finset (Fin n))]
      simp
    rw [hi, add_zero] at huniv
    simpa only [total] using huniv.symm
  have htotal : total = 0 := by
    calc
      total = ∑ i : Fin n, z i := rfl
      _ = ∑ i : Fin n, total := by
        apply Finset.sum_congr rfl
        intro i _
        exact hzTotal i
      _ = n • total := by simp
      _ = 0 := by
        rcases hn with ⟨k, rfl⟩
        rw [add_nsmul]
        exact CharTwo.add_self_eq_zero _
  funext i
  rw [hzTotal i, htotal]
  rfl

/-- The real-valued complete quadratic function on the binary cube. -/
def completeQuadratic (n : ℕ) : 𝔽₂^[n] → ℝ :=
  realSignEncodedFunction completeQuadraticBit

/-- The sign-valued complete quadratic function on the sign cube. -/
def completeQuadraticBoolean (n : ℕ) : BooleanFunction n :=
  fun x ↦ signEncode (completeQuadraticBit ((binaryCubeSignEquiv n).symm x))

private def sym2CoordinateProduct
    (x : 𝔽₂^[n]) : Sym2 (Fin n) → 𝔽₂ :=
  Sym2.lift ⟨fun i j ↦ x i * x j, fun i j ↦ mul_comm (x i) (x j)⟩

private theorem completeQuadraticBit_eq_sym2_sum
    (x : 𝔽₂^[n]) :
    completeQuadraticBit x =
      ∑ ij ∈ (Finset.univ : Finset (Fin n)).sym2 with ¬ij.IsDiag,
        sym2CoordinateProduct x ij := by
  rw [Finset.sum_sym2_filter_not_isDiag, completeQuadraticBit]
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * x j) =
        ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rfl
    _ = ∑ ij : Fin n × Fin n,
        if ij.1 < ij.2 then x ij.1 * x ij.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ ij ∈
          (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ij ↦ ij.1 < ij.2),
        sym2CoordinateProduct x s(ij.1, ij.2) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ij _
      by_cases hij : ij.1 < ij.2
      · simp [sym2CoordinateProduct]
      · rfl
    _ = ∑ ij ∈
          (Finset.univ : Finset (Fin n)).offDiag.filter
            (fun ij ↦ ij.1 < ij.2),
        sym2CoordinateProduct x s(ij.1, ij.2) := by
      congr 1
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_offDiag,
        true_and]
      constructor
      · intro hij
        exact ⟨hij.ne, hij⟩
      · exact fun hij ↦ hij.2

private theorem completeQuadraticBit_comp_perm
    (π : Equiv.Perm (Fin n)) (x : 𝔽₂^[n]) :
    completeQuadraticBit (fun i ↦ x (π i)) = completeQuadraticBit x := by
  let e : Sym2 (Fin n) ≃ Sym2 (Fin n) := {
    toFun := Sym2.map π
    invFun := Sym2.map π.symm
    left_inv := fun q ↦ by
      change (Sym2.map π.symm ∘ Sym2.map π) q = q
      rw [← Sym2.map_comp]
      simp
    right_inv := fun q ↦ by
      change (Sym2.map π ∘ Sym2.map π.symm) q = q
      rw [← Sym2.map_comp]
      simp
  }
  rw [completeQuadraticBit_eq_sym2_sum,
    completeQuadraticBit_eq_sym2_sum]
  refine Finset.sum_equiv e ?_ ?_
  · intro q
    simp only [Finset.mem_filter, Finset.mem_sym2_iff,
      Finset.mem_univ, implies_true, true_and]
    change ¬q.IsDiag ↔ ¬(Sym2.map π q).IsDiag
    exact not_congr (Sym2.isDiag_map π.injective).symm
  · intro q hq
    change sym2CoordinateProduct (fun i ↦ x (π i)) q =
      sym2CoordinateProduct x (Sym2.map π q)
    exact (Sym2.lift_map_apply
      ⟨fun i j ↦ x i * x j, fun i j ↦ mul_comm (x i) (x j)⟩ q).symm

/-- The binary-cube form of `CQ` is the sign of the sum of all quadratic monomials. -/
theorem completeQuadratic_apply (x : 𝔽₂^[n]) :
    completeQuadratic n x = binarySign (completeQuadraticBit x) := by
  rw [completeQuadratic, realSignEncodedFunction, signEncodedFunction,
    signValue_signEncode_eq_binarySign]

/-- The sign-cube complete quadratic function agrees with its binary formula. -/
theorem completeQuadraticBoolean_binaryCubeSignEquiv (x : 𝔽₂^[n]) :
    completeQuadraticBoolean n (binaryCubeSignEquiv n x) =
      signEncode (completeQuadraticBit x) := by
  simp [completeQuadraticBoolean]

/-- The complete quadratic Boolean function is symmetric. -/
theorem completeQuadraticBoolean_isSymmetric :
    IsSymmetric (completeQuadraticBoolean n) := by
  intro π x
  have hbinary :
      (binaryCubeSignEquiv n).symm (permuteInput π x) =
        fun i ↦ (binaryCubeSignEquiv n).symm x (π i) := by
    funext i
    have hleft :=
      congrFun ((binaryCubeSignEquiv n).apply_symm_apply
        (permuteInput π x)) i
    have hright :=
      congrFun ((binaryCubeSignEquiv n).apply_symm_apply x) (π i)
    rw [binaryCubeSignEquiv_apply, permuteInput] at hleft
    rw [binaryCubeSignEquiv_apply] at hright
    exact binarySignEquiv.injective (hleft.trans hright.symm)
  rw [completeQuadraticBoolean, completeQuadraticBoolean, hbinary,
    completeQuadraticBit_comp_perm]

/-- Exercise 5.12(c): `CQₙ` is computed by a threshold-of-thresholds circuit with at most
`2n` inner gates. -/
theorem completeQuadraticBoolean_hasThresholdOfThresholdsSizeAtMost_two_mul :
    HasThresholdOfThresholdsSizeAtMost
      (completeQuadraticBoolean n) (2 * n) := by
  rcases symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul
    (completeQuadraticBoolean n) completeQuadraticBoolean_isSymmetric with
    ⟨t, ht, hsum⟩
  exact ⟨t, ht,
    isThresholdOfThresholds_of_isRealSumOfLinearThresholds
      (completeQuadraticBoolean n) t hsum⟩

@[simp] private theorem completeQuadraticBit_zero :
    completeQuadraticBit (0 : 𝔽₂^[n]) = 0 := by
  simp [completeQuadraticBit]

@[simp] private theorem completeQuadraticPolarFrequency_zero :
    completeQuadraticPolarFrequency (0 : 𝔽₂^[n]) = 0 := by
  funext i
  simp [completeQuadraticPolarFrequency]

private theorem completeQuadratic_mul_translate
    (y z : 𝔽₂^[n]) :
    completeQuadratic n y * completeQuadratic n (z + y) =
      binarySign (completeQuadraticBit z) *
        vectorWalshCharacter (completeQuadraticPolarFrequency z) y := by
  rw [completeQuadratic_apply, completeQuadratic_apply]
  rw [add_comm z y, completeQuadraticBit_add]
  rw [← AddChar.map_add_eq_mul]
  rw [completeQuadraticPolar_eq_dotProduct, vectorWalshCharacter_apply]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  calc
    completeQuadraticBit y +
          (completeQuadraticBit y + completeQuadraticBit z +
            f₂DotProduct (completeQuadraticPolarFrequency z) y) =
        (completeQuadraticBit y + completeQuadraticBit y) +
          completeQuadraticBit z +
          f₂DotProduct (completeQuadraticPolarFrequency z) y := by
      ac_rfl
    _ = completeQuadraticBit z +
          f₂DotProduct (completeQuadraticPolarFrequency z) y := by
      rw [CharTwo.add_self_eq_zero, zero_add]

private theorem convolution_completeQuadratic_self
    (hn : Even n) (z : 𝔽₂^[n]) :
    convolution (completeQuadratic n) (completeQuadratic n) z =
      if z = 0 then 1 else 0 := by
  rw [convolution_apply_add]
  simp_rw [completeQuadratic_mul_translate]
  rw [← Finset.mul_expect, expect_vectorWalshCharacter]
  by_cases hz : z = 0
  · subst z
    simp
  · have hfrequency : completeQuadraticPolarFrequency z ≠ 0 := by
      intro hzero
      exact hz (completeQuadraticPolarFrequency_eq_zero_of_even hn hzero)
    simp [hz, hfrequency]

private theorem binaryFourierCoeff_singletonIndicator
    (S : Finset (Fin n)) :
    binaryFourierCoeff (fun z : 𝔽₂^[n] ↦ if z = 0 then 1 else 0) S =
      ((2 : ℝ) ^ n)⁻¹ := by
  classical
  rw [binaryFourierCoeff, Fintype.expect_eq_sum_div_card]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hcard : Fintype.card 𝔽₂^[n] = 2 ^ n :=
    Fintype.card_pi_const 𝔽₂ n
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  simp [χ, coordinateSum, div_eq_mul_inv]

private theorem vectorFourierCoeff_completeQuadratic_sq
    (hn : Even n) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (completeQuadratic n) γ ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
  have hconvolution :=
    binaryFourierCoeff_convolution
      (completeQuadratic n) (completeQuadratic n) (f₂Support γ)
  have hfunction :
      convolution (completeQuadratic n) (completeQuadratic n) =
        fun z ↦ if z = 0 then 1 else 0 := by
    funext z
    exact convolution_completeQuadratic_self hn z
  rw [hfunction,
    binaryFourierCoeff_singletonIndicator] at hconvolution
  simpa only [vectorFourierCoeff, pow_two] using hconvolution.symm

/-- In even dimension every Fourier coefficient of the complete quadratic function has
absolute value `2⁻ⁿᐟ²`. -/
theorem abs_vectorFourierCoeff_completeQuadratic
    (hn : Even n) (γ : 𝔽₂^[n]) :
    |vectorFourierCoeff (completeQuadratic n) γ| =
      ((2 : ℝ) ^ (n / 2))⁻¹ := by
  rcases hn with ⟨m, rfl⟩
  have hsquare :=
    vectorFourierCoeff_completeQuadratic_sq
      (n := m + m) ⟨m, rfl⟩ γ
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf]
  have htarget :
      (((2 : ℝ) ^ m)⁻¹) ^ 2 = ((2 : ℝ) ^ (m + m))⁻¹ := by
    rw [pow_two, pow_add, mul_inv_rev]
  have habsSquare :
      |vectorFourierCoeff (completeQuadratic (m + m)) γ| ^ 2 =
        (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
    rw [sq_abs, hsquare, htarget]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp habsSquare with h | h
  · exact h
  · have hleft : 0 ≤ |vectorFourierCoeff (completeQuadratic (m + m)) γ| :=
      abs_nonneg _
    have hright : 0 < ((2 : ℝ) ^ m)⁻¹ := by positivity
    linarith

/-- The sign-cube encoding of `CQ` is the canonical reindexing of its binary-cube form. -/
theorem completeQuadraticBoolean_toReal (n : ℕ) :
    (completeQuadraticBoolean n).toReal =
      binaryFunctionOnSignCube (completeQuadratic n) := by
  funext x
  simp [completeQuadraticBoolean, BooleanFunction.toReal, binaryFunctionOnSignCube,
    completeQuadratic, realSignEncodedFunction, signEncodedFunction]

/-- In even dimension every sign-cube Fourier coefficient of `CQ` has absolute value
`2⁻ⁿᐟ²`. -/
theorem abs_fourierCoeff_completeQuadraticBoolean
    (hn : Even n) (S : Finset (Fin n)) :
    |fourierCoeff (completeQuadraticBoolean n).toReal S| =
      ((2 : ℝ) ^ (n / 2))⁻¹ := by
  let γ : 𝔽₂^[n] := (f₂CubeEquivFinset n).symm S
  have hsupport : f₂Support γ = S :=
    (f₂CubeEquivFinset n).apply_symm_apply S
  have hcoeff := abs_vectorFourierCoeff_completeQuadratic hn γ
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube, hsupport,
    ← completeQuadraticBoolean_toReal] at hcoeff
  exact hcoeff

private theorem pow_two_half_le_polynomialSparsity_completeQuadraticBoolean
    (hn : Even n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation (completeQuadraticBoolean n) p)
    (hp : p ≠ 0) :
    2 ^ (n / 2) ≤ polynomialSparsity p := by
  have hmass :=
    one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation
      (completeQuadraticBoolean n) p (fourierSupport p) hrep hp (Subset.rfl)
  simp_rw [abs_fourierCoeff_completeQuadraticBoolean hn] at hmass
  rw [Finset.sum_const, nsmul_eq_mul] at hmass
  change 1 ≤
    (polynomialSparsity p : ℝ) * ((2 : ℝ) ^ (n / 2))⁻¹ at hmass
  have hpowNonneg : 0 ≤ (2 : ℝ) ^ (n / 2) := by positivity
  have hcancel :
      ((2 : ℝ) ^ (n / 2))⁻¹ * (2 : ℝ) ^ (n / 2) = 1 := by
    exact inv_mul_cancel₀ (by positivity)
  have hreal :
      (2 : ℝ) ^ (n / 2) ≤ polynomialSparsity p := by
    calc
      (2 : ℝ) ^ (n / 2) =
          1 * (2 : ℝ) ^ (n / 2) := by ring
      _ ≤ ((polynomialSparsity p : ℝ) *
            ((2 : ℝ) ^ (n / 2))⁻¹) *
          (2 : ℝ) ^ (n / 2) :=
        mul_le_mul_of_nonneg_right hmass hpowNonneg
      _ = polynomialSparsity p := by
        rw [mul_assoc, hcancel, mul_one]
  exact_mod_cast hreal

private theorem completeQuadraticBoolean_ne_one_of_pos_even
    (hn : Even n) (hnPos : 0 < n) :
    completeQuadraticBoolean n ≠ 1 := by
  let i : Fin n := ⟨0, hnPos⟩
  intro hconstant
  have hzero :
      fourierCoeff (completeQuadraticBoolean n).toReal {i} = 0 := by
    rw [hconstant]
    simp [BooleanFunction.toReal, fourierCoeff, expect_monomial]
  have hflat :=
    abs_fourierCoeff_completeQuadraticBoolean hn ({i} : Finset (Fin n))
  rw [hzero, abs_zero] at hflat
  have hpositive : 0 < ((2 : ℝ) ^ (n / 2))⁻¹ := by positivity
  linarith

/-- Exercise 5.12(d) in the book's positive even-dimensional regime. The positivity
hypothesis excludes the degenerate constant function `CQ₀ = 1`, whose zero polynomial is
a threshold representation. -/
theorem pow_two_half_le_polynomialSparsity_completeQuadraticBoolean_of_pos
    (hn : Even n) (hnPos : 0 < n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation (completeQuadraticBoolean n) p) :
    2 ^ (n / 2) ≤ polynomialSparsity p := by
  apply pow_two_half_le_polynomialSparsity_completeQuadraticBoolean hn p hrep
  intro hp
  apply completeQuadraticBoolean_ne_one_of_pos_even hn hnPos
  funext x
  have hx := hrep x
  rw [hp] at hx
  simpa [thresholdSign] using hx

/-- Exercise 5.12(d), in threshold-of-parities circuit language. -/
theorem pow_two_half_le_thresholdOfParitiesSize_completeQuadraticBoolean
    (hn : Even n) (hnPos : 0 < n) (s : ℕ)
    (h : IsThresholdOfParities (completeQuadraticBoolean n) s) :
    2 ^ (n / 2) ≤ s := by
  rcases h with ⟨p, hrep, hs⟩
  exact
    (pow_two_half_le_polynomialSparsity_completeQuadraticBoolean_of_pos
      hn hnPos p hrep).trans hs

end FABL
