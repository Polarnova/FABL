/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.SparsePolynomialApproximation
import FABL.Chapter03.SubspacesAndDecisionTrees.DecisionTrees

/-!
# Sparse polynomial thresholds for DNF formulas

Book item: Exercise 5.13.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

open F₂DecisionTree

namespace DNFTerm

/-- The zero-one indicator that a DNF term is satisfied. -/
noncomputable def trueIndicator (T : DNFTerm n) (x : {−1,1}^[n]) : ℝ :=
  if T.eval x = -1 then 1 else 0

@[simp] theorem trueIndicator_eq_one_iff (T : DNFTerm n) (x : {−1,1}^[n]) :
    T.trueIndicator x = 1 ↔ T.eval x = -1 := by
  simp [trueIndicator]

theorem trueIndicator_nonneg (T : DNFTerm n) (x : {−1,1}^[n]) :
    0 ≤ T.trueIndicator x := by
  by_cases hx : T.eval x = -1 <;> simp [trueIndicator, hx]

/-- A binary base point realizing the partial sign assignment of a DNF term. -/
noncomputable def binaryBasePoint (T : DNFTerm n) : 𝔽₂^[n] :=
  fun i ↦ if hi : i ∈ T.support then binarySignEquiv.symm (T.requiredAt i hi) else 0

private theorem trueIndicator_binaryCubeSignEquiv (T : DNFTerm n) :
    (fun x : 𝔽₂^[n] ↦ T.trueIndicator (binaryCubeSignEquiv n x)) =
      setIndicator
        (binaryAffineSubspace
          (coordinateZeroSubspace T.support) T.binaryBasePoint : Set 𝔽₂^[n]) := by
  classical
  funext x
  have hcoordinate :
      x ∈ binaryAffineSubspace
          (coordinateZeroSubspace T.support) T.binaryBasePoint ↔
        ∀ i ∈ T.support, x i = T.binaryBasePoint i := by
    rw [mem_binaryAffineSubspace_iff_add_mem, mem_coordinateZeroSubspace_iff]
    constructor
    · intro hx i hi
      have hzero := hx i hi
      change x i + T.binaryBasePoint i = 0 at hzero
      exact (add_eq_zero_iff_eq_neg.mp hzero).trans
        (ZMod.neg_eq_self_mod_two (T.binaryBasePoint i))
    · intro hx i hi
      change x i + T.binaryBasePoint i = 0
      rw [hx i hi]
      exact ZModModule.add_self _
  have hmatch :
      x ∈ binaryAffineSubspace
          (coordinateZeroSubspace T.support) T.binaryBasePoint ↔
        T.eval (binaryCubeSignEquiv n x) = -1 := by
    rw [hcoordinate, T.eval_eq_neg_one_iff_requiredAt]
    constructor
    · intro hx i hi
      have hxi : x i = T.binaryBasePoint i := hx i hi
      rw [binaryCubeSignEquiv_apply, hxi]
      change binarySignEquiv (T.binaryBasePoint i) = T.requiredAt i hi
      simp only [binaryBasePoint, hi, dite_true]
      exact binarySignEquiv.apply_symm_apply _
    · intro hx i hi
      apply binarySignEquiv.injective
      change signEncode (x i) = signEncode (T.binaryBasePoint i)
      rw [← binaryCubeSignEquiv_apply]
      calc
        binaryCubeSignEquiv n x i = T.requiredAt i hi := hx i hi
        _ = signEncode (T.binaryBasePoint i) := by
          change T.requiredAt i hi = binarySignEquiv (T.binaryBasePoint i)
          simp only [binaryBasePoint, hi, dite_true]
          exact (binarySignEquiv.apply_symm_apply _).symm
  by_cases hx : T.eval (binaryCubeSignEquiv n x) = -1
  · rw [trueIndicator, if_pos hx]
    rw [setIndicator, Set.indicator_of_mem (hmatch.mpr hx)]
  · rw [trueIndicator, if_neg hx]
    rw [setIndicator, Set.indicator_of_notMem]
    exact fun hmem ↦ hx (hmatch.mp hmem)

/-- A term's zero-one true indicator has Fourier one-norm exactly one. -/
theorem fourierOneNorm_trueIndicator (T : DNFTerm n) :
    fourierOneNorm T.trueIndicator = 1 := by
  rw [fourierOneNorm_eq_spectralPNorm_one, trueIndicator_binaryCubeSignEquiv]
  exact spectralPNorm_one_setIndicator_binaryAffineSubspace
    (coordinateZeroSubspace T.support) T.binaryBasePoint

end DNFTerm

private theorem fourierCoeff_sum
    {ι : Type*} [Fintype ι]
    (f : ι → {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (∑ i, f i) S = ∑ i, fourierCoeff (f i) S := by
  classical
  unfold fourierCoeff
  calc
    (𝔼 x, (∑ i, f i) x * monomial S x) =
        𝔼 x, ∑ i, f i x * monomial S x := by
      apply Finset.expect_congr rfl
      intro x _
      simp [Finset.sum_mul]
    _ = ∑ i, 𝔼 x, f i x * monomial S x := by
      rw [Finset.expect_sum_comm]

private theorem fourierOneNorm_sum_le
    {ι : Type*} [Fintype ι] (f : ι → {−1,1}^[n] → ℝ) :
    fourierOneNorm (∑ i, f i) ≤ ∑ i, fourierOneNorm (f i) := by
  classical
  unfold fourierOneNorm
  simp_rw [fourierCoeff_sum]
  calc
    (∑ S : Finset (Fin n), |∑ i, fourierCoeff (f i) S|) ≤
        ∑ S : Finset (Fin n), ∑ i, |fourierCoeff (f i) S| := by
      apply Finset.sum_le_sum
      intro S _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ S : Finset (Fin n), |fourierCoeff (f i) S| := by
      rw [Finset.sum_comm]

namespace DNFFormula

/-- The number, as a real-valued cube function, of terms satisfied by an input. -/
noncomputable def satisfiedTermCount (φ : DNFFormula n) (x : {−1,1}^[n]) : ℝ :=
  ∑ i : Fin φ.terms.length, (φ.terms.get i).trueIndicator x

theorem satisfiedTermCount_eq_zero_of_no_satisfied_term
    (φ : DNFFormula n) (x : {−1,1}^[n])
    (hnone : ¬∃ T ∈ φ.terms, T.eval x = -1) :
    φ.satisfiedTermCount x = 0 := by
  unfold satisfiedTermCount
  apply Finset.sum_eq_zero
  intro i _
  have hne : (φ.terms.get i).eval x ≠ -1 := by
    intro hi
    exact hnone ⟨φ.terms.get i, List.get_mem φ.terms i, hi⟩
  rw [DNFTerm.trueIndicator, if_neg]
  change (φ.terms.get i).eval x ≠ -1
  exact hne

theorem one_le_satisfiedTermCount_of_satisfied_term
    (φ : DNFFormula n) (x : {−1,1}^[n]) {T : DNFTerm n}
    (hT : T ∈ φ.terms) (hTx : T.eval x = -1) :
    1 ≤ φ.satisfiedTermCount x := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hT
  unfold satisfiedTermCount
  have hone : (φ.terms.get i).trueIndicator x = 1 := by
    rw [hi]
    exact (DNFTerm.trueIndicator_eq_one_iff T x).2 hTx
  rw [← hone]
  exact Finset.single_le_sum
    (fun j _ ↦ (φ.terms.get j).trueIndicator_nonneg x)
    (Finset.mem_univ i)

/-- The satisfied-term count has Fourier one-norm at most the DNF size. -/
theorem fourierOneNorm_satisfiedTermCount_le (φ : DNFFormula n) :
    fourierOneNorm φ.satisfiedTermCount ≤ (φ.size : ℝ) := by
  let terms : Fin φ.terms.length → {−1,1}^[n] → ℝ :=
    fun i ↦ (φ.terms.get i).trueIndicator
  have hcount : φ.satisfiedTermCount = ∑ i, terms i := by
    funext x
    simp [satisfiedTermCount, terms]
  rw [hcount]
  calc
    fourierOneNorm (∑ i, terms i) ≤ ∑ i, fourierOneNorm (terms i) :=
      fourierOneNorm_sum_le terms
    _ = ∑ _i : Fin φ.terms.length, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (φ.terms.get i).fourierOneNorm_trueIndicator
    _ = (φ.size : ℝ) := by simp [DNFFormula.size]

/-- A DNF is the threshold at one half of its satisfied-term count. -/
theorem toBooleanFunction_eq_thresholdSign_satisfiedTermCount
    (φ : DNFFormula n) (x : {−1,1}^[n]) :
    φ.toBooleanFunction x =
      thresholdSign ((1 : ℝ) / 2 - φ.satisfiedTermCount x) := by
  by_cases htrue : ∃ T ∈ φ.terms, T.eval x = -1
  · have hφ : φ.toBooleanFunction x = -1 :=
      (φ.eval_eq_neg_one_iff x).2 htrue
    obtain ⟨T, hT, hTx⟩ := htrue
    have hcount := φ.one_le_satisfiedTermCount_of_satisfied_term x hT hTx
    rw [hφ, thresholdSign_of_neg]
    linarith
  · have hφne : φ.toBooleanFunction x ≠ -1 := by
      intro hφ
      exact htrue ((φ.eval_eq_neg_one_iff x).1 hφ)
    have hφ : φ.toBooleanFunction x = 1 := by
      rcases Int.units_eq_one_or (φ.toBooleanFunction x) with h | h
      · exact h
      · exact (hφne h).elim
    have hcount := φ.satisfiedTermCount_eq_zero_of_no_satisfied_term x htrue
    rw [hφ, hcount, thresholdSign_of_nonneg]
    norm_num

end DNFFormula

private theorem polynomialSparsity_half_sub_le
    (q : {−1,1}^[n] → ℝ) :
    polynomialSparsity (fun x ↦ (1 : ℝ) / 2 - q x) ≤ polynomialSparsity q + 1 := by
  classical
  have hsupport :
      fourierSupport (fun x ↦ (1 : ℝ) / 2 - q x) ⊆
        insert ∅ (fourierSupport q) := by
    intro S hS
    by_cases hSempt : S = ∅
    · exact Finset.mem_insert.mpr (Or.inl hSempt)
    · apply Finset.mem_insert.mpr
      right
      rw [mem_fourierSupport]
      intro hq
      have hconst :
          fourierCoeff (fun _ : {−1,1}^[n] ↦ (1 : ℝ) / 2) S = 0 := by
        unfold fourierCoeff
        rw [← Finset.mul_expect, expect_monomial, if_neg hSempt]
        ring
      have hshift :
          fourierCoeff (fun x ↦ (1 : ℝ) / 2 - q x) S = 0 := by
        rw [fourierCoeff_sub, hconst, hq]
        ring
      exact (mem_fourierSupport _ S).1 hS hshift
  unfold polynomialSparsity
  exact (Finset.card_le_card hsupport).trans
    (Finset.card_insert_le ∅ (fourierSupport q))

/-- Exercise 5.13(b), formula form: a positive-dimensional DNF has a polynomial threshold
representation of sparsity at most `17 n s²`, where `s` is its number of terms. -/
theorem DNFFormula.exists_polynomialThresholdRepresentation_sparsity_le_quadratic
    (hn : 0 < n) (φ : DNFFormula n) :
    ∃ p : {−1,1}^[n] → ℝ,
      IsPolynomialThresholdRepresentation φ.toBooleanFunction p ∧
        polynomialSparsity p ≤ 17 * n * φ.size ^ 2 := by
  classical
  by_cases hsize : φ.size = 0
  · have hterms : φ.terms = [] := List.eq_nil_of_length_eq_zero hsize
    refine ⟨0, ?_, ?_⟩
    · intro x
      simp [DNFFormula.toBooleanFunction, DNFFormula.eval, hterms, thresholdSign]
    · simp [polynomialSparsity, fourierSupport, fourierCoeff]
  · have hsizePos : 0 < φ.size := Nat.pos_of_ne_zero hsize
    let sampleCount := 16 * n * φ.size ^ 2
    have hnorm :
        fourierOneNorm φ.satisfiedTermCount ≤ (φ.size : ℝ) :=
      φ.fourierOneNorm_satisfiedTermCount_le
    have hsquare :
        fourierOneNorm φ.satisfiedTermCount ^ 2 ≤ (φ.size : ℝ) ^ 2 := by
      nlinarith [fourierOneNorm_nonneg φ.satisfiedTermCount]
    have hsample :
        4 * (n : ℝ) * fourierOneNorm φ.satisfiedTermCount ^ 2 /
              ((1 : ℝ) / 2) ^ 2 ≤
            (sampleCount : ℝ) := by
      calc
        4 * (n : ℝ) * fourierOneNorm φ.satisfiedTermCount ^ 2 /
              ((1 : ℝ) / 2) ^ 2 =
            16 * (n : ℝ) * fourierOneNorm φ.satisfiedTermCount ^ 2 := by ring
        _ ≤ 16 * (n : ℝ) * (φ.size : ℝ) ^ 2 := by
          gcongr
        _ = (sampleCount : ℝ) := by
          simp [sampleCount, Nat.cast_mul, Nat.cast_pow]
    obtain ⟨q, hqSparsity, hqApprox⟩ :=
      exists_sparsePolynomial_uniformApproximation
        hn φ.satisfiedTermCount (δ := (1 : ℝ) / 2) (by norm_num) hsample
    let p : {−1,1}^[n] → ℝ := fun x ↦ (1 : ℝ) / 2 - q x
    refine ⟨p, ?_, ?_⟩
    · intro x
      rw [φ.toBooleanFunction_eq_thresholdSign_satisfiedTermCount x]
      by_cases htrue : ∃ T ∈ φ.terms, T.eval x = -1
      · obtain ⟨T, hT, hTx⟩ := htrue
        have hcount := φ.one_le_satisfiedTermCount_of_satisfied_term x hT hTx
        have happrox := abs_lt.mp (hqApprox x)
        have hcountNeg :
            (1 : ℝ) / 2 - φ.satisfiedTermCount x < 0 := by
          linarith
        have hpneg : p x < 0 := by
          dsimp [p]
          linarith
        rw [thresholdSign_of_neg hcountNeg, thresholdSign_of_neg hpneg]
      · have hcount := φ.satisfiedTermCount_eq_zero_of_no_satisfied_term x htrue
        have happrox := abs_lt.mp (hqApprox x)
        have hppos : 0 < p x := by
          dsimp [p]
          linarith
        rw [hcount, thresholdSign_of_nonneg (by norm_num), thresholdSign_of_nonneg hppos.le]
    · have hpShift :
          polynomialSparsity p ≤ polynomialSparsity q + 1 := by
        exact polynomialSparsity_half_sub_le q
      have hone : 1 ≤ n * φ.size ^ 2 := by
        exact Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (Nat.ne_of_gt hn) (pow_ne_zero 2 (Nat.ne_of_gt hsizePos)))
      calc
        polynomialSparsity p ≤ polynomialSparsity q + 1 := hpShift
        _ ≤ sampleCount + 1 := Nat.add_le_add_right hqSparsity 1
        _ = 16 * (n * φ.size ^ 2) + 1 := by
          simp [sampleCount]
          ring
        _ ≤ 16 * (n * φ.size ^ 2) + n * φ.size ^ 2 :=
          Nat.add_le_add_left hone _
        _ = 17 * n * φ.size ^ 2 := by ring

/-- Exercise 5.13(b): every size-`s` DNF on a positive-dimensional cube has a polynomial
threshold representation of sparsity at most `17 n s²`. -/
theorem exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic
    (hn : 0 < n) {f : BooleanFunction n} {s : ℕ} (hf : HasDNFSizeLE f s) :
    ∃ p : {−1,1}^[n] → ℝ,
      IsPolynomialThresholdRepresentation f p ∧
        polynomialSparsity p ≤ 17 * n * s ^ 2 := by
  obtain ⟨φ, hφSize, rfl⟩ := hf
  obtain ⟨p, hrep, hp⟩ :=
    φ.exists_polynomialThresholdRepresentation_sparsity_le_quadratic hn
  refine ⟨p, hrep, hp.trans ?_⟩
  gcongr

/-- Exercise 5.13(a): every size-`s` DNF on a positive-dimensional cube has a polynomial
threshold representation of sparsity at most `17 n s³`. -/
theorem exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_cubic
    (hn : 0 < n) {f : BooleanFunction n} {s : ℕ} (hf : HasDNFSizeLE f s) :
    ∃ p : {−1,1}^[n] → ℝ,
      IsPolynomialThresholdRepresentation f p ∧
        polynomialSparsity p ≤ 17 * n * s ^ 3 := by
  obtain ⟨p, hrep, hp⟩ :=
    exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic hn hf
  refine ⟨p, hrep, hp.trans ?_⟩
  by_cases hs : s = 0
  · simp [hs]
  · have hsOne : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
    calc
      17 * n * s ^ 2 = 17 * n * (s ^ 2 * 1) := by ring
      _ ≤ 17 * n * (s ^ 2 * s) := by gcongr
      _ = 17 * n * s ^ 3 := by ring

end FABL
