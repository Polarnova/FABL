/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.Circuits
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parity formulas and bounded-depth circuit constructions

Book item: Exercise 4.12.

This module gives the exact DNF and CNF constructions and lower bounds, followed by the
block-recursive alternating circuits that establish the depth-dependent parity upper bounds.  It
also contains the parity Fourier obstruction used by Corollary 4.32.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

/-! ## Exact DNF construction and lower bound -/


/-- Flipping any coordinate negates full parity. -/
theorem parityFunction_univ_flipCoordinate {n : ℕ} (x : {−1,1}^[n]) (i : Fin n) :
    parityFunction (Finset.univ : Finset (Fin n)) (flipCoordinate x i) =
      -parityFunction (Finset.univ : Finset (Fin n)) x := by
  rw [parityFunction, parityFunction, flipCoordinate, setCoordinate,
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

/-- Every coordinate is pivotal for full parity. -/
theorem parityFunction_univ_isPivotal {n : ℕ} (x : {−1,1}^[n]) (i : Fin n) :
    IsPivotal (parityFunction (Finset.univ : Finset (Fin n))) i x := by
  rw [IsPivotal, parityFunction_univ_flipCoordinate]
  rcases Int.units_eq_one_or
      (parityFunction (Finset.univ : Finset (Fin n)) x) with h | h <;> simp [h]

/-- Exercise 4.12(b): every term in a DNF computing parity has width exactly `n`. -/
theorem DNFFormula.term_width_eq_dimension_of_computes_parity
    {n : ℕ} (φ : DNFFormula n)
    (hφ : φ.toBooleanFunction = parityFunction (Finset.univ : Finset (Fin n)))
    (T : DNFTerm n) (hT : T ∈ φ.terms) :
    T.width = n := by
  classical
  let p := T.satisfyingEquiv.symm (fun _ ↦ (1 : Sign))
  let x : {−1,1}^[n] := p.1
  have hTx : T.eval x = -1 := p.2
  have hφx : φ.eval x = -1 :=
    (DNFFormula.eval_eq_neg_one_iff φ x).2 ⟨T, hT, hTx⟩
  have hpivotal :
      (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x) =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsNegOnePivotal]
    refine ⟨hφx, ?_⟩
    rw [hφ]
    exact parityFunction_univ_isPivotal x i
  have hlower := card_negOnePivotal_le_term_width φ x T hT hTx
  rw [hpivotal] at hlower
  have hlower' : n ≤ T.width := by simpa using hlower
  exact Nat.le_antisymm T.width_le_dimension hlower'

/-- Nonconstant full parity is balanced. -/
theorem parityFunction_univ_isBalanced {n : ℕ} (hn : 0 < n) :
    IsBalanced (parityFunction (Finset.univ : Finset (Fin n))).toReal := by
  rw [IsBalanced, parityFunction_toReal, mean, expect_monomial]
  rw [if_neg]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty).ne_empty

/-- Exactly half of the inputs to nonconstant full parity have value `-1`. -/
theorem parityFunction_univ_neg_one_probability {n : ℕ} (hn : 0 < n) :
    uniformProbability
        (fun x : {−1,1}^[n] ↦ parityFunction (Finset.univ : Finset (Fin n)) x = -1) =
      (2 : ℝ)⁻¹ := by
  have hbalanced := parityFunction_univ_isBalanced hn
  have hone := (isBalanced_iff_uniformProbability_one_eq_half _).1 hbalanced
  have htotal := uniformProbability_one_add_neg_one_eq_one
    (parityFunction (Finset.univ : Finset (Fin n)))
  linarith

/-- The canonical minterm expansion of nonconstant full parity has `2 ^ (n - 1)` terms. -/
theorem size_mintermDNF_parityFunction_univ {n : ℕ} (hn : 0 < n) :
    (mintermDNF (parityFunction (Finset.univ : Finset (Fin n)))).size = 2 ^ (n - 1) := by
  classical
  have hprobability := parityFunction_univ_neg_one_probability hn
  rw [uniformProbability, Fintype.expect_eq_sum_div_card] at hprobability
  simp only [Finset.sum_boole] at hprobability
  simp only [mintermDNF, DNFFormula.size, List.length_map, Finset.length_toList]
  have hcard : Fintype.card ({−1,1}^[n]) = 2 ^ n := by
    simp [Fintype.card_pi, Sign]
  rw [hcard] at hprobability
  field_simp at hprobability
  cases n with
  | zero => omega
  | succ k =>
      have hreal :
          ((Finset.univ.filter fun x : {−1,1}^[k + 1] ↦
              parityFunction (Finset.univ : Finset (Fin (k + 1))) x = -1).card : ℝ) =
            (2 ^ k : ℝ) := by
        simpa [pow_succ] using hprobability
      exact_mod_cast hreal

/-- The probability that a DNF is true is at most the sum of its term probabilities. -/
theorem DNFFormula.uniformProbability_eval_neg_one_le_term_sum {n : ℕ}
    (φ : DNFFormula n) :
    uniformProbability (fun x ↦ φ.eval x = -1) ≤
      (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum := by
  classical
  rw [uniformProbability]
  calc
    (𝔼 x, if φ.eval x = -1 then (1 : ℝ) else 0) ≤
        𝔼 x, (φ.terms.map fun T ↦ if T.eval x = -1 then (1 : ℝ) else 0).sum := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hφ : φ.eval x = -1
      · obtain ⟨T, hT, hTx⟩ := (DNFFormula.eval_eq_neg_one_iff φ x).1 hφ
        rw [if_pos hφ]
        apply List.single_le_sum (fun y hy ↦ by
          obtain ⟨U, _, rfl⟩ := List.mem_map.mp hy
          split_ifs <;> norm_num)
        exact List.mem_map.mpr ⟨T, hT, by simp [hTx]⟩
      · simp only [if_neg hφ]
        exact List.sum_nonneg fun y hy ↦ by
          obtain ⟨T, _, rfl⟩ := List.mem_map.mp hy
          split_ifs <;> norm_num
    _ = (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum := by
      rw [expect_sum_list_map]
      congr 1
      apply List.map_congr_left
      intro T _
      simpa [uniformProbability] using uniformProbability_DNFTerm_eval_neg_one T

/-- Every DNF computing nonconstant full parity has at least `2 ^ (n - 1)` terms. -/
theorem DNFFormula.size_lower_bound_of_computes_parity
    {n : ℕ} (hn : 0 < n) (φ : DNFFormula n)
    (hφ : φ.toBooleanFunction = parityFunction (Finset.univ : Finset (Fin n))) :
    2 ^ (n - 1) ≤ φ.size := by
  have hprobability :
      uniformProbability (fun x ↦ φ.eval x = -1) = (2 : ℝ)⁻¹ := by
    rw [show φ.eval = parityFunction (Finset.univ : Finset (Fin n)) by exact hφ]
    exact parityFunction_univ_neg_one_probability hn
  have hterm (T : DNFTerm n) (hT : T ∈ φ.terms) : T.width = n :=
    φ.term_width_eq_dimension_of_computes_parity hφ T hT
  have hunion := φ.uniformProbability_eval_neg_one_le_term_sum
  rw [hprobability] at hunion
  have hsum :
      (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum =
        (φ.size : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    calc
      (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum =
          (φ.terms.map fun _ ↦ ((2 : ℝ) ^ n)⁻¹).sum := by
        congr 1
        apply List.map_congr_left
        intro T hT
        rw [hterm T hT]
      _ = (φ.size : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by simp [DNFFormula.size]
  rw [hsum] at hunion
  have hreal : (2 : ℝ) ^ (n - 1) ≤ (φ.size : ℝ) := by
    cases n with
    | zero => omega
    | succ k =>
        simp only [Nat.succ_sub_one]
        rw [pow_succ] at hunion
        have hdiv :
            (2 : ℝ)⁻¹ ≤ (φ.size : ℝ) / (2 * (2 : ℝ) ^ k) := by
          simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hunion
        have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ k)).1 hdiv
        calc
          (2 : ℝ) ^ k = (2 : ℝ)⁻¹ * (2 * (2 : ℝ) ^ k) := by
            field_simp
          _ ≤ (φ.size : ℝ) := hmul
  exact_mod_cast hreal

/-- Exercise 4.12(a): canonical optimal DNF for full parity. -/
noncomputable def parityDNF (n : ℕ) : DNFFormula n :=
  mintermDNF (parityFunction (Finset.univ : Finset (Fin n)))

theorem parityDNF_toBooleanFunction (n : ℕ) :
    (parityDNF n).toBooleanFunction =
      parityFunction (Finset.univ : Finset (Fin n)) := by
  exact mintermDNF_toBooleanFunction _

theorem size_parityDNF {n : ℕ} (hn : 0 < n) :
    (parityDNF n).size = 2 ^ (n - 1) := by
  exact size_mintermDNF_parityFunction_univ hn

/-- Exercise 4.12(a)–(b): the least DNF size of nonconstant parity is `2 ^ (n - 1)`. -/
theorem DNFsize_parityFunction_univ {n : ℕ} (hn : 0 < n) :
    DNFsize (parityFunction (Finset.univ : Finset (Fin n))) = 2 ^ (n - 1) := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨parityDNF n, (size_parityDNF hn).le,
      parityDNF_toBooleanFunction n⟩
  · obtain ⟨φ, hsize, hφ⟩ :=
      hasDNFSizeLE_DNFsize (parityFunction (Finset.univ : Finset (Fin n)))
    exact (φ.size_lower_bound_of_computes_parity hn hφ).trans hsize


/-! ## Exact CNF construction and lower bound -/


/-- Boolean duality negates the mean. -/
theorem mean_booleanDual {n : ℕ} (f : BooleanFunction n) :
    mean (CNFFormula.booleanDual f).toReal = -mean f.toReal := by
  rw [mean, mean]
  calc
    (𝔼 x, (CNFFormula.booleanDual f).toReal x) =
        𝔼 x, -f.toReal (signCubeNegEquiv n x) := by
      apply Finset.expect_congr rfl
      intro x _
      simp [CNFFormula.booleanDual, BooleanFunction.toReal, signCubeNegEquiv, signValue]
    _ = 𝔼 x, -f.toReal x := by
      exact Fintype.expect_equiv (signCubeNegEquiv n)
        (fun x ↦ -f.toReal (signCubeNegEquiv n x))
        (fun x ↦ -f.toReal x) (fun _ ↦ rfl)
    _ = -(𝔼 x, f.toReal x) := Finset.expect_neg_distrib Finset.univ f.toReal

/-- Boolean duality preserves balance. -/
theorem isBalanced_booleanDual {n : ℕ} (f : BooleanFunction n)
    (hf : IsBalanced f.toReal) :
    IsBalanced (CNFFormula.booleanDual f).toReal := by
  rw [IsBalanced, mean_booleanDual, hf, neg_zero]

/-- A balanced sign-valued function has `-1` probability exactly one half. -/
theorem uniformProbability_neg_one_eq_half_of_isBalanced {n : ℕ}
    (f : BooleanFunction n) (hf : IsBalanced f.toReal) :
    uniformProbability (fun x ↦ f x = -1) = (2 : ℝ)⁻¹ := by
  have hone := (isBalanced_iff_uniformProbability_one_eq_half f).1 hf
  have htotal := uniformProbability_one_add_neg_one_eq_one f
  linarith

/-- The canonical minterm DNF of a balanced `n`-variable function has `2 ^ (n - 1)` terms. -/
theorem size_mintermDNF_of_isBalanced {n : ℕ} (hn : 0 < n)
    (f : BooleanFunction n) (hf : IsBalanced f.toReal) :
    (mintermDNF f).size = 2 ^ (n - 1) := by
  classical
  have hprobability := uniformProbability_neg_one_eq_half_of_isBalanced f hf
  rw [uniformProbability, Fintype.expect_eq_sum_div_card] at hprobability
  simp only [Finset.sum_boole] at hprobability
  simp only [mintermDNF, DNFFormula.size, List.length_map, Finset.length_toList]
  have hcard : Fintype.card ({−1,1}^[n]) = 2 ^ n := by
    simp [Fintype.card_pi, Sign]
  rw [hcard] at hprobability
  field_simp at hprobability
  cases n with
  | zero => omega
  | succ k =>
      have hreal :
          ((Finset.univ.filter fun x : {−1,1}^[k + 1] ↦ f x = -1).card : ℝ) =
            (2 ^ k : ℝ) := by
        simpa [pow_succ] using hprobability
      exact_mod_cast hreal

/-- Applying Boolean duality to two functions is injective. -/
theorem CNFFormula.booleanDual_injective {n : ℕ} :
    Function.Injective (CNFFormula.booleanDual : BooleanFunction n → BooleanFunction n) := by
  intro f g h
  funext x
  have hx := congrFun h (fun i ↦ -x i)
  simpa [CNFFormula.booleanDual] using hx

/-- Every coordinate is pivotal for the Boolean dual of full parity. -/
theorem booleanDual_parityFunction_univ_isPivotal {n : ℕ}
    (x : {−1,1}^[n]) (i : Fin n) :
    IsPivotal
      (CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n)))) i x := by
  have hnegFlip :
      (fun j ↦ -(flipCoordinate x i) j) =
        flipCoordinate (fun j ↦ -x j) i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [flipCoordinate, setCoordinate]
    · simp [flipCoordinate, setCoordinate, Function.update_of_ne hji]
  rw [IsPivotal]
  simp only [CNFFormula.booleanDual, hnegFlip,
    parityFunction_univ_flipCoordinate]
  rcases Int.units_eq_one_or
      (parityFunction (Finset.univ : Finset (Fin n)) (fun j ↦ -x j)) with h | h <;>
    simp [h]

/-- Every term in a DNF for the Boolean dual of full parity has full width. -/
theorem DNFFormula.term_width_eq_dimension_of_computes_booleanDual_parity
    {n : ℕ} (φ : DNFFormula n)
    (hφ : φ.toBooleanFunction =
      CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))))
    (T : DNFTerm n) (hT : T ∈ φ.terms) :
    T.width = n := by
  classical
  let p := T.satisfyingEquiv.symm (fun _ ↦ (1 : Sign))
  let x : {−1,1}^[n] := p.1
  have hTx : T.eval x = -1 := p.2
  have hφx : φ.eval x = -1 :=
    (DNFFormula.eval_eq_neg_one_iff φ x).2 ⟨T, hT, hTx⟩
  have hpivotal :
      (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x) =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsNegOnePivotal]
    refine ⟨hφx, ?_⟩
    rw [hφ]
    exact booleanDual_parityFunction_univ_isPivotal x i
  have hlower := card_negOnePivotal_le_term_width φ x T hT hTx
  rw [hpivotal] at hlower
  exact Nat.le_antisymm T.width_le_dimension (by simpa using hlower)

/-- Exercise 4.12(b), CNF form: every clause in a CNF computing parity has width `n`. -/
theorem CNFFormula.clause_width_eq_dimension_of_computes_parity
    {n : ℕ} (ψ : CNFFormula n)
    (hψ : ψ.toBooleanFunction =
      parityFunction (Finset.univ : Finset (Fin n)))
    (C : DNFTerm n) (hC : C ∈ ψ.clauses) :
    C.width = n := by
  let φ := CNFFormula.switchAndOr ψ
  have hφ : φ.toBooleanFunction =
      CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))) := by
    dsimp [φ]
    rw [CNFFormula.switchAndOr_toBooleanFunction, hψ]
  exact φ.term_width_eq_dimension_of_computes_booleanDual_parity hφ C hC

/-- Exercise 4.12(b), CNF form: every CNF for nonconstant parity has at least
`2 ^ (n - 1)` clauses. -/
theorem CNFFormula.size_lower_bound_of_computes_parity
    {n : ℕ} (hn : 0 < n) (ψ : CNFFormula n)
    (hψ : ψ.toBooleanFunction =
      parityFunction (Finset.univ : Finset (Fin n))) :
    2 ^ (n - 1) ≤ ψ.size := by
  let φ := CNFFormula.switchAndOr ψ
  have hφ : φ.toBooleanFunction =
      CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))) := by
    dsimp [φ]
    rw [CNFFormula.switchAndOr_toBooleanFunction, hψ]
  have hprobability :
      uniformProbability (fun x ↦ φ.eval x = -1) = (2 : ℝ)⁻¹ := by
    rw [show φ.eval =
      CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))) by exact hφ]
    exact uniformProbability_neg_one_eq_half_of_isBalanced _
      (isBalanced_booleanDual _ (parityFunction_univ_isBalanced hn))
  have hterm (T : DNFTerm n) (hT : T ∈ φ.terms) : T.width = n :=
    φ.term_width_eq_dimension_of_computes_booleanDual_parity hφ T hT
  have hunion := φ.uniformProbability_eval_neg_one_le_term_sum
  rw [hprobability] at hunion
  have hsum :
      (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum =
        (φ.size : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
    calc
      (φ.terms.map fun T ↦ ((2 : ℝ) ^ T.width)⁻¹).sum =
          (φ.terms.map fun _ ↦ ((2 : ℝ) ^ n)⁻¹).sum := by
        congr 1
        apply List.map_congr_left
        intro T hT
        rw [hterm T hT]
      _ = (φ.size : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
        simp [DNFFormula.size]
  rw [hsum] at hunion
  have hreal : (2 : ℝ) ^ (n - 1) ≤ (φ.size : ℝ) := by
    cases n with
    | zero => omega
    | succ k =>
        simp only [Nat.succ_sub_one]
        rw [pow_succ] at hunion
        have hdiv :
            (2 : ℝ)⁻¹ ≤ (φ.size : ℝ) / (2 * (2 : ℝ) ^ k) := by
          simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
            using hunion
        have hmul :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ k)).1 hdiv
        calc
          (2 : ℝ) ^ k = (2 : ℝ)⁻¹ * (2 * (2 : ℝ) ^ k) := by
            field_simp
          _ ≤ (φ.size : ℝ) := hmul
  have hsize : 2 ^ (n - 1) ≤ φ.size := by
    exact_mod_cast hreal
  simpa [φ, CNFFormula.switchAndOr, DNFFormula.size, CNFFormula.size] using hsize

/-- Exercise 4.12(a): canonical CNF for full parity, obtained from its Boolean dual. -/
noncomputable def parityCNF (n : ℕ) : CNFFormula n where
  clauses :=
    (mintermDNF
      (CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))))).terms

theorem size_parityCNF {n : ℕ} (hn : 0 < n) :
    (parityCNF n).size = 2 ^ (n - 1) := by
  change
    (mintermDNF
      (CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))))).size = 2 ^ (n - 1)
  apply size_mintermDNF_of_isBalanced hn
  exact isBalanced_booleanDual _ (parityFunction_univ_isBalanced hn)

theorem parityCNF_toBooleanFunction (n : ℕ) :
    (parityCNF n).toBooleanFunction =
      parityFunction (Finset.univ : Finset (Fin n)) := by
  apply CNFFormula.booleanDual_injective
  rw [← CNFFormula.switchAndOr_toBooleanFunction]
  change
    (mintermDNF
      (CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n))))).toBooleanFunction =
      CNFFormula.booleanDual
        (parityFunction (Finset.univ : Finset (Fin n)))
  exact mintermDNF_toBooleanFunction _


/-! ## Alternating bounded-depth constructions -/


/-! ## Finite block assignments -/

abbrev ParityBlockAssignment (r : ℕ) := Fin r → Sign

theorem card_parityBlockAssignment (r : ℕ) :
    Fintype.card (ParityBlockAssignment r) = 2 ^ r := by
  simp [ParityBlockAssignment, Fintype.card_units_int]

/-- Canonical enumeration of sign assignments to a block of `r` inputs. -/
noncomputable def parityBlockAssignmentEquiv (r : ℕ) :
    Fin (2 ^ r) ≃ ParityBlockAssignment r :=
  finCongr (card_parityBlockAssignment r).symm |>.trans
    (Fintype.equivFin (ParityBlockAssignment r)).symm

/-- Product of the signs in a block assignment. -/
def parityBlockProduct {r : ℕ} (a : ParityBlockAssignment r) : Sign :=
  ∏ j, a j

/-- Slots in block `g` which correspond to genuine coordinates rather than padding. -/
def parityBlockSlots (n r g : ℕ) :=
  {j : Fin r // g * r + j.1 < n}

/-- The ambient coordinate corresponding to a genuine slot of block `g`. -/
def parityBlockCoordinate {n r g : ℕ} (j : parityBlockSlots n r g) : Fin n :=
  ⟨g * r + j.1.1, j.2⟩

theorem parityBlockCoordinate_injective {n r g : ℕ} :
    Function.Injective (parityBlockCoordinate (n := n) (r := r) (g := g)) := by
  intro i j hij
  apply Subtype.ext
  apply Fin.ext
  have hval : g * r + i.1.1 = g * r + j.1.1 := by
    simpa [parityBlockCoordinate] using congrArg Fin.val hij
  omega

noncomputable instance parityBlockSlotsFintype (n r g : ℕ) :
    Fintype (parityBlockSlots n r g) := by
  unfold parityBlockSlots
  infer_instance

/-- Minterm selecting one assignment on the genuine coordinates of a padded block. -/
noncomputable def parityBlockMinterm (n r g : ℕ) (a : ParityBlockAssignment r) :
    DNFTerm n where
  literals := (Finset.univ : Finset (parityBlockSlots n r g)).toList.map fun j ↦
    ⟨parityBlockCoordinate j, a j.1⟩
  nodupIndices := by
    simp only [List.map_map, Function.comp_def]
    exact (Finset.nodup_toList (Finset.univ : Finset (parityBlockSlots n r g))).map
      parityBlockCoordinate_injective

/-- Actual assignment on a padded block; unused slots have neutral parity sign `1`. -/
def parityBlockValue (n r g : ℕ) (x : {−1,1}^[n]) : ParityBlockAssignment r :=
  fun j ↦ if h : g * r + j.1 < n then x ⟨g * r + j.1, h⟩ else 1

/-- A block assignment is valid when every padded slot carries the neutral sign. -/
def IsValidParityBlockAssignment (n r g : ℕ) (a : ParityBlockAssignment r) : Prop :=
  ∀ j : Fin r, n ≤ g * r + j.1 → a j = 1

/-- Normalize a block assignment by replacing every padded coordinate by the neutral sign. -/
def normalizeParityBlockAssignment (n r g : ℕ) (a : ParityBlockAssignment r) :
    ParityBlockAssignment r :=
  fun j ↦ if g * r + j.1 < n then a j else 1

theorem normalizeParityBlockAssignment_valid (n r g : ℕ) (a : ParityBlockAssignment r) :
    IsValidParityBlockAssignment n r g (normalizeParityBlockAssignment n r g a) := by
  intro j hj
  simp [normalizeParityBlockAssignment, Nat.not_lt.mpr hj]

theorem normalizeParityBlockAssignment_eq_self {n r g : ℕ}
    {a : ParityBlockAssignment r} (ha : IsValidParityBlockAssignment n r g a) :
    normalizeParityBlockAssignment n r g a = a := by
  funext j
  by_cases hj : g * r + j.1 < n
  · simp [normalizeParityBlockAssignment, hj]
  · simp [normalizeParityBlockAssignment, hj, ha j (Nat.le_of_not_gt hj)]

theorem parityBlockValue_valid (n r g : ℕ) (x : {−1,1}^[n]) :
    IsValidParityBlockAssignment n r g (parityBlockValue n r g x) := by
  intro j hj
  simp [parityBlockValue, Nat.not_lt.mpr hj]

theorem parityBlockMinterm_eval_eq_neg_one_iff
    (n r g : ℕ) (a : ParityBlockAssignment r) (x : {−1,1}^[n]) :
    (parityBlockMinterm n r g a).eval x = -1 ↔
      normalizeParityBlockAssignment n r g a = parityBlockValue n r g x := by
  rw [DNFTerm.eval_eq_neg_one_iff]
  constructor
  · intro h
    funext j
    by_cases hj : g * r + j.1 < n
    · let slot : parityBlockSlots n r g := ⟨j, hj⟩
      have hliteral :
          (⟨parityBlockCoordinate slot, a slot.1⟩ : Literal n) ∈
            (parityBlockMinterm n r g a).literals := by
        change _ ∈ (Finset.univ : Finset (parityBlockSlots n r g)).toList.map _
        apply List.mem_map.mpr
        exact ⟨slot, by simp, rfl⟩
      have hvalue := h _ hliteral
      simpa [normalizeParityBlockAssignment, parityBlockValue, hj, slot,
        parityBlockCoordinate] using hvalue.symm
    · simp [normalizeParityBlockAssignment, parityBlockValue, hj]
  · intro h ℓ hℓ
    simp only [parityBlockMinterm, List.mem_map, Finset.mem_toList] at hℓ
    obtain ⟨j, ⟨-, rfl⟩⟩ := hℓ
    have hj : g * r + j.1.1 < n := j.2
    have hcoordinate := congrFun h j.1
    simpa [normalizeParityBlockAssignment, parityBlockValue, hj, parityBlockCoordinate] using
      hcoordinate.symm

/-! ## Uniform layer indexing -/

/-- Number of nodes in a parity-construction layer with `r ^ q` blocks. -/
def parityLayerSize (r q : ℕ) : ℕ :=
  r ^ q * 2 ^ r

/-- Nodes are indexed by a block and one sign assignment on its `r` children. -/
noncomputable def parityLayerEquiv (r q : ℕ) :
    Fin (parityLayerSize r q) ≃ Fin (r ^ q) × ParityBlockAssignment r :=
  (finProdFinEquiv (m := r ^ q) (n := 2 ^ r)).symm |>.trans
    ((Equiv.refl (Fin (r ^ q))).prodCongr (parityBlockAssignmentEquiv r))

@[simp] theorem parityLayerEquiv_symm_apply_apply (r q : ℕ)
    (i : Fin (parityLayerSize r q)) :
    (parityLayerEquiv r q).symm (parityLayerEquiv r q i) = i := by
  exact Equiv.symm_apply_apply _ _

@[simp] theorem parityLayerEquiv_apply_symm_apply (r q : ℕ)
    (i : Fin (r ^ q) × ParityBlockAssignment r) :
    parityLayerEquiv r q ((parityLayerEquiv r q).symm i) = i := by
  exact Equiv.apply_symm_apply _ _

/-- Canonical block/child decomposition of the groups in two adjacent layers. -/
def parityChildGroupEquiv (r q : ℕ) :
    Fin (r ^ q) × Fin r ≃ Fin (r ^ (q + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ r q)).symm

/-- Child block `j` of a block one layer higher in the `r`-ary decomposition. -/
def parityChildGroup {r q : ℕ} (g : Fin (r ^ q)) (j : Fin r) : Fin (r ^ (q + 1)) :=
  parityChildGroupEquiv r q (g, j)

@[simp] theorem parityChildGroup_val {r q : ℕ} (g : Fin (r ^ q)) (j : Fin r) :
    (parityChildGroup g j).1 = g.1 * r + j.1 := by
  simp [parityChildGroup, parityChildGroupEquiv, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem parityChildGroup_injective {r q : ℕ} :
    Function.Injective (fun gj : Fin (r ^ q) × Fin r ↦ parityChildGroup gj.1 gj.2) := by
  exact (parityChildGroupEquiv r q).injective

/-! ## Semantic `r`-ary parity tree -/

/-- Input sign at a natural coordinate, padded by the neutral sign beyond dimension `n`. -/
def paddedParityInput (n : ℕ) (x : {−1,1}^[n]) (i : ℕ) : Sign :=
  if h : i < n then x ⟨i, h⟩ else 1

/-- Parity of an `r`-ary subtree. Height zero is one (possibly padded) input. -/
def parityTreeValue (n r : ℕ) (x : {−1,1}^[n]) : ℕ → ℕ → Sign
  | 0, g => paddedParityInput n x g
  | t + 1, g => ∏ j : Fin r, parityTreeValue n r x t (g * r + j.1)

@[simp] theorem parityTreeValue_zero (n r g : ℕ) (x : {−1,1}^[n]) :
    parityTreeValue n r x 0 g = paddedParityInput n x g := rfl

@[simp] theorem parityTreeValue_succ (n r t g : ℕ) (x : {−1,1}^[n]) :
    parityTreeValue n r x (t + 1) g =
      ∏ j : Fin r, parityTreeValue n r x t (g * r + j.1) := rfl

/-- The `r` child parities seen by one node at tree height `t + 1`. -/
def parityTreeAssignment (n r t g : ℕ) (x : {−1,1}^[n]) : ParityBlockAssignment r :=
  fun j ↦ parityTreeValue n r x t (g * r + j.1)

@[simp] theorem parityBlockProduct_treeAssignment (n r t g : ℕ) (x : {−1,1}^[n]) :
    parityBlockProduct (parityTreeAssignment n r t g x) =
      parityTreeValue n r x (t + 1) g := by
  rfl

theorem parityTreeAssignment_zero_eq_blockValue (n r g : ℕ) (x : {−1,1}^[n]) :
    parityTreeAssignment n r 0 g x = parityBlockValue n r g x := by
  funext j
  simp [parityTreeAssignment, parityBlockValue, paddedParityInput]

/-! ## Exact-assignment nodes and inter-layer wiring -/

/-- Value of an exact-assignment node: AND minterms are true on a match, whereas OR clauses
are false on a match. -/
def parityExactNodeValue (gate : CircuitGate) (isMatch : Bool) : Sign :=
  match gate, isMatch with
  | .and, true => -1
  | .and, false => 1
  | .or, true => 1
  | .or, false => -1

@[simp] theorem parityExactNodeValue_and_true :
    parityExactNodeValue .and true = -1 := rfl

@[simp] theorem parityExactNodeValue_and_false :
    parityExactNodeValue .and false = 1 := rfl

@[simp] theorem parityExactNodeValue_or_true :
    parityExactNodeValue .or true = 1 := rfl

@[simp] theorem parityExactNodeValue_or_false :
    parityExactNodeValue .or false = -1 := rfl

/-- Canonical values of one layer when every node is read as an exact-assignment test. -/
noncomputable def parityLayerValues (r q : ℕ) (gate : CircuitGate)
    (actual : Fin (r ^ q) → ParityBlockAssignment r) :
    Fin (parityLayerSize r q) → Sign :=
  fun i ↦
    let ga := parityLayerEquiv r q i
    parityExactNodeValue gate (decide (ga.2 = actual ga.1))

@[simp] theorem parityLayerValues_and_eq_neg_one_iff (r q : ℕ)
    (actual : Fin (r ^ q) → ParityBlockAssignment r)
    (i : Fin (parityLayerSize r q)) :
    parityLayerValues r q .and actual i = -1 ↔
      (parityLayerEquiv r q i).2 = actual (parityLayerEquiv r q i).1 := by
  by_cases h : (parityLayerEquiv r q i).2 = actual (parityLayerEquiv r q i).1 <;>
    simp [parityLayerValues, parityExactNodeValue, h]

@[simp] theorem parityLayerValues_or_eq_neg_one_iff (r q : ℕ)
    (actual : Fin (r ^ q) → ParityBlockAssignment r)
    (i : Fin (parityLayerSize r q)) :
    parityLayerValues r q .or actual i = -1 ↔
      (parityLayerEquiv r q i).2 ≠ actual (parityLayerEquiv r q i).1 := by
  by_cases h : (parityLayerEquiv r q i).2 = actual (parityLayerEquiv r q i).1 <;>
    simp [parityLayerValues, parityExactNodeValue, h]

@[simp] theorem parityLayerValues_or_eq_one_iff (r q : ℕ)
    (actual : Fin (r ^ q) → ParityBlockAssignment r)
    (i : Fin (parityLayerSize r q)) :
    parityLayerValues r q .or actual i = 1 ↔
      (parityLayerEquiv r q i).2 = actual (parityLayerEquiv r q i).1 := by
  by_cases h : (parityLayerEquiv r q i).2 = actual (parityLayerEquiv r q i).1 <;>
    simp [parityLayerValues, parityExactNodeValue, h]

/-- Actual child-parity assignment at the next coarser level. -/
def parityNextActualAssignment {r q : ℕ}
    (actual : Fin (r ^ (q + 1)) → ParityBlockAssignment r)
    (g : Fin (r ^ q)) : ParityBlockAssignment r :=
  fun j ↦ parityBlockProduct (actual (parityChildGroup g j))

/-- Incoming wires of the exact-assignment node `(g,a)` in the next layer. They select precisely
the current nodes whose child parity disagrees with the sign prescribed by `a`. -/
noncomputable def parityNextNodeInputs (r q : ℕ)
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r) :
    Finset (Fin (parityLayerSize r (q + 1))) :=
  Finset.univ.filter fun i ↦
    let hb := parityLayerEquiv r (q + 1) i
    ∃ j : Fin r, hb.1 = parityChildGroup g j ∧ parityBlockProduct hb.2 ≠ a j

@[simp] theorem mem_parityNextNodeInputs_iff (r q : ℕ)
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r)
    (i : Fin (parityLayerSize r (q + 1))) :
    i ∈ parityNextNodeInputs r q g a ↔
      ∃ j : Fin r,
        (parityLayerEquiv r (q + 1) i).1 = parityChildGroup g j ∧
          parityBlockProduct (parityLayerEquiv r (q + 1) i).2 ≠ a j := by
  simp [parityNextNodeInputs]

theorem exists_apply_ne_of_ne {r : ℕ} {a b : ParityBlockAssignment r} (h : a ≠ b) :
    ∃ j, a j ≠ b j := by
  by_contra hall
  apply h
  funext j
  exact not_ne_iff.mp (not_exists.mp hall j)

/-- One alternating layer carries the exact-assignment invariant to the next layer. -/
theorem eval_parityNextNodeInputs (r q : ℕ) (gate : CircuitGate)
    (actual : Fin (r ^ (q + 1)) → ParityBlockAssignment r)
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r) :
    gate.dual.evalFinset (parityLayerValues r (q + 1) gate actual)
        (parityNextNodeInputs r q g a) =
      parityExactNodeValue gate.dual
        (decide (a = parityNextActualAssignment actual g)) := by
  classical
  cases gate with
  | and =>
      have hexists :
          (∃ i ∈ parityNextNodeInputs r q g a,
              parityLayerValues r (q + 1) .and actual i = -1) ↔
            a ≠ parityNextActualAssignment actual g := by
        constructor
        · rintro ⟨i, hi, hvalue⟩ hmatch
          obtain ⟨j, hgroup, hproduct⟩ :=
            (mem_parityNextNodeInputs_iff r q g a i).mp hi
          have hnode := (parityLayerValues_and_eq_neg_one_iff r (q + 1) actual i).mp hvalue
          have htarget := congrFun hmatch j
          rw [hnode, hgroup] at hproduct
          exact hproduct htarget.symm
        · intro hmatch
          obtain ⟨j, hj⟩ := exists_apply_ne_of_ne hmatch
          let b := actual (parityChildGroup g j)
          let i : Fin (parityLayerSize r (q + 1)) :=
            (parityLayerEquiv r (q + 1)).symm (parityChildGroup g j, b)
          refine ⟨i, ?_, ?_⟩
          · apply (mem_parityNextNodeInputs_iff r q g a i).mpr
            refine ⟨j, ?_, ?_⟩
            · simp [i]
            · simp only [i, Equiv.apply_symm_apply]
              change parityBlockProduct (actual (parityChildGroup g j)) ≠ a j
              intro hproduct
              apply hj
              simpa [parityNextActualAssignment] using hproduct.symm
          · apply (parityLayerValues_and_eq_neg_one_iff r (q + 1) actual i).mpr
            simp [i, b]
      change (if ∃ i ∈ parityNextNodeInputs r q g a,
          parityLayerValues r (q + 1) .and actual i = -1 then -1 else 1) = _
      by_cases hmatch : a = parityNextActualAssignment actual g
      · have hnone : ¬(∃ i ∈ parityNextNodeInputs r q g a,
            parityLayerValues r (q + 1) .and actual i = -1) :=
          fun h ↦ (hexists.mp h) hmatch
        rw [if_neg hnone]
        simp [parityExactNodeValue, hmatch]
      · have hsome : ∃ i ∈ parityNextNodeInputs r q g a,
            parityLayerValues r (q + 1) .and actual i = -1 :=
          hexists.mpr hmatch
        rw [if_pos hsome]
        simp [parityExactNodeValue, hmatch]
  | or =>
      have hforall :
          (∀ i ∈ parityNextNodeInputs r q g a,
              parityLayerValues r (q + 1) .or actual i = -1) ↔
            a = parityNextActualAssignment actual g := by
        constructor
        · intro hall
          funext j
          by_contra hj
          let b := actual (parityChildGroup g j)
          let i : Fin (parityLayerSize r (q + 1)) :=
            (parityLayerEquiv r (q + 1)).symm (parityChildGroup g j, b)
          have hi : i ∈ parityNextNodeInputs r q g a := by
            apply (mem_parityNextNodeInputs_iff r q g a i).mpr
            refine ⟨j, ?_, ?_⟩
            · simp [i]
            · simp only [i, Equiv.apply_symm_apply]
              change parityBlockProduct (actual (parityChildGroup g j)) ≠ a j
              intro hproduct
              apply hj
              simpa [parityNextActualAssignment] using hproduct.symm
          have hvalue := hall i hi
          have hmismatch :=
            (parityLayerValues_or_eq_neg_one_iff r (q + 1) actual i).mp hvalue
          exact hmismatch (by simp [i, b])
        · intro hmatch i hi
          obtain ⟨j, hgroup, hproduct⟩ :=
            (mem_parityNextNodeInputs_iff r q g a i).mp hi
          apply (parityLayerValues_or_eq_neg_one_iff r (q + 1) actual i).mpr
          intro hnode
          have htarget := congrFun hmatch j
          rw [hnode, hgroup] at hproduct
          exact hproduct htarget.symm
      change (if ∀ i ∈ parityNextNodeInputs r q g a,
          parityLayerValues r (q + 1) .or actual i = -1 then -1 else 1) = _
      by_cases hmatch : a = parityNextActualAssignment actual g
      · have hall : ∀ i ∈ parityNextNodeInputs r q g a,
            parityLayerValues r (q + 1) .or actual i = -1 :=
          hforall.mpr hmatch
        rw [if_pos hall]
        simp [parityExactNodeValue, hmatch]
      · have hnotall : ¬(∀ i ∈ parityNextNodeInputs r q g a,
            parityLayerValues r (q + 1) .or actual i = -1) :=
          fun h ↦ hmatch (hforall.mp h)
        rw [if_neg hnotall]
        simp [parityExactNodeValue, hmatch]

/-! ## Concrete layers -/

/-- The bottom AND layer: all padded minterms for each bottom block. -/
noncomputable def parityFirstLayer (n r q : ℕ) : List (DNFTerm n) :=
  List.ofFn fun i : Fin (parityLayerSize r q) ↦
    let ga := parityLayerEquiv r q i
    parityBlockMinterm n r ga.1.1 ga.2

@[simp] theorem length_parityFirstLayer (n r q : ℕ) :
    (parityFirstLayer n r q).length = parityLayerSize r q := by
  simp [parityFirstLayer]

/-- Semantic values of the padded bottom layer. Assignments differing only on padding denote the
same minterm, so normalization is part of the node label rather than an extra circuit input. -/
noncomputable def parityBottomLayerValues (n r q : ℕ) (x : {−1,1}^[n]) :
    Fin (parityLayerSize r q) → Sign :=
  fun i ↦
    let ga := parityLayerEquiv r q i
    parityExactNodeValue .and
      (decide (normalizeParityBlockAssignment n r ga.1.1 ga.2 =
        parityTreeAssignment n r 0 ga.1.1 x))

theorem eval_parityFirstLayer (n r q : ℕ) (x : {−1,1}^[n])
    (i : Fin (parityLayerSize r q)) :
    CircuitGate.and.evalTerm
        ((parityFirstLayer n r q).get
          (i.cast (length_parityFirstLayer n r q).symm)) x =
      parityBottomLayerValues n r q x i := by
  classical
  let ga := parityLayerEquiv r q i
  have heval := parityBlockMinterm_eval_eq_neg_one_iff n r ga.1.1 ga.2 x
  have hactual : parityTreeAssignment n r 0 ga.1.1 x = parityBlockValue n r ga.1.1 x :=
    parityTreeAssignment_zero_eq_blockValue n r ga.1.1 x
  simp only [CircuitGate.evalTerm]
  rw [show (parityFirstLayer n r q).get
      (i.cast (length_parityFirstLayer n r q).symm) =
        parityBlockMinterm n r ga.1.1 ga.2 by
    simp [parityFirstLayer, ga]]
  change (parityBlockMinterm n r ga.1.1 ga.2).eval x =
    parityExactNodeValue .and
      (decide (normalizeParityBlockAssignment n r ga.1.1 ga.2 =
        parityTreeAssignment n r 0 ga.1.1 x))
  by_cases hmatch : normalizeParityBlockAssignment n r ga.1.1 ga.2 =
      parityTreeAssignment n r 0 ga.1.1 x
  · have hneg : (parityBlockMinterm n r ga.1.1 ga.2).eval x = -1 :=
      heval.mpr (hmatch.trans hactual)
    simp [parityExactNodeValue, hmatch, hneg]
  · have hnotneg : (parityBlockMinterm n r ga.1.1 ga.2).eval x ≠ -1 := by
      intro hneg
      exact hmatch ((heval.mp hneg).trans hactual.symm)
    rcases Int.units_eq_one_or ((parityBlockMinterm n r ga.1.1 ga.2).eval x) with hone | hneg
    · simp [parityExactNodeValue, hmatch, hone]
    · exact (hnotneg hneg).elim

/-- All exact-assignment gates in one non-output layer. -/
noncomputable def parityNextLayer (r q : ℕ) :
    List (Finset (Fin (parityLayerSize r (q + 1)))) :=
  List.ofFn fun i : Fin (parityLayerSize r q) ↦
    let ga := parityLayerEquiv r q i
    parityNextNodeInputs r q ga.1 ga.2

@[simp] theorem length_parityNextLayer (r q : ℕ) :
    (parityNextLayer r q).length = parityLayerSize r q := by
  simp [parityNextLayer]

theorem get_parityNextLayer (r q : ℕ) (i : Fin (parityLayerSize r q)) :
    (parityNextLayer r q).get
        (i.cast (length_parityNextLayer r q).symm) =
      let ga := parityLayerEquiv r q i
      parityNextNodeInputs r q ga.1 ga.2 := by
  simp [parityNextLayer]

/-- Incoming wires of the output gate. The top group is constrained to have parity `-1`. -/
noncomputable def parityOutputInputs (r : ℕ) (gate : CircuitGate) :
    Finset (Fin (parityLayerSize r 0)) := by
  classical
  exact Finset.univ.filter fun i ↦
    match gate with
    | .and => parityBlockProduct (parityLayerEquiv r 0 i).2 = -1
    | .or => parityBlockProduct (parityLayerEquiv r 0 i).2 ≠ -1

@[simp] theorem mem_parityOutputInputs_and_iff (r : ℕ)
    (i : Fin (parityLayerSize r 0)) :
    i ∈ parityOutputInputs r .and ↔
      parityBlockProduct (parityLayerEquiv r 0 i).2 = -1 := by
  simp [parityOutputInputs]

@[simp] theorem mem_parityOutputInputs_or_iff (r : ℕ)
    (i : Fin (parityLayerSize r 0)) :
    i ∈ parityOutputInputs r .or ↔
      parityBlockProduct (parityLayerEquiv r 0 i).2 ≠ -1 := by
  simp [parityOutputInputs]

/-- The final alternating gate reads the parity of the unique top block. -/
theorem eval_parityOutputInputs (r : ℕ) (gate : CircuitGate)
    (actual : Fin (r ^ 0) → ParityBlockAssignment r) :
    gate.dual.evalFinset (parityLayerValues r 0 gate actual)
        (parityOutputInputs r gate) =
      parityBlockProduct (actual ⟨0, by simp⟩) := by
  classical
  cases gate with
  | and =>
      have hexists :
          (∃ i ∈ parityOutputInputs r .and,
              parityLayerValues r 0 .and actual i = -1) ↔
            parityBlockProduct (actual ⟨0, by simp⟩) = -1 := by
        constructor
        · rintro ⟨i, hi, hvalue⟩
          have hproduct := (mem_parityOutputInputs_and_iff r i).mp hi
          have hnode := (parityLayerValues_and_eq_neg_one_iff r 0 actual i).mp hvalue
          rw [hnode] at hproduct
          have hg : (parityLayerEquiv r 0 i).1 = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          rwa [hg] at hproduct
        · intro hproduct
          let g : Fin (r ^ 0) := ⟨0, by simp⟩
          let i : Fin (parityLayerSize r 0) :=
            (parityLayerEquiv r 0).symm (g, actual g)
          refine ⟨i, ?_, ?_⟩
          · apply (mem_parityOutputInputs_and_iff r i).mpr
            simp only [i, Equiv.apply_symm_apply]
            have hg : g = ⟨0, by simp⟩ := by
              apply Fin.ext
              simp [g]
            simpa only [hg] using hproduct
          · apply (parityLayerValues_and_eq_neg_one_iff r 0 actual i).mpr
            simp only [i, Equiv.apply_symm_apply]
      change (if ∃ i ∈ parityOutputInputs r .and,
          parityLayerValues r 0 .and actual i = -1 then -1 else 1) = _
      rcases Int.units_eq_one_or (parityBlockProduct (actual ⟨0, by simp⟩)) with hone | hneg
      · have hnone : ¬(∃ i ∈ parityOutputInputs r .and,
            parityLayerValues r 0 .and actual i = -1) := by
          intro h
          have := hexists.mp h
          have : (1 : Sign) = -1 := hone.symm.trans this
          norm_num at this
        rw [if_neg hnone]
        exact hone.symm
      · have hsome : ∃ i ∈ parityOutputInputs r .and,
            parityLayerValues r 0 .and actual i = -1 := hexists.mpr hneg
        rw [if_pos hsome]
        exact hneg.symm
  | or =>
      have hforall :
          (∀ i ∈ parityOutputInputs r .or,
              parityLayerValues r 0 .or actual i = -1) ↔
            parityBlockProduct (actual ⟨0, by simp⟩) = -1 := by
        constructor
        · intro hall
          by_contra hproduct
          let g : Fin (r ^ 0) := ⟨0, by simp⟩
          let i : Fin (parityLayerSize r 0) :=
            (parityLayerEquiv r 0).symm (g, actual g)
          have hi : i ∈ parityOutputInputs r .or := by
            apply (mem_parityOutputInputs_or_iff r i).mpr
            simp only [i, Equiv.apply_symm_apply]
            intro heq
            apply hproduct
            simpa [g] using heq
          have hvalue := hall i hi
          have hmismatch := (parityLayerValues_or_eq_neg_one_iff r 0 actual i).mp hvalue
          exact hmismatch (by simp only [i, Equiv.apply_symm_apply])
        · intro hproduct i hi
          have hnodeProduct := (mem_parityOutputInputs_or_iff r i).mp hi
          apply (parityLayerValues_or_eq_neg_one_iff r 0 actual i).mpr
          intro hnode
          rw [hnode] at hnodeProduct
          apply hnodeProduct
          have hg : (parityLayerEquiv r 0 i).1 = ⟨0, by simp⟩ := by
            apply Fin.ext
            simp
          rwa [hg]
      change (if ∀ i ∈ parityOutputInputs r .or,
          parityLayerValues r 0 .or actual i = -1 then -1 else 1) = _
      rcases Int.units_eq_one_or (parityBlockProduct (actual ⟨0, by simp⟩)) with hone | hneg
      · have hnotall : ¬(∀ i ∈ parityOutputInputs r .or,
            parityLayerValues r 0 .or actual i = -1) := by
          intro h
          have := hforall.mp h
          have : (1 : Sign) = -1 := hone.symm.trans this
          norm_num at this
        rw [if_neg hnotall]
        exact hone.symm
      · have hall : ∀ i ∈ parityOutputInputs r .or,
            parityLayerValues r 0 .or actual i = -1 := hforall.mpr hneg
        rw [if_pos hall]
        exact hneg.symm

/-! ## Padded bottom-layer bridge -/

@[simp] theorem parityBottomLayerValues_eq_neg_one_iff (n r q : ℕ)
    (x : {−1,1}^[n]) (i : Fin (parityLayerSize r q)) :
    parityBottomLayerValues n r q x i = -1 ↔
      normalizeParityBlockAssignment n r (parityLayerEquiv r q i).1.1
          (parityLayerEquiv r q i).2 =
        parityTreeAssignment n r 0 (parityLayerEquiv r q i).1.1 x := by
  by_cases h : normalizeParityBlockAssignment n r (parityLayerEquiv r q i).1.1
      (parityLayerEquiv r q i).2 =
        parityTreeAssignment n r 0 (parityLayerEquiv r q i).1.1 x <;>
    simp [parityBottomLayerValues, parityExactNodeValue, h]

theorem parityNextActualAssignment_tree (n r t q : ℕ) (x : {−1,1}^[n])
    (g : Fin (r ^ q)) :
    parityNextActualAssignment
        (fun h : Fin (r ^ (q + 1)) ↦ parityTreeAssignment n r t h.1 x) g =
      parityTreeAssignment n r (t + 1) g.1 x := by
  funext j
  simp [parityNextActualAssignment, parityTreeAssignment, parityChildGroup_val]

/-- Bottom-layer wires use normalized assignments, so padded coordinates behave as constants `1`. -/
noncomputable def parityBottomNextNodeInputs (n r q : ℕ)
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r) :
    Finset (Fin (parityLayerSize r (q + 1))) := by
  classical
  exact Finset.univ.filter fun i ↦
    let hb := parityLayerEquiv r (q + 1) i
    ∃ j : Fin r, hb.1 = parityChildGroup g j ∧
      parityBlockProduct (normalizeParityBlockAssignment n r hb.1.1 hb.2) ≠ a j

@[simp] theorem mem_parityBottomNextNodeInputs_iff (n r q : ℕ)
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r)
    (i : Fin (parityLayerSize r (q + 1))) :
    i ∈ parityBottomNextNodeInputs n r q g a ↔
      ∃ j : Fin r,
        (parityLayerEquiv r (q + 1) i).1 = parityChildGroup g j ∧
          parityBlockProduct (normalizeParityBlockAssignment n r
            (parityLayerEquiv r (q + 1) i).1.1
            (parityLayerEquiv r (q + 1) i).2) ≠ a j := by
  simp [parityBottomNextNodeInputs]

/-- The first OR layer restores the ordinary exact-assignment invariant after padding. -/
theorem eval_parityBottomNextNodeInputs (n r q : ℕ) (x : {−1,1}^[n])
    (g : Fin (r ^ q)) (a : ParityBlockAssignment r) :
    CircuitGate.or.evalFinset (parityBottomLayerValues n r (q + 1) x)
        (parityBottomNextNodeInputs n r q g a) =
      parityExactNodeValue .or
        (decide (a = parityTreeAssignment n r 1 g.1 x)) := by
  classical
  have hexists :
      (∃ i ∈ parityBottomNextNodeInputs n r q g a,
          parityBottomLayerValues n r (q + 1) x i = -1) ↔
        a ≠ parityTreeAssignment n r 1 g.1 x := by
    constructor
    · rintro ⟨i, hi, hvalue⟩ hmatch
      obtain ⟨j, hgroup, hproduct⟩ :=
        (mem_parityBottomNextNodeInputs_iff n r q g a i).mp hi
      have hnode := (parityBottomLayerValues_eq_neg_one_iff n r (q + 1) x i).mp hvalue
      have htarget := congrFun hmatch j
      rw [hnode, hgroup] at hproduct
      have htree :
          parityBlockProduct
              (parityTreeAssignment n r 0 (parityChildGroup g j).1 x) =
            parityTreeAssignment n r 1 g.1 x j := by
        simp [parityTreeAssignment, parityChildGroup_val]
      rw [htree] at hproduct
      exact hproduct htarget.symm
    · intro hmatch
      obtain ⟨j, hj⟩ := exists_apply_ne_of_ne hmatch
      let child := parityChildGroup g j
      let b := parityTreeAssignment n r 0 child.1 x
      let i : Fin (parityLayerSize r (q + 1)) :=
        (parityLayerEquiv r (q + 1)).symm (child, b)
      have hbvalid : IsValidParityBlockAssignment n r child.1 b := by
        dsimp only [b]
        rw [parityTreeAssignment_zero_eq_blockValue]
        exact parityBlockValue_valid n r child.1 x
      refine ⟨i, ?_, ?_⟩
      · apply (mem_parityBottomNextNodeInputs_iff n r q g a i).mpr
        refine ⟨j, ?_, ?_⟩
        · simp [i, child]
        · simp only [i, Equiv.apply_symm_apply]
          rw [normalizeParityBlockAssignment_eq_self hbvalid]
          intro hproduct
          apply hj
          have htree : parityBlockProduct b = parityTreeAssignment n r 1 g.1 x j := by
            simp [b, child, parityTreeAssignment, parityChildGroup_val]
          exact hproduct.symm.trans htree
      · apply (parityBottomLayerValues_eq_neg_one_iff n r (q + 1) x i).mpr
        simp only [i, Equiv.apply_symm_apply]
        exact normalizeParityBlockAssignment_eq_self hbvalid
  change (if ∃ i ∈ parityBottomNextNodeInputs n r q g a,
      parityBottomLayerValues n r (q + 1) x i = -1 then -1 else 1) = _
  by_cases hmatch : a = parityTreeAssignment n r 1 g.1 x
  · have hnone : ¬(∃ i ∈ parityBottomNextNodeInputs n r q g a,
        parityBottomLayerValues n r (q + 1) x i = -1) :=
      fun h ↦ (hexists.mp h) hmatch
    rw [if_neg hnone]
    simp [parityExactNodeValue, hmatch]
  · have hsome : ∃ i ∈ parityBottomNextNodeInputs n r q g a,
        parityBottomLayerValues n r (q + 1) x i = -1 := hexists.mpr hmatch
    rw [if_pos hsome]
    simp [parityExactNodeValue, hmatch]

/-! ## Alternating tails above the bottom layer -/

@[simp] theorem circuitTail_layerCount_cast {m k : ℕ} (h : m = k)
    (tail : CircuitTail m) :
    (cast (congrArg CircuitTail h) tail).layerCount = tail.layerCount := by
  subst h
  rfl

@[simp] theorem circuitTail_internalNodeCount_cast {m k : ℕ} (h : m = k)
    (tail : CircuitTail m) :
    (cast (congrArg CircuitTail h) tail).internalNodeCount = tail.internalNodeCount := by
  subst h
  rfl

@[simp] theorem circuitTail_eval_cast {m k : ℕ} (h : m = k)
    (tail : CircuitTail m) (gate : CircuitGate) (values : Fin k → Sign) :
    (cast (congrArg CircuitTail h) tail).eval gate values =
      tail.eval gate (fun i ↦ values (i.cast h)) := by
  subst h
  rfl

theorem eval_parityNextLayer (r q : ℕ) (gate : CircuitGate)
    (actual : Fin (r ^ (q + 1)) → ParityBlockAssignment r)
    (i : Fin (parityLayerSize r q)) :
    gate.dual.evalFinset (parityLayerValues r (q + 1) gate actual)
        ((parityNextLayer r q).get
          (i.cast (length_parityNextLayer r q).symm)) =
      parityLayerValues r q gate.dual
        (parityNextActualAssignment actual) i := by
  rw [get_parityNextLayer]
  change gate.dual.evalFinset (parityLayerValues r (q + 1) gate actual)
      (parityNextNodeInputs r q (parityLayerEquiv r q i).1
        (parityLayerEquiv r q i).2) = _
  exact eval_parityNextNodeInputs r q gate actual
    (parityLayerEquiv r q i).1 (parityLayerEquiv r q i).2

/-- Alternating circuit layers from an ordinary exact-assignment layer through the output. -/
noncomputable def parityStandardTail (r : ℕ) :
    (q : ℕ) → (gate : CircuitGate) → CircuitTail (parityLayerSize r q)
  | 0, gate => .output (parityOutputInputs r gate)
  | q + 1, gate =>
      .layer (parityNextLayer r q)
        (cast (congrArg CircuitTail (length_parityNextLayer r q).symm)
          (parityStandardTail r q gate.dual))

@[simp] theorem parityStandardTail_layerCount (r q : ℕ) (gate : CircuitGate) :
    (parityStandardTail r q gate).layerCount = q + 1 := by
  induction q generalizing gate with
  | zero => simp [parityStandardTail, CircuitTail.layerCount]
  | succ q ih =>
      simp [parityStandardTail, CircuitTail.layerCount, ih]
      omega

@[simp] theorem parityStandardTail_internalNodeCount (r q : ℕ) (gate : CircuitGate) :
    (parityStandardTail r q gate).internalNodeCount =
      ∑ k ∈ Finset.range q, parityLayerSize r k := by
  induction q generalizing gate with
  | zero => simp [parityStandardTail, CircuitTail.internalNodeCount]
  | succ q ih =>
      simp [parityStandardTail, CircuitTail.internalNodeCount, ih, Finset.sum_range_succ,
        Nat.add_comm]

theorem parityStandardTail_eval (n r q t : ℕ) (gate : CircuitGate)
    (x : {−1,1}^[n]) :
    (parityStandardTail r q gate).eval gate.dual
        (parityLayerValues r q gate
          (fun g ↦ parityTreeAssignment n r t g.1 x)) =
      parityTreeValue n r x (t + q + 1) 0 := by
  induction q generalizing t gate with
  | zero =>
      have hout := eval_parityOutputInputs r gate
        (fun g : Fin (r ^ 0) ↦ parityTreeAssignment n r t g.1 x)
      simpa [parityStandardTail, CircuitTail.eval, parityTreeAssignment] using hout
  | succ q ih =>
      simp only [parityStandardTail, CircuitTail.eval]
      rw [circuitTail_eval_cast (length_parityNextLayer r q).symm]
      have hlayer :
          (fun i : Fin (parityLayerSize r q) ↦
              gate.dual.evalFinset
                (parityLayerValues r (q + 1) gate
                  (fun g ↦ parityTreeAssignment n r t g.1 x))
                ((parityNextLayer r q).get
                  (i.cast (length_parityNextLayer r q).symm))) =
            parityLayerValues r q gate.dual
              (fun g ↦ parityTreeAssignment n r (t + 1) g.1 x) := by
        funext i
        rw [eval_parityNextLayer]
        congr 1
        funext g
        exact parityNextActualAssignment_tree n r t q x g
      rw [hlayer]
      rw [CircuitGate.dual_dual]
      have hexponent : t + 1 + q + 1 = t + (q + 1) + 1 := by omega
      rw [← hexponent]
      simpa only [CircuitGate.dual_dual] using ih (t := t + 1) gate.dual

/-! ## Complete padded circuits of depth at least three -/

/-- The first OR layer above the padded minterms. -/
noncomputable def parityBottomNextLayer (n r q : ℕ) :
    List (Finset (Fin (parityLayerSize r (q + 1)))) :=
  List.ofFn fun i : Fin (parityLayerSize r q) ↦
    let ga := parityLayerEquiv r q i
    parityBottomNextNodeInputs n r q ga.1 ga.2

@[simp] theorem length_parityBottomNextLayer (n r q : ℕ) :
    (parityBottomNextLayer n r q).length = parityLayerSize r q := by
  simp [parityBottomNextLayer]

theorem get_parityBottomNextLayer (n r q : ℕ) (i : Fin (parityLayerSize r q)) :
    (parityBottomNextLayer n r q).get
        (i.cast (length_parityBottomNextLayer n r q).symm) =
      let ga := parityLayerEquiv r q i
      parityBottomNextNodeInputs n r q ga.1 ga.2 := by
  simp [parityBottomNextLayer]

theorem eval_parityBottomNextLayer (n r q : ℕ) (x : {−1,1}^[n])
    (i : Fin (parityLayerSize r q)) :
    CircuitGate.or.evalFinset (parityBottomLayerValues n r (q + 1) x)
        ((parityBottomNextLayer n r q).get
          (i.cast (length_parityBottomNextLayer n r q).symm)) =
      parityLayerValues r q .or
        (fun g ↦ parityTreeAssignment n r 1 g.1 x) i := by
  rw [get_parityBottomNextLayer]
  change CircuitGate.or.evalFinset (parityBottomLayerValues n r (q + 1) x)
      (parityBottomNextNodeInputs n r q (parityLayerEquiv r q i).1
        (parityLayerEquiv r q i).2) = _
  exact eval_parityBottomNextNodeInputs n r q x
    (parityLayerEquiv r q i).1 (parityLayerEquiv r q i).2

/-- Tail of the padded construction. Its input layer consists of bottom minterms with
`r ^ (q + 1)` blocks; the resulting circuit has `q + 2` further layers including output. -/
noncomputable def parityPaddedTail (n r q : ℕ) :
    CircuitTail (parityLayerSize r (q + 1)) :=
  .layer (parityBottomNextLayer n r q)
    (cast (congrArg CircuitTail (length_parityBottomNextLayer n r q).symm)
      (parityStandardTail r q .or))

@[simp] theorem parityPaddedTail_layerCount (n r q : ℕ) :
    (parityPaddedTail n r q).layerCount = q + 2 := by
  simp [parityPaddedTail, CircuitTail.layerCount]
  omega

@[simp] theorem parityPaddedTail_internalNodeCount (n r q : ℕ) :
    (parityPaddedTail n r q).internalNodeCount =
      ∑ k ∈ Finset.range (q + 1), parityLayerSize r k := by
  simp [parityPaddedTail, CircuitTail.internalNodeCount,
    parityStandardTail_internalNodeCount, Finset.sum_range_succ, Nat.add_comm]

theorem parityPaddedTail_eval (n r q : ℕ) (x : {−1,1}^[n]) :
    (parityPaddedTail n r q).eval .or
        (parityBottomLayerValues n r (q + 1) x) =
      parityTreeValue n r x (q + 2) 0 := by
  simp only [parityPaddedTail, CircuitTail.eval]
  rw [circuitTail_eval_cast (length_parityBottomNextLayer n r q).symm]
  have hlayer :
      (fun i : Fin (parityLayerSize r q) ↦
          CircuitGate.or.evalFinset (parityBottomLayerValues n r (q + 1) x)
            ((parityBottomNextLayer n r q).get
              (i.cast (length_parityBottomNextLayer n r q).symm))) =
        parityLayerValues r q .or
          (fun g ↦ parityTreeAssignment n r 1 g.1 x) := by
    funext i
    exact eval_parityBottomNextLayer n r q x i
  rw [hlayer]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    parityStandardTail_eval n r q 1 .or x

/-- Exercise 4.12(c)-(d), parameterized construction. Here `q + 2 = d - 1` is the number
of non-output internal layers, so the circuit depth is `q + 3`. -/
noncomputable def parityDepthCircuitFromBlocks (n r q : ℕ) : DepthCircuit n where
  layer1Gate := .and
  layer1 := parityFirstLayer n r (q + 1)
  tail := cast
    (congrArg CircuitTail (length_parityFirstLayer n r (q + 1)).symm)
    (parityPaddedTail n r q)

@[simp] theorem depth_parityDepthCircuitFromBlocks (n r q : ℕ) :
    (parityDepthCircuitFromBlocks n r q).depth = q + 3 := by
  simp [parityDepthCircuitFromBlocks, DepthCircuit.depth]
  omega

@[simp] theorem size_parityDepthCircuitFromBlocks (n r q : ℕ) :
    (parityDepthCircuitFromBlocks n r q).size =
      ∑ k ∈ Finset.range (q + 2), parityLayerSize r k := by
  simp [parityDepthCircuitFromBlocks, DepthCircuit.size,
    Finset.sum_range_succ, Nat.add_comm]

theorem eval_parityDepthCircuitFromBlocks (n r q : ℕ) (x : {−1,1}^[n]) :
    (parityDepthCircuitFromBlocks n r q).eval x =
      parityTreeValue n r x (q + 2) 0 := by
  rw [DepthCircuit.eval]
  change (cast
      (congrArg CircuitTail (length_parityFirstLayer n r (q + 1)).symm)
      (parityPaddedTail n r q)).eval .or
        ((parityDepthCircuitFromBlocks n r q).evalLayer1 x) = _
  rw [circuitTail_eval_cast (length_parityFirstLayer n r (q + 1)).symm]
  convert parityPaddedTail_eval n r q x using 1
  apply congrArg ((parityPaddedTail n r q).eval .or)
  funext i
  simpa only using eval_parityFirstLayer n r (q + 1) x i

/-! ## Identification with full parity -/

/-- Flatten one `r`-ary digit and a lower-level index into the next power of `r`. -/
def parityTreeIndexEquiv (r t : ℕ) :
    Fin r × Fin (r ^ t) ≃ Fin (r ^ (t + 1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ]; ac_rfl))

@[simp] theorem parityTreeIndexEquiv_val (r t : ℕ) (jk : Fin r × Fin (r ^ t)) :
    (parityTreeIndexEquiv r t jk).1 = jk.1.1 * r ^ t + jk.2.1 := by
  simp [parityTreeIndexEquiv, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem parityTreeValue_eq_prod_fin (n r t g : ℕ) (x : {−1,1}^[n]) :
    parityTreeValue n r x t g =
      ∏ k : Fin (r ^ t), paddedParityInput n x (g * r ^ t + k.1) := by
  induction t generalizing g with
  | zero =>
      simp [parityTreeValue, paddedParityInput]
  | succ t ih =>
      rw [parityTreeValue_succ]
      simp_rw [ih]
      rw [← Fintype.prod_prod_type']
      apply Fintype.prod_equiv (parityTreeIndexEquiv r t)
      intro jk
      congr 1
      simp [parityTreeIndexEquiv_val, pow_succ]
      ring

theorem prod_paddedParityInput_eq_prod (n m : ℕ) (x : {−1,1}^[n]) (hnm : n ≤ m) :
    (∏ i : Fin m, paddedParityInput n x i.1) = ∏ i : Fin n, x i := by
  classical
  change (∏ i : Fin m, if h : i.1 < n then x ⟨i.1, h⟩ else 1) = _
  rw [Fintype.prod_dite]
  simp only [Finset.prod_const_one, mul_one]
  symm
  apply Fintype.prod_equiv (Fin.castLEquiv hnm)
  intro i
  rfl

/-- Padding by neutral signs does not change full parity. -/
theorem parityTreeValue_eq_parityFunction (n r h : ℕ) (x : {−1,1}^[n])
    (hcover : n ≤ r ^ h) :
    parityTreeValue n r x h 0 =
      parityFunction (Finset.univ : Finset (Fin n)) x := by
  rw [parityTreeValue_eq_prod_fin]
  simp only [zero_mul, zero_add]
  rw [prod_paddedParityInput_eq_prod n (r ^ h) x hcover]
  simp [parityFunction]

theorem toBooleanFunction_parityDepthCircuitFromBlocks (n r q : ℕ)
    (hcover : n ≤ r ^ (q + 2)) :
    (parityDepthCircuitFromBlocks n r q).toBooleanFunction =
      parityFunction (Finset.univ : Finset (Fin n)) := by
  funext x
  rw [DepthCircuit.toBooleanFunction, eval_parityDepthCircuitFromBlocks]
  exact parityTreeValue_eq_parityFunction n r (q + 2) x hcover

/-! ## Quantitative bounds and the canonical block side -/

theorem sum_parityLayerSize_le (r h : ℕ) (hr : 1 ≤ r) (hh : 0 < h) :
    (∑ k ∈ Finset.range h, parityLayerSize r k) ≤
      h * r ^ (h - 1) * 2 ^ r := by
  calc
    (∑ k ∈ Finset.range h, parityLayerSize r k) ≤
        (Finset.range h).card • (r ^ (h - 1) * 2 ^ r) := by
      apply Finset.sum_le_card_nsmul
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [parityLayerSize]
      gcongr
      omega
    _ = h * r ^ (h - 1) * 2 ^ r := by simp [mul_assoc]

theorem size_parityDepthCircuitFromBlocks_le (n r q : ℕ) (hr : 1 ≤ r) :
    (parityDepthCircuitFromBlocks n r q).size ≤
      (q + 2) * r ^ (q + 1) * 2 ^ r := by
  rw [size_parityDepthCircuitFromBlocks]
  simpa only [Nat.add_sub_cancel] using sum_parityLayerSize_le r (q + 2) hr (by omega)

/-- Real `h`th root used by the canonical block decomposition. -/
noncomputable def parityRealRoot (n h : ℕ) : ℝ :=
  (n : ℝ) ^ ((h : ℝ)⁻¹)

/-- Ceiling of the real `h`th root, clamped to one so every block has a genuine arity. -/
noncomputable def parityBlockSide (n h : ℕ) : ℕ :=
  max 1 ⌈parityRealRoot n h⌉₊

theorem parityRealRoot_nonneg (n h : ℕ) : 0 ≤ parityRealRoot n h := by
  exact Real.rpow_nonneg (by positivity) _

/-- The polynomial part of the block count is exactly the exponent appearing in the book. -/
theorem parityRealRoot_pow_pred (n h : ℕ) (hh : 0 < h) :
    parityRealRoot n h ^ (h - 1) =
      (n : ℝ) ^ (1 - (h : ℝ)⁻¹) := by
  rw [parityRealRoot, ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp [hh']

theorem one_le_parityBlockSide (n h : ℕ) : 1 ≤ parityBlockSide n h := by
  exact le_max_left _ _

theorem parityRealRoot_le_blockSide (n h : ℕ) :
    parityRealRoot n h ≤ (parityBlockSide n h : ℝ) := by
  calc
    parityRealRoot n h ≤ (⌈parityRealRoot n h⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (parityBlockSide n h : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈parityRealRoot n h⌉₊

/-- The ceiling loses less than one; this is the explicit bridge to the book's root scale. -/
theorem parityBlockSide_le_root_add_one (n h : ℕ) :
    (parityBlockSide n h : ℝ) ≤ parityRealRoot n h + 1 := by
  rw [parityBlockSide, Nat.cast_max]
  apply max_le
  · simpa only [Nat.cast_one, zero_add, add_comm] using
      add_le_add_right (parityRealRoot_nonneg n h) (1 : ℝ)
  · exact (Nat.ceil_lt_add_one (parityRealRoot_nonneg n h)).le

theorem parityBlockSide_pow_covers (n h : ℕ) (hh : 0 < h) :
    n ≤ parityBlockSide n h ^ h := by
  have hroot : parityRealRoot n h ^ h = (n : ℝ) := by
    exact Real.rpow_inv_natCast_pow (by positivity) hh.ne'
  have hreal : (n : ℝ) ≤ (parityBlockSide n h : ℝ) ^ h := by
    rw [← hroot]
    exact pow_le_pow_left₀ (parityRealRoot_nonneg n h)
      (parityRealRoot_le_blockSide n h) h
  exact_mod_cast hreal

theorem DepthCircuit.width_le_dimension {n : ℕ} (C : DepthCircuit n) : C.width ≤ n := by
  rw [DepthCircuit.width, DNFFormula.width_le_iff]
  intro term hterm
  exact term.width_le_dimension

/-- Canonical finite form of Exercise 4.12(d). Setting `d = q + 3` and
`r = ⌈n^(1/(d-1))⌉` gives exactly the book's block construction. -/
theorem hasDepthCircuit_parity_canonical (n q : ℕ) :
    DepthCircuit.HasDepthCircuit (parityFunction (Finset.univ : Finset (Fin n)))
      (q + 3)
      ((q + 2) * parityBlockSide n (q + 2) ^ (q + 1) *
        2 ^ parityBlockSide n (q + 2)) n := by
  let r := parityBlockSide n (q + 2)
  refine ⟨parityDepthCircuitFromBlocks n r q,
    depth_parityDepthCircuitFromBlocks n r q, ?_,
    (parityDepthCircuitFromBlocks n r q).width_le_dimension, ?_⟩
  · exact size_parityDepthCircuitFromBlocks_le n r q (one_le_parityBlockSide n (q + 2))
  · exact toBooleanFunction_parityDepthCircuitFromBlocks n r q
      (parityBlockSide_pow_covers n (q + 2) (by omega))

/-- Root-scale envelope for the canonical circuit. This is the explicit finite inequality behind
`O(n^(1-1/(d-1))) * 2^(n^(1/(d-1)))`; the two `+1`s are absorbed by constant factors. -/
theorem canonicalParityCircuit_size_real_le (n q : ℕ) :
    ((parityDepthCircuitFromBlocks n (parityBlockSide n (q + 2)) q).size : ℝ) ≤
      (q + 2 : ℝ) * (parityRealRoot n (q + 2) + 1) ^ (q + 1) *
        (2 : ℝ) ^ (parityRealRoot n (q + 2) + 1) := by
  let r := parityBlockSide n (q + 2)
  have hsizeNat := size_parityDepthCircuitFromBlocks_le n r q
    (one_le_parityBlockSide n (q + 2))
  have hsizeReal :
      ((parityDepthCircuitFromBlocks n r q).size : ℝ) ≤
        (q + 2 : ℝ) * (r : ℝ) ^ (q + 1) * (2 : ℝ) ^ r := by
    exact_mod_cast hsizeNat
  have hside : (r : ℝ) ≤ parityRealRoot n (q + 2) + 1 :=
    parityBlockSide_le_root_add_one n (q + 2)
  have hpoly : (r : ℝ) ^ (q + 1) ≤
      (parityRealRoot n (q + 2) + 1) ^ (q + 1) :=
    pow_le_pow_left₀ (by positivity) hside _
  have hexponential : (2 : ℝ) ^ r ≤
      (2 : ℝ) ^ (parityRealRoot n (q + 2) + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hside
  calc
    ((parityDepthCircuitFromBlocks n r q).size : ℝ) ≤
        (q + 2 : ℝ) * (r : ℝ) ^ (q + 1) * (2 : ℝ) ^ r := hsizeReal
    _ ≤ (q + 2 : ℝ) * (parityRealRoot n (q + 2) + 1) ^ (q + 1) *
        (2 : ℝ) ^ r := by gcongr
    _ ≤ (q + 2 : ℝ) * (parityRealRoot n (q + 2) + 1) ^ (q + 1) *
        (2 : ℝ) ^ (parityRealRoot n (q + 2) + 1) := by
      apply mul_le_mul_of_nonneg_left hexponential
      exact mul_nonneg (by positivity)
        (pow_nonneg (add_nonneg (parityRealRoot_nonneg n (q + 2)) (by norm_num)) _)

/-- Exercise 4.12(c): the depth-three square-root block construction. -/
theorem hasDepthCircuit_parity_depth_three (n : ℕ) :
    DepthCircuit.HasDepthCircuit (parityFunction (Finset.univ : Finset (Fin n))) 3
      (2 * parityBlockSide n 2 * 2 ^ parityBlockSide n 2) n := by
  simpa only [Nat.zero_add, Nat.add_zero, pow_one] using
    hasDepthCircuit_parity_canonical n 0

/-- The `d = 2` endpoint of Exercise 4.12(d), supplied by the canonical parity DNF. -/
theorem hasDepthCircuit_parity_depth_two (n : ℕ) :
    DepthCircuit.HasDepthCircuit (parityFunction (Finset.univ : Finset (Fin n))) 2
      (2 ^ parityBlockSide n 1) n := by
  let φ := parityDNF n
  refine ⟨DepthCircuit.ofDNF φ, DepthCircuit.depth_ofDNF φ, ?_,
    (DepthCircuit.ofDNF φ).width_le_dimension, ?_⟩
  · rw [DepthCircuit.size_ofDNF]
    calc
      φ.size ≤ 2 ^ n := size_mintermDNF_le _
      _ ≤ 2 ^ parityBlockSide n 1 := by
        apply Nat.pow_le_pow_right (by decide)
        simpa only [pow_one] using parityBlockSide_pow_covers n 1 (by omega)
  · rw [DepthCircuit.toBooleanFunction_ofDNF]
    exact parityDNF_toBooleanFunction n

/-- Exercise 4.12(d) with the book's full range `d ≥ 2`, without weakening its parity target
or changing the layered alternating circuit model. -/
theorem hasDepthCircuit_parity_general (n d : ℕ) (hd : 2 ≤ d) :
    DepthCircuit.HasDepthCircuit (parityFunction (Finset.univ : Finset (Fin n))) d
      ((d - 1) * parityBlockSide n (d - 1) ^ (d - 2) *
        2 ^ parityBlockSide n (d - 1)) n := by
  rcases hd.eq_or_lt with rfl | hd
  · simpa using hasDepthCircuit_parity_depth_two n
  · have hthree : d - 3 + 3 = d := by omega
    have htwo : d - 3 + 2 = d - 1 := by omega
    have hone : d - 3 + 1 = d - 2 := by omega
    simpa only [hthree, htwo, hone] using hasDepthCircuit_parity_canonical n (d - 3)


/-! ## Fourier obstruction to approximating parity -/


variable {n : ℕ}

/-- Agreement and disagreement probabilities of two Boolean functions add to one. -/
theorem uniformProbability_eq_add_ne (f g : BooleanFunction n) :
    uniformProbability (fun x ↦ f x = g x) +
      uniformProbability (fun x ↦ f x ≠ g x) = 1 := by
  classical
  unfold uniformProbability
  rw [← Finset.expect_add_distrib]
  calc
    (𝔼 x, ((if f x = g x then (1 : ℝ) else 0) +
      (if f x ≠ g x then (1 : ℝ) else 0))) =
        𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      by_cases h : f x = g x <;> simp [h]
    _ = 1 := Fintype.expect_const 1

/-- The top Fourier coefficient is twice the agreement advantage over one half with parity. -/
theorem fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one
    (f : BooleanFunction n) :
    fourierCoeff f.toReal (Finset.univ : Finset (Fin n)) =
      2 * uniformProbability (fun x ↦
        f x = parityFunction (Finset.univ : Finset (Fin n)) x) - 1 := by
  let parity := parityFunction (Finset.univ : Finset (Fin n))
  have htotal := uniformProbability_eq_add_ne f parity
  calc
    fourierCoeff f.toReal (Finset.univ : Finset (Fin n)) =
        ⟪f.toReal, parity.toReal⟫ᵤ := by
      rw [parityFunction_toReal, fourierCoeff_eq_uniformInner]
    _ = uniformProbability (fun x ↦ f x = parity x) -
        uniformProbability (fun x ↦ f x ≠ parity x) :=
      uniformInner_eq_uniformProbability_eq_sub_ne f parity
    _ = 2 * uniformProbability (fun x ↦ f x = parity x) - 1 := by linarith

/-- If a Boolean function has constant agreement advantage `ε₀` with parity, then a Fourier
concentration error below `4 ε₀²` cannot use a cutoff below the top degree. -/
theorem parityAgreement_forces_concentration_cutoff
    (f : BooleanFunction n) {ε₀ ε k : ℝ}
    (hε₀ : 0 < ε₀) (hε : ε < 4 * ε₀ ^ 2)
    (hagreement :
      1 / 2 + ε₀ ≤ uniformProbability (fun x ↦
        f x = parityFunction (Finset.univ : Finset (Fin n)) x))
    (hconcentration : IsFourierSpectrumConcentratedUpTo f.toReal ε k) :
    (n : ℝ) ≤ k := by
  by_contra hkn
  have hk : k < (n : ℝ) := lt_of_not_ge hkn
  have hcoeff :
      2 * ε₀ ≤ fourierCoeff f.toReal (Finset.univ : Finset (Fin n)) := by
    rw [fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one]
    linarith
  have htop :
      fourierCoeff f.toReal (Finset.univ : Finset (Fin n)) ^ 2 ≤
        fourierWeightAboveReal k f.toReal := by
    unfold fourierWeightAboveReal fourierWeight
    apply Finset.single_le_sum (fun S _ ↦ sq_nonneg (fourierCoeff f.toReal S))
    simp [hk]
  have hupper :
      fourierCoeff f.toReal (Finset.univ : Finset (Fin n)) ^ 2 ≤ ε :=
    htop.trans hconcentration
  nlinarith


end FABL
