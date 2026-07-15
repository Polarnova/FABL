/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.Circuits
public import FABL.Chapter04.Switching
public import FABL.Chapter04.DNFFormulas
public import FABL.Chapter04.DNFFourier
public import FABL.Chapter04.HastadSwitching
public import FABL.Chapter04.RandomRestrictions

/-!
# Total influence of bounded-depth circuits

Book items: Exercise 4.20 and Theorem 4.30.

The proof follows the book's random-restriction induction.  Its pure core works directly with
the semantic evaluation of a `CircuitTail`: switching a whole layer supplies bounded-width
descriptions for the next tail without constructing a second circuit syntax.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {m n : ℕ}

namespace CircuitGate

/-- The width certificate matching the connective of a circuit layer. -/
def HasWidthLE (gate : CircuitGate) (f : BooleanFunction n) (w : ℕ) : Prop :=
  match gate with
  | .and => HasCNFWidthLE f w
  | .or => HasDNFWidthLE f w

theorem hasWidthLE_mono {gate : CircuitGate} {f : BooleanFunction n} {u v : ℕ}
    (huv : u ≤ v) (hf : gate.HasWidthLE f u) : gate.HasWidthLE f v := by
  cases gate with
  | and =>
      obtain ⟨ψ, hψ, rfl⟩ := hf
      exact ⟨ψ, hψ.trans huv, rfl⟩
  | or =>
      obtain ⟨φ, hφ, rfl⟩ := hf
      exact ⟨φ, hφ.trans huv, rfl⟩

/-- Pointwise lifting of a gate to Boolean functions. -/
def evalFinsetFunction (gate : CircuitGate) (values : Fin m → BooleanFunction n)
    (inputs : Finset (Fin m)) : BooleanFunction n :=
  fun x ↦ gate.evalFinset (fun i ↦ values i x) inputs

@[simp] theorem evalFinsetFunction_apply (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) (inputs : Finset (Fin m)) (x : {−1,1}^[n]) :
    gate.evalFinsetFunction values inputs x =
      gate.evalFinset (fun i ↦ values i x) inputs := rfl

/-- Combining formulas with the matching gate preserves their common width bound. -/
theorem hasWidthLE_evalFinsetFunction (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) (inputs : Finset (Fin m)) {w : ℕ}
    (hvalues : ∀ i ∈ inputs, gate.HasWidthLE (values i) w) :
    gate.HasWidthLE (gate.evalFinsetFunction values inputs) w := by
  classical
  cases gate with
  | or =>
      let formula : Fin m → DNFFormula n := fun i ↦
        if hi : i ∈ inputs then Classical.choose (hvalues i hi) else ⟨[]⟩
      have formula_spec (i : Fin m) (hi : i ∈ inputs) :
          (formula i).width ≤ w ∧ (formula i).toBooleanFunction = values i := by
        simpa [formula, hi] using Classical.choose_spec (hvalues i hi)
      let combined : DNFFormula n :=
        ⟨inputs.toList.flatMap fun i ↦ (formula i).terms⟩
      have hwidth : combined.width ≤ w := by
        rw [DNFFormula.width_le_iff]
        intro term hterm
        simp only [combined, List.mem_flatMap, Finset.mem_toList] at hterm
        obtain ⟨i, hi, hterm⟩ := hterm
        exact DNFFormula.width_le_of_mem (formula i) hterm |>.trans
          (formula_spec i hi).1
      refine ⟨combined, hwidth, ?_⟩
      funext x
      have hneg : combined.eval x = -1 ↔
          CircuitGate.or.evalFinset (fun i ↦ values i x) inputs = -1 := by
        rw [DNFFormula.eval_eq_neg_one_iff,
          CircuitGate.evalFinset_or_eq_neg_one_iff]
        simp only [combined, List.mem_flatMap, Finset.mem_toList]
        constructor
        · rintro ⟨term, ⟨i, hi, hterm⟩, htermx⟩
          refine ⟨i, hi, ?_⟩
          have hformula := formula_spec i hi
          rw [← hformula.2]
          exact (DNFFormula.eval_eq_neg_one_iff (formula i) x).2 ⟨term, hterm, htermx⟩
        · rintro ⟨i, hi, hix⟩
          have hformula := formula_spec i hi
          rw [← hformula.2] at hix
          obtain ⟨term, hterm, htermx⟩ :=
            (DNFFormula.eval_eq_neg_one_iff (formula i) x).1 hix
          exact ⟨term, ⟨i, hi, hterm⟩, htermx⟩
      change combined.eval x =
        CircuitGate.or.evalFinset (fun i ↦ values i x) inputs
      rcases Int.units_eq_one_or (combined.eval x) with hc | hc <;>
        rcases Int.units_eq_one_or
          (CircuitGate.or.evalFinset (fun i ↦ values i x) inputs) with hg | hg
      · exact hc.trans hg.symm
      · exact False.elim (by simpa [hc] using hneg.mpr hg)
      · exact False.elim (by simpa [hg] using hneg.mp hc)
      · exact hc.trans hg.symm
  | and =>
      let formula : Fin m → CNFFormula n := fun i ↦
        if hi : i ∈ inputs then Classical.choose (hvalues i hi) else ⟨[]⟩
      have formula_spec (i : Fin m) (hi : i ∈ inputs) :
          (formula i).width ≤ w ∧ (formula i).toBooleanFunction = values i := by
        simpa [formula, hi] using Classical.choose_spec (hvalues i hi)
      let combined : CNFFormula n :=
        ⟨inputs.toList.flatMap fun i ↦ (formula i).clauses⟩
      have hwidth : combined.width ≤ w := by
        change (DNFFormula.mk combined.clauses).width ≤ w
        rw [DNFFormula.width_le_iff]
        intro clause hclause
        simp only [combined, List.mem_flatMap, Finset.mem_toList] at hclause
        obtain ⟨i, hi, hclause⟩ := hclause
        have hiwidth := (formula_spec i hi).1
        change (DNFFormula.mk (formula i).clauses).width ≤ w at hiwidth
        exact DNFFormula.width_le_of_mem (DNFFormula.mk (formula i).clauses) hclause |>.trans
          hiwidth
      refine ⟨combined, hwidth, ?_⟩
      funext x
      have hneg : combined.eval x = -1 ↔
          CircuitGate.and.evalFinset (fun i ↦ values i x) inputs = -1 := by
        rw [show combined.eval x = -1 ↔
            ∀ clause ∈ combined.clauses, CNFFormula.clauseEval clause x = -1 by
              simp [CNFFormula.eval, List.all_eq_true],
          CircuitGate.evalFinset_and_eq_neg_one_iff]
        constructor
        · intro hall i hi
          have hformula := formula_spec i hi
          rw [← hformula.2]
          change (formula i).eval x = -1
          rw [show (formula i).eval x = -1 ↔
              ∀ clause ∈ (formula i).clauses,
                CNFFormula.clauseEval clause x = -1 by
            simp [CNFFormula.eval, List.all_eq_true]]
          intro clause hclause
          exact hall clause (by
            simp only [combined, List.mem_flatMap, Finset.mem_toList]
            exact ⟨i, hi, hclause⟩)
        · intro hall clause hclause
          simp only [combined, List.mem_flatMap, Finset.mem_toList] at hclause
          obtain ⟨i, hi, hclause⟩ := hclause
          have hix := hall i hi
          have hformula := formula_spec i hi
          rw [← hformula.2] at hix
          change (formula i).eval x = -1 at hix
          have hallClauses :
              ∀ C ∈ (formula i).clauses, CNFFormula.clauseEval C x = -1 := by
            rw [show (formula i).eval x = -1 ↔
                ∀ C ∈ (formula i).clauses,
                  CNFFormula.clauseEval C x = -1 by
              simp [CNFFormula.eval, List.all_eq_true]] at hix
            exact hix
          exact hallClauses clause hclause
      change combined.eval x =
        CircuitGate.and.evalFinset (fun i ↦ values i x) inputs
      rcases Int.units_eq_one_or (combined.eval x) with hc | hc <;>
        rcases Int.units_eq_one_or
          (CircuitGate.and.evalFinset (fun i ↦ values i x) inputs) with hg | hg
      · exact hc.trans hg.symm
      · exact False.elim (by simpa [hc] using hneg.mpr hg)
      · exact False.elim (by simpa [hg] using hneg.mp hc)
      · exact hc.trans hg.symm

end CircuitGate

namespace F₂DecisionTree

/-- Minimum decision-tree depth gives a DNF width certificate. -/
theorem hasDNFWidthLE_decisionTreeDepth (f : BooleanFunction n) :
    HasDNFWidthLE f (decisionTreeDepth (binaryOfBooleanFunction f)) := by
  obtain ⟨T, hT, hdepth⟩ :=
    exists_computingTree_depth_eq_decisionTreeDepth (binaryOfBooleanFunction f)
  have hwidth := (hasDNFSizeWidth_of_computes T f hT).2
  simpa [hdepth] using hwidth

end F₂DecisionTree

/-- Applying Boolean duality to two functions is injective. -/
theorem booleanDual_injective :
    Function.Injective (CNFFormula.booleanDual : BooleanFunction n → BooleanFunction n) := by
  intro f g h
  funext x
  have hx := congrFun h (fun i ↦ -x i)
  simpa [CNFFormula.booleanDual] using hx

/-- Minimum decision-tree depth also gives a CNF width certificate. -/
theorem F₂DecisionTree.hasCNFWidthLE_decisionTreeDepth (f : BooleanFunction n) :
    HasCNFWidthLE f (F₂DecisionTree.decisionTreeDepth (binaryOfBooleanFunction f)) := by
  let g := CNFFormula.booleanDual f
  have hbinary : binaryOfBooleanFunction g =
      binaryBooleanDual (binaryOfBooleanFunction f) := by
    funext x
    simp only [g, binaryOfBooleanFunction, binaryBooleanDual, CNFFormula.booleanDual]
    congr 2
    funext i
    exact (signEncode_binaryCubeComplement x i).symm
  have hdepth :
      F₂DecisionTree.decisionTreeDepth (binaryOfBooleanFunction g) =
        F₂DecisionTree.decisionTreeDepth (binaryOfBooleanFunction f) := by
    rw [hbinary, decisionTreeDepth_binaryBooleanDual]
  obtain ⟨φ, hφwidth, hφ⟩ := F₂DecisionTree.hasDNFWidthLE_decisionTreeDepth g
  let ψ : CNFFormula n := ⟨φ.terms⟩
  refine ⟨ψ, ?_, ?_⟩
  · simpa [ψ, CNFFormula.width] using hφwidth.trans_eq hdepth
  · apply booleanDual_injective
    calc
      CNFFormula.booleanDual ψ.toBooleanFunction = φ.toBooleanFunction := by
        simpa [ψ, CNFFormula.switchAndOr] using
          (CNFFormula.switchAndOr_toBooleanFunction ψ).symm
      _ = CNFFormula.booleanDual f := hφ

/-- A decision tree supplies the width certificate required by either possible next gate. -/
theorem CircuitGate.hasWidthLE_decisionTreeDepth (gate : CircuitGate)
    (f : BooleanFunction n) :
    gate.HasWidthLE f
      (F₂DecisionTree.decisionTreeDepth (binaryOfBooleanFunction f)) := by
  cases gate with
  | and => exact F₂DecisionTree.hasCNFWidthLE_decisionTreeDepth f
  | or => exact F₂DecisionTree.hasDNFWidthLE_decisionTreeDepth f

/-- The width bound for either a DNF or a CNF gives the same influence estimate. -/
theorem totalInfluence_le_two_mul_of_hasWidthLE
    (gate : CircuitGate) (f : BooleanFunction n) {w : ℕ}
    (hf : gate.HasWidthLE f w) :
    totalInfluence f.toReal ≤ 2 * w := by
  cases gate with
  | or => exact totalInfluence_le_two_mul_of_hasDNFWidthLE hf
  | and => exact totalInfluence_le_two_mul_of_hasCNFWidthLE hf

/-- A width-zero formula computes a constant function, for either layer connective. -/
theorem CircuitGate.exists_eq_const_of_hasWidthLE_zero
    (gate : CircuitGate) (f : BooleanFunction n) (hf : gate.HasWidthLE f 0) :
    ∃ c : Sign, f = fun _ ↦ c := by
  classical
  let x₀ : {−1,1}^[n] := fun _ ↦ 1
  cases gate with
  | or =>
      obtain ⟨φ, hφwidth, hφ⟩ := hf
      have hzero : φ.width = 0 := Nat.eq_zero_of_le_zero hφwidth
      refine ⟨f x₀, funext fun x ↦ ?_⟩
      rw [← hφ]
      exact φ.toBooleanFunction_eq_of_width_eq_zero hzero x x₀
  | and =>
      obtain ⟨ψ, hψwidth, hψ⟩ := hf
      let φ := CNFFormula.switchAndOr ψ
      have hφzero : φ.width = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa [φ, CNFFormula.switchAndOr, CNFFormula.width] using hψwidth
      refine ⟨f x₀, funext fun x ↦ ?_⟩
      rw [← hψ]
      have hconst := φ.toBooleanFunction_eq_of_width_eq_zero hφzero
        (fun i ↦ -x i) (fun i ↦ -x₀ i)
      rw [CNFFormula.switchAndOr_toBooleanFunction] at hconst
      simpa [CNFFormula.booleanDual] using congrArg Neg.neg hconst

namespace CircuitTail

/-- Semantic evaluation of a tail whose input nodes already compute Boolean functions. -/
def evalFunction (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) : BooleanFunction n :=
  fun x ↦ tail.eval gate (fun i ↦ values i x)

@[simp] theorem evalFunction_output (inputs : Finset (Fin m)) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) :
    (CircuitTail.output inputs).evalFunction gate values =
      gate.evalFinsetFunction values inputs := rfl

@[simp] theorem evalFunction_layer (gates : List (Finset (Fin m)))
    (rest : CircuitTail gates.length) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) :
    (CircuitTail.layer gates rest).evalFunction gate values =
      rest.evalFunction gate.dual
        (fun i ↦ gate.evalFinsetFunction values (gates.get i)) := rfl

/-- Restriction commutes with the pure evaluation of a circuit tail. -/
theorem extendedSignRestriction_evalFunction (tail : CircuitTail m)
    (gate : CircuitGate) (values : Fin m → BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    extendedSignRestriction (tail.evalFunction gate values) J z =
      tail.evalFunction gate
        (fun i ↦ extendedSignRestriction (values i) J z) := by
  funext x
  rfl

/-- A tail fed only constant functions computes a constant function. -/
theorem exists_eq_const_evalFunction_of_values
    (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) (constants : Fin m → Sign)
    (hvalues : ∀ i, values i = fun _ ↦ constants i) :
    ∃ c : Sign, tail.evalFunction gate values = fun _ ↦ c := by
  induction tail generalizing gate with
  | output inputs =>
      refine ⟨gate.evalFinset constants inputs, funext fun x ↦ ?_⟩
      simp only [evalFunction, CircuitTail.eval]
      congr 2
      funext i
      rw [hvalues i]
  | layer gates rest ih =>
      let nextConstants : Fin gates.length → Sign := fun i ↦
        gate.evalFinset constants (gates.get i)
      have hnext : ∀ i,
          gate.evalFinsetFunction values (gates.get i) =
            fun _ ↦ nextConstants i := by
        intro i
        funext x
        simp only [CircuitGate.evalFinsetFunction, nextConstants]
        congr 2
        funext j
        rw [hvalues j]
      simpa only [evalFunction_layer] using
        ih gate.dual
          (fun i ↦ gate.evalFinsetFunction values (gates.get i)) nextConstants hnext

/-- A tail whose input functions have width zero has zero total influence. -/
theorem totalInfluence_evalFunction_eq_zero_of_width_zero
    (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n)
    (hvalues : ∀ i, gate.HasWidthLE (values i) 0) :
    totalInfluence (tail.evalFunction gate values).toReal = 0 := by
  classical
  let constants : Fin m → Sign := fun i ↦
    Classical.choose (gate.exists_eq_const_of_hasWidthLE_zero (values i) (hvalues i))
  have hconstant (i : Fin m) : values i = fun _ ↦ constants i := by
    exact Classical.choose_spec
      (gate.exists_eq_const_of_hasWidthLE_zero (values i) (hvalues i))
  obtain ⟨c, hc⟩ :=
    tail.exists_eq_const_evalFunction_of_values gate values constants hconstant
  rw [hc]
  change totalInfluence (fun _ ↦ signValue c) = 0
  exact totalInfluence_const (signValue c)

end CircuitTail

/-- Maximum restricted decision-tree depth in a finite layer. -/
noncomputable def maxRestrictedDecisionTreeDepth
    (values : Fin m → BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) : ℕ :=
  Finset.univ.sup fun i ↦ restrictedDecisionTreeDepth (values i) J z

theorem restrictedDecisionTreeDepth_le_max
    (values : Fin m → BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin m) :
    restrictedDecisionTreeDepth (values i) J z ≤
      maxRestrictedDecisionTreeDepth values J z := by
  exact Finset.le_sup (s := (Finset.univ : Finset (Fin m)))
    (f := fun i ↦ restrictedDecisionTreeDepth (values i) J z) (Finset.mem_univ i)

/-- Every restricted function in a layer has either matching formula presentation at the
maximum decision-tree depth of that layer. -/
theorem CircuitGate.hasWidthLE_extendedSignRestriction_max
    (gate : CircuitGate) (values : Fin m → BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) (i : Fin m) :
    gate.HasWidthLE (extendedSignRestriction (values i) J z)
      (maxRestrictedDecisionTreeDepth values J z) := by
  apply gate.hasWidthLE_mono (restrictedDecisionTreeDepth_le_max values J z i)
  have h := gate.hasWidthLE_decisionTreeDepth
    (extendedSignRestriction (values i) J z)
  change gate.HasWidthLE (extendedSignRestriction (values i) J z)
    (restrictedDecisionTreeDepth (values i) J z)
  simpa [restrictedDecisionTreeDepth, restrictedBinaryFunction,
    binaryOfBooleanFunction] using h

/-- The exponential of a finite supremum is bounded by one plus the sum of exponentials. -/
theorem two_pow_sup_le_one_add_sum {ι : Type*}
    (s : Finset ι) (depth : ι → ℕ) :
    2 ^ s.sup depth ≤ 1 + ∑ i ∈ s, 2 ^ depth i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sup_insert, Finset.sum_insert ha]
      by_cases h : depth a ≤ s.sup depth
      · rw [max_eq_right h]
        exact ih.trans (Nat.add_le_add_left (Nat.le_add_left _ _) 1)
      · rw [max_eq_left (Nat.le_of_not_ge h)]
        omega

/-- A soft logarithm-plus-exponential bound valid for every natural number. -/
theorem natCast_le_add_pow_div_pow (d q : ℕ) :
    (d : ℝ) ≤ (q : ℝ) + (2 : ℝ) ^ d / (2 : ℝ) ^ q := by
  by_cases hdq : d ≤ q
  · have hratio : 0 ≤ (2 : ℝ) ^ d / (2 : ℝ) ^ q := by positivity
    exact (show (d : ℝ) ≤ (q : ℝ) by exact_mod_cast hdq).trans
      (le_add_of_nonneg_right hratio)
  · have hqd : q ≤ d := Nat.le_of_not_ge hdq
    let r := d - q
    have hdr : d = q + r := by omega
    have hr : (r : ℝ) ≤ (2 : ℝ) ^ r := by
      have h := Nat.cast_le_pow_div_sub (a := (2 : ℝ)) (by norm_num) r
      norm_num at h
      exact h
    have hratio : (2 : ℝ) ^ d / (2 : ℝ) ^ q = (2 : ℝ) ^ r := by
      rw [hdr, pow_add]
      field_simp
    calc
      (d : ℝ) = (q : ℝ) + (r : ℝ) := by exact_mod_cast hdr
      _ ≤ (q : ℝ) + (2 : ℝ) ^ r := by linarith
      _ = (q : ℝ) + (2 : ℝ) ^ d / (2 : ℝ) ^ q := by rw [hratio]

/-- A quarter-power switching tail gives a logarithmic expectation for the largest
decision-tree depth among `m` functions. -/
theorem expect_maxRestrictedDecisionTreeDepth_le_clog_add_two_of_failure_le_quarter
    (values : Fin m → BooleanFunction n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hfailure : ∀ i k,
      switchingFailureProbability (values i) δ k ≤ (1 / 4 : ℝ) ^ k) :
    expectRandomRestriction n δ (fun J z ↦
        (maxRestrictedDecisionTreeDepth values J z : ℝ)) ≤
      (Nat.clog 2 (m + 1) : ℝ) + 2 := by
  classical
  let q := Nat.clog 2 (m + 1)
  let maxDepth := fun (J : Finset (Fin n)) (z : FixedSignCube J) ↦
    maxRestrictedDecisionTreeDepth values J z
  have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      (maxDepth J z : ℝ) ≤
        (q : ℝ) + ((2 ^ maxDepth J z : ℕ) : ℝ) / (2 : ℝ) ^ q := by
    simpa using natCast_le_add_pow_div_pow (maxDepth J z) q
  have hpowPoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      ((2 ^ maxDepth J z : ℕ) : ℝ) ≤
        1 + ∑ i : Fin m,
          ((2 ^ restrictedDecisionTreeDepth (values i) J z : ℕ) : ℝ) := by
    exact_mod_cast two_pow_sup_le_one_add_sum (Finset.univ : Finset (Fin m))
      (fun i ↦ restrictedDecisionTreeDepth (values i) J z)
  have hpowExpect :
      expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) ≤ 1 + 2 * m := by
    calc
      expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) ≤
          expectRandomRestriction n δ (fun J z ↦
            1 + ∑ i : Fin m,
              ((2 ^ restrictedDecisionTreeDepth (values i) J z : ℕ) : ℝ)) :=
        expectRandomRestriction_mono hδ0 hδ1 hpowPoint
      _ = 1 + ∑ i : Fin m, expectRandomRestriction n δ (fun J z ↦
            ((2 ^ restrictedDecisionTreeDepth (values i) J z : ℕ) : ℝ)) := by
        rw [expectRandomRestriction_add, expectRandomRestriction_const,
          ← sum_expectRandomRestriction]
      _ ≤ 1 + ∑ _i : Fin m, (2 : ℝ) := by
        gcongr with i
        exact expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter
          (values i) δ (hfailure i)
      _ = 1 + 2 * m := by simp [mul_comm]
  have hqpowNat : m + 1 ≤ 2 ^ q := Nat.le_pow_clog (by norm_num) (m + 1)
  have hqpow : (m + 1 : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast hqpowNat
  calc
    expectRandomRestriction n δ (fun J z ↦ (maxDepth J z : ℝ)) ≤
        expectRandomRestriction n δ (fun J z ↦
          (q : ℝ) + ((2 ^ maxDepth J z : ℕ) : ℝ) / (2 : ℝ) ^ q) :=
      expectRandomRestriction_mono hδ0 hδ1 hpoint
    _ = (q : ℝ) + ((2 : ℝ) ^ q)⁻¹ *
        expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) := by
      rw [expectRandomRestriction_add, expectRandomRestriction_const]
      simp only [div_eq_mul_inv]
      have hcomm :
          expectRandomRestriction n δ (fun J z ↦
            ((2 ^ maxDepth J z : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹) =
            expectRandomRestriction n δ (fun J z ↦
              ((2 : ℝ) ^ q)⁻¹ * ((2 ^ maxDepth J z : ℕ) : ℝ)) := by
        congr 1
        funext J z
        ring
      rw [hcomm, expectRandomRestriction_const_mul]
    _ ≤ (q : ℝ) + ((2 : ℝ) ^ q)⁻¹ * (1 + 2 * m) := by
      gcongr
    _ ≤ (q : ℝ) + 2 := by
      have hdenom : 0 < (2 : ℝ) ^ q := by positivity
      have hnum : (1 : ℝ) + 2 * m ≤ 2 * (m + 1) := by
        linarith
      have hscaled : (1 : ℝ) + 2 * m ≤ 2 * (2 : ℝ) ^ q :=
        hnum.trans (mul_le_mul_of_nonneg_left hqpow (by norm_num))
      have := (div_le_iff₀ hdenom).2 hscaled
      simpa [div_eq_mul_inv, mul_comm] using add_le_add_left this (q : ℝ)
    _ = (Nat.clog 2 (m + 1) : ℝ) + 2 := rfl

/-- Explicit logarithmic factor used by the circuit-influence induction. -/
def circuitInfluenceLog (s : ℕ) : ℕ := Nat.clog 2 (s + 1) + 2

/-- One depth-reduction step costs `20` times the explicit logarithmic factor. -/
def circuitInfluenceStep (s : ℕ) : ℝ := 20 * circuitInfluenceLog s

/-- The exact quarter-power instance of Håstad's Switching Lemma used below. -/
def HasQuarterSwitchingBound : Prop :=
  ∀ {N w : ℕ} (f : BooleanFunction N), 0 < w →
    (HasDNFWidthLE f w ∨ HasCNFWidthLE f w) → ∀ k : ℕ,
      switchingFailureProbability f (1 / (20 * (w : ℝ))) k ≤
        (1 / 4 : ℝ) ^ k

theorem CircuitGate.hasDNFWidthLE_or_hasCNFWidthLE
    (gate : CircuitGate) (f : BooleanFunction n) {w : ℕ}
    (hf : gate.HasWidthLE f w) :
    HasDNFWidthLE f w ∨ HasCNFWidthLE f w := by
  cases gate with
  | and => exact Or.inr hf
  | or => exact Or.inl hf

/-- Exercise 4.20(a), in the stronger semantic-tail form used by the proof. -/
theorem CircuitTail.totalInfluence_evalFunction_le_of_quarterSwitching
    (hSwitching : HasQuarterSwitchingBound)
    (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) {w s : ℕ}
    (hsize : tail.internalNodeCount + 1 ≤ s)
    (hvalues : ∀ i, gate.HasWidthLE (values i) w) :
    totalInfluence (tail.evalFunction gate values).toReal ≤
      2 * w * circuitInfluenceStep s ^ (tail.layerCount - 1) := by
  classical
  induction tail generalizing gate w s with
  | output inputs =>
      have hout : gate.HasWidthLE (gate.evalFinsetFunction values inputs) w :=
        gate.hasWidthLE_evalFinsetFunction values inputs (fun i _ ↦ hvalues i)
      have hbound := totalInfluence_le_two_mul_of_hasWidthLE gate
        (gate.evalFinsetFunction values inputs) hout
      simpa [CircuitTail.evalFunction_output, CircuitTail.layerCount,
        circuitInfluenceStep] using hbound
  | layer gates rest ih =>
      by_cases hwzero : w = 0
      · subst w
        rw [(CircuitTail.layer gates rest).totalInfluence_evalFunction_eq_zero_of_width_zero
          gate values hvalues]
        norm_num
      · have hw : 0 < w := Nat.pos_of_ne_zero hwzero
        let nextValues : Fin gates.length → BooleanFunction n := fun i ↦
          gate.evalFinsetFunction values (gates.get i)
        have hnext (i : Fin gates.length) : gate.HasWidthLE (nextValues i) w := by
          apply gate.hasWidthLE_evalFinsetFunction values (gates.get i)
          intro j _
          exact hvalues j
        let δ : ℝ := 1 / (20 * (w : ℝ))
        have hδ0 : 0 < δ := by
          dsimp [δ]
          positivity
        have hδ1 : δ ≤ 1 := by
          have hwreal : (1 : ℝ) ≤ w := by exact_mod_cast hw
          dsimp [δ]
          have hdenom : (1 : ℝ) ≤ 20 * (w : ℝ) := by nlinarith
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenom
        have hfailure (i : Fin gates.length) (k : ℕ) :
            switchingFailureProbability (nextValues i) δ k ≤ (1 / 4 : ℝ) ^ k := by
          exact hSwitching (nextValues i) hw
            (gate.hasDNFWidthLE_or_hasCNFWidthLE (nextValues i) (hnext i)) k
        have hmax :=
          expect_maxRestrictedDecisionTreeDepth_le_clog_add_two_of_failure_le_quarter
            nextValues hδ0.le hδ1 hfailure
        have hgates : gates.length ≤ s := by
          simp only [CircuitTail.internalNodeCount] at hsize
          omega
        have hlog : circuitInfluenceLog gates.length ≤ circuitInfluenceLog s := by
          unfold circuitInfluenceLog
          exact Nat.add_le_add_right
            (Nat.clog_mono_right 2 (Nat.add_le_add_right hgates 1)) 2
        have hmax' :
            expectRandomRestriction n δ (fun J z ↦
                (maxRestrictedDecisionTreeDepth nextValues J z : ℝ)) ≤
              circuitInfluenceLog s := by
          exact hmax.trans (by
            change (Nat.clog 2 (gates.length + 1) : ℝ) + 2 ≤
              (circuitInfluenceLog s : ℝ)
            exact_mod_cast hlog)
        have hrestSize : rest.internalNodeCount + 1 ≤ s := by
          simp only [CircuitTail.internalNodeCount] at hsize
          omega
        let power : ℝ := circuitInfluenceStep s ^ (rest.layerCount - 1)
        have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
            totalInfluence
                (extendedSignRestriction
                  ((CircuitTail.layer gates rest).evalFunction gate values).toReal J z) ≤
              2 * (maxRestrictedDecisionTreeDepth nextValues J z : ℝ) * power := by
          change totalInfluence
              (BooleanFunction.toReal
                (extendedSignRestriction
                  ((CircuitTail.layer gates rest).evalFunction gate values) J z)) ≤ _
          rw [CircuitTail.extendedSignRestriction_evalFunction]
          change totalInfluence
              (BooleanFunction.toReal
                (rest.evalFunction gate.dual
                  (fun i ↦ extendedSignRestriction (nextValues i) J z))) ≤ _
          have hrestricted (i : Fin gates.length) :
              gate.dual.HasWidthLE (extendedSignRestriction (nextValues i) J z)
                (maxRestrictedDecisionTreeDepth nextValues J z) :=
            gate.dual.hasWidthLE_extendedSignRestriction_max nextValues J z i
          simpa [power] using ih gate.dual
            (fun i ↦ extendedSignRestriction (nextValues i) J z)
            (w := maxRestrictedDecisionTreeDepth nextValues J z) (s := s)
            hrestSize hrestricted
        have hexpect :
            expectRandomRestriction n δ (fun J z ↦
                totalInfluence
                  (extendedSignRestriction
                    ((CircuitTail.layer gates rest).evalFunction gate values).toReal J z)) ≤
              2 * power * circuitInfluenceLog s := by
          calc
            expectRandomRestriction n δ (fun J z ↦
                totalInfluence
                  (extendedSignRestriction
                    ((CircuitTail.layer gates rest).evalFunction gate values).toReal J z)) ≤
                expectRandomRestriction n δ (fun J z ↦
                  2 * (maxRestrictedDecisionTreeDepth nextValues J z : ℝ) * power) :=
              expectRandomRestriction_mono hδ0.le hδ1 hpoint
            _ = (2 * power) * expectRandomRestriction n δ (fun J z ↦
                  (maxRestrictedDecisionTreeDepth nextValues J z : ℝ)) := by
              have hfactor := expectRandomRestriction_const_mul δ (2 * power)
                (fun J z ↦ (maxRestrictedDecisionTreeDepth nextValues J z : ℝ))
              calc
                expectRandomRestriction n δ (fun J z ↦
                    2 * (maxRestrictedDecisionTreeDepth nextValues J z : ℝ) * power) =
                    expectRandomRestriction n δ (fun J z ↦
                      (2 * power) *
                        (maxRestrictedDecisionTreeDepth nextValues J z : ℝ)) := by
                  congr 1
                  funext J z
                  ring
                _ = (2 * power) * expectRandomRestriction n δ (fun J z ↦
                    (maxRestrictedDecisionTreeDepth nextValues J z : ℝ)) := hfactor
            _ ≤ (2 * power) * circuitInfluenceLog s := by
              have hpower : 0 ≤ power := by
                dsimp [power, circuitInfluenceStep, circuitInfluenceLog]
                positivity
              exact mul_le_mul_of_nonneg_left hmax' (mul_nonneg (by norm_num) hpower)
            _ = 2 * power * circuitInfluenceLog s := rfl
        have hcorollary := expect_totalInfluence_extended_randomRestriction
          ((CircuitTail.layer gates rest).evalFunction gate values).toReal δ
        have hscaled : δ *
              totalInfluence ((CircuitTail.layer gates rest).evalFunction gate values).toReal ≤
            2 * power * circuitInfluenceLog s := by
          rw [← hcorollary]
          exact hexpect
        have hdivide :
            totalInfluence ((CircuitTail.layer gates rest).evalFunction gate values).toReal ≤
              (2 * power * circuitInfluenceLog s) / δ :=
          (le_div_iff₀ hδ0).2 (by simpa [mul_comm] using hscaled)
        have hstep : 0 < circuitInfluenceStep s := by
          unfold circuitInfluenceStep circuitInfluenceLog
          positivity
        have hpow : circuitInfluenceStep s ^ rest.layerCount =
            power * circuitInfluenceStep s := by
          have hcount := rest.one_le_layerCount
          rw [show rest.layerCount = (rest.layerCount - 1) + 1 by omega, pow_succ]
        calc
          totalInfluence ((CircuitTail.layer gates rest).evalFunction gate values).toReal ≤
              (2 * power * circuitInfluenceLog s) / δ := hdivide
          _ = 2 * (w : ℝ) * circuitInfluenceStep s ^ rest.layerCount := by
            rw [hpow]
            dsimp [δ, circuitInfluenceStep]
            field_simp
          _ = 2 * (w : ℝ) *
              circuitInfluenceStep s ^
                ((CircuitTail.layer gates rest).layerCount - 1) := by
            simp [CircuitTail.layerCount]

namespace DepthCircuit

/-- Function computed by a single layer-one node. -/
def layer1Function (C : DepthCircuit n) (i : Fin C.layer1.length) : BooleanFunction n :=
  fun x ↦ C.evalLayer1 x i

theorem layer1Function_hasWidthLE (C : DepthCircuit n)
    (i : Fin C.layer1.length) :
    C.layer1Gate.dual.HasWidthLE (C.layer1Function i) C.width := by
  classical
  cases hgate : C.layer1Gate with
  | and =>
      let φ : DNFFormula n := ⟨[C.layer1.get i]⟩
      refine ⟨φ, ?_, ?_⟩
      · change (C.layer1.get i).width ≤ C.width
        exact DNFFormula.width_le_of_mem (DNFFormula.mk C.layer1)
          (List.get_mem C.layer1 i)
      · funext x
        change φ.eval x = C.layer1Gate.evalTerm (C.layer1.get i) x
        simp only [φ, DNFFormula.eval, CircuitGate.evalTerm, hgate,
          List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
        change (if C.layer1[i].eval x = -1 then -1 else 1) = C.layer1[i].eval x
        rcases Int.units_eq_one_or (C.layer1[i].eval x) with hx | hx <;>
          simp only [Fin.getElem_fin] at hx <;> simp [hx]
  | or =>
      let ψ : CNFFormula n := ⟨[C.layer1.get i]⟩
      refine ⟨ψ, ?_, ?_⟩
      · change (C.layer1.get i).width ≤ C.width
        exact DNFFormula.width_le_of_mem (DNFFormula.mk C.layer1)
          (List.get_mem C.layer1 i)
      · funext x
        change ψ.eval x = C.layer1Gate.evalTerm (C.layer1.get i) x
        simp [ψ, CNFFormula.eval, CircuitGate.evalTerm, CNFFormula.clauseEval, hgate]

theorem evalFunction_layer1 (C : DepthCircuit n) :
    C.tail.evalFunction C.layer1Gate.dual C.layer1Function = C.toBooleanFunction := rfl

/-- The exact `(d,w,s')` circuit predicate from Exercise 4.20.  The final `+1` counts the
singleton output node, so the tail count covers precisely layers `2` through `d`. -/
def HasDepthWidthTailSizeCircuit
    (f : BooleanFunction n) (d w s' : ℕ) : Prop :=
  ∃ C : DepthCircuit n,
    C.depth = d ∧ C.width ≤ w ∧ C.tail.internalNodeCount + 1 ≤ s' ∧
      C.toBooleanFunction = f

/-- O'Donnell, Exercise 4.20(a), with all hidden constants made explicit. -/
theorem exercise4_20_of_quarterSwitching
    (hSwitching : HasQuarterSwitchingBound)
    {f : BooleanFunction n} {d w s' : ℕ}
    (hf : HasDepthWidthTailSizeCircuit f d w s') :
    totalInfluence f.toReal ≤
      2 * w * circuitInfluenceStep s' ^ (d - 2) := by
  obtain ⟨C, hdepth, hwidth, htailSize, rfl⟩ := hf
  have hbase (i : Fin C.layer1.length) :
      C.layer1Gate.dual.HasWidthLE (C.layer1Function i) w :=
    C.layer1Gate.dual.hasWidthLE_mono hwidth (C.layer1Function_hasWidthLE i)
  have hbound := C.tail.totalInfluence_evalFunction_le_of_quarterSwitching
    hSwitching C.layer1Gate.dual C.layer1Function htailSize hbase
  rw [C.evalFunction_layer1] at hbound
  have hcount := C.tail.one_le_layerCount
  simp only [DepthCircuit.depth] at hdepth
  have hexponent : C.tail.layerCount - 1 = d - 2 := by omega
  simpa [hexponent] using hbound

end DepthCircuit

/-! ## Size-only consequence: Exercise 4.20(b) and Theorem 4.30 -/


variable {n m : ℕ}

/-- The quarter-power switching estimate used in the circuit-influence argument, obtained by
specializing Håstad's Switching Lemma at `δ = 1 / (20w)`. -/
theorem hastadQuarterSwitchingBound : HasQuarterSwitchingBound := by
  intro N w f hw hf k
  have hδ0 : (0 : ℝ) ≤ 1 / (20 * (w : ℝ)) := by positivity
  have hδ1 : (1 / (20 * (w : ℝ)) : ℝ) ≤ 1 := by
    have hwReal : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hdenom : (0 : ℝ) < 20 * (w : ℝ) := by positivity
    rw [div_le_iff₀ hdenom]
    nlinarith
  calc
    switchingFailureProbability f (1 / (20 * (w : ℝ))) k ≤
        (5 * (1 / (20 * (w : ℝ))) * w) ^ k :=
      hastadSwitchingLemma hδ0 hδ1 hf
    _ = (1 / 4 : ℝ) ^ k := by
      congr 1
      have hwReal : (w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
      field_simp
      norm_num

namespace CoordRestriction

/-- Complete a coordinate restriction by a sign-cube input on its free coordinates. -/
def completeSign (ρ : Fin n → CoordRestriction) (x : {−1,1}^[n]) : {−1,1}^[n] :=
  fun i ↦ match ρ i with
    | .free => x i
    | .fixOne => 1
    | .fixNegOne => -1

/-- Sign-cube presentation of a coordinate restriction. -/
def restrictSign (f : BooleanFunction n)
    (ρ : Fin n → CoordRestriction) : BooleanFunction n :=
  fun x ↦ f (completeSign ρ x)

theorem completeSign_coordRestrictionOf (J : Finset (Fin n))
    (z : FixedSignCube J) (x : {−1,1}^[n]) :
    completeSign (coordRestrictionOf J z) x =
      combineSignCube J (fun i : J ↦ x i) z := by
  funext i
  by_cases hi : i ∈ J
  · rw [combineSignCube_apply_free J (fun j : J ↦ x j) z ⟨i, hi⟩]
    simp [completeSign, coordRestrictionOf, hi]
  · rw [combineSignCube_apply_fixed J (fun j : J ↦ x j) z ⟨i, hi⟩]
    rcases Int.units_eq_one_or (z ⟨i, hi⟩) with hz | hz <;>
      simp [completeSign, coordRestrictionOf, hi, hz]

theorem restrictSign_coordRestrictionOf (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictSign f (coordRestrictionOf J z) = extendedSignRestriction f J z := by
  funext x
  rw [restrictSign, extendedSignRestriction, completeSign_coordRestrictionOf]

theorem completeSign_negateAssignment (ρ : Fin n → CoordRestriction)
    (x : {−1,1}^[n]) :
    completeSign (negateAssignment ρ) (fun i ↦ -x i) =
      fun i ↦ -completeSign ρ x i := by
  funext i
  cases hρ : ρ i <;>
    simp [completeSign, negateAssignment, negateState, hρ]

theorem restrictSign_booleanDual (f : BooleanFunction n)
    (ρ : Fin n → CoordRestriction) :
    restrictSign (CNFFormula.booleanDual f) ρ =
      CNFFormula.booleanDual (restrictSign f (negateAssignment ρ)) := by
  funext x
  unfold restrictSign CNFFormula.booleanDual
  congr 2
  exact (completeSign_negateAssignment ρ x).symm

end CoordRestriction

namespace DNFTerm

/-- Literals of a term that remain free after a coordinate restriction. -/
def freeRestriction (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) : DNFTerm n where
  literals := T.literals.filter fun ℓ ↦ decide (ρ ℓ.index = .free)
  nodupIndices := by
    simpa [List.filter_map] using
      T.nodupIndices.filter fun i ↦ decide (ρ i = .free)

/-- The one-term DNF left by a restriction, or False when the term is falsified. -/
def restrictionFormula (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) : DNFFormula n :=
  if T.notFalsified ρ then ⟨[T.freeRestriction ρ]⟩ else DNFFormula.empty

theorem width_restrictionFormula (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    (T.restrictionFormula ρ).width = T.restrictedWidthOf ρ := by
  by_cases hfalse : T.literals.any fun ℓ ↦ ℓ.isFalsified ρ
  · have hnot : T.notFalsified ρ = false := by
      simp [DNFTerm.notFalsified, hfalse]
    simp [restrictionFormula, hnot, restrictedWidthOf, hfalse,
      DNFFormula.empty, DNFFormula.width]
  · have hnot : T.notFalsified ρ = true := by
      simp [DNFTerm.notFalsified, hfalse]
    simp [restrictionFormula, hnot, restrictedWidthOf, hfalse,
      DNFFormula.width, freeRestriction, DNFTerm.width]

private theorem sign_eq_of_neg_one_iff {a b : Sign}
    (h : a = -1 ↔ b = -1) : a = b := by
  rcases Int.units_eq_one_or a with ha | ha <;>
    rcases Int.units_eq_one_or b with hb | hb <;> simp_all

theorem restrictionFormula_toBooleanFunction (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    (T.restrictionFormula ρ).toBooleanFunction =
      CoordRestriction.restrictSign T.eval ρ := by
  funext x
  apply sign_eq_of_neg_one_iff
  by_cases hnot : T.notFalsified ρ = true
  · simp only [restrictionFormula, hnot, if_pos, DNFFormula.toBooleanFunction,
      DNFFormula.eval_eq_neg_one_iff, List.mem_singleton, exists_eq_left,
      DNFTerm.eval_eq_neg_one_iff, CoordRestriction.restrictSign]
    constructor
    · intro hfree ℓ hℓ
      have hsafe : ℓ.isFalsified ρ = false :=
        (T.notFalsified_iff ρ).1 hnot ℓ hℓ
      cases hρ : ρ ℓ.index with
      | free =>
          simp only [CoordRestriction.completeSign, hρ]
          exact hfree ℓ (by simp [freeRestriction, hℓ, hρ])
      | fixOne =>
          simp only [CoordRestriction.completeSign, hρ]
          simp [Literal.isFalsified, hρ] at hsafe
          rcases Int.units_eq_one_or ℓ.required with hr | hr <;> simp_all
      | fixNegOne =>
          simp only [CoordRestriction.completeSign, hρ]
          simp [Literal.isFalsified, hρ] at hsafe
          rcases Int.units_eq_one_or ℓ.required with hr | hr <;> simp_all
    · intro hall ℓ hℓ
      simp only [freeRestriction, List.mem_filter, decide_eq_true_eq] at hℓ
      obtain ⟨hℓT, hfree⟩ := hℓ
      simpa [CoordRestriction.completeSign, hfree] using hall ℓ hℓT
  · have hfalse : T.notFalsified ρ = false := Bool.eq_false_of_not_eq_true hnot
    have hany : T.literals.any (fun ℓ ↦ ℓ.isFalsified ρ) = true := by
      simpa [DNFTerm.notFalsified] using hfalse
    obtain ⟨ℓ, hℓ, hℓfalse⟩ := List.any_eq_true.mp hany
    have hmismatch : CoordRestriction.completeSign ρ x ℓ.index ≠ ℓ.required := by
      cases hρ : ρ ℓ.index with
      | free => simp [Literal.isFalsified, hρ] at hℓfalse
      | fixOne =>
          have hrequired : ℓ.required ≠ (1 : Sign) := by
            simpa only [Literal.isFalsified, hρ, decide_eq_true_eq] using hℓfalse
          simp only [CoordRestriction.completeSign, hρ]
          exact fun h ↦ hrequired h.symm
      | fixNegOne =>
          have hrequired : ℓ.required ≠ (-1 : Sign) := by
            simpa only [Literal.isFalsified, hρ, decide_eq_true_eq] using hℓfalse
          simp only [CoordRestriction.completeSign, hρ]
          exact fun h ↦ hrequired h.symm
    have hterm : T.eval (CoordRestriction.completeSign ρ x) ≠ -1 := by
      intro htrue
      exact hmismatch ((T.eval_eq_neg_one_iff _).1 htrue ℓ hℓ)
    simp [restrictionFormula, hfalse, DNFFormula.toBooleanFunction,
      CoordRestriction.restrictSign, hterm]

theorem hasDNFWidthLE_restrictSign (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    HasDNFWidthLE (CoordRestriction.restrictSign T.eval ρ)
      (T.restrictedWidthOf ρ) :=
  ⟨T.restrictionFormula ρ, T.width_restrictionFormula ρ |>.le,
    T.restrictionFormula_toBooleanFunction ρ⟩

end DNFTerm

theorem CNFFormula.clauseEval_eq_booleanDual_eval (T : DNFTerm n) :
    CNFFormula.clauseEval T = CNFFormula.booleanDual T.eval := by
  funext x
  have h := CNFFormula.clauseEval_neg_iff_termEval T (fun i ↦ -x i)
  simp only [neg_neg] at h
  rcases Int.units_eq_one_or (CNFFormula.clauseEval T x) with hc | hc <;>
    rcases Int.units_eq_one_or (T.eval fun i ↦ -x i) with ht | ht <;>
      simp_all [CNFFormula.booleanDual]

/-- Boolean duality turns a DNF width certificate into a CNF width certificate. -/
theorem HasDNFWidthLE.booleanDual {f : BooleanFunction n} {w : ℕ}
    (hf : HasDNFWidthLE f w) :
    HasCNFWidthLE (CNFFormula.booleanDual f) w := by
  obtain ⟨φ, hwidth, hφ⟩ := hf
  let ψ : CNFFormula n := ⟨φ.terms⟩
  refine ⟨ψ, ?_, ?_⟩
  · simpa [ψ, CNFFormula.width] using hwidth
  · apply booleanDual_injective
    calc
      CNFFormula.booleanDual ψ.toBooleanFunction = φ.toBooleanFunction := by
        simpa [ψ, CNFFormula.switchAndOr] using
          (CNFFormula.switchAndOr_toBooleanFunction ψ).symm
      _ = f := hφ
      _ = CNFFormula.booleanDual (CNFFormula.booleanDual f) := by
        funext x
        simp [CNFFormula.booleanDual]

theorem DNFTerm.hasCNFWidthLE_restrictSign_clause (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    HasCNFWidthLE
      (CoordRestriction.restrictSign (CNFFormula.clauseEval T) ρ)
      (T.restrictedWidthOf (CoordRestriction.negateAssignment ρ)) := by
  rw [CNFFormula.clauseEval_eq_booleanDual_eval,
    CoordRestriction.restrictSign_booleanDual]
  exact (T.hasDNFWidthLE_restrictSign
    (CoordRestriction.negateAssignment ρ)).booleanDual

/-- Residual width of one layer-one gate under a coordinate restriction. -/
noncomputable def DNFTerm.restrictedGateWidth (gate : CircuitGate) (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) : ℕ :=
  match gate with
  | .and => T.restrictedWidthOf ρ
  | .or => T.restrictedWidthOf (CoordRestriction.negateAssignment ρ)

theorem CircuitGate.hasWidthLE_restrictSign_evalTerm (gate : CircuitGate)
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) :
    gate.dual.HasWidthLE
      (CoordRestriction.restrictSign (gate.evalTerm T) ρ)
      (T.restrictedGateWidth gate ρ) := by
  cases gate with
  | and => simpa [CircuitGate.evalTerm, DNFTerm.restrictedGateWidth] using
      T.hasDNFWidthLE_restrictSign ρ
  | or => simpa [CircuitGate.evalTerm, DNFTerm.restrictedGateWidth] using
      T.hasCNFWidthLE_restrictSign_clause ρ

namespace DepthCircuit

/-- Largest residual layer-one width after a coordinate restriction. -/
noncomputable def maxLayer1RestrictedWidth (C : DepthCircuit n)
    (ρ : Fin n → CoordRestriction) : ℕ :=
  Finset.univ.sup fun i : Fin C.layer1.length ↦
    (C.layer1.get i).restrictedGateWidth C.layer1Gate ρ

theorem layer1RestrictedWidth_le_max (C : DepthCircuit n)
    (ρ : Fin n → CoordRestriction) (i : Fin C.layer1.length) :
    (C.layer1.get i).restrictedGateWidth C.layer1Gate ρ ≤
      C.maxLayer1RestrictedWidth ρ :=
  Finset.le_sup (s := (Finset.univ : Finset (Fin C.layer1.length)))
    (f := fun i ↦ (C.layer1.get i).restrictedGateWidth C.layer1Gate ρ)
    (Finset.mem_univ i)

theorem layer1Function_hasWidthLE_extendedSignRestriction_max
    (C : DepthCircuit n) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin C.layer1.length) :
    C.layer1Gate.dual.HasWidthLE
      (extendedSignRestriction (C.layer1Function i) J z)
      (C.maxLayer1RestrictedWidth (coordRestrictionOf J z)) := by
  apply C.layer1Gate.dual.hasWidthLE_mono
    (C.layer1RestrictedWidth_le_max (coordRestrictionOf J z) i)
  rw [← CoordRestriction.restrictSign_coordRestrictionOf]
  simpa [layer1Function, evalLayer1] using
    C.layer1Gate.hasWidthLE_restrictSign_evalTerm
      (C.layer1.get i) (coordRestrictionOf J z)

end DepthCircuit

theorem restrictionAssignmentWeightAt_half
    (ρ : Fin n → CoordRestriction) :
    restrictionAssignmentWeightAt (1 / 2) ρ = restrictionAssignmentWeight ρ := by
  unfold restrictionAssignmentWeightAt restrictionAssignmentWeight
  apply Finset.prod_congr rfl
  intro i _
  cases ρ i <;> norm_num [coordRestrictionWeightAt, coordRestrictionWeight]

@[simp] theorem restrictionAssignmentWeight_negateAssignment
    (ρ : Fin n → CoordRestriction) :
    restrictionAssignmentWeight (CoordRestriction.negateAssignment ρ) =
      restrictionAssignmentWeight ρ := by
  unfold restrictionAssignmentWeight
  apply Finset.prod_congr rfl
  intro i _
  cases hρ : ρ i <;>
    simp [CoordRestriction.negateAssignment, CoordRestriction.negateState,
      coordRestrictionWeight, hρ]

/-- Width in blocks of five, chosen so the `3/4` tail becomes a quarter-power tail. -/
noncomputable def DNFTerm.blockedRestrictedGateWidth (gate : CircuitGate)
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) : ℕ :=
  T.restrictedGateWidth gate ρ / 5

theorem three_quarters_pow_five_mul_le_quarter_pow (k : ℕ) :
    (3 / 4 : ℝ) ^ (5 * k) ≤ (1 / 4 : ℝ) ^ k := by
  rw [pow_mul]
  gcongr
  norm_num

theorem DNFTerm.expect_blockedRestrictedGateWidth_failure_le_quarter
    (T : DNFTerm n) (gate : CircuitGate) (k : ℕ) :
    expectRandomRestriction n (1 / 2) (fun J z ↦
        if k ≤ T.blockedRestrictedGateWidth gate (coordRestrictionOf J z)
          then (1 : ℝ) else 0) ≤
      (1 / 4 : ℝ) ^ k := by
  classical
  rw [expectRandomRestriction_eq_sum_assignment]
  simp only [coordRestrictionOf_restrictionAtomOfAssignment,
    restrictionAssignmentWeightAt_half]
  have hdirect :
      (∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
          (if k ≤ T.restrictedWidthOf ρ / 5 then (1 : ℝ) else 0)) ≤
        (1 / 4 : ℝ) ^ k := by
    calc
      (∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
          (if k ≤ T.restrictedWidthOf ρ / 5 then (1 : ℝ) else 0)) ≤
          ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if 5 * k ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        apply mul_le_mul_of_nonneg_left _ (restrictionAssignmentWeight_nonneg ρ)
        split_ifs <;> norm_num
        omega
      _ ≤ (3 / 4 : ℝ) ^ (5 * k) := restrictedWidth_ge_probability_le T (5 * k)
      _ ≤ (1 / 4 : ℝ) ^ k := three_quarters_pow_five_mul_le_quarter_pow k
  cases gate with
  | and => simpa [blockedRestrictedGateWidth, restrictedGateWidth] using hdirect
  | or =>
      rw [show (∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
          (if k ≤ T.blockedRestrictedGateWidth CircuitGate.or ρ then (1 : ℝ) else 0)) =
          ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if k ≤ T.restrictedWidthOf ρ / 5 then (1 : ℝ) else 0) by
        calc
          (∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
              (if k ≤ T.blockedRestrictedGateWidth CircuitGate.or ρ
                then (1 : ℝ) else 0)) =
              ∑ ρ : Fin n → CoordRestriction,
                restrictionAssignmentWeight (CoordRestriction.negateAssignment ρ) *
                  (if k ≤ T.restrictedWidthOf
                      (CoordRestriction.negateAssignment ρ) / 5 then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro ρ _
            simp [blockedRestrictedGateWidth, restrictedGateWidth]
          _ = ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
                (if k ≤ T.restrictedWidthOf ρ / 5 then (1 : ℝ) else 0) := by
            simpa [coordRestrictionNegationEquiv] using
              coordRestrictionNegationEquiv.sum_comp
                (fun ρ ↦ restrictionAssignmentWeight ρ *
                  (if k ≤ T.restrictedWidthOf ρ / 5 then (1 : ℝ) else 0))]
      exact hdirect

/-- A quarter-power tail bounds the expected binary exponential of any bounded natural statistic. -/
theorem expect_two_pow_le_two_of_tail_le_quarter
    (depth : (J : Finset (Fin n)) → FixedSignCube J → ℕ)
    (N : ℕ) (δ : ℝ)
    (hdepth : ∀ J z, depth J z ≤ N)
    (htail : ∀ k : ℕ,
      expectRandomRestriction n δ (fun J z ↦
        if k ≤ depth J z then (1 : ℝ) else 0) ≤ (1 / 4 : ℝ) ^ k) :
    expectRandomRestriction n δ (fun J z ↦
        ((2 ^ depth J z : ℕ) : ℝ)) ≤ 2 := by
  have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      ((2 ^ depth J z : ℕ) : ℝ) =
        1 + ∑ j ∈ Finset.range N,
          ((2 ^ j : ℕ) : ℝ) * if j + 1 ≤ depth J z then 1 else 0 :=
    two_pow_eq_one_add_sum_tailIndicators (hdepth J z)
  calc
    expectRandomRestriction n δ (fun J z ↦ ((2 ^ depth J z : ℕ) : ℝ)) =
        expectRandomRestriction n δ (fun J z ↦
          1 + ∑ j ∈ Finset.range N,
            ((2 ^ j : ℕ) : ℝ) * if j + 1 ≤ depth J z then 1 else 0) := by
      congr 1
      funext J z
      exact hpoint J z
    _ = 1 + ∑ j ∈ Finset.range N,
        ((2 ^ j : ℕ) : ℝ) *
          expectRandomRestriction n δ (fun J z ↦
            if j + 1 ≤ depth J z then (1 : ℝ) else 0) := by
      rw [expectRandomRestriction_add, expectRandomRestriction_const,
        expectRandomRestriction_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [expectRandomRestriction_const_mul]
    _ ≤ 1 + ∑ j ∈ Finset.range N,
        ((2 ^ j : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (j + 1) := by
      gcongr with j hj
      exact htail (j + 1)
    _ = 1 + (1 / 4 : ℝ) * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [two_pow_mul_quarter_pow_succ]
    _ ≤ 1 + (1 / 4 : ℝ) * 2 := by
      gcongr
      exact sum_geometric_two_le N
    _ ≤ 2 := by norm_num

theorem DNFTerm.expect_two_pow_blockedRestrictedGateWidth_le_two
    (T : DNFTerm n) (gate : CircuitGate) :
    expectRandomRestriction n (1 / 2) (fun J z ↦
        ((2 ^ T.blockedRestrictedGateWidth gate (coordRestrictionOf J z) : ℕ) : ℝ)) ≤
      2 := by
  apply expect_two_pow_le_two_of_tail_le_quarter
    (fun J z ↦ T.blockedRestrictedGateWidth gate (coordRestrictionOf J z)) n (1 / 2)
  · intro J z
    apply (Nat.div_le_self _ _).trans
    cases gate with
    | and => exact (T.restrictedWidthOf_le_width _).trans T.width_le_dimension
    | or => exact (T.restrictedWidthOf_le_width _).trans T.width_le_dimension
  · exact T.expect_blockedRestrictedGateWidth_failure_le_quarter gate

/-- A finite supremum has logarithmic expectation when every binary exponential moment is at most
two. -/
theorem expect_sup_le_clog_add_two_of_twoPow_le_two
    (depth : Fin m → (J : Finset (Fin n)) → FixedSignCube J → ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmoment : ∀ i,
      expectRandomRestriction n δ (fun J z ↦
        ((2 ^ depth i J z : ℕ) : ℝ)) ≤ 2) :
    expectRandomRestriction n δ (fun J z ↦
        ((Finset.univ.sup fun i : Fin m ↦ depth i J z : ℕ) : ℝ)) ≤
      (Nat.clog 2 (m + 1) : ℝ) + 2 := by
  classical
  let q := Nat.clog 2 (m + 1)
  let maxDepth := fun (J : Finset (Fin n)) (z : FixedSignCube J) ↦
    Finset.univ.sup fun i : Fin m ↦ depth i J z
  have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      (maxDepth J z : ℝ) ≤
        (q : ℝ) + ((2 ^ maxDepth J z : ℕ) : ℝ) / (2 : ℝ) ^ q := by
    simpa using natCast_le_add_pow_div_pow (maxDepth J z) q
  have hpowPoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      ((2 ^ maxDepth J z : ℕ) : ℝ) ≤
        1 + ∑ i : Fin m, ((2 ^ depth i J z : ℕ) : ℝ) := by
    exact_mod_cast two_pow_sup_le_one_add_sum (Finset.univ : Finset (Fin m))
      (fun i ↦ depth i J z)
  have hpowExpect :
      expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) ≤ 1 + 2 * m := by
    calc
      expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) ≤
          expectRandomRestriction n δ (fun J z ↦
            1 + ∑ i : Fin m, ((2 ^ depth i J z : ℕ) : ℝ)) :=
        expectRandomRestriction_mono hδ0 hδ1 hpowPoint
      _ = 1 + ∑ i : Fin m, expectRandomRestriction n δ (fun J z ↦
            ((2 ^ depth i J z : ℕ) : ℝ)) := by
        rw [expectRandomRestriction_add, expectRandomRestriction_const,
          ← sum_expectRandomRestriction]
      _ ≤ 1 + ∑ _i : Fin m, (2 : ℝ) := by
        gcongr with i
        exact hmoment i
      _ = 1 + 2 * m := by simp [mul_comm]
  have hqpowNat : m + 1 ≤ 2 ^ q := Nat.le_pow_clog (by norm_num) (m + 1)
  have hqpow : (m + 1 : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast hqpowNat
  calc
    expectRandomRestriction n δ (fun J z ↦ (maxDepth J z : ℝ)) ≤
        expectRandomRestriction n δ (fun J z ↦
          (q : ℝ) + ((2 ^ maxDepth J z : ℕ) : ℝ) / (2 : ℝ) ^ q) :=
      expectRandomRestriction_mono hδ0 hδ1 hpoint
    _ = (q : ℝ) + ((2 : ℝ) ^ q)⁻¹ *
        expectRandomRestriction n δ (fun J z ↦
          ((2 ^ maxDepth J z : ℕ) : ℝ)) := by
      rw [expectRandomRestriction_add, expectRandomRestriction_const]
      simp only [div_eq_mul_inv]
      have hcomm :
          expectRandomRestriction n δ (fun J z ↦
            ((2 ^ maxDepth J z : ℕ) : ℝ) * ((2 : ℝ) ^ q)⁻¹) =
            expectRandomRestriction n δ (fun J z ↦
              ((2 : ℝ) ^ q)⁻¹ * ((2 ^ maxDepth J z : ℕ) : ℝ)) := by
        congr 1
        funext J z
        ring
      rw [hcomm, expectRandomRestriction_const_mul]
    _ ≤ (q : ℝ) + ((2 : ℝ) ^ q)⁻¹ * (1 + 2 * m) := by
      gcongr
    _ ≤ (q : ℝ) + 2 := by
      have hdenom : 0 < (2 : ℝ) ^ q := by positivity
      have hnum : (1 : ℝ) + 2 * m ≤ 2 * (m + 1) := by linarith
      have hscaled : (1 : ℝ) + 2 * m ≤ 2 * (2 : ℝ) ^ q :=
        hnum.trans (mul_le_mul_of_nonneg_left hqpow (by norm_num))
      have hdivision := (div_le_iff₀ hdenom).2 hscaled
      simpa [div_eq_mul_inv, mul_comm] using add_le_add_left hdivision (q : ℝ)
    _ = (Nat.clog 2 (m + 1) : ℝ) + 2 := rfl

namespace DepthCircuit

/-- Largest blocked residual width among the layer-one gates. -/
noncomputable def maxLayer1BlockedWidth (C : DepthCircuit n)
    (ρ : Fin n → CoordRestriction) : ℕ :=
  Finset.univ.sup fun i : Fin C.layer1.length ↦
    (C.layer1.get i).blockedRestrictedGateWidth C.layer1Gate ρ

theorem maxLayer1RestrictedWidth_le_blocked (C : DepthCircuit n)
    (ρ : Fin n → CoordRestriction) :
    C.maxLayer1RestrictedWidth ρ ≤ 5 * C.maxLayer1BlockedWidth ρ + 4 := by
  apply Finset.sup_le
  intro i hi
  have hblock :
      (C.layer1.get i).blockedRestrictedGateWidth C.layer1Gate ρ ≤
        C.maxLayer1BlockedWidth ρ :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin C.layer1.length)))
      (f := fun i ↦ (C.layer1.get i).blockedRestrictedGateWidth C.layer1Gate ρ) hi
  unfold DNFTerm.blockedRestrictedGateWidth at hblock
  omega

/-- Explicit logarithmic width produced by the initial half-random restriction. -/
def initialRestrictionWidth (s : ℕ) : ℕ := 5 * circuitInfluenceLog s + 4

theorem expect_maxLayer1RestrictedWidth_le (C : DepthCircuit n) :
    expectRandomRestriction n (1 / 2) (fun J z ↦
        (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) ≤
      initialRestrictionWidth C.layer1.length := by
  have hblocked :
      expectRandomRestriction n (1 / 2) (fun J z ↦
          (C.maxLayer1BlockedWidth (coordRestrictionOf J z) : ℝ)) ≤
        (Nat.clog 2 (C.layer1.length + 1) : ℝ) + 2 := by
    simpa [maxLayer1BlockedWidth] using
      expect_sup_le_clog_add_two_of_twoPow_le_two
        (fun i J z ↦ (C.layer1.get i).blockedRestrictedGateWidth C.layer1Gate
          (coordRestrictionOf J z)) (by norm_num) (by norm_num)
        (fun i ↦ (C.layer1.get i).expect_two_pow_blockedRestrictedGateWidth_le_two
          C.layer1Gate)
  calc
    expectRandomRestriction n (1 / 2) (fun J z ↦
        (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) ≤
        expectRandomRestriction n (1 / 2) (fun J z ↦
          5 * (C.maxLayer1BlockedWidth (coordRestrictionOf J z) : ℝ) + 4) := by
      apply expectRandomRestriction_mono (by norm_num) (by norm_num)
      intro J z
      exact_mod_cast C.maxLayer1RestrictedWidth_le_blocked (coordRestrictionOf J z)
    _ = 5 * expectRandomRestriction n (1 / 2) (fun J z ↦
          (C.maxLayer1BlockedWidth (coordRestrictionOf J z) : ℝ)) + 4 := by
      rw [expectRandomRestriction_add, expectRandomRestriction_const_mul,
        expectRandomRestriction_const]
    _ ≤ 5 * ((Nat.clog 2 (C.layer1.length + 1) : ℝ) + 2) + 4 := by
      gcongr
    _ = initialRestrictionWidth C.layer1.length := by
      simp [initialRestrictionWidth, circuitInfluenceLog]

theorem initialRestrictionWidth_mono {a b : ℕ} (hab : a ≤ b) :
    initialRestrictionWidth a ≤ initialRestrictionWidth b := by
  unfold initialRestrictionWidth circuitInfluenceLog
  gcongr

theorem initialRestrictionWidth_le_step_succ (s : ℕ) :
    initialRestrictionWidth s ≤ circuitInfluenceStep (s + 1) := by
  have hlog : circuitInfluenceLog s ≤ circuitInfluenceLog (s + 1) := by
    unfold circuitInfluenceLog
    gcongr
    exact Nat.le_succ s
  have hpositive : 1 ≤ circuitInfluenceLog (s + 1) := by
    unfold circuitInfluenceLog
    omega
  have hlogReal : (circuitInfluenceLog s : ℝ) ≤
      circuitInfluenceLog (s + 1) := by exact_mod_cast hlog
  have hpositiveReal : (1 : ℝ) ≤ circuitInfluenceLog (s + 1) := by
    exact_mod_cast hpositive
  simp only [initialRestrictionWidth, circuitInfluenceStep, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- Computability by a depth-`d`, size-at-most-`s` circuit, with no width hypothesis. -/
def HasDepthSizeCircuit (f : BooleanFunction n) (d s : ℕ) : Prop :=
  ∃ w, HasDepthCircuit f d s w

/-- Exercise 4.20(b), with the constants in the deduction from part (a) explicit. -/
theorem exercise4_20b_of_quarterSwitching
    (hSwitching : HasQuarterSwitchingBound)
    {f : BooleanFunction n} {d s : ℕ}
    (hf : HasDepthSizeCircuit f d s) :
    totalInfluence f.toReal ≤
      4 * initialRestrictionWidth s * circuitInfluenceStep (s + 1) ^ (d - 2) := by
  obtain ⟨_w, C, hdepth, hsize, _hwidth, rfl⟩ := hf
  let power : ℝ := circuitInfluenceStep (s + 1) ^ (d - 2)
  have htailSize : C.tail.internalNodeCount + 1 ≤ s + 1 := by
    simp only [DepthCircuit.size] at hsize
    omega
  have hlayerSize : C.layer1.length ≤ s := by
    simp only [DepthCircuit.size] at hsize
    omega
  have hwidthExpect :
      expectRandomRestriction n (1 / 2) (fun J z ↦
          (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) ≤
        initialRestrictionWidth s := by
    exact C.expect_maxLayer1RestrictedWidth_le.trans
      (by exact_mod_cast initialRestrictionWidth_mono hlayerSize)
  have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
      totalInfluence
          (extendedSignRestriction C.toBooleanFunction.toReal J z) ≤
        2 * (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ) * power := by
    have hbound := C.tail.totalInfluence_evalFunction_le_of_quarterSwitching
      hSwitching C.layer1Gate.dual
      (fun i ↦ extendedSignRestriction (C.layer1Function i) J z)
      htailSize (C.layer1Function_hasWidthLE_extendedSignRestriction_max J z)
    rw [← CircuitTail.extendedSignRestriction_evalFunction,
      C.evalFunction_layer1] at hbound
    have hcount := C.tail.one_le_layerCount
    simp only [DepthCircuit.depth] at hdepth
    have hexponent : C.tail.layerCount - 1 = d - 2 := by omega
    simpa [power, hexponent] using hbound
  have hexpect :
      expectRandomRestriction n (1 / 2) (fun J z ↦
          totalInfluence
            (extendedSignRestriction C.toBooleanFunction.toReal J z)) ≤
        2 * power * initialRestrictionWidth s := by
    calc
      expectRandomRestriction n (1 / 2) (fun J z ↦
          totalInfluence
            (extendedSignRestriction C.toBooleanFunction.toReal J z)) ≤
          expectRandomRestriction n (1 / 2) (fun J z ↦
            2 * (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ) * power) :=
        expectRandomRestriction_mono (by norm_num) (by norm_num) hpoint
      _ = (2 * power) * expectRandomRestriction n (1 / 2) (fun J z ↦
            (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) := by
        have hfactor := expectRandomRestriction_const_mul (n := n) (1 / 2) (2 * power)
          (fun J z ↦
            (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ))
        calc
          expectRandomRestriction n (1 / 2) (fun J z ↦
              2 * (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ) * power) =
              expectRandomRestriction n (1 / 2) (fun J z ↦
                (2 * power) *
                  (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) := by
            congr 1
            funext J z
            ring
          _ = (2 * power) * expectRandomRestriction n (1 / 2) (fun J z ↦
                (C.maxLayer1RestrictedWidth (coordRestrictionOf J z) : ℝ)) := hfactor
      _ ≤ (2 * power) * initialRestrictionWidth s := by
        exact mul_le_mul_of_nonneg_left hwidthExpect
          (mul_nonneg (by norm_num)
            (by dsimp [power, circuitInfluenceStep, circuitInfluenceLog]; positivity))
      _ = 2 * power * initialRestrictionWidth s := rfl
  have hcorollary := expect_totalInfluence_extended_randomRestriction
    C.toBooleanFunction.toReal (1 / 2)
  have hscaled :
      (1 / 2 : ℝ) * totalInfluence C.toBooleanFunction.toReal ≤
        2 * power * initialRestrictionWidth s := by
    rw [← hcorollary]
    exact hexpect
  dsimp [power] at hscaled ⊢
  linarith

/-- O'Donnell, Theorem 4.30, in an explicit form that directly implies the book's
`O(log s)^(d-1)` bound for every fixed depth `d`. -/
theorem theorem4_30_of_quarterSwitching
    (hSwitching : HasQuarterSwitchingBound)
    {f : BooleanFunction n} {d s : ℕ}
    (hf : HasDepthSizeCircuit f d s) :
    totalInfluence f.toReal ≤
      4 * circuitInfluenceStep (s + 1) ^ (d - 1) := by
  have hbound := exercise4_20b_of_quarterSwitching hSwitching hf
  obtain ⟨_w, C, hdepth, _, _, _⟩ := hf
  have hd : 2 ≤ d := by rw [← hdepth]; exact C.depth_ge_two
  have hstep : 0 ≤ circuitInfluenceStep (s + 1) := by
    unfold circuitInfluenceStep circuitInfluenceLog
    positivity
  calc
    totalInfluence f.toReal ≤
        4 * initialRestrictionWidth s *
          circuitInfluenceStep (s + 1) ^ (d - 2) := hbound
    _ ≤ 4 * circuitInfluenceStep (s + 1) *
          circuitInfluenceStep (s + 1) ^ (d - 2) := by
      gcongr
      exact initialRestrictionWidth_le_step_succ s
    _ = 4 * circuitInfluenceStep (s + 1) ^ (d - 1) := by
      rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
      ring

/-- O'Donnell, Exercise 4.20(a), with an explicit constant. -/
theorem exercise4_20
    {f : BooleanFunction n} {d w s' : ℕ}
    (hf : HasDepthWidthTailSizeCircuit f d w s') :
    totalInfluence f.toReal ≤
      2 * w * circuitInfluenceStep s' ^ (d - 2) :=
  exercise4_20_of_quarterSwitching hastadQuarterSwitchingBound hf

/-- O'Donnell, Exercise 4.20(b), with an explicit constant. -/
theorem exercise4_20b
    {f : BooleanFunction n} {d s : ℕ}
    (hf : HasDepthSizeCircuit f d s) :
    totalInfluence f.toReal ≤
      4 * initialRestrictionWidth s * circuitInfluenceStep (s + 1) ^ (d - 2) :=
  exercise4_20b_of_quarterSwitching hastadQuarterSwitchingBound hf

/-- O'Donnell, Theorem 4.30, with an explicit bound implying the stated
`O(log s)^(d-1)` estimate at every fixed depth. -/
theorem theorem4_30
    {f : BooleanFunction n} {d s : ℕ}
    (hf : HasDepthSizeCircuit f d s) :
    totalInfluence f.toReal ≤
      4 * circuitInfluenceStep (s + 1) ^ (d - 1) :=
  theorem4_30_of_quarterSwitching hastadQuarterSwitchingBound hf

end DepthCircuit


end FABL
