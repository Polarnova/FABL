/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.CircuitInfluence
public import FABL.Chapter04.Switching
public import FABL.Chapter04.Parity

/-!
# Circuit compression, LMN, learning, and the parity lower bound

Book items: Lemma 4.28, the Linial--Mansour--Nisan Theorem, Theorem 4.31, and
Corollary 4.32.

The proof follows the book's width-truncation argument with explicit finite cutoffs.  The error
budget assigns one quarter to the restricted-circuit Fourier tail and one quarter to the squared
`L²` perturbation before applying Exercise 3.17.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal Real

@[expose] public section

namespace FABL

/-! ## Width truncation for layered circuits -/


variable {m n : ℕ}

namespace CircuitGate

/-- Neutral input for a gate: True for AND and False for OR. -/
def neutral : CircuitGate → Sign
  | .and => -1
  | .or => 1

@[simp] theorem neutral_and : CircuitGate.and.neutral = -1 := rfl

@[simp] theorem neutral_or : CircuitGate.or.neutral = 1 := rfl

end CircuitGate

/-- Pull a finite set back along an embedding. -/
def embeddingPreimage (e : Fin m ↪ Fin n) (inputs : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ e i ∈ inputs

@[simp] theorem mem_embeddingPreimage (e : Fin m ↪ Fin n)
    (inputs : Finset (Fin n)) (i : Fin m) :
    i ∈ embeddingPreimage e inputs ↔ e i ∈ inputs := by
  simp [embeddingPreimage]

namespace CircuitGate

/-- Removing inputs and assigning the gate-neutral value to them does not change evaluation. -/
theorem evalFinset_embeddingPreimage_extend (gate : CircuitGate)
    (e : Fin m ↪ Fin n) (values : Fin m → Sign) (inputs : Finset (Fin n)) :
    gate.evalFinset values (embeddingPreimage e inputs) =
      gate.evalFinset (Function.extend e values fun _ ↦ gate.neutral) inputs := by
  cases gate with
  | and =>
      have hiff :
          (∀ i ∈ embeddingPreimage e inputs, values i = -1) ↔
            ∀ j ∈ inputs, Function.extend e values (fun _ ↦ (-1 : Sign)) j = -1 := by
        constructor
        · intro h j hj
          by_cases hjImage : ∃ i, e i = j
          · obtain ⟨i, rfl⟩ := hjImage
            rw [e.injective.extend_apply]
            exact h i (by simpa using hj)
          · rw [Function.extend_apply' values (fun _ ↦ (-1 : Sign)) j hjImage]
        · intro h i hi
          have hiValue := h (e i) ((mem_embeddingPreimage e inputs i).mp hi)
          rw [e.injective.extend_apply] at hiValue
          exact hiValue
      unfold evalFinset
      exact if_congr (by simpa [embeddingPreimage] using hiff) rfl rfl
  | or =>
      have hiff :
          (∃ i ∈ embeddingPreimage e inputs, values i = -1) ↔
            ∃ j ∈ inputs, Function.extend e values (fun _ ↦ (1 : Sign)) j = -1 := by
        constructor
        · rintro ⟨i, hi, hvalue⟩
          refine ⟨e i, (mem_embeddingPreimage e inputs i).mp hi, ?_⟩
          rw [e.injective.extend_apply]
          exact hvalue
        · rintro ⟨j, hj, hvalue⟩
          by_cases hjImage : ∃ i, e i = j
          · obtain ⟨i, rfl⟩ := hjImage
            refine ⟨i, (mem_embeddingPreimage e inputs i).mpr hj, ?_⟩
            rw [e.injective.extend_apply] at hvalue
            exact hvalue
          · rw [Function.extend_apply' values (fun _ ↦ (1 : Sign)) j hjImage] at hvalue
            simp at hvalue
      unfold evalFinset
      exact if_congr (by simpa [embeddingPreimage] using hiff) rfl rfl

end CircuitGate

namespace CircuitTail

/-- Transport the input arity of a tail along an equality. -/
def castInput {m k : ℕ} (h : m = k) (tail : CircuitTail m) : CircuitTail k :=
  h ▸ tail

@[simp] theorem layerCount_castInput {m k : ℕ} (h : m = k) (tail : CircuitTail m) :
    (tail.castInput h).layerCount = tail.layerCount := by
  subst k
  rfl

@[simp] theorem internalNodeCount_castInput {m k : ℕ} (h : m = k)
    (tail : CircuitTail m) :
    (tail.castInput h).internalNodeCount = tail.internalNodeCount := by
  subst k
  rfl

theorem eval_castInput {m k : ℕ} (h : m = k) (tail : CircuitTail m)
    (gate : CircuitGate) (values : Fin k → Sign) :
    (tail.castInput h).eval gate values =
      tail.eval gate (fun i ↦ values (Fin.cast h i)) := by
  subst k
  rfl

/-- Delete first-layer inputs outside the image of an embedding while preserving every higher
layer. -/
noncomputable def pullInputs {m k : ℕ} (tail : CircuitTail m) (e : Fin k ↪ Fin m) :
    CircuitTail k :=
  match tail with
  | .output inputs => .output (embeddingPreimage e inputs)
  | .layer gates rest =>
      let pulled := gates.map (embeddingPreimage e)
      .layer pulled (rest.castInput (by simp [pulled]))

theorem layerCount_pullInputs {m k : ℕ} (tail : CircuitTail m) (e : Fin k ↪ Fin m) :
    (tail.pullInputs e).layerCount = tail.layerCount := by
  cases tail <;> simp [pullInputs, layerCount]

theorem internalNodeCount_pullInputs {m k : ℕ} (tail : CircuitTail m)
    (e : Fin k ↪ Fin m) :
    (tail.pullInputs e).internalNodeCount = tail.internalNodeCount := by
  cases tail <;> simp [pullInputs, internalNodeCount]

/-- Pulling first-layer wires is semantically the same as extending the retained values by the
neutral value for the first tail gate. -/
theorem eval_pullInputs {m k : ℕ} (tail : CircuitTail m) (gate : CircuitGate)
    (e : Fin k ↪ Fin m) (values : Fin k → Sign) :
    (tail.pullInputs e).eval gate values =
      tail.eval gate (Function.extend e values fun _ ↦ gate.neutral) := by
  cases tail with
  | output inputs =>
      exact CircuitGate.evalFinset_embeddingPreimage_extend gate e values inputs
  | layer gates rest =>
      simp only [pullInputs, eval, eval_castInput]
      congr 1
      funext i
      simp only [List.get_eq_getElem, Fin.val_cast, List.getElem_map]
      exact CircuitGate.evalFinset_embeddingPreimage_extend gate e values (gates.get i)

end CircuitTail

namespace DepthCircuit

/-- A clause with `r` distinct literals is false with probability exactly `2⁻ʳ`. -/
theorem uniformProbability_clauseEval_one (T : DNFTerm n) :
    uniformProbability (fun x ↦ CNFFormula.clauseEval T x = 1) =
      ((2 : ℝ) ^ T.width)⁻¹ := by
  let negCube : {−1,1}^[n] ≃ {−1,1}^[n] :=
    { toFun := fun x i ↦ -x i
      invFun := fun x i ↦ -x i
      left_inv := fun x ↦ by funext i; simp
      right_inv := fun x ↦ by funext i; simp }
  calc
    uniformProbability (fun x ↦ CNFFormula.clauseEval T x = 1) =
        uniformProbability (fun x ↦ CNFFormula.clauseEval T (negCube x) = 1) := by
      unfold uniformProbability
      symm
      exact Fintype.expect_equiv negCube
        (fun x ↦ if CNFFormula.clauseEval T (negCube x) = 1 then (1 : ℝ) else 0)
        (fun x ↦ if CNFFormula.clauseEval T x = 1 then (1 : ℝ) else 0)
        (fun _ ↦ rfl)
    _ = uniformProbability (fun x ↦ T.eval x = -1) := by
      unfold uniformProbability
      apply Finset.expect_congr rfl
      intro x _
      change (if CNFFormula.clauseEval T (fun i ↦ -x i) = 1 then (1 : ℝ) else 0) =
        if T.eval x = -1 then (1 : ℝ) else 0
      have hiff := CNFFormula.clauseEval_neg_iff_termEval T x
      by_cases h : T.eval x = -1
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun hclause ↦ h (hiff.mp hclause))]
    _ = ((2 : ℝ) ^ T.width)⁻¹ := uniformProbability_DNFTerm_eval_neg_one T

/-- A layer-one gate differs from the neutral input of layer two with probability `2⁻ʳ`, where
`r` is its fan-in. -/
theorem uniformProbability_evalLayer1_ne_neutral (C : DepthCircuit n)
    (i : Fin C.layer1.length) :
    uniformProbability (fun x ↦
      C.evalLayer1 x i ≠ C.layer1Gate.dual.neutral) =
      ((2 : ℝ) ^ (C.layer1.get i).width)⁻¹ := by
  cases hgate : C.layer1Gate with
  | and =>
      simp only [evalLayer1, hgate, CircuitGate.evalTerm, CircuitGate.dual_and,
        CircuitGate.neutral_or]
      calc
        uniformProbability (fun x ↦ (C.layer1.get i).eval x ≠ (1 : Sign)) =
            uniformProbability (fun x ↦ (C.layer1.get i).eval x = -1) := by
          unfold uniformProbability
          apply Finset.expect_congr rfl
          intro x _
          change (if (C.layer1.get i).eval x ≠ (1 : Sign) then (1 : ℝ) else 0) =
            if (C.layer1.get i).eval x = -1 then (1 : ℝ) else 0
          rcases Int.units_eq_one_or ((C.layer1.get i).eval x) with hx | hx
          · rw [hx]
            norm_num
          · rw [hx]
            norm_num
        _ = _ := uniformProbability_DNFTerm_eval_neg_one (C.layer1.get i)
  | or =>
      simp only [evalLayer1, hgate, CircuitGate.evalTerm, CircuitGate.dual_or,
        CircuitGate.neutral_and]
      calc
        uniformProbability (fun x ↦
            CNFFormula.clauseEval (C.layer1.get i) x ≠ (-1 : Sign)) =
            uniformProbability (fun x ↦
              CNFFormula.clauseEval (C.layer1.get i) x = 1) := by
          unfold uniformProbability
          apply Finset.expect_congr rfl
          intro x _
          change (if CNFFormula.clauseEval (C.layer1.get i) x ≠ (-1 : Sign)
              then (1 : ℝ) else 0) =
            if CNFFormula.clauseEval (C.layer1.get i) x = 1 then (1 : ℝ) else 0
          rcases Int.units_eq_one_or (CNFFormula.clauseEval (C.layer1.get i) x) with hx | hx
          · rw [hx]
            norm_num
          · rw [hx]
            norm_num
        _ = _ := uniformProbability_clauseEval_one (C.layer1.get i)

/-- Indices of layer-one nodes whose fan-in is at most `w`. -/
noncomputable def retainedLayer1Indices (C : DepthCircuit n) (w : ℕ) :
    Finset (Fin C.layer1.length) :=
  Finset.univ.filter fun i ↦ (C.layer1.get i).width ≤ w

/-- Canonical inclusion of the retained layer-one nodes into the original layer. -/
noncomputable def retainedLayer1Embedding (C : DepthCircuit n) (w : ℕ) :
    Fin (C.retainedLayer1Indices w).card ↪ Fin C.layer1.length :=
  (C.retainedLayer1Indices w).equivFin.symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem retainedLayer1Embedding_equivFin (C : DepthCircuit n) (w : ℕ)
    (i : C.retainedLayer1Indices w) :
    C.retainedLayer1Embedding w ((C.retainedLayer1Indices w).equivFin i) = i := by
  simp [retainedLayer1Embedding]

theorem retainedLayer1Embedding_mem (C : DepthCircuit n) (w : ℕ)
    (i : Fin (C.retainedLayer1Indices w).card) :
    C.retainedLayer1Embedding w i ∈ C.retainedLayer1Indices w := by
  change (((C.retainedLayer1Indices w).equivFin.symm i :
    C.retainedLayer1Indices w) : Fin C.layer1.length) ∈ C.retainedLayer1Indices w
  exact (C.retainedLayer1Indices w).equivFin.symm i |>.property

/-- The retained layer-one terms, in the canonical finite-set order. -/
noncomputable def retainedLayer1 (C : DepthCircuit n) (w : ℕ) : List (DNFTerm n) :=
  List.ofFn fun i : Fin (C.retainedLayer1Indices w).card ↦
    C.layer1.get (C.retainedLayer1Embedding w i)

@[simp] theorem length_retainedLayer1 (C : DepthCircuit n) (w : ℕ) :
    (C.retainedLayer1 w).length = (C.retainedLayer1Indices w).card := by
  simp [retainedLayer1]

@[simp] theorem get_retainedLayer1 (C : DepthCircuit n) (w : ℕ)
    (i : Fin (C.retainedLayer1 w).length) :
    (C.retainedLayer1 w).get i =
      C.layer1.get (C.retainedLayer1Embedding w
        (Fin.cast (C.length_retainedLayer1 w) i)) := by
  simp [retainedLayer1]
  congr 2

/-- Delete all layer-one nodes wider than `w` and their outgoing wires. -/
noncomputable def truncateWidth (C : DepthCircuit n) (w : ℕ) : DepthCircuit n where
  layer1Gate := C.layer1Gate
  layer1 := C.retainedLayer1 w
  tail := (C.tail.pullInputs (C.retainedLayer1Embedding w)).castInput
    (C.length_retainedLayer1 w).symm

@[simp] theorem layer1Gate_truncateWidth (C : DepthCircuit n) (w : ℕ) :
    (C.truncateWidth w).layer1Gate = C.layer1Gate := rfl

@[simp] theorem depth_truncateWidth (C : DepthCircuit n) (w : ℕ) :
    (C.truncateWidth w).depth = C.depth := by
  simpa [truncateWidth, depth] using
    C.tail.layerCount_pullInputs (C.retainedLayer1Embedding w)

theorem size_truncateWidth_le (C : DepthCircuit n) (w : ℕ) :
    (C.truncateWidth w).size ≤ C.size := by
  simp only [truncateWidth, size, CircuitTail.internalNodeCount_castInput,
    CircuitTail.internalNodeCount_pullInputs]
  have hcard : (C.retainedLayer1Indices w).card ≤ C.layer1.length := by
    simpa using Finset.card_le_univ (C.retainedLayer1Indices w)
  simpa using Nat.add_le_add_right hcard C.tail.internalNodeCount

theorem width_truncateWidth_le (C : DepthCircuit n) (w : ℕ) :
    (C.truncateWidth w).width ≤ w := by
  rw [width, DNFFormula.width_le_iff]
  intro term hterm
  simp only [truncateWidth] at hterm
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hterm
  rw [get_retainedLayer1]
  have hi := C.retainedLayer1Embedding_mem w
    (Fin.cast (C.length_retainedLayer1 w) i)
  exact (Finset.mem_filter.mp hi).2

/-- Evaluation of the truncated circuit is evaluation of the original tail after extending the
retained layer-one values by the neutral value of the layer-two gate. -/
theorem eval_truncateWidth (C : DepthCircuit n) (w : ℕ) (x : {−1,1}^[n]) :
    (C.truncateWidth w).eval x =
      C.tail.eval C.layer1Gate.dual
        (Function.extend (C.retainedLayer1Embedding w)
          (fun i ↦ C.evalLayer1 x (C.retainedLayer1Embedding w i))
          fun _ ↦ C.layer1Gate.dual.neutral) := by
  change
    (((C.tail.pullInputs (C.retainedLayer1Embedding w)).castInput
      (C.length_retainedLayer1 w).symm).eval C.layer1Gate.dual
        (fun i ↦ C.layer1Gate.evalTerm ((C.retainedLayer1 w).get i) x)) = _
  rw [CircuitTail.eval_castInput, CircuitTail.eval_pullInputs]
  apply congrArg (fun values ↦ C.tail.eval C.layer1Gate.dual values)
  apply congrArg (fun values ↦ Function.extend (C.retainedLayer1Embedding w) values
    fun _ ↦ C.layer1Gate.dual.neutral)
  funext i
  simp only [evalLayer1]
  rw [get_retainedLayer1]
  congr 2

/-- If every deleted layer-one node already has the neutral value for layer two, truncation does
not change the circuit output. -/
theorem eval_truncateWidth_eq_of_deleted_neutral (C : DepthCircuit n) (w : ℕ)
    (x : {−1,1}^[n])
    (hdeleted : ∀ i : Fin C.layer1.length, i ∉ C.retainedLayer1Indices w →
      C.evalLayer1 x i = C.layer1Gate.dual.neutral) :
    (C.truncateWidth w).eval x = C.eval x := by
  rw [C.eval_truncateWidth w x]
  unfold eval
  congr 1
  funext j
  by_cases hjImage : ∃ i, C.retainedLayer1Embedding w i = j
  · obtain ⟨i, rfl⟩ := hjImage
    rw [(C.retainedLayer1Embedding w).injective.extend_apply]
  · rw [Function.extend_apply'
      (fun i ↦ C.evalLayer1 x (C.retainedLayer1Embedding w i))
      (fun _ ↦ C.layer1Gate.dual.neutral) j hjImage]
    symm
    apply hdeleted j
    intro hj
    let i := (C.retainedLayer1Indices w).equivFin ⟨j, hj⟩
    exact hjImage ⟨i, by
      dsimp [i]
      exact C.retainedLayer1Embedding_equivFin w ⟨j, hj⟩⟩

/-- Any disagreement caused by width truncation is witnessed by a deleted non-neutral layer-one
node. -/
theorem exists_deletedLayer1_of_eval_ne_truncateWidth (C : DepthCircuit n) (w : ℕ)
    {x : {−1,1}^[n]} (hne : C.eval x ≠ (C.truncateWidth w).eval x) :
    ∃ i : Fin C.layer1.length,
      i ∉ C.retainedLayer1Indices w ∧
      C.evalLayer1 x i ≠ C.layer1Gate.dual.neutral := by
  by_contra hnone
  push Not at hnone
  have heq := C.eval_truncateWidth_eq_of_deleted_neutral w x hnone
  exact hne heq.symm

/-- Deleting all layer-one nodes wider than `w` changes the computed function on at most
`size(C) · 2⁻ʷ` of the cube. -/
theorem relativeHammingDist_truncateWidth_le (C : DepthCircuit n) (w : ℕ) :
    relativeHammingDist C.toBooleanFunction (C.truncateWidth w).toBooleanFunction ≤
      (C.size : ℝ) * ((2 : ℝ) ^ w)⁻¹ := by
  classical
  let deleted := (Finset.univ : Finset (Fin C.layer1.length)).filter fun i ↦
    i ∉ C.retainedLayer1Indices w
  rw [← uniformProbability_ne_eq_relativeHammingDist]
  change (𝔼 x, if C.eval x ≠ (C.truncateWidth w).eval x then (1 : ℝ) else 0) ≤ _
  have hpoint (x : {−1,1}^[n]) :
      (if C.eval x ≠ (C.truncateWidth w).eval x then (1 : ℝ) else 0) ≤
        ∑ i ∈ deleted,
          if C.evalLayer1 x i ≠ C.layer1Gate.dual.neutral then (1 : ℝ) else 0 := by
    by_cases hne : C.eval x ≠ (C.truncateWidth w).eval x
    · rw [if_pos hne]
      obtain ⟨i, hiDeleted, hiValue⟩ := C.exists_deletedLayer1_of_eval_ne_truncateWidth w hne
      have hi : i ∈ deleted := by simp [deleted, hiDeleted]
      have hnonneg : ∀ j ∈ deleted,
          0 ≤ (if C.evalLayer1 x j ≠ C.layer1Gate.dual.neutral then (1 : ℝ) else 0) := by
        intro j _
        split_ifs <;> norm_num
      simpa [hiValue] using Finset.single_le_sum hnonneg hi
    · rw [if_neg hne]
      exact Finset.sum_nonneg fun i _ ↦ by split_ifs <;> norm_num
  calc
    (𝔼 x, if C.eval x ≠ (C.truncateWidth w).eval x then (1 : ℝ) else 0) ≤
        𝔼 x, (∑ i ∈ deleted,
          if C.evalLayer1 x i ≠ C.layer1Gate.dual.neutral then (1 : ℝ) else 0) :=
      Finset.expect_le_expect fun x _ ↦ hpoint x
    _ = ∑ i ∈ deleted,
        (𝔼 x, if C.evalLayer1 x i ≠ C.layer1Gate.dual.neutral then (1 : ℝ) else 0) := by
      rw [Finset.expect_sum_comm]
    _ = ∑ i ∈ deleted, ((2 : ℝ) ^ (C.layer1.get i).width)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [uniformProbability] using C.uniformProbability_evalLayer1_ne_neutral i
    _ ≤ ∑ _i ∈ deleted, ((2 : ℝ) ^ w)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hiNot : i ∉ C.retainedLayer1Indices w := (Finset.mem_filter.mp hi).2
      have hiWidth : w < (C.layer1.get i).width := by
        simpa [retainedLayer1Indices] using hiNot
      exact inv_anti₀ (by positivity : 0 < (2 : ℝ) ^ w)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hiWidth.le)
    _ = (deleted.card : ℝ) * ((2 : ℝ) ^ w)⁻¹ := by simp
    _ ≤ (C.size : ℝ) * ((2 : ℝ) ^ w)⁻¹ := by
      gcongr
      have hcard : deleted.card ≤ C.size := by
        calc
          deleted.card ≤ C.layer1.length := by
            simpa using Finset.card_le_univ deleted
          _ ≤ C.size := Nat.le_add_right C.layer1.length C.tail.internalNodeCount
      exact_mod_cast hcard

/-- The logarithmic width cutoff used in the LMN theorem changes the circuit on at most `ε` of
the cube. -/
theorem relativeHammingDist_truncateWidth_cutoff_le (C : DepthCircuit n)
    {ε : ℝ} (hε : 0 < ε) :
    relativeHammingDist C.toBooleanFunction
      (C.truncateWidth (dnfWidthTruncationCutoff C.size ε)).toBooleanFunction ≤ ε := by
  calc
    relativeHammingDist C.toBooleanFunction
        (C.truncateWidth (dnfWidthTruncationCutoff C.size ε)).toBooleanFunction ≤
        (C.size : ℝ) * ((2 : ℝ) ^ dnfWidthTruncationCutoff C.size ε)⁻¹ :=
      C.relativeHammingDist_truncateWidth_le _
    _ ≤ ε := by
      by_cases hsize : C.size = 0
      · simp [hsize, hε.le]
      · exact mul_inv_two_pow_dnfWidthTruncationCutoff_le C.size
          (Nat.pos_of_ne_zero hsize) hε

/-- The truncated circuit retains the original depth and size upper bound and has the requested
width bound. -/
theorem hasDepthCircuit_truncateWidth (C : DepthCircuit n) (w : ℕ) :
    HasDepthCircuit (C.truncateWidth w).toBooleanFunction C.depth C.size w :=
  ⟨C.truncateWidth w, C.depth_truncateWidth w,
    C.size_truncateWidth_le w, C.width_truncateWidth_le w, rfl⟩

end DepthCircuit


/-! ## Random-restriction compression of layered circuits -/


variable {m n : ℕ}

/-- The single-layer restriction rate used in the LMN depth reduction. -/
noncomputable def switchingLayerRate (w : ℕ) : ℝ := 1 / (10 * (w : ℝ))

/-- Restriction rate after one width-`w` layer and `r` width-`ℓ` layers. -/
noncomputable def circuitCompressionRate (w ℓ r : ℕ) : ℝ :=
  switchingLayerRate w * switchingLayerRate ℓ ^ r

theorem switchingLayerRate_nonneg (w : ℕ) : 0 ≤ switchingLayerRate w := by
  exact one_div_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg w))

theorem switchingLayerRate_le_one {w : ℕ} (hw : 0 < w) :
    switchingLayerRate w ≤ 1 := by
  unfold switchingLayerRate
  have hwReal : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hdenom : (1 : ℝ) ≤ 10 * (w : ℝ) := by nlinarith
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenom

theorem circuitCompressionRate_nonneg (w ℓ r : ℕ) :
    0 ≤ circuitCompressionRate w ℓ r := by
  exact mul_nonneg (switchingLayerRate_nonneg w)
    (pow_nonneg (switchingLayerRate_nonneg ℓ) r)

theorem circuitCompressionRate_le_one {w ℓ r : ℕ} (hw : 0 < w) (hℓ : 0 < ℓ) :
    circuitCompressionRate w ℓ r ≤ 1 := by
  unfold circuitCompressionRate
  exact mul_le_one₀ (switchingLayerRate_le_one hw)
    (pow_nonneg (switchingLayerRate_nonneg ℓ) r)
    (pow_le_one₀ (switchingLayerRate_nonneg ℓ) (switchingLayerRate_le_one hℓ))

theorem circuitCompressionRate_split {w ℓ r : ℕ} (hr : 1 ≤ r) :
    switchingLayerRate w * circuitCompressionRate ℓ ℓ (r - 1) =
      circuitCompressionRate w ℓ r := by
  have hr' : r = (r - 1) + 1 := by omega
  have hpow : switchingLayerRate ℓ ^ r =
      switchingLayerRate ℓ ^ (r - 1) * switchingLayerRate ℓ := by
    calc
      switchingLayerRate ℓ ^ r = switchingLayerRate ℓ ^ ((r - 1) + 1) :=
        congrArg (switchingLayerRate ℓ ^ ·) hr'
      _ = switchingLayerRate ℓ ^ (r - 1) * switchingLayerRate ℓ := pow_succ _ _
  simp only [circuitCompressionRate]
  calc
    switchingLayerRate w *
        (switchingLayerRate ℓ * switchingLayerRate ℓ ^ (r - 1)) =
        switchingLayerRate w *
          (switchingLayerRate ℓ ^ (r - 1) * switchingLayerRate ℓ) := by ring
    _ = switchingLayerRate w * switchingLayerRate ℓ ^ r := by rw [hpow]

/-- The exact `(1/2)^k` specialization of Håstad's Switching Lemma used by LMN. -/
def HasHalfSwitchingBound : Prop :=
  ∀ {N w : ℕ} (f : BooleanFunction N), 0 < w →
    (HasDNFWidthLE f w ∨ HasCNFWidthLE f w) → ∀ k : ℕ,
      switchingFailureProbability f (switchingLayerRate w) k ≤ (1 / 2 : ℝ) ^ k

namespace CircuitGate

/-- Canonical restriction commutes with the pointwise evaluation of a gate. -/
theorem reindexedSignRestriction_evalFinsetFunction
    (gate : CircuitGate) (values : Fin m → BooleanFunction n)
    (inputs : Finset (Fin m)) (J : Finset (Fin n)) (z : FixedSignCube J) :
    reindexedSignRestriction (gate.evalFinsetFunction values inputs) J z =
      gate.evalFinsetFunction
        (fun i ↦ reindexedSignRestriction (values i) J z) inputs := by
  rfl

/-- A restricted function of decision-tree depth at most `ℓ` has the formula width required by
either possible next circuit layer. -/
theorem hasWidthLE_reindexedSignRestriction_of_depth_le
    (gate : CircuitGate) (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) {ℓ : ℕ}
    (hdepth : restrictedDecisionTreeDepth f J z ≤ ℓ) :
    gate.HasWidthLE (reindexedSignRestriction f J z) ℓ := by
  apply gate.hasWidthLE_mono hdepth
  have h := gate.hasWidthLE_decisionTreeDepth (reindexedSignRestriction f J z)
  have heq :
      F₂DecisionTree.decisionTreeDepth
          (binaryOfBooleanFunction (reindexedSignRestriction f J z)) =
        restrictedDecisionTreeDepth f J z := by
    rw [restrictedDecisionTreeDepth_eq_reindexedSignRestriction]
    rfl
  simpa [heq] using h

end CircuitGate

namespace CircuitTail

/-- Canonical restriction commutes with semantic evaluation of every remaining circuit layer. -/
theorem reindexedSignRestriction_evalFunction
    (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    reindexedSignRestriction (tail.evalFunction gate values) J z =
      tail.evalFunction gate
        (fun i ↦ reindexedSignRestriction (values i) J z) := by
  rfl

/-- Semantic circuit depth reduction.  Every non-output tail node contributes one
`(1/2)^ℓ` switching failure; the final output contributes `(1/2)^k`. -/
theorem switchingFailureProbability_evalFunction_le_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    (tail : CircuitTail m) (gate : CircuitGate)
    (values : Fin m → BooleanFunction n) {w ℓ k : ℕ}
    (hw : 0 < w) (hℓ : 0 < ℓ)
    (hvalues : ∀ i, gate.HasWidthLE (values i) w) :
    switchingFailureProbability (tail.evalFunction gate values)
        (circuitCompressionRate w ℓ (tail.layerCount - 1)) k ≤
      (tail.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ + (1 / 2 : ℝ) ^ k := by
  classical
  induction tail generalizing n gate w with
  | output inputs =>
      have hformula :
          gate.HasWidthLE (gate.evalFinsetFunction values inputs) w :=
        gate.hasWidthLE_evalFinsetFunction values inputs fun i _ ↦ hvalues i
      have hbound := hSwitching (gate.evalFinsetFunction values inputs) hw
        (gate.hasDNFWidthLE_or_hasCNFWidthLE _ hformula) k
      simpa [evalFunction_output, circuitCompressionRate, CircuitTail.layerCount,
        CircuitTail.internalNodeCount] using hbound
  | layer gates rest ih =>
      let nextValues : Fin gates.length → BooleanFunction n := fun i ↦
        gate.evalFinsetFunction values (gates.get i)
      have hnext (i : Fin gates.length) : gate.HasWidthLE (nextValues i) w := by
        apply gate.hasWidthLE_evalFinsetFunction values (gates.get i)
        intro j _
        exact hvalues j
      let innerRate := circuitCompressionRate ℓ ℓ (rest.layerCount - 1)
      have hinner0 : 0 ≤ innerRate := circuitCompressionRate_nonneg ℓ ℓ _
      have hinner1 : innerRate ≤ 1 := circuitCompressionRate_le_one hℓ hℓ
      have hrate :
          switchingLayerRate w * innerRate =
            circuitCompressionRate w ℓ
              ((CircuitTail.layer gates rest).layerCount - 1) := by
        simpa [innerRate, CircuitTail.layerCount] using
          (circuitCompressionRate_split
            (w := w) (ℓ := ℓ) rest.one_le_layerCount)
      have hpoint (J : Finset (Fin n)) (z : FixedSignCube J) :
          switchingFailureProbability
              (reindexedSignRestriction
                ((CircuitTail.layer gates rest).evalFunction gate values) J z)
              innerRate k ≤
            ((rest.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ +
                (1 / 2 : ℝ) ^ k) +
              ∑ i : Fin gates.length,
                switchingFailureIndicator (nextValues i) ℓ J z := by
        have hreindex :
            reindexedSignRestriction
                ((CircuitTail.layer gates rest).evalFunction gate values) J z =
              rest.evalFunction gate.dual
                (fun i ↦ reindexedSignRestriction (nextValues i) J z) := by
          rfl
        rw [hreindex]
        by_cases hgood :
            ∀ i : Fin gates.length,
              restrictedDecisionTreeDepth (nextValues i) J z < ℓ
        · have hrestricted (i : Fin gates.length) :
              gate.dual.HasWidthLE
                (reindexedSignRestriction (nextValues i) J z) ℓ :=
            gate.dual.hasWidthLE_reindexedSignRestriction_of_depth_le
              (nextValues i) J z (Nat.le_of_lt (hgood i))
          have hrecursive := ih gate.dual
            (fun i ↦ reindexedSignRestriction (nextValues i) J z)
            hℓ hrestricted
          have hsumNonneg :
              0 ≤ ∑ i : Fin gates.length,
                switchingFailureIndicator (nextValues i) ℓ J z :=
            Finset.sum_nonneg fun i _ ↦
              switchingFailureIndicator_nonneg (nextValues i) ℓ J z
          exact hrecursive.trans (le_add_of_nonneg_right hsumNonneg)
        · push Not at hgood
          obtain ⟨i, hi⟩ := hgood
          have hindicator :
              switchingFailureIndicator (nextValues i) ℓ J z = 1 := by
            simp [switchingFailureIndicator, hi]
          have hsum :
              1 ≤ ∑ j : Fin gates.length,
                switchingFailureIndicator (nextValues j) ℓ J z := by
            calc
              1 = switchingFailureIndicator (nextValues i) ℓ J z := hindicator.symm
              _ ≤ ∑ j : Fin gates.length,
                  switchingFailureIndicator (nextValues j) ℓ J z := by
                exact Finset.single_le_sum
                  (fun j _ ↦ switchingFailureIndicator_nonneg (nextValues j) ℓ J z)
                  (Finset.mem_univ i)
          have hprob :
              switchingFailureProbability
                  (rest.evalFunction gate.dual
                    (fun j ↦ reindexedSignRestriction (nextValues j) J z))
                  innerRate k ≤ 1 :=
            switchingFailureProbability_le_one hinner0 hinner1
          have hbaseNonneg :
              0 ≤ (rest.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ +
                (1 / 2 : ℝ) ^ k := by positivity
          exact hprob.trans (hsum.trans (le_add_of_nonneg_left hbaseNonneg))
      rw [← hrate,
        switchingFailureProbability_mul
          ((CircuitTail.layer gates rest).evalFunction gate values)
          (switchingLayerRate_nonneg w) (switchingLayerRate_le_one hw)
          hinner0 hinner1 k]
      calc
        expectRandomRestriction n (switchingLayerRate w) (fun J z ↦
            switchingFailureProbability
              (reindexedSignRestriction
                ((CircuitTail.layer gates rest).evalFunction gate values) J z)
              innerRate k) ≤
            expectRandomRestriction n (switchingLayerRate w) (fun J z ↦
              ((rest.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ +
                  (1 / 2 : ℝ) ^ k) +
                ∑ i : Fin gates.length,
                  switchingFailureIndicator (nextValues i) ℓ J z) :=
          expectRandomRestriction_mono
            (switchingLayerRate_nonneg w) (switchingLayerRate_le_one hw) hpoint
        _ = ((rest.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ +
                (1 / 2 : ℝ) ^ k) +
              ∑ i : Fin gates.length,
                switchingFailureProbability (nextValues i)
                  (switchingLayerRate w) ℓ := by
          rw [expectRandomRestriction_add, expectRandomRestriction_const,
            expectRandomRestriction_sum]
          rfl
        _ ≤ ((rest.internalNodeCount : ℝ) * (1 / 2 : ℝ) ^ ℓ +
                (1 / 2 : ℝ) ^ k) +
              ∑ _i : Fin gates.length, (1 / 2 : ℝ) ^ ℓ := by
          gcongr with i
          exact hSwitching (nextValues i) hw
            (gate.hasDNFWidthLE_or_hasCNFWidthLE _ (hnext i)) ℓ
        _ = (((CircuitTail.layer gates rest).internalNodeCount : ℕ) : ℝ) *
              (1 / 2 : ℝ) ^ ℓ + (1 / 2 : ℝ) ^ k := by
          simp only [CircuitTail.internalNodeCount, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

end CircuitTail

namespace DepthCircuit

/-- The semantic compression bound specialized to the intrinsic layered-circuit model. -/
theorem switchingFailureProbability_le_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    (C : DepthCircuit n) {s w ℓ k : ℕ}
    (hsize : C.size ≤ s) (hwidth : C.width ≤ w)
    (hw : 0 < w) (hℓ : 0 < ℓ) :
    switchingFailureProbability C.toBooleanFunction
        (circuitCompressionRate w ℓ (C.depth - 2)) k ≤
      (s : ℝ) * (1 / 2 : ℝ) ^ ℓ + (1 / 2 : ℝ) ^ k := by
  have hvalues (i : Fin C.layer1.length) :
      C.layer1Gate.dual.HasWidthLE (C.layer1Function i) w :=
    C.layer1Gate.dual.hasWidthLE_mono hwidth (C.layer1Function_hasWidthLE i)
  have hbound := C.tail.switchingFailureProbability_evalFunction_le_of_halfSwitching
    hSwitching C.layer1Gate.dual C.layer1Function hw hℓ hvalues (k := k)
  rw [C.evalFunction_layer1] at hbound
  have hexponent : C.tail.layerCount - 1 = C.depth - 2 := by
    have hcount := C.tail.one_le_layerCount
    simp only [DepthCircuit.depth]
    omega
  rw [hexponent] at hbound
  have htailSize : C.tail.internalNodeCount ≤ s := by
    exact (Nat.le_add_left _ _).trans (by simpa [DepthCircuit.size] using hsize)
  exact hbound.trans (by
    gcongr)

end DepthCircuit

/-! ## Exact finite cutoffs in Lemma 4.28 -/

/-- Integer interpretation of the book's `ℓ = log₂(2s / ε)`. -/
noncomputable def lmnLayerCutoff (s : ℕ) (ε : ℝ) : ℕ :=
  dnfWidthTruncationCutoff s (ε / 2)

/-- Integer interpretation of the book's final threshold `log₂(2 / ε)`. -/
noncomputable def lmnOutputCutoff (ε : ℝ) : ℕ :=
  dnfWidthTruncationCutoff 1 (ε / 2)

theorem mul_half_pow_lmnLayerCutoff_le {s : ℕ} {ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) :
    (s : ℝ) * (1 / 2 : ℝ) ^ lmnLayerCutoff s ε ≤ ε / 2 := by
  have h := mul_inv_two_pow_dnfWidthTruncationCutoff_le s hs (half_pos hε)
  simpa [lmnLayerCutoff, one_div, inv_pow] using h

theorem half_pow_lmnOutputCutoff_le {ε : ℝ} (hε : 0 < ε) :
    (1 / 2 : ℝ) ^ lmnOutputCutoff ε ≤ ε / 2 := by
  have h := mul_inv_two_pow_dnfWidthTruncationCutoff_le 1 (by omega) (half_pos hε)
  simpa [lmnOutputCutoff, one_div, inv_pow] using h

theorem lmnLayerCutoff_pos {s : ℕ} {ε : ℝ}
    (hs : 0 < s) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < lmnLayerCutoff s ε := by
  by_contra hnonpos
  have hzero : lmnLayerCutoff s ε = 0 := Nat.eq_zero_of_not_pos hnonpos
  have hbound := mul_half_pow_lmnLayerCutoff_le hs hε0
  rw [hzero] at hbound
  norm_num at hbound
  have hsReal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- The final decision-tree threshold is positive throughout the error range used in
Lemma 4.28. -/
theorem lmnOutputCutoff_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < lmnOutputCutoff ε := by
  by_contra hnonpos
  have hzero : lmnOutputCutoff ε = 0 := Nat.eq_zero_of_not_pos hnonpos
  have hbound := half_pow_lmnOutputCutoff_le hε0
  rw [hzero] at hbound
  norm_num at hbound
  linarith

/-- O'Donnell, Lemma 4.28, with the two real logarithmic thresholds interpreted by natural
ceilings.  The positive-width and positive-size hypotheses make the displayed book parameters
defined; the excluded zero-width circuits are constant and form a separate degenerate endpoint. -/
theorem lemma4_28_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    {f : BooleanFunction n} {d s w : ℕ}
    (hf : DepthCircuit.HasDepthCircuit f d s w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 0 < s) (hw : 0 < w) :
    switchingFailureProbability f
        (circuitCompressionRate w (lmnLayerCutoff s ε) (d - 2))
        (lmnOutputCutoff ε) ≤ ε := by
  obtain ⟨C, hdepth, hsize, hwidth, rfl⟩ := hf
  have hℓ := lmnLayerCutoff_pos hs hε0 hε1
  have hbound := C.switchingFailureProbability_le_of_halfSwitching
    hSwitching hsize hwidth hw hℓ (k := lmnOutputCutoff ε)
  rw [hdepth] at hbound
  calc
    switchingFailureProbability C.toBooleanFunction
        (circuitCompressionRate w (lmnLayerCutoff s ε) (d - 2))
        (lmnOutputCutoff ε) ≤
        (s : ℝ) * (1 / 2 : ℝ) ^ lmnLayerCutoff s ε +
          (1 / 2 : ℝ) ^ lmnOutputCutoff ε := hbound
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (mul_half_pow_lmnLayerCutoff_le hs hε0)
      (half_pow_lmnOutputCutoff_le hε0)
    _ = ε := by ring


variable {n : ℕ}

/-- Width retained after the Proposition 4.9 truncation step in the LMN proof. -/
noncomputable def lmnWidthCutoff (s : ℕ) (ε : ℝ) : ℕ :=
  dnfWidthTruncationCutoff s (ε / 16)

/-- Exact natural degree cutoff in the finite form of the LMN theorem. -/
noncomputable def lmnDegreeCutoff (d s : ℕ) (ε : ℝ) : ℕ :=
  ⌈3 * (lmnOutputCutoff (ε / 12) : ℝ) /
      circuitCompressionRate (lmnWidthCutoff s ε)
        (lmnLayerCutoff s (ε / 12)) (d - 2)⌉₊

/-- Squared normalized `L²` distance between sign functions is four times their relative Hamming
distance. -/
theorem uniformLpNorm_sub_toReal_sq_eq_four_mul_relativeHammingDist
    (f g : BooleanFunction n) :
    uniformLpNorm 2 (fun x ↦ f.toReal x - g.toReal x) ^ 2 =
      4 * relativeHammingDist f g := by
  classical
  rw [uniformLpNorm_two_sq_eq_uniformInner, uniformInner,
    RCLike.wInner_cWeight_eq_expect,
    ← uniformProbability_ne_eq_relativeHammingDist]
  rw [uniformProbability]
  calc
    (𝔼 x, @inner ℝ ℝ _ (f.toReal x - g.toReal x)
        (f.toReal x - g.toReal x)) =
        𝔼 x, 4 * (if f x ≠ g x then (1 : ℝ) else 0) := by
      apply Finset.expect_congr rfl
      intro x _
      rcases Int.units_eq_one_or (f x) with hf | hf <;>
        rcases Int.units_eq_one_or (g x) with hg | hg <;>
          simp [BooleanFunction.toReal, hf, hg, pow_two] <;> norm_num
    _ = 4 * (𝔼 x, if f x ≠ g x then (1 : ℝ) else 0) := by
      exact (Finset.mul_expect Finset.univ
        (fun x ↦ if f x ≠ g x then (1 : ℝ) else 0) 4).symm

/-- Relative Hamming distance is symmetric. -/
theorem relativeHammingDist_comm (f g : BooleanFunction n) :
    relativeHammingDist f g = relativeHammingDist g f := by
  unfold relativeHammingDist
  rw [hammingDist_comm]

/-- The LMN width cutoff is positive in the theorem's parameter range. -/
theorem lmnWidthCutoff_pos {s : ℕ} {ε : ℝ}
    (hs : 1 < s) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    0 < lmnWidthCutoff s ε := by
  by_contra hnonpos
  have hzero : lmnWidthCutoff s ε = 0 := Nat.eq_zero_of_not_pos hnonpos
  have hbound := mul_inv_two_pow_dnfWidthTruncationCutoff_le s
    (by omega : 0 < s) (by positivity : 0 < ε / 16)
  change (s : ℝ) * ((2 : ℝ) ^ lmnWidthCutoff s ε)⁻¹ ≤ ε / 16 at hbound
  rw [hzero] at hbound
  norm_num at hbound
  have hsReal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

/-- The explicit LMN restriction rate is positive. -/
theorem lmnRestrictionRate_pos {d s : ℕ} {ε : ℝ}
    (hs : 1 < s) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    0 < circuitCompressionRate (lmnWidthCutoff s ε)
      (lmnLayerCutoff s (ε / 12)) (d - 2) := by
  have hw := lmnWidthCutoff_pos hs hε0 hε1
  have hη0 : 0 < ε / 12 := by positivity
  have hη1 : ε / 12 ≤ 1 := by linarith
  have hℓ := lmnLayerCutoff_pos (by omega : 0 < s) hη0 hη1
  unfold circuitCompressionRate switchingLayerRate
  positivity

/-- Width truncation at the LMN cutoff changes a size-`s` circuit on at most `ε / 16` of the
cube. -/
theorem DepthCircuit.relativeHammingDist_truncateWidth_lmnWidthCutoff_le
    (C : DepthCircuit n) {s : ℕ} (hsize : C.size ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hs : 0 < s) :
    relativeHammingDist C.toBooleanFunction
      (C.truncateWidth (lmnWidthCutoff s ε)).toBooleanFunction ≤ ε / 16 := by
  calc
    relativeHammingDist C.toBooleanFunction
        (C.truncateWidth (lmnWidthCutoff s ε)).toBooleanFunction ≤
        (C.size : ℝ) * ((2 : ℝ) ^ lmnWidthCutoff s ε)⁻¹ :=
      C.relativeHammingDist_truncateWidth_le _
    _ ≤ (s : ℝ) * ((2 : ℝ) ^ lmnWidthCutoff s ε)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize)
        (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
    _ ≤ ε / 16 := by
      simpa [lmnWidthCutoff] using
        (mul_inv_two_pow_dnfWidthTruncationCutoff_le s hs
          (by positivity : 0 < ε / 16))

/-- Exact finite form of the LMN Theorem.  The displayed natural cutoff is an explicit
representative of the book's
`O(log(s / ε)^(d - 1) * log(1 / ε))` degree bound. -/
theorem lmn_theorem_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    {f : BooleanFunction n} {d s : ℕ}
    (hf : ∃ w, DepthCircuit.HasDepthCircuit f d s w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hs : 1 < s) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε (lmnDegreeCutoff d s ε) := by
  obtain ⟨_w, C, hdepth, hsize, _hwidth, rfl⟩ := hf
  let η : ℝ := ε / 12
  let W : ℕ := lmnWidthCutoff s ε
  let C' : DepthCircuit n := C.truncateWidth W
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hs0 : 0 < s := by omega
  have hW : 0 < W := by
    dsimp [W]
    exact lmnWidthCutoff_pos hs hε0 hε1
  have hCircuit : DepthCircuit.HasDepthCircuit C'.toBooleanFunction d s W := by
    refine ⟨C', ?_, ?_, ?_, rfl⟩
    · simp [C', hdepth]
    · exact (C.size_truncateWidth_le W).trans hsize
    · exact C.width_truncateWidth_le W
  let δ : ℝ := circuitCompressionRate W (lmnLayerCutoff s η) (d - 2)
  let k : ℕ := lmnOutputCutoff η
  have hℓ : 0 < lmnLayerCutoff s η :=
    lmnLayerCutoff_pos hs0 hη0 hη1
  have hδ0 : 0 < δ := by
    dsimp [δ, circuitCompressionRate, switchingLayerRate]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact circuitCompressionRate_le_one hW hℓ
  have hk : 0 < k := by
    dsimp [k]
    exact lmnOutputCutoff_pos hη0 hη1
  have hfailure : switchingFailureProbability C'.toBooleanFunction δ k ≤ η := by
    simpa [δ, k] using
      (lemma4_28_of_halfSwitching hSwitching hCircuit hη0 hη1 hs0 hW)
  have hrestricted :
      IsFourierSpectrumConcentratedUpTo C'.toBooleanFunction.toReal (ε / 4)
        (3 * (k : ℝ) / δ) := by
    apply (lemma4_21 C'.toBooleanFunction hδ0 hδ1 hk).mono_error
    dsimp [η] at hfailure
    linarith
  have hcutoff : 3 * (k : ℝ) / δ ≤ (lmnDegreeCutoff d s ε : ℝ) := by
    exact Nat.le_ceil _
  have hrestricted' :
      IsFourierSpectrumConcentratedUpTo C'.toBooleanFunction.toReal (ε / 4)
        (lmnDegreeCutoff d s ε : ℝ) := by
    apply hrestricted.mono_cutoff
    simpa [lmnDegreeCutoff, δ, k, W, η] using hcutoff
  have hrestrictedOn :
      IsFourierSpectrumConcentratedOn C'.toBooleanFunction.toReal (ε / 4)
        (↑(lowDegreeFourierFamily n (lmnDegreeCutoff d s ε)) :
          Set (Finset (Fin n))) := by
    exact (isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff
      C'.toBooleanFunction.toReal (ε / 4) (lmnDegreeCutoff d s ε)).2 hrestricted'
  have hdist :
      relativeHammingDist C.toBooleanFunction C'.toBooleanFunction ≤ ε / 16 := by
    dsimp [C', W]
    exact C.relativeHammingDist_truncateWidth_lmnWidthCutoff_le hsize hε0 hs0
  have hl2 :
      uniformLpNorm 2
          (fun x ↦ C'.toBooleanFunction.toReal x - C.toBooleanFunction.toReal x) ^ 2 ≤
        ε / 4 := by
    rw [uniformLpNorm_sub_toReal_sq_eq_four_mul_relativeHammingDist]
    rw [relativeHammingDist_comm]
    have hscaled := mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have htransfer := hrestrictedOn.transfer_of_uniformLpNorm_sub_sq_le
    C'.toBooleanFunction.toReal C.toBooleanFunction.toReal
    (↑(lowDegreeFourierFamily n (lmnDegreeCutoff d s ε)) :
      Set (Finset (Fin n))) hl2
  have htransfer' :
      IsFourierSpectrumConcentratedOn C.toBooleanFunction.toReal ε
        (↑(lowDegreeFourierFamily n (lmnDegreeCutoff d s ε)) :
          Set (Finset (Fin n))) := by
    convert htransfer using 1
    ring
  exact (isFourierSpectrumConcentratedOn_lowDegreeFourierFamily_iff
    C.toBooleanFunction.toReal ε (lmnDegreeCutoff d s ε)).1 htransfer'

/-! ## Learning bounded-depth circuits -/


variable {n : ℕ}

/-- Boolean functions computable by a depth-`d` circuit of size at most `s`, with no artificial
restriction on the bottom fan-in. -/
def depthSizeCircuitClass (n d s : ℕ) : Set (BooleanFunction n) :=
  {target | ∃ width, DepthCircuit.HasDepthCircuit target d s width}

/-- Exact number of random examples used by the degree-`k` Low-Degree Algorithm. -/
noncomputable def lowDegreeLearnerRandomExampleCost
    (n k : ℕ) (ε : PositiveLearningParameter) : ℕ :=
  (lowDegreeFourierFamily n k).card *
    finiteFamilySamplesPerCoefficient (lowDegreeFourierFamily n k)
      (lowDegreeFourierFamily_nonempty n k) ε

/-- Exact local-work charge of the degree-`k` Low-Degree Algorithm. -/
noncomputable def lowDegreeLearnerWorkCost
    (n k : ℕ) (ε : PositiveLearningParameter) : ℕ :=
  lowDegreeLearnerRandomExampleCost n k ε +
    lowDegreeLearnerRandomExampleCost n k ε * (n + 1)

/-- Every execution of the Low-Degree Algorithm has its constructor-derived exact cost. -/
theorem lowDegreeFourierEstimatorProgram_cost_eq
    (target : BooleanFunction n) (k : ℕ) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (lowDegreeFourierEstimatorProgram n k ε)).support) :
    outcome.2 =
      ⟨lowDegreeLearnerRandomExampleCost n k ε, 0,
        lowDegreeLearnerWorkCost n k ε⟩ := by
  simpa [lowDegreeFourierEstimatorProgram, lowDegreeLearnerRandomExampleCost,
    lowDegreeLearnerWorkCost] using
    finiteFamilyFourierEstimatorProgram_cost_eq target
      (lowDegreeFourierFamily n k) (lowDegreeFourierFamily_nonempty n k) ε
      outcome houtcome

/-- Any proved upper bound on the exact work schedule bounds every execution path, including its
random-example count; the learner makes no membership queries. -/
theorem lowDegreeFourierEstimatorProgram_cost_le_workBound
    (target : BooleanFunction n) (k workBound : ℕ)
    (ε : PositiveLearningParameter)
    (hwork : lowDegreeLearnerWorkCost n k ε ≤ workBound)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (lowDegreeFourierEstimatorProgram n k ε)).support) :
    outcome.2.randomExamples ≤ workBound ∧
      outcome.2.queries = 0 ∧ outcome.2.work ≤ workBound := by
  rw [lowDegreeFourierEstimatorProgram_cost_eq target k ε outcome houtcome]
  refine ⟨?_, rfl, hwork⟩
  apply le_trans ?_ hwork
  simp only [lowDegreeLearnerWorkCost]
  omega

/-- Exact finite form of O'Donnell's Theorem 4.31. The concentration premise is the output of
the LMN theorem at half the requested learning error. Its explicit cutoff determines a
random-example program, and a separate work bound records the asymptotic arithmetic. -/
theorem theorem4_31_of_lowDegreeConcentration
    (d size degree workBound : ℕ) (ε : PositiveLearningParameter)
    (hconcentration : ∀ target ∈ depthSizeCircuitClass n d size,
      IsFourierSpectrumConcentratedUpTo target.toReal ((ε.1 : ℝ) / 2) degree)
    (hwork : lowDegreeLearnerWorkCost n degree ε ≤ workBound) :
    (∀ target ∈ depthSizeCircuitClass n d size,
      LearningProgram.eventProbability
          (lowDegreeFourierEstimatorProgram n degree ε) target
          (fun outcome ↦
            (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
        (1 / 10 : ℝ)) ∧
      ∀ target outcome,
        outcome ∈
            (LearningProgram.runWithCost target
              (lowDegreeFourierEstimatorProgram n degree ε)).support →
          outcome.2.randomExamples ≤ workBound ∧
            outcome.2.queries = 0 ∧ outcome.2.work ≤ workBound := by
  constructor
  · intro target htarget
    exact lowDegreeFourierEstimatorProgram_failureProbability_le_one_tenth
      target degree ε (hconcentration target htarget)
  · intro target outcome houtcome
    exact lowDegreeFourierEstimatorProgram_cost_le_workBound
      target degree workBound ε hwork outcome houtcome

/-- Degree used by the LMN Low-Degree learner at half of the requested classification error. -/
noncomputable def lmnCircuitLearningDegree
    (d size : ℕ) (ε : PositiveLearningParameter) : ℕ :=
  lmnDegreeCutoff d size ((ε.1 : ℝ) / 2)

/-- Exact target-independent work schedule of the LMN Low-Degree learner. -/
noncomputable def lmnCircuitLearnerWorkCost
    (n d size : ℕ) (ε : PositiveLearningParameter) : ℕ :=
  lowDegreeLearnerWorkCost n (lmnCircuitLearningDegree d size ε) ε

/-- O'Donnell's Theorem 4.31 in finite executable form.  The learner uses only random examples,
and every path has the exact target-independent work bound displayed in the conclusion. -/
theorem theorem4_31_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    (d size : ℕ) (hsize : 1 < size) (ε : PositiveLearningParameter) :
    (∀ target ∈ depthSizeCircuitClass n d size,
      LearningProgram.eventProbability
          (lowDegreeFourierEstimatorProgram n
            (lmnCircuitLearningDegree d size ε) ε) target
          (fun outcome ↦
            (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
        (1 / 10 : ℝ)) ∧
      ∀ target outcome,
        outcome ∈
            (LearningProgram.runWithCost target
              (lowDegreeFourierEstimatorProgram n
                (lmnCircuitLearningDegree d size ε) ε)).support →
          outcome.2.randomExamples ≤ lmnCircuitLearnerWorkCost n d size ε ∧
            outcome.2.queries = 0 ∧
            outcome.2.work ≤ lmnCircuitLearnerWorkCost n d size ε := by
  apply theorem4_31_of_lowDegreeConcentration d size
    (lmnCircuitLearningDegree d size ε)
    (lmnCircuitLearnerWorkCost n d size ε) ε
  · intro target htarget
    have hε := positiveLearningParameter_toReal_mem_Ioc ε
    have hε0 : 0 < (ε.1 : ℝ) := hε.1
    have hε1 : (ε.1 : ℝ) ≤ 1 / 2 := hε.2
    exact lmn_theorem_of_halfSwitching hSwitching htarget
      (half_pos hε0) (by linarith) hsize
  · exact le_rfl

/-- The number of Fourier coefficients learned in Theorem 4.31 has the standard explicit
`(k + 1) * (n + 1)^k` bound. -/
theorem card_lmnCircuitLearningFamily_le
    (d size : ℕ) (ε : PositiveLearningParameter) :
    (lowDegreeFourierFamily n (lmnCircuitLearningDegree d size ε)).card ≤
      (lmnCircuitLearningDegree d size ε + 1) *
        (n + 1) ^ lmnCircuitLearningDegree d size ε :=
  card_lowDegreeFourierFamily_le n (lmnCircuitLearningDegree d size ε)


/-! ## Constant-depth circuit lower bounds for parity -/


variable {n : ℕ}

/-- O'Donnell, Corollary 4.32, with the asymptotic size lower bound expressed as its exact finite
LMN-cutoff obstruction. -/
theorem DepthCircuit.corollary4_32_of_halfSwitching
    (hSwitching : HasHalfSwitchingBound)
    (C : DepthCircuit n) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hagreement :
      1 / 2 + ε₀ ≤ uniformProbability (fun x ↦
        C.toBooleanFunction x = parityFunction (Finset.univ : Finset (Fin n)) x)) :
    ∀ s : ℕ, 1 < s →
      lmnDegreeCutoff C.depth s (2 * ε₀ ^ 2) < n → s < C.size := by
  have hprobability :
      uniformProbability (fun x ↦
        C.toBooleanFunction x = parityFunction (Finset.univ : Finset (Fin n)) x) ≤ 1 :=
    uniformProbability_le_one _
  have hε₀half : ε₀ ≤ 1 / 2 := by linarith
  intro s hs hcutoff
  by_contra hsizeNot
  have hsize : C.size ≤ s := Nat.le_of_not_gt hsizeNot
  have hCircuit :
      ∃ w, DepthCircuit.HasDepthCircuit C.toBooleanFunction C.depth s w := by
    refine ⟨C.width, C, rfl, hsize, le_rfl, rfl⟩
  have hη0 : 0 < 2 * ε₀ ^ 2 := by positivity
  have hη1 : 2 * ε₀ ^ 2 ≤ 1 / 2 := by nlinarith
  have hconcentration :=
    lmn_theorem_of_halfSwitching hSwitching hCircuit hη0 hη1 hs
  have hdegree :
      (n : ℝ) ≤ (lmnDegreeCutoff C.depth s (2 * ε₀ ^ 2) : ℕ) :=
    parityAgreement_forces_concentration_cutoff C.toBooleanFunction hε₀
      (by nlinarith) hagreement hconcentration
  have hdegreeNat : n ≤ lmnDegreeCutoff C.depth s (2 * ε₀ ^ 2) := by
    exact_mod_cast hdegree
  omega

/-! ## Book-facing consequences of the exact switching lemma -/

/-- Håstad's Switching Lemma supplies the half-tail hypothesis used throughout the LMN proof. -/
theorem hastadHalfSwitchingBoundForCircuits : HasHalfSwitchingBound := by
  intro N w f hw hf k
  simpa [switchingLayerRate] using hastadHalfSwitchingBound f hw hf k

/-- O'Donnell, Lemma 4.28, with logarithms interpreted by the explicit natural ceilings. -/
theorem lemma4_28
    {f : BooleanFunction n} {d s w : ℕ}
    (hf : DepthCircuit.HasDepthCircuit f d s w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 0 < s) (hw : 0 < w) :
    switchingFailureProbability f
        (circuitCompressionRate w (lmnLayerCutoff s ε) (d - 2))
        (lmnOutputCutoff ε) ≤ ε :=
  lemma4_28_of_halfSwitching hastadHalfSwitchingBoundForCircuits
    hf hε0 hε1 hs hw

/-- O'Donnell's LMN Theorem with its finite explicit degree cutoff. -/
theorem lmn_theorem
    {f : BooleanFunction n} {d s : ℕ}
    (hf : ∃ w, DepthCircuit.HasDepthCircuit f d s w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hs : 1 < s) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε (lmnDegreeCutoff d s ε) :=
  lmn_theorem_of_halfSwitching hastadHalfSwitchingBoundForCircuits
    hf hε0 hε1 hs

/-- O'Donnell, Theorem 4.31, as an executable random-example learner with exact pathwise cost. -/
theorem theorem4_31
    (d size : ℕ) (hsize : 1 < size) (ε : PositiveLearningParameter) :
    (∀ target ∈ depthSizeCircuitClass n d size,
      LearningProgram.eventProbability
          (lowDegreeFourierEstimatorProgram n
            (lmnCircuitLearningDegree d size ε) ε) target
          (fun outcome ↦
            (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
        (1 / 10 : ℝ)) ∧
      ∀ target outcome,
        outcome ∈
            (LearningProgram.runWithCost target
              (lowDegreeFourierEstimatorProgram n
                (lmnCircuitLearningDegree d size ε) ε)).support →
          outcome.2.randomExamples ≤ lmnCircuitLearnerWorkCost n d size ε ∧
            outcome.2.queries = 0 ∧
            outcome.2.work ≤ lmnCircuitLearnerWorkCost n d size ε :=
  theorem4_31_of_halfSwitching hastadHalfSwitchingBoundForCircuits
    d size hsize ε

/-- O'Donnell, Corollary 4.32, in exact finite inverse-cutoff form. -/
theorem DepthCircuit.corollary4_32
    (C : DepthCircuit n) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hagreement :
      1 / 2 + ε₀ ≤ uniformProbability (fun x ↦
        C.toBooleanFunction x = parityFunction (Finset.univ : Finset (Fin n)) x)) :
    ∀ s : ℕ, 1 < s →
      lmnDegreeCutoff C.depth s (2 * ε₀ ^ 2) < n → s < C.size :=
  C.corollary4_32_of_halfSwitching hastadHalfSwitchingBoundForCircuits
    hε₀ hagreement

end FABL
