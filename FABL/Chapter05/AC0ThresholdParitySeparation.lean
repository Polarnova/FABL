/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.Restrictions
public import FABL.Chapter04.Parity
public import FABL.Chapter05.InnerProductModTwo
public import FABL.Chapter05.ThresholdCircuits

/-!
# AC⁰ versus threshold-of-parities

Book item: Exercise 5.14.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

private theorem two_mul_sq_le_two_pow_of_seven_le
    (m : ℕ) (hm : 7 ≤ m) :
    2 * m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num
  | succ m hm ih =>
      have hsquare : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by
        nlinarith
      calc
        2 * (m + 1) ^ 2 ≤ 2 * (2 * m ^ 2) :=
          Nat.mul_le_mul_left 2 hsquare
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ac_rfl

private theorem activeCoordinateCount_le_dimension
    (m : ℕ) (hm : 7 ≤ m) :
    m * m + m * m ≤ 2 ^ m := by
  simpa [two_mul, pow_two] using
    two_mul_sq_le_two_pow_of_seven_le m hm

private def blockCoordinateValue
    (m : ℕ) (b : Fin m) (j : Fin (m + m)) : ℕ :=
  if j.1 < m then b.1 * m + j.1
  else m * m + b.1 * m + (j.1 - m)

private theorem blockCoordinateValue_lt_active
    (m : ℕ) (b : Fin m) (j : Fin (m + m)) :
    blockCoordinateValue m b j < m * m + m * m := by
  by_cases hj : j.1 < m
  · rw [blockCoordinateValue, if_pos hj]
    have hb :
        b.1 * m + j.1 < m * m := by
      calc
        b.1 * m + j.1 < b.1 * m + m :=
          Nat.add_lt_add_left hj _
        _ = (b.1 + 1) * m := by simp [Nat.add_mul]
        _ ≤ m * m :=
          Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.2)
    omega
  · rw [blockCoordinateValue, if_neg hj]
    have hjUpper : j.1 - m < m := by omega
    have hb :
        b.1 * m + (j.1 - m) < m * m := by
      calc
        b.1 * m + (j.1 - m) < b.1 * m + m :=
          Nat.add_lt_add_left hjUpper _
        _ = (b.1 + 1) * m := by simp [Nat.add_mul]
        _ ≤ m * m :=
          Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.2)
    omega

private def blockCoordinate
    (m : ℕ) (hm : 7 ≤ m) (b : Fin m) (j : Fin (m + m)) :
    Fin (2 ^ m) :=
  ⟨blockCoordinateValue m b j,
    (blockCoordinateValue_lt_active m b j).trans_le
      (activeCoordinateCount_le_dimension m hm)⟩

private theorem blockCoordinate_injective
    (m : ℕ) (hm : 7 ≤ m) (b : Fin m) :
    Function.Injective (blockCoordinate m hm b) := by
  intro i j hij
  apply Fin.ext
  have hval :
      blockCoordinateValue m b i =
        blockCoordinateValue m b j :=
    congrArg Fin.val hij
  by_cases hi : i.1 < m <;> by_cases hj : j.1 < m
  · simp only [blockCoordinateValue, if_pos hi, if_pos hj] at hval
    omega
  · have hleft :
        blockCoordinateValue m b i < m * m := by
      rw [blockCoordinateValue, if_pos hi]
      calc
        b.1 * m + i.1 < b.1 * m + m :=
          Nat.add_lt_add_left hi _
        _ = (b.1 + 1) * m := by simp [Nat.add_mul]
        _ ≤ m * m :=
          Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.2)
    have hright :
        m * m ≤ blockCoordinateValue m b j := by
      rw [blockCoordinateValue, if_neg hj]
      exact
        (Nat.le_add_right (m * m) (b.1 * m)).trans
          (Nat.le_add_right (m * m + b.1 * m) (j.1 - m))
    omega
  · have hleft :
        m * m ≤ blockCoordinateValue m b i := by
      rw [blockCoordinateValue, if_neg hi]
      exact
        (Nat.le_add_right (m * m) (b.1 * m)).trans
          (Nat.le_add_right (m * m + b.1 * m) (i.1 - m))
    have hright :
        blockCoordinateValue m b j < m * m := by
      rw [blockCoordinateValue, if_pos hj]
      calc
        b.1 * m + j.1 < b.1 * m + m :=
          Nat.add_lt_add_left hj _
        _ = (b.1 + 1) * m := by simp [Nat.add_mul]
        _ ≤ m * m :=
          Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.2)
    omega
  · simp only [blockCoordinateValue, if_neg hi, if_neg hj] at hval
    omega

private def blockInput
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m]) (b : Fin m) :
    {−1,1}^[m + m] :=
  fun j ↦ x (blockCoordinate m hm b j)

private noncomputable def blockMinterm
    (m : ℕ) (hm : 7 ≤ m) (b : Fin m)
    (a : ParityBlockAssignment (m + m)) :
    DNFTerm (2 ^ m) where
  literals :=
    (Finset.univ : Finset (Fin (m + m))).toList.map
      fun j ↦ ⟨blockCoordinate m hm b j, a j⟩
  nodupIndices := by
    simp only [List.map_map, Function.comp_def]
    exact
      (Finset.nodup_toList
        (Finset.univ : Finset (Fin (m + m)))).map
          (blockCoordinate_injective m hm b)

private theorem width_blockMinterm
    (m : ℕ) (hm : 7 ≤ m) (b : Fin m)
    (a : ParityBlockAssignment (m + m)) :
    (blockMinterm m hm b a).width = m + m := by
  simp [blockMinterm, DNFTerm.width]

private theorem blockMinterm_eval_eq_neg_one_iff
    (m : ℕ) (hm : 7 ≤ m) (b : Fin m)
    (a : ParityBlockAssignment (m + m))
    (x : {−1,1}^[2 ^ m]) :
    (blockMinterm m hm b a).eval x = -1 ↔
      a = blockInput m hm x b := by
  rw [DNFTerm.eval_eq_neg_one_iff]
  constructor
  · intro h
    funext j
    have hliteral :
        (⟨blockCoordinate m hm b j, a j⟩ : Literal (2 ^ m)) ∈
          (blockMinterm m hm b a).literals := by
      change _ ∈
        (Finset.univ : Finset (Fin (m + m))).toList.map _
      exact List.mem_map.mpr ⟨j, by simp, rfl⟩
    exact (h _ hliteral).symm
  · intro h ℓ hℓ
    simp only [blockMinterm, List.mem_map, Finset.mem_toList] at hℓ
    obtain ⟨j, ⟨-, rfl⟩⟩ := hℓ
    simpa [blockInput] using (congrFun h j).symm

private def blockLayerSize (m : ℕ) : ℕ :=
  m * 2 ^ (m + m)

private noncomputable def blockAssignmentIndexEquiv
    (m : ℕ) :
    Fin (blockLayerSize m) ≃
      Fin m × ParityBlockAssignment (m + m) :=
  (finProdFinEquiv (m := m) (n := 2 ^ (m + m))).symm |>.trans
    ((Equiv.refl (Fin m)).prodCongr
      (parityBlockAssignmentEquiv (m + m)))

private noncomputable def blockFirstLayer
    (m : ℕ) (hm : 7 ≤ m) :
    List (DNFTerm (2 ^ m)) :=
  List.ofFn fun i : Fin (blockLayerSize m) ↦
    let ba := blockAssignmentIndexEquiv m i
    blockMinterm m hm ba.1 ba.2

@[simp] private theorem length_blockFirstLayer
    (m : ℕ) (hm : 7 ≤ m) :
    (blockFirstLayer m hm).length = blockLayerSize m := by
  simp [blockFirstLayer]

private theorem eval_blockFirstLayer
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m])
    (i : Fin (blockLayerSize m)) :
    CircuitGate.and.evalTerm
        ((blockFirstLayer m hm).get
          (i.cast (length_blockFirstLayer m hm).symm)) x = -1 ↔
      (blockAssignmentIndexEquiv m i).2 =
        blockInput m hm x (blockAssignmentIndexEquiv m i).1 := by
  simp only [CircuitGate.evalTerm]
  rw [show
      (blockFirstLayer m hm).get
          (i.cast (length_blockFirstLayer m hm).symm) =
        blockMinterm m hm (blockAssignmentIndexEquiv m i).1
          (blockAssignmentIndexEquiv m i).2 by
    simp [blockFirstLayer]]
  exact blockMinterm_eval_eq_neg_one_iff m hm _ _ x

private def blockInnerProductValue
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m])
    (b : Fin m) : Sign :=
  innerProductModTwoBoolean m (blockInput m hm x b)

private def blockOutputPattern
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m]) :
    ParityBlockAssignment m :=
  fun b ↦ blockInnerProductValue m hm x b

/-- Exercise 5.14: the product of `m` copies of `IP₂ₘ`, using the first `2m²`
coordinates of an `N = 2ᵐ` dimensional sign cube. -/
def ac0ThresholdParityTarget
    (m : ℕ) (hm : 7 ≤ m) :
    BooleanFunction (2 ^ m) :=
  fun x ↦
    ∏ b : Fin m,
      innerProductModTwoBoolean m fun j ↦
        x ⟨if j.1 < m then b.1 * m + j.1
            else m * m + b.1 * m + (j.1 - m), by
          change blockCoordinateValue m b j < 2 ^ m
          exact (blockCoordinateValue_lt_active m b j).trans_le
            (activeCoordinateCount_le_dimension m hm)⟩

private theorem ac0ThresholdParityTarget_apply
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m]) :
    ac0ThresholdParityTarget m hm x =
      parityBlockProduct (blockOutputPattern m hm x) := by
  apply Finset.prod_congr rfl
  intro b _
  congr 1

private noncomputable def clauseNodeInputs
    (m : ℕ) (C : DNFTerm m) :
    Finset (Fin (blockLayerSize m)) := by
  classical
  exact Finset.univ.filter fun i ↦
    ∃ ℓ ∈ C.literals,
      let ba := blockAssignmentIndexEquiv m i
      ba.1 = ℓ.index ∧
        innerProductModTwoBoolean m ba.2 = ℓ.required

private noncomputable def blockMiddleLayer
    (m : ℕ) :
    List (Finset (Fin (blockLayerSize m))) :=
  (parityCNF m).clauses.map (clauseNodeInputs m)

private theorem length_blockMiddleLayer
    (m : ℕ) (hm : 7 ≤ m) :
    (blockMiddleLayer m).length = 2 ^ (m - 1) := by
  rw [blockMiddleLayer, List.length_map]
  exact size_parityCNF (by omega)

private noncomputable def ac0ThresholdParityCircuit
    (m : ℕ) (hm : 7 ≤ m) :
    DepthCircuit (2 ^ m) where
  layer1Gate := .and
  layer1 := blockFirstLayer m hm
  tail := cast
    (congrArg CircuitTail (length_blockFirstLayer m hm).symm)
    (.layer (blockMiddleLayer m) (.output Finset.univ))

@[simp] private theorem depth_ac0ThresholdParityCircuit
    (m : ℕ) (hm : 7 ≤ m) :
    (ac0ThresholdParityCircuit m hm).depth = 3 := by
  unfold DepthCircuit.depth ac0ThresholdParityCircuit
  change 1 +
      (cast (congrArg CircuitTail
        (length_blockFirstLayer m hm).symm)
        (.layer (blockMiddleLayer m)
          (.output Finset.univ))).layerCount = 3
  rw [circuitTail_layerCount_cast]
  case h => exact (length_blockFirstLayer m hm).symm
  rfl

private theorem size_ac0ThresholdParityCircuit
    (m : ℕ) (hm : 7 ≤ m) :
    (ac0ThresholdParityCircuit m hm).size ≤
      m * 2 ^ (2 * m) + 2 ^ m := by
  unfold DepthCircuit.size ac0ThresholdParityCircuit
  change (blockFirstLayer m hm).length +
      (cast (congrArg CircuitTail
        (length_blockFirstLayer m hm).symm)
        (.layer (blockMiddleLayer m)
          (.output Finset.univ))).internalNodeCount ≤
        m * 2 ^ (2 * m) + 2 ^ m
  rw [circuitTail_internalNodeCount_cast]
  case h => exact (length_blockFirstLayer m hm).symm
  simp only [CircuitTail.internalNodeCount, Nat.add_zero]
  rw [length_blockFirstLayer m hm, length_blockMiddleLayer m hm]
  rw [blockLayerSize]
  have hpow : 2 ^ (m - 1) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1)
  calc
    m * 2 ^ (m + m) + 2 ^ (m - 1) ≤
        m * 2 ^ (m + m) + 2 ^ m :=
      Nat.add_le_add_left hpow _
    _ = m * 2 ^ (2 * m) + 2 ^ m := by
      rw [show m + m = 2 * m by omega]

private theorem blockFirstLayer_width
    (m : ℕ) (hm : 7 ≤ m) :
    (DNFFormula.mk (blockFirstLayer m hm)).width = m + m := by
  apply Nat.le_antisymm
  · rw [DNFFormula.width_le_iff]
    intro T hT
    change T ∈ blockFirstLayer m hm at hT
    rw [blockFirstLayer, List.mem_ofFn'] at hT
    obtain ⟨i, rfl⟩ := hT
    exact (width_blockMinterm m hm
      (blockAssignmentIndexEquiv m i).1
      (blockAssignmentIndexEquiv m i).2).le
  · have hsizePos : 0 < blockLayerSize m := by
      simp [blockLayerSize]
      omega
    let i : Fin (blockLayerSize m) := ⟨0, hsizePos⟩
    have hmem :
        (blockFirstLayer m hm).get
            (i.cast (length_blockFirstLayer m hm).symm) ∈
          blockFirstLayer m hm :=
      List.get_mem _ _
    have hlower :=
      DNFFormula.width_le_of_mem
        (DNFFormula.mk (blockFirstLayer m hm)) hmem
    rw [show
        (blockFirstLayer m hm).get
            (i.cast (length_blockFirstLayer m hm).symm) =
          blockMinterm m hm (blockAssignmentIndexEquiv m i).1
            (blockAssignmentIndexEquiv m i).2 by
      simp [blockFirstLayer],
      width_blockMinterm] at hlower
    exact hlower

@[simp] private theorem width_ac0ThresholdParityCircuit
    (m : ℕ) (hm : 7 ≤ m) :
    (ac0ThresholdParityCircuit m hm).width = 2 * m := by
  unfold DepthCircuit.width ac0ThresholdParityCircuit
  rw [blockFirstLayer_width]
  omega

private theorem eval_clauseNodeInputs
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m])
    (C : DNFTerm m) :
    CircuitGate.or.evalFinset
        (fun i : Fin (blockLayerSize m) ↦
          CircuitGate.and.evalTerm
            ((blockFirstLayer m hm).get
              (i.cast (length_blockFirstLayer m hm).symm)) x)
        (clauseNodeInputs m C) =
      CNFFormula.clauseEval C (blockOutputPattern m hm x) := by
  have hclause :
      CNFFormula.clauseEval C (blockOutputPattern m hm x) = -1 ↔
        ∃ ℓ ∈ C.literals,
          blockOutputPattern m hm x ℓ.index = ℓ.required := by
    simp [CNFFormula.clauseEval, Literal.eval]
  have hneg :
      CircuitGate.or.evalFinset
          (fun i : Fin (blockLayerSize m) ↦
            CircuitGate.and.evalTerm
              ((blockFirstLayer m hm).get
                (i.cast (length_blockFirstLayer m hm).symm)) x)
          (clauseNodeInputs m C) = -1 ↔
        CNFFormula.clauseEval C (blockOutputPattern m hm x) = -1 := by
    rw [CircuitGate.evalFinset_or_eq_neg_one_iff, hclause]
    constructor
    · rintro ⟨i, hi, hix⟩
      have hi' := hi
      simp only [clauseNodeInputs, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi'
      obtain ⟨ℓ, hℓ, hindex, hvalue⟩ := hi'
      have hassignment :=
        (eval_blockFirstLayer m hm x i).1 hix
      refine ⟨ℓ, hℓ, ?_⟩
      rw [blockOutputPattern, blockInnerProductValue, ← hindex,
        ← hassignment]
      exact hvalue
    · rintro ⟨ℓ, hℓ, hvalue⟩
      let i : Fin (blockLayerSize m) :=
        (blockAssignmentIndexEquiv m).symm
          (ℓ.index, blockInput m hm x ℓ.index)
      refine ⟨i, ?_, ?_⟩
      · simp only [clauseNodeInputs, Finset.mem_filter,
          Finset.mem_univ, true_and]
        refine ⟨ℓ, hℓ, ?_, ?_⟩
        · simp [i]
        · simpa [i, blockOutputPattern, blockInnerProductValue]
            using hvalue
      · exact (eval_blockFirstLayer m hm x i).2 (by simp [i])
  by_cases hleft :
      CircuitGate.or.evalFinset
          (fun i : Fin (blockLayerSize m) ↦
            CircuitGate.and.evalTerm
              ((blockFirstLayer m hm).get
                (i.cast (length_blockFirstLayer m hm).symm)) x)
          (clauseNodeInputs m C) = -1
  · exact hleft.trans (hneg.mp hleft).symm
  · have hright :
        CNFFormula.clauseEval C (blockOutputPattern m hm x) ≠ -1 :=
      fun h ↦ hleft (hneg.mpr h)
    exact
      (CNFFormula.sign_eq_of_ne_neg _ 1 (by simpa using hleft)).trans
        (CNFFormula.sign_eq_of_ne_neg _ 1 (by simpa using hright)).symm

private theorem eval_blockMiddleLayer_get
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m])
    (i : Fin (blockMiddleLayer m).length) :
    CircuitGate.or.evalFinset
        (fun j : Fin (blockLayerSize m) ↦
          CircuitGate.and.evalTerm
            ((blockFirstLayer m hm).get
              (j.cast (length_blockFirstLayer m hm).symm)) x)
        ((blockMiddleLayer m).get i) =
      CNFFormula.clauseEval
        ((parityCNF m).clauses.get
          (i.cast (by simp [blockMiddleLayer])))
        (blockOutputPattern m hm x) := by
  rw [show
      (blockMiddleLayer m).get i =
        clauseNodeInputs m
          ((parityCNF m).clauses.get
            (i.cast (by simp [blockMiddleLayer]))) by
    simp [blockMiddleLayer]]
  exact eval_clauseNodeInputs m hm x _

private theorem eval_blockMiddleLayer
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m]) :
    CircuitGate.and.evalFinset
        (fun i : Fin (blockMiddleLayer m).length ↦
          CircuitGate.or.evalFinset
            (fun j : Fin (blockLayerSize m) ↦
              CircuitGate.and.evalTerm
                ((blockFirstLayer m hm).get
                  (j.cast (length_blockFirstLayer m hm).symm)) x)
            ((blockMiddleLayer m).get i))
        Finset.univ =
      (parityCNF m).eval (blockOutputPattern m hm x) := by
  have hneg :
      CircuitGate.and.evalFinset
          (fun i : Fin (blockMiddleLayer m).length ↦
            CircuitGate.or.evalFinset
              (fun j : Fin (blockLayerSize m) ↦
                CircuitGate.and.evalTerm
                  ((blockFirstLayer m hm).get
                    (j.cast (length_blockFirstLayer m hm).symm)) x)
              ((blockMiddleLayer m).get i))
          Finset.univ = -1 ↔
        (parityCNF m).eval (blockOutputPattern m hm x) = -1 := by
    rw [CircuitGate.evalFinset_and_eq_neg_one_iff]
    simp only [Finset.mem_univ, forall_const]
    rw [show
        (parityCNF m).eval (blockOutputPattern m hm x) = -1 ↔
          ∀ C ∈ (parityCNF m).clauses,
            CNFFormula.clauseEval C (blockOutputPattern m hm x) = -1 by
      simp [CNFFormula.eval, List.all_eq_true],
      List.forall_mem_iff_get]
    constructor
    · intro h i
      have hi :=
        h (i.cast (by simp [blockMiddleLayer]))
      rw [eval_blockMiddleLayer_get m hm x] at hi
      simpa using hi
    · intro h i
      rw [eval_blockMiddleLayer_get m hm x]
      exact h _
  by_cases hleft :
      CircuitGate.and.evalFinset
          (fun i : Fin (blockMiddleLayer m).length ↦
            CircuitGate.or.evalFinset
              (fun j : Fin (blockLayerSize m) ↦
                CircuitGate.and.evalTerm
                  ((blockFirstLayer m hm).get
                    (j.cast (length_blockFirstLayer m hm).symm)) x)
              ((blockMiddleLayer m).get i))
          Finset.univ = -1
  · exact hleft.trans (hneg.mp hleft).symm
  · have hright :
        (parityCNF m).eval (blockOutputPattern m hm x) ≠ -1 :=
      fun h ↦ hleft (hneg.mpr h)
    exact
      (CNFFormula.sign_eq_of_ne_neg _ 1 (by simpa using hleft)).trans
        (CNFFormula.sign_eq_of_ne_neg _ 1 (by simpa using hright)).symm

private theorem eval_ac0ThresholdParityCircuit
    (m : ℕ) (hm : 7 ≤ m) (x : {−1,1}^[2 ^ m]) :
    (ac0ThresholdParityCircuit m hm).eval x =
      ac0ThresholdParityTarget m hm x := by
  unfold DepthCircuit.eval ac0ThresholdParityCircuit
  change
    (cast (congrArg CircuitTail
      (length_blockFirstLayer m hm).symm)
      (.layer (blockMiddleLayer m)
        (.output Finset.univ))).eval .or
      (fun i ↦ CircuitGate.and.evalTerm
        ((blockFirstLayer m hm).get i) x) =
      ac0ThresholdParityTarget m hm x
  rw [circuitTail_eval_cast]
  case h => exact (length_blockFirstLayer m hm).symm
  simp only [CircuitTail.eval, CircuitGate.dual_or]
  rw [eval_blockMiddleLayer]
  change
    (parityCNF m).toBooleanFunction
        (blockOutputPattern m hm x) =
      ac0ThresholdParityTarget m hm x
  rw [parityCNF_toBooleanFunction,
    ac0ThresholdParityTarget_apply]
  simp [parityFunction, parityBlockProduct]

private theorem ac0ThresholdParityCircuit_size_le_cube
    (m : ℕ) :
    m * 2 ^ (2 * m) + 2 ^ m ≤ (2 ^ m) ^ 3 := by
  have hm :
      m + 1 ≤ 2 ^ m :=
    Nat.succ_le_iff.mpr m.lt_two_pow_self
  have hone : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hfactor :
      m * 2 ^ m + 1 ≤ 2 ^ m * 2 ^ m := by
    calc
      m * 2 ^ m + 1 ≤ m * 2 ^ m + 2 ^ m :=
        Nat.add_le_add_left hone _
      _ = (m + 1) * 2 ^ m := by
        rw [Nat.add_mul, one_mul]
      _ ≤ 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul_right (2 ^ m) hm
  have hpow :
      2 ^ (2 * m) = (2 ^ m) ^ 2 := by
    rw [show 2 * m = m * 2 by omega, pow_mul]
  calc
    m * 2 ^ (2 * m) + 2 ^ m =
        (m * 2 ^ m + 1) * 2 ^ m := by
      rw [hpow]
      ring
    _ ≤ (2 ^ m * 2 ^ m) * 2 ^ m :=
      Nat.mul_le_mul_right (2 ^ m) hfactor
    _ = (2 ^ m) ^ 3 := by ring

/-- Exercise 5.14: for `m ≥ 7` and `N = 2ᵐ`, the product of `m` disjoint
copies of `IP₂ₘ` is computed by a depth-three AC⁰ circuit of size at most
`N³` and bottom fan-in `2m`. -/
theorem hasDepthCircuit_ac0ThresholdParityTarget
    (m : ℕ) (hm : 7 ≤ m) :
    DepthCircuit.HasDepthCircuit
      (ac0ThresholdParityTarget m hm) 3 ((2 ^ m) ^ 3) (2 * m) := by
  refine ⟨ac0ThresholdParityCircuit m hm,
    depth_ac0ThresholdParityCircuit m hm, ?_, ?_, ?_⟩
  · exact
      (size_ac0ThresholdParityCircuit m hm).trans
        (ac0ThresholdParityCircuit_size_le_cube m)
  · exact (width_ac0ThresholdParityCircuit m hm).le
  · funext x
    exact eval_ac0ThresholdParityCircuit m hm x

private def reindexSignCube
    {ι κ : Type*} (e : κ ≃ ι) :
    (κ → Sign) ≃ (ι → Sign) where
  toFun x i := x (e.symm i)
  invFun y j := y (e j)
  left_inv x := by
    funext j
    simp
  right_inv y := by
    funext i
    simp

private theorem fourierCoeff_reindexSignCube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (e : Fin k ≃ ι)
    (f : (ι → Sign) → ℝ) (S : Finset (Fin k)) :
    fourierCoeff (fun x ↦ f (reindexSignCube e x)) S =
      indexedFourierCoeff f (S.map e.toEmbedding) := by
  classical
  unfold fourierCoeff indexedFourierCoeff
  apply Fintype.expect_equiv (reindexSignCube e)
  intro x
  congr 1
  rw [indexedMonomial, Finset.prod_map]
  simp [monomial, reindexSignCube]

private def reindexedRestriction
    {n k : ℕ} (p : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J)
    (e : Fin k ≃ J) :
    {−1,1}^[k] → ℝ :=
  fun x ↦ signRestriction p J z (reindexSignCube e x)

private theorem fourierCoeff_reindexedRestriction
    {n k : ℕ} (p : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J)
    (e : Fin k ≃ J) (S : Finset (Fin k)) :
    fourierCoeff (reindexedRestriction p J z e) S =
      restrictionFourierCoeff p J (S.map e.toEmbedding) z := by
  exact fourierCoeff_reindexSignCube e (signRestriction p J z) S

private theorem exists_ambientFrequency_of_reindexedRestriction_memSupport
    {n k : ℕ} (p : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J)
    (e : Fin k ≃ J) (S : Finset (Fin k))
    (hS : S ∈ fourierSupport (reindexedRestriction p J z e)) :
    ∃ T : Finset (FixedIndex J),
      fourierCoeff p
        (liftFreeFrequency (S.map e.toEmbedding) ∪
          liftFixedFrequency T) ≠ 0 := by
  have hcoeff :=
    (mem_fourierSupport (reindexedRestriction p J z e) S).1 hS
  rw [fourierCoeff_reindexedRestriction,
    restrictionFourierCoeff_eq_sum] at hcoeff
  obtain ⟨T, -, hT⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  refine ⟨T, ?_⟩
  intro hzero
  exact hT (by rw [hzero, zero_mul])

private theorem freeFrequencyPart_lift_union
    {n : ℕ} (J : Finset (Fin n)) (S : Finset J)
    (T : Finset (FixedIndex J)) :
    freeFrequencyPart J
        (liftFreeFrequency S ∪ liftFixedFrequency T) = S := by
  classical
  ext i
  simp [freeFrequencyPart, liftFreeFrequency,
    liftFixedFrequency]

private theorem polynomialSparsity_reindexedRestriction_le
    {n k : ℕ} (p : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J)
    (e : Fin k ≃ J) :
    polynomialSparsity (reindexedRestriction p J z e) ≤
      polynomialSparsity p := by
  classical
  let restrictedSupport :=
    fourierSupport (reindexedRestriction p J z e)
  let witness :
      restrictedSupport → Finset (FixedIndex J) :=
    fun S ↦ Classical.choose
      (exists_ambientFrequency_of_reindexedRestriction_memSupport
        p J z e S.1 S.2)
  have hwitness (S : restrictedSupport) :
      fourierCoeff p
        (liftFreeFrequency (S.1.map e.toEmbedding) ∪
          liftFixedFrequency (witness S)) ≠ 0 :=
    Classical.choose_spec
      (exists_ambientFrequency_of_reindexedRestriction_memSupport
        p J z e S.1 S.2)
  let supportMap :
      restrictedSupport → fourierSupport p :=
    fun S ↦
      ⟨liftFreeFrequency (S.1.map e.toEmbedding) ∪
          liftFixedFrequency (witness S),
        (mem_fourierSupport p _).2 (hwitness S)⟩
  have hinjective : Function.Injective supportMap := by
    intro S T hST
    apply Subtype.ext
    apply Finset.map_injective e.toEmbedding
    have hfree :=
      congrArg (freeFrequencyPart J)
        (congrArg Subtype.val hST)
    simpa [supportMap, freeFrequencyPart_lift_union] using hfree
  unfold polynomialSparsity
  exact Finset.card_le_card_of_injective hinjective

private def ac0ActiveCoordinates
    (m : ℕ) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter fun i ↦
    i.1 < m * m + m * m

private def ac0ActiveCoordinateEquiv
    (m : ℕ) (hm : 7 ≤ m) :
    Fin (m * m + m * m) ≃ ac0ActiveCoordinates m where
  toFun i :=
    ⟨⟨i.1, i.2.trans_le
      (activeCoordinateCount_le_dimension m hm)⟩, by
      simp [ac0ActiveCoordinates, i.2]⟩
  invFun i :=
    ⟨i.1.1, by
      have hi := i.2
      change i.1 ∈
        Finset.univ.filter
          (fun j : Fin (2 ^ m) ↦
            j.1 < m * m + m * m) at hi
      exact (Finset.mem_filter.mp hi).2⟩
  left_inv i := by
    apply Fin.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    rfl

private def ac0InactiveAssignment
    (m : ℕ) :
    FixedSignCube (ac0ActiveCoordinates m) :=
  fun _ ↦ 1

private theorem combine_ac0ActiveCoordinates
    (m : ℕ) (hm : 7 ≤ m)
    (y : {−1,1}^[m * m + m * m])
    (i : Fin (m * m + m * m)) :
    combineSignCube (ac0ActiveCoordinates m)
        (reindexSignCube (ac0ActiveCoordinateEquiv m hm) y)
        (ac0InactiveAssignment m)
        ⟨i.1, i.2.trans_le
          (activeCoordinateCount_le_dimension m hm)⟩ =
      y i := by
  let j : ac0ActiveCoordinates m :=
    ⟨⟨i.1, i.2.trans_le
      (activeCoordinateCount_le_dimension m hm)⟩, by
      simp [ac0ActiveCoordinates, i.2]⟩
  rw [show
      (⟨i.1, i.2.trans_le
        (activeCoordinateCount_le_dimension m hm)⟩ :
          Fin (2 ^ m)) = j.1 by rfl,
    combineSignCube_apply_free
      (ac0ActiveCoordinates m)
      (reindexSignCube (ac0ActiveCoordinateEquiv m hm) y)
      (ac0InactiveAssignment m) j]
  change y ((ac0ActiveCoordinateEquiv m hm).symm j) = y i
  congr 1

private theorem signEncode_sum
    {ι : Type*}
    (s : Finset ι) (a : ι → 𝔽₂) :
    signEncode (∑ i ∈ s, a i) =
      ∏ i ∈ s, signEncode (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [hi, signEncode_add, ih]

private theorem prod_innerProductModTwoBoolean_blocks
    (m : ℕ) (a c : 𝔽₂^[m * m]) :
    (∏ b : Fin m,
      innerProductModTwoBoolean m
        (binaryCubeSignEquiv (m + m)
          (joinF₂CubeBlocks
            (fun j ↦ a (finProdFinEquiv (b, j)))
            (fun j ↦ c (finProdFinEquiv (b, j)))))) =
      innerProductModTwoBoolean (m * m)
        (binaryCubeSignEquiv (m * m + m * m)
          (joinF₂CubeBlocks a c)) := by
  simp_rw [
    innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks]
  rw [← signEncode_sum
    (s := (Finset.univ : Finset (Fin m)))]
  congr 1
  unfold f₂DotProduct dotProduct
  calc
    (∑ b : Fin m, ∑ j : Fin m,
        a (finProdFinEquiv (b, j)) *
          c (finProdFinEquiv (b, j))) =
        ∑ bj : Fin m × Fin m,
          a (finProdFinEquiv bj) *
            c (finProdFinEquiv bj) := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ k : Fin (m * m), a k * c k :=
      Equiv.sum_comp finProdFinEquiv
        (fun k ↦ a k * c k)

private theorem ac0ThresholdParityTarget_activeRestriction
    (m : ℕ) (hm : 7 ≤ m)
    (y : {−1,1}^[m * m + m * m]) :
    ac0ThresholdParityTarget m hm
        (combineSignCube (ac0ActiveCoordinates m)
          (reindexSignCube (ac0ActiveCoordinateEquiv m hm) y)
          (ac0InactiveAssignment m)) =
      innerProductModTwoBoolean (m * m) y := by
  obtain ⟨z, rfl⟩ :=
    (binaryCubeSignEquiv (m * m + m * m)).surjective y
  let a : 𝔽₂^[m * m] :=
    (f₂CubeBlockEquiv (m * m) z).1
  let c : 𝔽₂^[m * m] :=
    (f₂CubeBlockEquiv (m * m) z).2
  have hz :
      joinF₂CubeBlocks a c = z := by
    exact (f₂CubeBlockEquiv (m * m)).symm_apply_apply z
  rw [← hz]
  have hblock (b : Fin m) :
      (fun j : Fin (m + m) ↦
        combineSignCube (ac0ActiveCoordinates m)
          (reindexSignCube (ac0ActiveCoordinateEquiv m hm)
            (binaryCubeSignEquiv (m * m + m * m)
              (joinF₂CubeBlocks a c)))
          (ac0InactiveAssignment m)
          ⟨blockCoordinateValue m b j,
            (blockCoordinateValue_lt_active m b j).trans_le
              (activeCoordinateCount_le_dimension m hm)⟩) =
        binaryCubeSignEquiv (m + m)
          (joinF₂CubeBlocks
            (fun j ↦ a (finProdFinEquiv (b, j)))
            (fun j ↦ c (finProdFinEquiv (b, j)))) := by
    funext j
    refine Fin.addCases (m := m) (n := m) ?_ ?_ j
    · intro i
      rw [combine_ac0ActiveCoordinates m hm
        (binaryCubeSignEquiv (m * m + m * m)
          (joinF₂CubeBlocks a c))
        ⟨blockCoordinateValue m b (Fin.castAdd m i),
          blockCoordinateValue_lt_active m b (Fin.castAdd m i)⟩]
      rw [show
          (⟨blockCoordinateValue m b (Fin.castAdd m i),
            blockCoordinateValue_lt_active m b (Fin.castAdd m i)⟩ :
              Fin (m * m + m * m)) =
            Fin.castAdd (m * m) (finProdFinEquiv (b, i)) by
        apply Fin.ext
        simp [blockCoordinateValue, finProdFinEquiv_apply_val,
          Nat.mul_comm]
        omega]
      simp
    · intro i
      rw [combine_ac0ActiveCoordinates m hm
        (binaryCubeSignEquiv (m * m + m * m)
          (joinF₂CubeBlocks a c))
        ⟨blockCoordinateValue m b (Fin.natAdd m i),
          blockCoordinateValue_lt_active m b (Fin.natAdd m i)⟩]
      rw [show
          (⟨blockCoordinateValue m b (Fin.natAdd m i),
            blockCoordinateValue_lt_active m b (Fin.natAdd m i)⟩ :
              Fin (m * m + m * m)) =
            Fin.natAdd (m * m) (finProdFinEquiv (b, i)) by
        apply Fin.ext
        simp [blockCoordinateValue, finProdFinEquiv_apply_val,
          Nat.mul_comm]
        omega]
      simp
  rw [ac0ThresholdParityTarget]
  calc
    (∏ b : Fin m,
      innerProductModTwoBoolean m
        (fun j ↦
          combineSignCube (ac0ActiveCoordinates m)
            (reindexSignCube (ac0ActiveCoordinateEquiv m hm)
              (binaryCubeSignEquiv (m * m + m * m)
                (joinF₂CubeBlocks a c)))
            (ac0InactiveAssignment m)
            ⟨blockCoordinateValue m b j,
              (blockCoordinateValue_lt_active m b j).trans_le
                (activeCoordinateCount_le_dimension m hm)⟩)) =
        ∏ b : Fin m,
          innerProductModTwoBoolean m
            (binaryCubeSignEquiv (m + m)
              (joinF₂CubeBlocks
                (fun j ↦ a (finProdFinEquiv (b, j)))
                (fun j ↦ c (finProdFinEquiv (b, j))))) := by
      apply Finset.prod_congr rfl
      intro b _
      rw [hblock b]
    _ = innerProductModTwoBoolean (m * m)
        (binaryCubeSignEquiv (m * m + m * m)
          (joinF₂CubeBlocks a c)) :=
      prod_innerProductModTwoBoolean_blocks m a c

/-- Exercise 5.14: every polynomial threshold representation of the explicit
AC⁰ function has at least `2^(m²)` nonzero Fourier monomials. -/
theorem pow_two_sq_le_polynomialSparsity_ac0ThresholdParityTarget
    (m : ℕ) (hm : 7 ≤ m)
    (p : {−1,1}^[2 ^ m] → ℝ)
    (hrep :
      IsPolynomialThresholdRepresentation
        (ac0ThresholdParityTarget m hm) p) :
    2 ^ (m ^ 2) ≤ polynomialSparsity p := by
  let q : {−1,1}^[m * m + m * m] → ℝ :=
    reindexedRestriction p
      (ac0ActiveCoordinates m)
      (ac0InactiveAssignment m)
      (ac0ActiveCoordinateEquiv m hm)
  have hrepRestricted :
      IsPolynomialThresholdRepresentation
        (innerProductModTwoBoolean (m * m)) q := by
    intro y
    rw [← ac0ThresholdParityTarget_activeRestriction m hm y]
    simpa [q, reindexedRestriction, signRestriction] using
      hrep
        (combineSignCube (ac0ActiveCoordinates m)
          (reindexSignCube (ac0ActiveCoordinateEquiv m hm) y)
          (ac0InactiveAssignment m))
  have hmSquarePos : 0 < m * m := by
    have hmPos : 0 < m := by omega
    positivity
  have hlower :
      2 ^ (m * m) ≤ polynomialSparsity q :=
    pow_two_le_polynomialSparsity_innerProductModTwo_of_pos
      hmSquarePos q hrepRestricted
  have hrestriction :
      polynomialSparsity q ≤ polynomialSparsity p :=
    polynomialSparsity_reindexedRestriction_le p
      (ac0ActiveCoordinates m)
      (ac0InactiveAssignment m)
      (ac0ActiveCoordinateEquiv m hm)
  simpa [pow_two] using hlower.trans hrestriction

/-- Exercise 5.14 in threshold-of-parities language. With `N = 2ᵐ`, every
such circuit for the explicit depth-three AC⁰ function has size at least
`N^(log₂ N)`. -/
theorem pow_two_pow_log_le_thresholdOfParitiesSize_ac0ThresholdParityTarget
    (m : ℕ) (hm : 7 ≤ m) (s : ℕ)
    (h :
      IsThresholdOfParities
        (ac0ThresholdParityTarget m hm) s) :
    (2 ^ m) ^ Nat.log 2 (2 ^ m) ≤ s := by
  rcases h with ⟨p, hrep, hs⟩
  calc
    (2 ^ m) ^ Nat.log 2 (2 ^ m) =
        2 ^ (m ^ 2) := by
      rw [Nat.log_pow (by decide : 1 < 2), ← pow_mul, pow_two]
    _ ≤ polynomialSparsity p :=
      pow_two_sq_le_polynomialSparsity_ac0ThresholdParityTarget
        m hm p hrep
    _ ≤ s := hs

end FABL
