/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.LearningAndTesting.JuntaLearningReduction
import Mathlib.Tactic.DeriveEncodable

/-!
# Finite decision-tree hypotheses

This file supplies the finite, executable hypothesis representation used by the exact
random-example junta learner.  The raw tree forgets the dependent available-coordinate index of
`F₂DecisionTree`; the erasure theorem preserves evaluation.
-/

open Finset
open scoped BooleanCube

set_option autoImplicit false

namespace FABL

/-- Constructive identification of the sign alphabet with bits. -/
def signBoolEquiv : Sign ≃ Bool where
  toFun value := value ≠ 1
  invFun bit := if bit then -1 else 1
  left_inv value := by
    rcases Int.units_eq_one_or value with h | h
    · simp [h]
    · simp [h]
  right_inv bit := by
    cases bit <;> simp

/-- Constructive encodability of the sign alphabet. -/
instance signEncodable : Encodable Sign :=
  Encodable.ofEquiv Bool signBoolEquiv

/-- A finitely encodable binary decision tree with sign-valued leaves. -/
inductive DecisionTreeHypothesis (n : ℕ) where
  | leaf (value : Sign)
  | query (coordinate : Fin n)
      (zeroChild oneChild : DecisionTreeHypothesis n)
  deriving DecidableEq, Encodable

namespace DecisionTreeHypothesis

/-- Evaluate a raw decision tree on the additive Boolean cube. -/
def eval {n : ℕ} : DecisionTreeHypothesis n → F₂Cube n → Sign
  | .leaf value, _ => value
  | .query coordinate zeroChild oneChild, x =>
      if x coordinate = 0 then zeroChild.eval x else oneChild.eval x

/-- Forget the dependent available-coordinate index of a verified decision tree. -/
def ofF₂DecisionTree {n : ℕ} {available : Finset (Fin n)} :
    F₂DecisionTree n Sign available → DecisionTreeHypothesis n
  | .leaf value => .leaf value
  | .query coordinate _ zeroChild oneChild =>
      .query coordinate (ofF₂DecisionTree zeroChild) (ofF₂DecisionTree oneChild)

/-- Erasing the dependent index preserves decision-tree evaluation. -/
@[simp] theorem eval_ofF₂DecisionTree {n : ℕ} {available : Finset (Fin n)}
    (tree : F₂DecisionTree n Sign available) (x : F₂Cube n) :
    (ofF₂DecisionTree tree).eval x = tree.eval x := by
  induction tree with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [ofF₂DecisionTree, eval, F₂DecisionTree.eval]
      split <;> assumption

/-- Boolean-function semantics of a raw decision-tree hypothesis. -/
def evaluate {n : ℕ} (tree : DecisionTreeHypothesis n) : BooleanFunction n :=
  fun x ↦ tree.eval ((binaryCubeSignEquiv n).symm x)

/-- A verified complete decision tree and its raw hypothesis have identical semantics. -/
@[simp] theorem evaluate_ofF₂DecisionTree {n : ℕ} (tree : DecisionTree n Sign) :
    evaluate (ofF₂DecisionTree tree) =
      fun x ↦ tree.eval ((binaryCubeSignEquiv n).symm x) := by
  funext x
  exact eval_ofF₂DecisionTree tree ((binaryCubeSignEquiv n).symm x)

/-- Structural work charged for evaluating a raw decision tree. -/
def evaluationWork {n : ℕ} : DecisionTreeHypothesis n → ℕ
  | .leaf _ => 1
  | .query _ zeroChild oneChild =>
      1 + max zeroChild.evaluationWork oneChild.evaluationWork

/-- Canonical finite binary encoding of a raw decision tree. -/
def encode {n : ℕ} (tree : DecisionTreeHypothesis n) : List Bool :=
  (Encodable.encode tree).bits

/-- Decoder for the canonical raw decision-tree encoding. -/
def decode {n : ℕ} (bits : List Bool) : Option (DecisionTreeHypothesis n) :=
  Encodable.decode (SparseFourierHypothesis.natOfBits bits)

/-- Encoding followed by decoding recovers the raw decision tree. -/
@[simp] theorem decode_encode {n : ℕ} (tree : DecisionTreeHypothesis n) :
    decode (encode tree) = some tree := by
  simp [decode, encode]

/-- Raw decision trees form an honest finite hypothesis language. -/
abbrev finiteRepresentation (n : ℕ) : FiniteHypothesisRepresentation n where
  Code := DecisionTreeHypothesis n
  encode := encode
  decode := decode
  decode_encode := decode_encode
  evaluate := evaluate
  evaluationWork := fun tree _ ↦ tree.evaluationWork

end DecisionTreeHypothesis

end FABL
