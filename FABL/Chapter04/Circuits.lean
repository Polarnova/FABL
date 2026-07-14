/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5
-/
module

public import FABL.Chapter04.DNFFormulas

/-!
# Depth-d circuits (Definitions 4.26–4.27)

Book items: Definition 4.26, Definition 4.27.

A layered alternating AND/OR circuit model matching O'Donnell §4.5. Depth-2 circuits
recover DNFs and CNFs.
-/

open scoped BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Definition 4.26 -/

/-- Gate label at an internal layer: AND or OR. -/
inductive CircuitGate
  | and
  | or
  deriving DecidableEq, Repr

/-- Evaluate a gate on a list of sign-valued inputs (`-1` = True). -/
def CircuitGate.eval : CircuitGate → List Sign → Sign
  | .and, xs => if xs.all (· = (-1 : Sign)) then -1 else 1
  | .or, xs => if xs.any (· = (-1 : Sign)) then -1 else 1

/-- O'Donnell, Definition 4.26: a depth-`d` circuit (`d ≥ 2`) is represented by its layer-1
gates (width-bounded DNF/CNF terms) together with alternating AND/OR layers above them.

Production uses an explicit layered model: layer 1 is a list of terms (each a list of
literals with nodup indices), and layers `2..d` are lists of gates taking wire indices
into the previous layer. The final layer has exactly one gate (the output).
-/
structure DepthCircuit (n : ℕ) where
  /-- Depth `d ≥ 2`. -/
  depth : ℕ
  depth_ge : 2 ≤ depth
  /-- Layer-1 gates as DNF terms (AND or OR of literals, depending on the bottom polarity). -/
  layer1 : List (DNFTerm n)
  /-- Polarity of layer 1: `true` means AND-of-literals (as in a CNF's clauses dualized, or
  DNF terms); book DNFs are OR of AND-terms, so layer 1 is AND-terms and layer 2 is a single OR. -/
  layer1IsAnd : Bool
  /-- Higher layers `2..depth`: each layer is a list of gates with fan-in wire indices into the
  previous layer. The last layer must have length 1. -/
  higherLayers : List (List (CircuitGate × List ℕ))
  /-- There are exactly `depth - 1` higher-layer slots (layers 2 through depth). -/
  higherLayers_length : higherLayers.length = depth - 1
  /-- Output layer is a singleton. -/
  output_singleton : ∀ h : higherLayers ≠ [],
      (higherLayers.getLast h).length = 1

namespace DepthCircuit

/-- Size: number of nodes in layers `1` through `depth-1` (book Definition 4.27). -/
def size (C : DepthCircuit n) : ℕ :=
  C.layer1.length +
    (C.higherLayers.dropLast.map List.length).sum

/-- Width: maximum fan-in of any layer-1 gate (book Definition 4.27). -/
def width (C : DepthCircuit n) : ℕ :=
  (DNFFormula.mk C.layer1).width

/-- Evaluate layer 1 on an input. -/
def evalLayer1 (C : DepthCircuit n) (x : {−1,1}^[n]) : List Sign :=
  C.layer1.map fun T ↦
    if C.layer1IsAnd then T.eval x
    else CNFFormula.clauseEval T x

/-- Evaluate a higher layer given previous layer values. -/
def evalHigherLayer (prev : List Sign) (gates : List (CircuitGate × List ℕ)) : List Sign :=
  gates.map fun ⟨g, wires⟩ ↦
    g.eval (wires.filterMap fun i ↦ prev[i]?)

/-- O'Donnell, Definition 4.26: the Boolean function computed by the circuit. -/
noncomputable def eval (C : DepthCircuit n) (x : {−1,1}^[n]) : Sign :=
  Id.run do
    let mut vals := C.evalLayer1 x
    for layer in C.higherLayers do
      vals := evalHigherLayer vals layer
    return vals.headD 1

noncomputable def toBooleanFunction (C : DepthCircuit n) : BooleanFunction n := C.eval

/-- Every DNF is a depth-2 circuit (OR of AND-terms). -/
def ofDNF (φ : DNFFormula n) : DepthCircuit n where
  depth := 2
  depth_ge := by decide
  layer1 := φ.terms
  layer1IsAnd := true
  higherLayers := [[(.or, List.range φ.terms.length)]]
  higherLayers_length := rfl
  output_singleton := by
    intro h
    simp [List.getLast]

theorem size_ofDNF (φ : DNFFormula n) : (ofDNF φ).size = φ.size := by
  simp [ofDNF, size, DNFFormula.size]

theorem width_ofDNF (φ : DNFFormula n) : (ofDNF φ).width = φ.width := by
  simp [ofDNF, width]

/-- Every CNF is a depth-2 circuit (AND of OR-clauses). -/
def ofCNF (ψ : CNFFormula n) : DepthCircuit n where
  depth := 2
  depth_ge := by decide
  layer1 := ψ.clauses
  layer1IsAnd := false
  higherLayers := [[(.and, List.range ψ.clauses.length)]]
  higherLayers_length := rfl
  output_singleton := by
    intro h
    simp [List.getLast]

theorem size_ofCNF (ψ : CNFFormula n) : (ofCNF ψ).size = ψ.size := by
  simp [ofCNF, size, CNFFormula.size]

theorem width_ofCNF (ψ : CNFFormula n) : (ofCNF ψ).width = ψ.width := by
  simp [ofCNF, width, CNFFormula.width]

/-- Predicate: computable by a depth-`d` circuit of size ≤ `s` and width ≤ `w`. -/
def HasDepthCircuit (f : BooleanFunction n) (d s w : ℕ) : Prop :=
  ∃ C : DepthCircuit n, C.depth = d ∧ C.size ≤ s ∧ C.width ≤ w ∧ C.toBooleanFunction = f

end DepthCircuit

end FABL
