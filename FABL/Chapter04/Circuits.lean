/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5 and Codex
-/
module

public import FABL.Chapter04.DNFFormulas

/-!
# Depth-d circuits (Definitions 4.26–4.27)

Book items: Definition 4.26, Definition 4.27.

The circuit tail is intrinsically well-formed: every wire has an in-range source, the output
layer is a singleton, and gate labels alternate by construction. Layer zero is represented
implicitly by the `2n` positive and negative literals available to each layer-one gate.
-/

open scoped BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Definition 4.26 -/

/-- Gate label at an internal layer: AND or OR. -/
inductive CircuitGate
  /-- Logical $\mathsf{AND}$ gate. -/
  | and
  /-- Logical $\mathsf{OR}$ gate. -/
  | or
  deriving DecidableEq, Repr

namespace CircuitGate

/-- The other gate label. Adjacent non-input layers have dual labels. -/
def dual : CircuitGate → CircuitGate
  | .and => .or
  | .or => .and

@[simp] theorem dual_and : CircuitGate.and.dual = .or := rfl

@[simp] theorem dual_or : CircuitGate.or.dual = .and := rfl

@[simp] theorem dual_dual (gate : CircuitGate) : gate.dual.dual = gate := by
  cases gate <;> rfl

/-- Evaluate a layer-one gate whose inputs are literals. -/
def evalTerm (gate : CircuitGate) (term : DNFTerm n) (x : {−1,1}^[n]) : Sign :=
  match gate with
  | .and => term.eval x
  | .or => CNFFormula.clauseEval term x

/-- Evaluate a gate whose incoming wires form a finite set of nodes in the previous layer. -/
def evalFinset {m : ℕ} (gate : CircuitGate) (values : Fin m → Sign)
    (inputs : Finset (Fin m)) : Sign :=
  match gate with
  | .and => if ∀ i ∈ inputs, values i = -1 then -1 else 1
  | .or => if ∃ i ∈ inputs, values i = -1 then -1 else 1

@[simp] theorem evalFinset_and_eq_neg_one_iff {m : ℕ} (values : Fin m → Sign)
    (inputs : Finset (Fin m)) :
    CircuitGate.and.evalFinset values inputs = -1 ↔
      ∀ i ∈ inputs, values i = -1 := by
  simp [evalFinset]

@[simp] theorem evalFinset_or_eq_neg_one_iff {m : ℕ} (values : Fin m → Sign)
    (inputs : Finset (Fin m)) :
    CircuitGate.or.evalFinset values inputs = -1 ↔
      ∃ i ∈ inputs, values i = -1 := by
  simp [evalFinset]

end CircuitGate

/-- The non-input layers above layer one of a circuit.

`CircuitTail m` consumes a layer containing exactly `m` nodes. An `output` tail adds the
singleton output layer. A `layer` tail adds an ordinary layer and then continues. The `Fin m`
wire endpoints make out-of-range wires unrepresentable; `Finset` makes parallel duplicate wires
unrepresentable. Gate labels are not stored per node, because Definition 4.26 requires a uniform
label on each layer and alternation between adjacent layers.
-/
inductive CircuitTail : ℕ → Type
  /-- The singleton output layer, represented by its incoming wires. -/
  | output {m : ℕ} (inputs : Finset (Fin m)) : CircuitTail m
  /-- One non-output layer followed by the remaining layers. -/
  | layer {m : ℕ} (gates : List (Finset (Fin m)))
      (rest : CircuitTail gates.length) : CircuitTail m

namespace CircuitTail

/-- Number of layers represented by the tail, including its output layer. -/
def layerCount {m : ℕ} : CircuitTail m → ℕ
  | .output _ => 1
  | .layer _ rest => 1 + rest.layerCount

theorem one_le_layerCount {m : ℕ} (tail : CircuitTail m) : 1 ≤ tail.layerCount := by
  cases tail <;> simp [layerCount]

theorem eq_output_of_layerCount_eq_one {m : ℕ} (tail : CircuitTail m)
    (hcount : tail.layerCount = 1) :
    ∃ inputs : Finset (Fin m), tail = .output inputs := by
  cases tail with
  | output inputs => exact ⟨inputs, rfl⟩
  | layer gates rest =>
      simp only [layerCount] at hcount
      have := rest.one_le_layerCount
      omega

/-- Number of non-output nodes represented by the tail. -/
def internalNodeCount {m : ℕ} : CircuitTail m → ℕ
  | .output _ => 0
  | .layer gates rest => gates.length + rest.internalNodeCount

/-- Evaluate all layers in a tail. The supplied label is the label of the first tail layer. -/
def eval {m : ℕ} : CircuitTail m → CircuitGate → (Fin m → Sign) → Sign
  | .output inputs, gate, values => gate.evalFinset values inputs
  | .layer gates rest, gate, values =>
      rest.eval gate.dual fun i => gate.evalFinset values (gates.get i)

end CircuitTail

/-- O'Donnell, Definition 4.26: a layered alternating depth-`d` circuit.

Layer zero is the canonical collection of the `2n` literals. Layer one is a list of gates over
those literals; `DNFTerm.nodupIndices` enforces the book's convention that a layer-one gate does
not use both a variable and its negation and does not repeat a variable. Higher-layer wires are
typed by their source layer, and `CircuitTail` ends in exactly one output gate.
-/
structure DepthCircuit (n : ℕ) where
  /-- Uniform label of the layer-one gates. -/
  layer1Gate : CircuitGate
  /-- Layer-one gates, represented by their literal inputs. -/
  layer1 : List (DNFTerm n)
  /-- Layers two through the singleton output layer. -/
  tail : CircuitTail layer1.length

namespace DepthCircuit

/-- Circuit depth, i.e. the number of non-input layers. -/
def depth (C : DepthCircuit n) : ℕ := 1 + C.tail.layerCount

theorem depth_ge_two (C : DepthCircuit n) : 2 ≤ C.depth := by
  simpa [depth] using Nat.add_le_add_left C.tail.one_le_layerCount 1

/-- Size: number of nodes in layers `1` through `depth - 1` (book Definition 4.27). -/
def size (C : DepthCircuit n) : ℕ :=
  C.layer1.length + C.tail.internalNodeCount

/-- Width: maximum fan-in of any layer-one gate (book Definition 4.27). -/
def width (C : DepthCircuit n) : ℕ :=
  (DNFFormula.mk C.layer1).width

/-- Evaluate layer one on an input. -/
def evalLayer1 (C : DepthCircuit n) (x : {−1,1}^[n]) : Fin C.layer1.length → Sign :=
  fun i => C.layer1Gate.evalTerm (C.layer1.get i) x

/-- The layer-one gates selected by the incoming wires of a layer-two gate. -/
noncomputable def selectedLayer1Terms (C : DepthCircuit n) (inputs : Finset (Fin C.layer1.length)) :
    List (DNFTerm n) :=
  inputs.toList.map C.layer1.get

/-- DNF syntax for a layer-two OR gate over layer-one AND gates. -/
noncomputable def selectedLayer1DNF (C : DepthCircuit n) (inputs : Finset (Fin C.layer1.length)) :
    DNFFormula n :=
  ⟨C.selectedLayer1Terms inputs⟩

/-- CNF syntax for a layer-two AND gate over layer-one OR gates. -/
noncomputable def selectedLayer1CNF (C : DepthCircuit n) (inputs : Finset (Fin C.layer1.length)) :
    CNFFormula n :=
  ⟨C.selectedLayer1Terms inputs⟩

theorem width_selectedLayer1DNF_le (C : DepthCircuit n)
    (inputs : Finset (Fin C.layer1.length)) :
    (C.selectedLayer1DNF inputs).width ≤ C.width := by
  rw [DNFFormula.width_le_iff]
  intro term hterm
  simp only [selectedLayer1DNF, selectedLayer1Terms, List.mem_map,
    Finset.mem_toList] at hterm
  obtain ⟨i, _, rfl⟩ := hterm
  exact DNFFormula.width_le_of_mem (DNFFormula.mk C.layer1) (List.get_mem C.layer1 i)

theorem width_selectedLayer1CNF_le (C : DepthCircuit n)
    (inputs : Finset (Fin C.layer1.length)) :
    (C.selectedLayer1CNF inputs).width ≤ C.width := by
  exact C.width_selectedLayer1DNF_le inputs

/-- Function computed by one gate at layer two. -/
def layer2GateFunction (C : DepthCircuit n)
    (inputs : Finset (Fin C.layer1.length)) : BooleanFunction n :=
  fun x => C.layer1Gate.dual.evalFinset (C.evalLayer1 x) inputs

theorem selectedLayer1DNF_toBooleanFunction (C : DepthCircuit n)
    (hgate : C.layer1Gate = .and) (inputs : Finset (Fin C.layer1.length)) :
    (C.selectedLayer1DNF inputs).toBooleanFunction = C.layer2GateFunction inputs := by
  funext x
  change (C.selectedLayer1DNF inputs).eval x = C.layer2GateFunction inputs x
  have hneg : (C.selectedLayer1DNF inputs).eval x = -1 ↔
      C.layer2GateFunction inputs x = -1 := by
    rw [DNFFormula.eval_eq_neg_one_iff]
    simp [selectedLayer1DNF, selectedLayer1Terms, layer2GateFunction, evalLayer1,
      CircuitGate.evalTerm, hgate]
  rcases Int.units_eq_one_or ((C.selectedLayer1DNF inputs).eval x) with hformula | hformula <;>
    rcases Int.units_eq_one_or (C.layer2GateFunction inputs x) with hgate | hgate <;>
    simp_all

theorem selectedLayer1CNF_toBooleanFunction (C : DepthCircuit n)
    (hgate : C.layer1Gate = .or) (inputs : Finset (Fin C.layer1.length)) :
    (C.selectedLayer1CNF inputs).toBooleanFunction = C.layer2GateFunction inputs := by
  funext x
  change (C.selectedLayer1CNF inputs).eval x = C.layer2GateFunction inputs x
  have hneg : (C.selectedLayer1CNF inputs).eval x = -1 ↔
      C.layer2GateFunction inputs x = -1 := by
    rw [show (C.selectedLayer1CNF inputs).eval x = -1 ↔
        ∀ clause ∈ (C.selectedLayer1CNF inputs).clauses,
          CNFFormula.clauseEval clause x = -1 by
      simp [CNFFormula.eval, List.all_eq_true]]
    simp [selectedLayer1CNF, selectedLayer1Terms, layer2GateFunction, evalLayer1,
      CircuitGate.evalTerm, hgate]
  rcases Int.units_eq_one_or ((C.selectedLayer1CNF inputs).eval x) with hformula | hformula <;>
    rcases Int.units_eq_one_or (C.layer2GateFunction inputs x) with hgate | hgate <;>
    simp_all

/-- Every layer-two gate has the DNF/CNF width premise required by Håstad's Switching Lemma. -/
theorem layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE (C : DepthCircuit n)
    (inputs : Finset (Fin C.layer1.length)) :
    HasDNFWidthLE (C.layer2GateFunction inputs) C.width ∨
      HasCNFWidthLE (C.layer2GateFunction inputs) C.width := by
  cases hgate : C.layer1Gate with
  | and =>
      exact Or.inl ⟨C.selectedLayer1DNF inputs, C.width_selectedLayer1DNF_le inputs,
        C.selectedLayer1DNF_toBooleanFunction hgate inputs⟩
  | or =>
      exact Or.inr ⟨C.selectedLayer1CNF inputs, C.width_selectedLayer1CNF_le inputs,
        C.selectedLayer1CNF_toBooleanFunction hgate inputs⟩

/-- O'Donnell, Definition 4.26: the Boolean function computed by the output gate. -/
def eval (C : DepthCircuit n) (x : {−1,1}^[n]) : Sign :=
  C.tail.eval C.layer1Gate.dual (C.evalLayer1 x)

def toBooleanFunction (C : DepthCircuit n) : BooleanFunction n := C.eval

/-- The depth-two case of the structural premise for Håstad's Switching Lemma. -/
theorem toBooleanFunction_hasDNFWidthLE_or_hasCNFWidthLE_of_depth_eq_two
    (C : DepthCircuit n) (hdepth : C.depth = 2) :
    HasDNFWidthLE C.toBooleanFunction C.width ∨
      HasCNFWidthLE C.toBooleanFunction C.width := by
  have hcount : C.tail.layerCount = 1 := by
    simp only [depth] at hdepth
    omega
  obtain ⟨inputs, htail⟩ := C.tail.eq_output_of_layerCount_eq_one hcount
  have heval : C.toBooleanFunction = C.layer2GateFunction inputs := by
    funext x
    simp [toBooleanFunction, eval, htail, layer2GateFunction, CircuitTail.eval]
  rw [heval]
  exact C.layer2GateFunction_hasDNFWidthLE_or_hasCNFWidthLE inputs

/-- Every DNF is a depth-two circuit (OR of AND terms). -/
def ofDNF (formula : DNFFormula n) : DepthCircuit n where
  layer1Gate := .and
  layer1 := formula.terms
  tail := .output Finset.univ

@[simp] theorem depth_ofDNF (formula : DNFFormula n) : (ofDNF formula).depth = 2 := rfl

theorem size_ofDNF (formula : DNFFormula n) : (ofDNF formula).size = formula.size := by
  simp [ofDNF, size, DNFFormula.size, CircuitTail.internalNodeCount]

theorem width_ofDNF (formula : DNFFormula n) : (ofDNF formula).width = formula.width := by
  simp [ofDNF, width]

/-- The depth-two embedding computes the original DNF. -/
theorem eval_ofDNF (formula : DNFFormula n) (x : {−1,1}^[n]) :
    (ofDNF formula).eval x = formula.eval x := by
  have hneg : (ofDNF formula).eval x = -1 ↔ formula.eval x = -1 := by
    rw [DNFFormula.eval_eq_neg_one_iff, List.exists_mem_iff_get]
    simp [ofDNF, eval, evalLayer1, CircuitTail.eval, CircuitGate.evalTerm]
  rcases Int.units_eq_one_or ((ofDNF formula).eval x) with hc | hc <;>
    rcases Int.units_eq_one_or (formula.eval x) with hf | hf <;>
    simp_all

/-- The Boolean function of the depth-two embedding is the DNF's Boolean function. -/
theorem toBooleanFunction_ofDNF (formula : DNFFormula n) :
    (ofDNF formula).toBooleanFunction = formula.toBooleanFunction := by
  funext x
  exact eval_ofDNF formula x

/-- Every CNF is a depth-two circuit (AND of OR clauses). -/
def ofCNF (formula : CNFFormula n) : DepthCircuit n where
  layer1Gate := .or
  layer1 := formula.clauses
  tail := .output Finset.univ

@[simp] theorem depth_ofCNF (formula : CNFFormula n) : (ofCNF formula).depth = 2 := rfl

theorem size_ofCNF (formula : CNFFormula n) : (ofCNF formula).size = formula.size := by
  simp [ofCNF, size, CNFFormula.size, CircuitTail.internalNodeCount]

theorem width_ofCNF (formula : CNFFormula n) : (ofCNF formula).width = formula.width := by
  simp [ofCNF, width, CNFFormula.width]

/-- The depth-two embedding computes the original CNF. -/
theorem eval_ofCNF (formula : CNFFormula n) (x : {−1,1}^[n]) :
    (ofCNF formula).eval x = formula.eval x := by
  have hneg : (ofCNF formula).eval x = -1 ↔ formula.eval x = -1 := by
    rw [show formula.eval x = -1 ↔
        ∀ clause ∈ formula.clauses, CNFFormula.clauseEval clause x = -1 by
      simp [CNFFormula.eval, List.all_eq_true], List.forall_mem_iff_get]
    simp [ofCNF, eval, evalLayer1, CircuitTail.eval, CircuitGate.evalTerm]
  rcases Int.units_eq_one_or ((ofCNF formula).eval x) with hc | hc <;>
    rcases Int.units_eq_one_or (formula.eval x) with hf | hf <;>
    simp_all

/-- The Boolean function of the depth-two embedding is the CNF's Boolean function. -/
theorem toBooleanFunction_ofCNF (formula : CNFFormula n) :
    (ofCNF formula).toBooleanFunction = formula.toBooleanFunction := by
  funext x
  exact eval_ofCNF formula x

/-- Predicate: computable by a depth-`d` circuit of size at most `s` and width at most `w`. -/
def HasDepthCircuit (f : BooleanFunction n) (d s w : ℕ) : Prop :=
  ∃ C : DepthCircuit n, C.depth = d ∧ C.size ≤ s ∧ C.width ≤ w ∧ C.toBooleanFunction = f

theorem hasDepthCircuit_toBooleanFunction (C : DepthCircuit n) :
    HasDepthCircuit C.toBooleanFunction C.depth C.size C.width :=
  ⟨C, rfl, le_rfl, le_rfl, rfl⟩

theorem hasDepthCircuit_ofDNF (formula : DNFFormula n) :
    HasDepthCircuit formula.toBooleanFunction 2 formula.size formula.width := by
  simpa only [depth_ofDNF, size_ofDNF, width_ofDNF, toBooleanFunction_ofDNF] using
    hasDepthCircuit_toBooleanFunction (ofDNF formula)

theorem hasDepthCircuit_ofCNF (formula : CNFFormula n) :
    HasDepthCircuit formula.toBooleanFunction 2 formula.size formula.width := by
  simpa only [depth_ofCNF, size_ofCNF, width_ofCNF, toBooleanFunction_ofCNF] using
    hasDepthCircuit_toBooleanFunction (ofCNF formula)

end DepthCircuit

end FABL
