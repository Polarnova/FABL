/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter03.LearningTheory.LowDegree
import FABL.Chapter06.F₂Polynomials.AlgebraicDegree
import FABL.Chapter06.F₂Polynomials.Encoding
import Mathlib.Analysis.Complex.ExponentialBounds
import FABL.Chapter06.F₂Polynomials.ExtremalBounds
import Mathlib.Logic.Equiv.Finset

/-!
# Exact random-example learning of low-degree F₂ polynomials

Book item: Exercise 6.30.

This module contains the executable characteristic-two row-reduction kernel and the ANF
evaluation-system adapter used by the exact low-degree polynomial learner.  Every elementary row
operation preserves the represented solution set, and the operation counter is computed by the
same recursion as elimination.
-/

open Finset MeasureTheory Set
open scoped BigOperators BooleanCube ENNReal

set_option autoImplicit false

namespace FABL

universe u

local instance lowDegreeF₂CubeMeasurableSpace (n : ℕ) : MeasurableSpace (F₂Cube n) := ⊤

local instance lowDegreeF₂CubeMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (F₂Cube n) where
  measurableSet_singleton _ := by simp

local instance exercise630SignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance exercise630SignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Executable row reduction over `𝔽₂` -/

/-- One finite linear equation over `𝔽₂`. -/
structure F₂LinearEquation (ν : Type u) where
  coefficient : ν → 𝔽₂
  constant : 𝔽₂

namespace F₂LinearEquation

variable {ν : Type u} [Fintype ν]

/-- Evaluation of the left-hand side of a finite `𝔽₂` equation. -/
def eval (equation : F₂LinearEquation ν) (assignment : ν → 𝔽₂) : 𝔽₂ :=
  ∑ coordinate, equation.coefficient coordinate * assignment coordinate

/-- An assignment satisfies an equation when its left-hand side is its constant term. -/
def IsSatisfied (equation : F₂LinearEquation ν) (assignment : ν → 𝔽₂) : Prop :=
  equation.eval assignment = equation.constant

/-- Addition of two equations is the characteristic-two elementary row operation. -/
def add (left right : F₂LinearEquation ν) : F₂LinearEquation ν where
  coefficient coordinate := left.coefficient coordinate + right.coefficient coordinate
  constant := left.constant + right.constant

@[simp] theorem eval_add (left right : F₂LinearEquation ν)
    (assignment : ν → 𝔽₂) :
    (left.add right).eval assignment = left.eval assignment + right.eval assignment := by
  simp only [eval, add, add_mul, Finset.sum_add_distrib]

/-- Adding a satisfied equation to a row preserves whether that row is satisfied. -/
theorem isSatisfied_add_iff_of_isSatisfied_right
    (left right : F₂LinearEquation ν) (assignment : ν → 𝔽₂)
    (hright : right.IsSatisfied assignment) :
    (left.add right).IsSatisfied assignment ↔ left.IsSatisfied assignment := by
  unfold IsSatisfied
  rw [eval_add, hright]
  change (left.eval assignment + right.constant =
      left.constant + right.constant) ↔ left.eval assignment = left.constant
  constructor
  · intro h
    calc
      left.eval assignment =
          (left.eval assignment + right.constant) + right.constant := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = (left.constant + right.constant) + right.constant :=
        congrArg (fun value : 𝔽₂ ↦ value + right.constant) h
      _ = left.constant := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · intro h
    exact congrArg (fun value : 𝔽₂ ↦ value + right.constant) h

/-- Clear one pivot column from a row. -/
def clearPivot (pivotVariable : ν) (pivot row : F₂LinearEquation ν) :
    F₂LinearEquation ν :=
  if row.coefficient pivotVariable = 0 then row else row.add pivot

omit [Fintype ν] in
/-- A pivot row with coefficient one clears its column. -/
theorem clearPivot_coefficient_eq_zero
    (pivotVariable : ν) (pivot row : F₂LinearEquation ν)
    (hpivot : pivot.coefficient pivotVariable = 1) :
    (clearPivot pivotVariable pivot row).coefficient pivotVariable = 0 := by
  unfold clearPivot
  split_ifs with h
  · exact h
  · change row.coefficient pivotVariable + pivot.coefficient pivotVariable = 0
    rw [hpivot, Fin.eq_one_of_ne_zero _ h]
    exact CharTwo.add_self_eq_zero 1

/-- Clearing by a satisfied pivot preserves the solution predicate of the row. -/
theorem isSatisfied_clearPivot_iff
    (pivotVariable : ν) (pivot row : F₂LinearEquation ν)
    (assignment : ν → 𝔽₂) (hpivot : pivot.IsSatisfied assignment) :
    (clearPivot pivotVariable pivot row).IsSatisfied assignment ↔
      row.IsSatisfied assignment := by
  unfold clearPivot
  split_ifs
  · rfl
  · exact isSatisfied_add_iff_of_isSatisfied_right row pivot assignment hpivot

end F₂LinearEquation

variable {ν : Type u} [Fintype ν] [DecidableEq ν]

/-- Simultaneous satisfaction of a finite list of equations. -/
def F₂SatisfiesRows (rows : List (F₂LinearEquation ν))
    (assignment : ν → 𝔽₂) : Prop :=
  ∀ row ∈ rows, row.IsSatisfied assignment

/-- Executably extract the first row with a nonzero coefficient in a requested column. -/
def extractF₂Pivot (pivotVariable : ν) :
    List (F₂LinearEquation ν) →
      Option (F₂LinearEquation ν × List (F₂LinearEquation ν))
  | [] => none
  | row :: rows =>
      if row.coefficient pivotVariable = 1 then
        some (row, rows)
      else
        match extractF₂Pivot pivotVariable rows with
        | none => none
        | some (pivot, remaining) => some (pivot, row :: remaining)

omit [Fintype ν] [DecidableEq ν] in
/-- A successfully extracted pivot has coefficient one. -/
theorem extractF₂Pivot_coefficient_eq_one
    (pivotVariable : ν) (rows : List (F₂LinearEquation ν))
    (pivot : F₂LinearEquation ν) (remaining : List (F₂LinearEquation ν))
    (hextract : extractF₂Pivot pivotVariable rows = some (pivot, remaining)) :
    pivot.coefficient pivotVariable = 1 := by
  induction rows generalizing pivot remaining with
  | nil => simp [extractF₂Pivot] at hextract
  | cons row rows ih =>
      rw [extractF₂Pivot] at hextract
      split at hextract
      next h =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hextract
        rcases hextract with ⟨rfl, rfl⟩
        exact h
      next hrow =>
        cases hrecursive : extractF₂Pivot pivotVariable rows with
        | none => simp [hrecursive] at hextract
        | some pivotResult =>
          rcases pivotResult with ⟨recursivePivot, rest⟩
          simp only [hrecursive] at hextract
          simp only [Option.some.injEq, Prod.mk.injEq] at hextract
          rcases hextract with ⟨rfl, rfl⟩
          exact ih (pivot := recursivePivot) (remaining := rest) hrecursive

omit [DecidableEq ν] in
/-- Pivot extraction is a row permutation, expressed by equality of solution predicates. -/
theorem extractF₂Pivot_satisfiesRows_iff
    (pivotVariable : ν) (rows : List (F₂LinearEquation ν))
    (pivot : F₂LinearEquation ν) (remaining : List (F₂LinearEquation ν))
    (hextract : extractF₂Pivot pivotVariable rows = some (pivot, remaining))
    (assignment : ν → 𝔽₂) :
    F₂SatisfiesRows rows assignment ↔
      pivot.IsSatisfied assignment ∧ F₂SatisfiesRows remaining assignment := by
  induction rows generalizing pivot remaining with
  | nil => simp [extractF₂Pivot] at hextract
  | cons row rows ih =>
      rw [extractF₂Pivot] at hextract
      split at hextract
      next h =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hextract
        rcases hextract with ⟨rfl, rfl⟩
        simp [F₂SatisfiesRows]
      next h =>
        cases hrecursive : extractF₂Pivot pivotVariable rows with
        | none => simp [hrecursive] at hextract
        | some pivotResult =>
          rcases pivotResult with ⟨recursivePivot, rest⟩
          simp only [hrecursive] at hextract
          simp only [Option.some.injEq, Prod.mk.injEq] at hextract
          rcases hextract with ⟨rfl, rfl⟩
          have hih := ih (pivot := recursivePivot) (remaining := rest) hrecursive
          simp only [F₂SatisfiesRows, List.mem_cons, forall_eq_or_imp] at hih ⊢
          tauto

omit [Fintype ν] [DecidableEq ν] in
/-- Failure to extract a pivot means the whole requested column is zero. -/
theorem extractF₂Pivot_eq_none_iff
    (pivotVariable : ν) (rows : List (F₂LinearEquation ν)) :
    extractF₂Pivot pivotVariable rows = none ↔
      ∀ row ∈ rows, row.coefficient pivotVariable = 0 := by
  induction rows with
  | nil => simp [extractF₂Pivot]
  | cons row rows ih =>
      by_cases hrow : row.coefficient pivotVariable = 1
      · constructor
        · intro hnone
          simp [extractF₂Pivot, hrow] at hnone
        · intro hall
          exfalso
          have hzero := hall row (by simp)
          simp [hrow] at hzero
      · have hzero : row.coefficient pivotVariable = 0 := by
          by_contra hne
          exact hrow (Fin.eq_one_of_ne_zero _ hne)
        cases hrecursive : extractF₂Pivot pivotVariable rows with
        | none =>
          constructor
          · intro _ candidate hcandidate
            rcases List.mem_cons.mp hcandidate with hhead | htailMember
            · simpa [hhead] using hzero
            · exact (ih.mp hrecursive) candidate htailMember
          · intro _
            simp [extractF₂Pivot, hrow, hrecursive]
        | some pivotResult =>
          rcases pivotResult with ⟨recursivePivot, rest⟩
          constructor
          · intro hnone
            simp [extractF₂Pivot, hrow, hrecursive] at hnone
          · intro hall
            exfalso
            have htail : ∀ candidate ∈ rows,
                candidate.coefficient pivotVariable = 0 := by
              intro candidate htailMember
              exact hall candidate (by simp [htailMember])
            have hnone := ih.mpr htail
            simp [hrecursive] at hnone

/-- Clear a pivot column from every remaining row. -/
def clearF₂PivotRows (pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (rows : List (F₂LinearEquation ν)) : List (F₂LinearEquation ν) :=
  rows.map (F₂LinearEquation.clearPivot pivotVariable pivot)

omit [DecidableEq ν] in
/-- Clearing a satisfied pivot from every row preserves their common solution set. -/
theorem satisfiesRows_clearF₂PivotRows_iff
    (pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (rows : List (F₂LinearEquation ν)) (assignment : ν → 𝔽₂)
    (hpivot : pivot.IsSatisfied assignment) :
    F₂SatisfiesRows (clearF₂PivotRows pivotVariable pivot rows) assignment ↔
      F₂SatisfiesRows rows assignment := by
  simp only [F₂SatisfiesRows, clearF₂PivotRows, List.mem_map]
  constructor
  · intro h row hrow
    have hclear := h (F₂LinearEquation.clearPivot pivotVariable pivot row)
      ⟨row, hrow, rfl⟩
    exact (F₂LinearEquation.isSatisfied_clearPivot_iff
      pivotVariable pivot row assignment hpivot).mp hclear
  · rintro h cleared ⟨row, hrow, rfl⟩
    exact (F₂LinearEquation.isSatisfied_clearPivot_iff
      pivotVariable pivot row assignment hpivot).mpr (h row hrow)

/-- Output of executable forward elimination. -/
structure F₂EliminationResult (ν : Type u) where
  pivots : List (ν × F₂LinearEquation ν)
  residual : List (F₂LinearEquation ν)
  work : ℕ

/-- Forward elimination and its exact elementary-operation charge. -/
def eliminateF₂Rows (coordinates : List ν) (rows : List (F₂LinearEquation ν)) :
    F₂EliminationResult ν :=
  match coordinates with
  | [] => ⟨[], rows, 0⟩
  | pivotVariable :: remainingVariables =>
      match extractF₂Pivot pivotVariable rows with
      | none =>
          let result := eliminateF₂Rows remainingVariables rows
          ⟨result.pivots, result.residual, rows.length + result.work⟩
      | some (pivot, remainingRows) =>
          let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
          let result := eliminateF₂Rows remainingVariables clearedRows
          ⟨(pivotVariable, pivot) :: result.pivots, result.residual,
            rows.length + remainingRows.length * (Fintype.card ν + 1) + result.work⟩
termination_by coordinates.length

omit [Fintype ν] [DecidableEq ν] in
/-- Successful pivot extraction removes exactly one row. -/
theorem extractF₂Pivot_remaining_length
    (pivotVariable : ν) (rows : List (F₂LinearEquation ν))
    (pivot : F₂LinearEquation ν) (remaining : List (F₂LinearEquation ν))
    (hextract : extractF₂Pivot pivotVariable rows = some (pivot, remaining)) :
    remaining.length + 1 = rows.length := by
  induction rows generalizing pivot remaining with
  | nil => simp [extractF₂Pivot] at hextract
  | cons row rows ih =>
      rw [extractF₂Pivot] at hextract
      split at hextract
      next =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hextract
        rcases hextract with ⟨rfl, rfl⟩
        simp
      next =>
        cases hrecursive : extractF₂Pivot pivotVariable rows with
        | none => simp [hrecursive] at hextract
        | some pivotResult =>
          rcases pivotResult with ⟨recursivePivot, rest⟩
          simp only [hrecursive] at hextract
          simp only [Option.some.injEq, Prod.mk.injEq] at hextract
          rcases hextract with ⟨rfl, rfl⟩
          simpa using ih (pivot := recursivePivot) (remaining := rest) hrecursive

omit [Fintype ν] [DecidableEq ν] in
@[simp] theorem length_clearF₂PivotRows
    (pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (rows : List (F₂LinearEquation ν)) :
    (clearF₂PivotRows pivotVariable pivot rows).length = rows.length := by
  simp [clearF₂PivotRows]

omit [DecidableEq ν] in
/-- Forward elimination produces at most one pivot per requested variable. -/
theorem eliminateF₂Rows_pivots_length_le
    (coordinates : List ν) (rows : List (F₂LinearEquation ν)) :
    (eliminateF₂Rows coordinates rows).pivots.length ≤ coordinates.length := by
  induction coordinates generalizing rows with
  | nil => simp [eliminateF₂Rows]
  | cons pivotVariable remainingVariables ih =>
      rw [eliminateF₂Rows]
      cases hextract : extractF₂Pivot pivotVariable rows with
      | none =>
        exact (ih rows).trans (Nat.le_succ remainingVariables.length)
      | some pivotResult =>
        rcases pivotResult with ⟨pivot, remainingRows⟩
        simpa only [List.length_cons] using
          Nat.succ_le_succ
            (ih (clearF₂PivotRows pivotVariable pivot remainingRows))

omit [DecidableEq ν] in
/-- The elementary-operation counter of forward elimination is bounded by the product of the
number of requested variables, input rows, and row width. -/
theorem eliminateF₂Rows_work_le
    (coordinates : List ν) (rows : List (F₂LinearEquation ν)) :
    (eliminateF₂Rows coordinates rows).work ≤
      coordinates.length * rows.length * (Fintype.card ν + 2) := by
  induction coordinates generalizing rows with
  | nil => simp [eliminateF₂Rows]
  | cons pivotVariable remainingVariables ih =>
      rw [eliminateF₂Rows]
      cases hextract : extractF₂Pivot pivotVariable rows with
      | none =>
        have hrow : rows.length ≤ rows.length * (Fintype.card ν + 2) := by
          simpa using Nat.mul_le_mul_left rows.length (show 1 ≤ Fintype.card ν + 2 by omega)
        calc
          rows.length + (eliminateF₂Rows remainingVariables rows).work ≤
              rows.length * (Fintype.card ν + 2) +
                remainingVariables.length * rows.length * (Fintype.card ν + 2) :=
            Nat.add_le_add hrow (ih rows)
          _ = (pivotVariable :: remainingVariables).length * rows.length *
                (Fintype.card ν + 2) := by
            simp only [List.length_cons]
            ring
      | some pivotResult =>
        rcases pivotResult with ⟨pivot, remainingRows⟩
        let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
        have hremaining : remainingRows.length ≤ rows.length := by
          have hlength := extractF₂Pivot_remaining_length pivotVariable rows pivot
            remainingRows hextract
          omega
        have hfirst :
            rows.length + remainingRows.length * (Fintype.card ν + 1) ≤
              rows.length * (Fintype.card ν + 2) := by
          calc
            rows.length + remainingRows.length * (Fintype.card ν + 1) ≤
                rows.length + rows.length * (Fintype.card ν + 1) :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_right (Fintype.card ν + 1) hremaining) _
            _ = rows.length * (Fintype.card ν + 2) := by ring
        have hrecursive : (eliminateF₂Rows remainingVariables clearedRows).work ≤
            remainingVariables.length * rows.length * (Fintype.card ν + 2) := by
          calc
            (eliminateF₂Rows remainingVariables clearedRows).work ≤
                remainingVariables.length * clearedRows.length *
                  (Fintype.card ν + 2) := ih clearedRows
            _ ≤ remainingVariables.length * rows.length *
                  (Fintype.card ν + 2) := by
              exact Nat.mul_le_mul_right (Fintype.card ν + 2)
                (Nat.mul_le_mul_left remainingVariables.length
                  (by simpa [clearedRows] using hremaining))
        change rows.length + remainingRows.length * (Fintype.card ν + 1) +
            (eliminateF₂Rows remainingVariables clearedRows).work ≤
          (pivotVariable :: remainingVariables).length * rows.length *
            (Fintype.card ν + 2)
        calc
          rows.length + remainingRows.length * (Fintype.card ν + 1) +
                (eliminateF₂Rows remainingVariables clearedRows).work ≤
              rows.length * (Fintype.card ν + 2) +
                remainingVariables.length * rows.length * (Fintype.card ν + 2) :=
            Nat.add_le_add hfirst hrecursive
          _ = (pivotVariable :: remainingVariables).length * rows.length *
                (Fintype.card ν + 2) := by
            simp only [List.length_cons]
            ring

omit [DecidableEq ν] in
/-- Forward elimination preserves exactly the original solution set. -/
theorem satisfiesRows_eliminateF₂Rows_iff
    (coordinates : List ν) (rows : List (F₂LinearEquation ν))
    (assignment : ν → 𝔽₂) :
    F₂SatisfiesRows rows assignment ↔
      (∀ pivot ∈ (eliminateF₂Rows coordinates rows).pivots,
          pivot.2.IsSatisfied assignment) ∧
        F₂SatisfiesRows (eliminateF₂Rows coordinates rows).residual assignment := by
  induction coordinates generalizing rows with
  | nil => simp [eliminateF₂Rows, F₂SatisfiesRows]
  | cons pivotVariable remainingVariables ih =>
      rw [eliminateF₂Rows]
      cases hextract : extractF₂Pivot pivotVariable rows with
      | none =>
        simpa only using ih rows
      | some pivotResult =>
        rcases pivotResult with ⟨pivot, remainingRows⟩
        rw [extractF₂Pivot_satisfiesRows_iff pivotVariable rows pivot remainingRows
          hextract assignment]
        let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
        let result := eliminateF₂Rows remainingVariables clearedRows
        change pivot.IsSatisfied assignment ∧ F₂SatisfiesRows remainingRows assignment ↔
          (∀ candidate ∈ (pivotVariable, pivot) :: result.pivots,
            candidate.2.IsSatisfied assignment) ∧
            F₂SatisfiesRows result.residual assignment
        constructor
        · rintro ⟨hpivot, hremaining⟩
          have hcleared : F₂SatisfiesRows clearedRows assignment :=
            (satisfiesRows_clearF₂PivotRows_iff pivotVariable pivot remainingRows
              assignment hpivot).mpr hremaining
          have hresult := (ih clearedRows).mp hcleared
          refine ⟨?_, hresult.2⟩
          intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with hhead | htailMember
          · simpa [hhead] using hpivot
          · exact hresult.1 candidate htailMember
        · rintro ⟨hpivots, hresidual⟩
          have hpivot : pivot.IsSatisfied assignment :=
            hpivots (pivotVariable, pivot) (by simp)
          have hresult :
              (∀ candidate ∈ result.pivots, candidate.2.IsSatisfied assignment) ∧
                F₂SatisfiesRows result.residual assignment := by
            refine ⟨?_, hresidual⟩
            intro candidate hcandidate
            exact hpivots candidate (by simp [hcandidate])
          have hcleared : F₂SatisfiesRows clearedRows assignment :=
            (ih clearedRows).mpr hresult
          exact ⟨hpivot,
            (satisfiesRows_clearF₂PivotRows_iff pivotVariable pivot remainingRows
              assignment hpivot).mp hcleared⟩

omit [Fintype ν] [DecidableEq ν] in
/-- Extraction preserves every rowwise invariant that holds on the input list. -/
theorem extractF₂Pivot_forall_iff
    (predicate : F₂LinearEquation ν → Prop) (pivotVariable : ν)
    (rows : List (F₂LinearEquation ν)) (pivot : F₂LinearEquation ν)
    (remaining : List (F₂LinearEquation ν))
    (hextract : extractF₂Pivot pivotVariable rows = some (pivot, remaining)) :
    (∀ row ∈ rows, predicate row) ↔
      predicate pivot ∧ ∀ row ∈ remaining, predicate row := by
  induction rows generalizing pivot remaining with
  | nil => simp [extractF₂Pivot] at hextract
  | cons row rows ih =>
      rw [extractF₂Pivot] at hextract
      split at hextract
      next =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hextract
        rcases hextract with ⟨rfl, rfl⟩
        simp
      next =>
        cases hrecursive : extractF₂Pivot pivotVariable rows with
        | none => simp [hrecursive] at hextract
        | some pivotResult =>
          rcases pivotResult with ⟨recursivePivot, rest⟩
          simp only [hrecursive] at hextract
          simp only [Option.some.injEq, Prod.mk.injEq] at hextract
          rcases hextract with ⟨rfl, rfl⟩
          have hih := ih (pivot := recursivePivot) (remaining := rest) hrecursive
          simp only [List.mem_cons, forall_eq_or_imp] at hih ⊢
          tauto

omit [Fintype ν] [DecidableEq ν] in
/-- An elementary clearing pass preserves a column that was already zero in both rows. -/
theorem clearF₂PivotRows_column_eq_zero
    (fixedVariable pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (rows : List (F₂LinearEquation ν))
    (hpivot : pivot.coefficient fixedVariable = 0)
    (hrows : ∀ row ∈ rows, row.coefficient fixedVariable = 0) :
    ∀ row ∈ clearF₂PivotRows pivotVariable pivot rows,
      row.coefficient fixedVariable = 0 := by
  intro cleared hcleared
  rcases List.mem_map.mp hcleared with ⟨row, hrow, hrowEq⟩
  rw [← hrowEq]
  unfold F₂LinearEquation.clearPivot
  split_ifs
  · exact hrows row hrow
  · simp [F₂LinearEquation.add, hpivot, hrows row hrow]

omit [DecidableEq ν] in
/-- Forward elimination preserves every column which is zero on all input rows. -/
theorem eliminateF₂Rows_preserves_zero_column
    (fixedVariable : ν) (coordinates : List ν)
    (rows : List (F₂LinearEquation ν))
    (hrows : ∀ row ∈ rows, row.coefficient fixedVariable = 0) :
    (∀ pivot ∈ (eliminateF₂Rows coordinates rows).pivots,
        pivot.2.coefficient fixedVariable = 0) ∧
      ∀ row ∈ (eliminateF₂Rows coordinates rows).residual,
        row.coefficient fixedVariable = 0 := by
  induction coordinates generalizing rows with
  | nil => simpa [eliminateF₂Rows] using hrows
  | cons pivotVariable remainingVariables ih =>
      rw [eliminateF₂Rows]
      cases hextract : extractF₂Pivot pivotVariable rows with
      | none => exact ih rows hrows
      | some pivotResult =>
        rcases pivotResult with ⟨pivot, remainingRows⟩
        have hextracted := (extractF₂Pivot_forall_iff
          (fun row ↦ row.coefficient fixedVariable = 0) pivotVariable rows
          pivot remainingRows hextract).mp hrows
        let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
        have hcleared : ∀ row ∈ clearedRows,
            row.coefficient fixedVariable = 0 :=
          clearF₂PivotRows_column_eq_zero fixedVariable pivotVariable pivot remainingRows
            hextracted.1 hextracted.2
        have hresult := ih clearedRows hcleared
        refine ⟨?_, hresult.2⟩
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hhead | htailMember
        · simpa [hhead] using hextracted.1
        · exact hresult.1 candidate htailMember

/-- The pivot rows produced by forward elimination form a triangular system in processing order. -/
def IsF₂Triangular : List (ν × F₂LinearEquation ν) → Prop
  | [] => True
  | (pivotVariable, pivot) :: pivots =>
      pivot.coefficient pivotVariable = 1 ∧
        (∀ later ∈ pivots, later.2.coefficient pivotVariable = 0) ∧
        IsF₂Triangular pivots

omit [DecidableEq ν] in
/-- Forward elimination produces a triangular pivot list. -/
theorem isF₂Triangular_eliminateF₂Rows
    (coordinates : List ν) (rows : List (F₂LinearEquation ν)) :
    IsF₂Triangular (eliminateF₂Rows coordinates rows).pivots := by
  induction coordinates generalizing rows with
  | nil => simp [eliminateF₂Rows, IsF₂Triangular]
  | cons pivotVariable remainingVariables ih =>
      rw [eliminateF₂Rows]
      cases hextract : extractF₂Pivot pivotVariable rows with
      | none => exact ih rows
      | some pivotResult =>
        rcases pivotResult with ⟨pivot, remainingRows⟩
        let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
        have hpivot : pivot.coefficient pivotVariable = 1 :=
          extractF₂Pivot_coefficient_eq_one pivotVariable rows pivot remainingRows hextract
        have hcleared : ∀ row ∈ clearedRows,
            row.coefficient pivotVariable = 0 := by
          intro row hrow
          change row ∈ clearF₂PivotRows pivotVariable pivot remainingRows at hrow
          rw [clearF₂PivotRows] at hrow
          rcases List.mem_map.mp hrow with ⟨original, _, hrowEq⟩
          rw [← hrowEq]
          exact F₂LinearEquation.clearPivot_coefficient_eq_zero
            pivotVariable pivot original hpivot
        have hzero :=
          (eliminateF₂Rows_preserves_zero_column pivotVariable remainingVariables
            clearedRows hcleared).1
        exact ⟨hpivot, hzero, ih clearedRows⟩

/-- Change one pivot coordinate to the unique value satisfying its pivot row, assuming all other
coordinates have already been assigned. -/
def setF₂PivotValue (pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (assignment : ν → 𝔽₂) : ν → 𝔽₂ :=
  Function.update assignment pivotVariable
    (pivot.constant +
      ∑ coordinate ∈ (Finset.univ.erase pivotVariable),
        pivot.coefficient coordinate * assignment coordinate)

/-- Updating a coordinate absent from an equation does not change its satisfaction predicate. -/
theorem isSatisfied_setF₂PivotValue_iff_of_coefficient_eq_zero
    (pivotVariable : ν) (pivot row : F₂LinearEquation ν)
    (assignment : ν → 𝔽₂) (hzero : row.coefficient pivotVariable = 0) :
    row.IsSatisfied (setF₂PivotValue pivotVariable pivot assignment) ↔
      row.IsSatisfied assignment := by
  have heval : row.eval (setF₂PivotValue pivotVariable pivot assignment) =
      row.eval assignment := by
    unfold F₂LinearEquation.eval
    apply Finset.sum_congr rfl
    intro coordinate _
    by_cases hcoordinate : coordinate = pivotVariable
    · subst coordinate
      simp [hzero]
    · simp [setF₂PivotValue, Function.update, hcoordinate]
  simp [F₂LinearEquation.IsSatisfied, heval]

/-- The pivot update satisfies its own row when its pivot coefficient is one. -/
theorem isSatisfied_setF₂PivotValue
    (pivotVariable : ν) (pivot : F₂LinearEquation ν)
    (assignment : ν → 𝔽₂) (hpivot : pivot.coefficient pivotVariable = 1) :
    pivot.IsSatisfied (setF₂PivotValue pivotVariable pivot assignment) := by
  classical
  unfold F₂LinearEquation.IsSatisfied F₂LinearEquation.eval
  rw [← Finset.sum_erase_add Finset.univ
    (fun coordinate ↦ pivot.coefficient coordinate *
      setF₂PivotValue pivotVariable pivot assignment coordinate)
    (Finset.mem_univ pivotVariable)]
  have herase :
      (∑ coordinate ∈ Finset.univ.erase pivotVariable,
          pivot.coefficient coordinate *
            setF₂PivotValue pivotVariable pivot assignment coordinate) =
        ∑ coordinate ∈ Finset.univ.erase pivotVariable,
          pivot.coefficient coordinate * assignment coordinate := by
    apply Finset.sum_congr rfl
    intro coordinate hcoordinate
    have hne : coordinate ≠ pivotVariable := (Finset.mem_erase.mp hcoordinate).1
    simp [setF₂PivotValue, Function.update, hne]
  rw [herase]
  simp only [setF₂PivotValue, Function.update_self, hpivot, one_mul]
  let total : 𝔽₂ :=
    ∑ coordinate ∈ Finset.univ.erase pivotVariable,
      pivot.coefficient coordinate * assignment coordinate
  change total + (pivot.constant + total) = pivot.constant
  calc
    total + (pivot.constant + total) = pivot.constant + (total + total) := by abel
    _ = pivot.constant := by rw [CharTwo.add_self_eq_zero, add_zero]

/-- Back substitution through a triangular pivot list, with all free variables set to zero. -/
def solveF₂Pivots : List (ν × F₂LinearEquation ν) → ν → 𝔽₂
  | [] => 0
  | (pivotVariable, pivot) :: pivots =>
      setF₂PivotValue pivotVariable pivot (solveF₂Pivots pivots)

/-- Back substitution satisfies every row of a triangular pivot list. -/
theorem solveF₂Pivots_satisfies
    (pivots : List (ν × F₂LinearEquation ν))
    (htriangular : IsF₂Triangular pivots) :
    ∀ pivot ∈ pivots, pivot.2.IsSatisfied (solveF₂Pivots pivots) := by
  induction pivots with
  | nil => simp
  | cons head pivots ih =>
      rcases head with ⟨pivotVariable, pivot⟩
      rcases htriangular with ⟨hpivot, hzero, htail⟩
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with hhead | htailMember
      · simpa [hhead, solveF₂Pivots] using
          isSatisfied_setF₂PivotValue pivotVariable pivot
            (solveF₂Pivots pivots) hpivot
      · exact (isSatisfied_setF₂PivotValue_iff_of_coefficient_eq_zero
          pivotVariable pivot candidate.2 (solveF₂Pivots pivots)
          (hzero candidate htailMember)).mpr (ih htail candidate htailMember)

omit [DecidableEq ν] in
/-- Every residual row is zero in each column that has already been processed. -/
theorem eliminateF₂Rows_residual_coefficient_eq_zero_of_mem
    (coordinates : List ν) (rows : List (F₂LinearEquation ν))
    (coordinate : ν) (hcoordinate : coordinate ∈ coordinates) :
    ∀ row ∈ (eliminateF₂Rows coordinates rows).residual,
      row.coefficient coordinate = 0 := by
  induction coordinates generalizing rows with
  | nil => simp at hcoordinate
  | cons pivotVariable remainingVariables ih =>
      rcases List.mem_cons.mp hcoordinate with hhead | htailCoordinate
      · subst coordinate
        rw [eliminateF₂Rows]
        cases hextract : extractF₂Pivot pivotVariable rows with
        | none =>
          have hrows := (extractF₂Pivot_eq_none_iff pivotVariable rows).mp hextract
          exact (eliminateF₂Rows_preserves_zero_column pivotVariable
            remainingVariables rows hrows).2
        | some pivotResult =>
          rcases pivotResult with ⟨pivot, remainingRows⟩
          have hpivot := extractF₂Pivot_coefficient_eq_one
            pivotVariable rows pivot remainingRows hextract
          let clearedRows := clearF₂PivotRows pivotVariable pivot remainingRows
          have hcleared : ∀ row ∈ clearedRows,
              row.coefficient pivotVariable = 0 := by
            intro row hrow
            change row ∈ clearF₂PivotRows pivotVariable pivot remainingRows at hrow
            rw [clearF₂PivotRows] at hrow
            rcases List.mem_map.mp hrow with ⟨original, _, hrowEq⟩
            rw [← hrowEq]
            exact F₂LinearEquation.clearPivot_coefficient_eq_zero
              pivotVariable pivot original hpivot
          exact (eliminateF₂Rows_preserves_zero_column pivotVariable
            remainingVariables clearedRows hcleared).2
      · rw [eliminateF₂Rows]
        cases hextract : extractF₂Pivot pivotVariable rows with
        | none => exact ih rows htailCoordinate
        | some pivotResult =>
          rcases pivotResult with ⟨pivot, remainingRows⟩
          exact ih (clearF₂PivotRows pivotVariable pivot remainingRows) htailCoordinate

/-- Computable enumeration of an encodable finite coordinate type. -/
def f₂LinearCoordinateList (ν : Type u) [Fintype ν] [Encodable ν] : List ν :=
  Encodable.sortedUniv ν

omit [DecidableEq ν] in
@[simp] theorem mem_f₂LinearCoordinateList
    [Encodable ν] (coordinate : ν) : coordinate ∈ f₂LinearCoordinateList ν := by
  simp [f₂LinearCoordinateList]

omit [DecidableEq ν] in
@[simp] theorem length_f₂LinearCoordinateList [Encodable ν] :
    (f₂LinearCoordinateList ν).length = Fintype.card ν := by
  simp [f₂LinearCoordinateList]

/-- The executable Gaussian solver: forward elimination followed by back substitution. -/
def solveF₂Rows [Encodable ν] (rows : List (F₂LinearEquation ν)) : ν → 𝔽₂ :=
  solveF₂Pivots (eliminateF₂Rows (f₂LinearCoordinateList ν) rows).pivots

/-- The executable solver returns a genuine solution whenever the input system is consistent. -/
theorem solveF₂Rows_satisfies_of_exists
    [Encodable ν]
    (rows : List (F₂LinearEquation ν))
    (hconsistent : ∃ assignment : ν → 𝔽₂, F₂SatisfiesRows rows assignment) :
    F₂SatisfiesRows rows (solveF₂Rows rows) := by
  let result := eliminateF₂Rows (f₂LinearCoordinateList ν) rows
  have hpivots : ∀ pivot ∈ result.pivots,
      pivot.2.IsSatisfied (solveF₂Rows rows) := by
    exact solveF₂Pivots_satisfies result.pivots
      (isF₂Triangular_eliminateF₂Rows (f₂LinearCoordinateList ν) rows)
  obtain ⟨witness, hwitness⟩ := hconsistent
  have hwitnessResult :=
    (satisfiesRows_eliminateF₂Rows_iff
      (f₂LinearCoordinateList ν) rows witness).mp hwitness
  have hresidual : F₂SatisfiesRows result.residual (solveF₂Rows rows) := by
    intro row hrow
    have hzero : ∀ coordinate, row.coefficient coordinate = 0 := by
      intro coordinate
      exact eliminateF₂Rows_residual_coefficient_eq_zero_of_mem
        (f₂LinearCoordinateList ν) rows coordinate (by simp) row hrow
    have hwitnessRow : row.IsSatisfied witness := hwitnessResult.2 row hrow
    unfold F₂LinearEquation.IsSatisfied F₂LinearEquation.eval at hwitnessRow ⊢
    simpa [hzero] using hwitnessRow
  exact (satisfiesRows_eliminateF₂Rows_iff (f₂LinearCoordinateList ν) rows
    (solveF₂Rows rows)).mpr ⟨hpivots, hresidual⟩

/-! ## Low-degree ANF systems -/

/-- A square-free monomial whose degree is at most `ℓ`. -/
abbrev LowDegreeMonomial (n ℓ : ℕ) :=
  {S : Finset (Fin n) // S.card ≤ ℓ}

/-- Coefficients of an ANF supported in degrees at most `ℓ`. -/
abbrev LowDegreeF₂Coefficients (n ℓ : ℕ) := LowDegreeMonomial n ℓ → 𝔽₂

/-- The monomial count in the low-degree linear system. -/
def lowDegreeF₂MonomialCount (n ℓ : ℕ) : ℕ :=
  Fintype.card (LowDegreeMonomial n ℓ)

/-- Low-degree monomials are counted by the first binomial coefficients. -/
theorem lowDegreeF₂MonomialCount_eq_sum_choose (n ℓ : ℕ) :
    lowDegreeF₂MonomialCount n ℓ = ∑ j ∈ Finset.range (ℓ + 1), Nat.choose n j := by
  classical
  unfold lowDegreeF₂MonomialCount
  rw [Fintype.card_subtype (fun S : Finset (Fin n) ↦ S.card ≤ ℓ)]
  change ({S : Finset (Fin n) | S.card ≤ ℓ} : Finset (Finset (Fin n))).card =
    ∑ j ∈ Finset.range (ℓ + 1), Nat.choose n j
  have hfamily :
      ({S : Finset (Fin n) | S.card ≤ ℓ} : Finset (Finset (Fin n))) =
        lowDegreeFourierFamily n ℓ := by
    ext S
    simp
  rw [hfamily, card_lowDegreeFourierFamily_eq_sum_choose]

/-- The Chapter 3 low-degree-family bound also bounds the ANF system dimension. -/
theorem lowDegreeF₂MonomialCount_le (n ℓ : ℕ) :
    lowDegreeF₂MonomialCount n ℓ ≤ (ℓ + 1) * (n + 1) ^ ℓ := by
  rw [lowDegreeF₂MonomialCount_eq_sum_choose]
  simpa [card_lowDegreeFourierFamily_eq_sum_choose] using
    card_lowDegreeFourierFamily_le n ℓ

/-- Evaluate a degree-at-most-`ℓ` coefficient vector on the binary cube. -/
def lowDegreeF₂Eval {n ℓ : ℕ} (coefficient : LowDegreeF₂Coefficients n ℓ)
    (x : F₂Cube n) : 𝔽₂ :=
  ∑ S, coefficient S * anfMonomial S.1 x

/-- Extend a low-degree coefficient vector by zero to all square-free monomials. -/
def extendLowDegreeF₂Coefficients {n ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) : ANFCoefficients n :=
  fun S ↦ if h : S.card ≤ ℓ then coefficient ⟨S, h⟩ else 0

/-- Extending by zero and evaluating as a full ANF is the low-degree evaluator. -/
theorem anfEval_extendLowDegreeF₂Coefficients {n ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) :
    anfEval (extendLowDegreeF₂Coefficients coefficient) = lowDegreeF₂Eval coefficient := by
  funext x
  classical
  unfold anfEval lowDegreeF₂Eval
  calc
    (∑ S : Finset (Fin n), extendLowDegreeF₂Coefficients coefficient S *
        anfMonomial S x) =
        ∑ S ∈ lowDegreeFourierFamily n ℓ,
          extendLowDegreeF₂Coefficients coefficient S * anfMonomial S x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hnot : ¬ S.card ≤ ℓ := by simpa using hS
      simp [extendLowDegreeF₂Coefficients, hnot]
    _ = ∑ S : LowDegreeMonomial n ℓ,
        extendLowDegreeF₂Coefficients coefficient S.1 * anfMonomial S.1 x := by
      exact Finset.sum_subtype (lowDegreeFourierFamily n ℓ)
        (fun S ↦ by simp)
        (fun S ↦ extendLowDegreeF₂Coefficients coefficient S * anfMonomial S x)
    _ = ∑ S : LowDegreeMonomial n ℓ,
        coefficient S * anfMonomial S.1 x := by
      apply Finset.sum_congr rfl
      intro S _
      simp [extendLowDegreeF₂Coefficients, S.2]

/-- Low-degree ANF evaluation is injective in its coefficient vector. -/
theorem lowDegreeF₂Eval_injective {n ℓ : ℕ} :
    Function.Injective (lowDegreeF₂Eval : LowDegreeF₂Coefficients n ℓ →
      F₂BooleanFunction n) := by
  intro left right heval
  have hext : extendLowDegreeF₂Coefficients left =
      extendLowDegreeF₂Coefficients right := by
    apply anfEval_injective
    rw [anfEval_extendLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) left,
      anfEval_extendLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) right, heval]
  funext S
  have hS := congrFun hext S.1
  simpa [extendLowDegreeF₂Coefficients, S.2] using hS

/-- Addition of coefficient vectors is evaluated pointwise. -/
theorem lowDegreeF₂Eval_add {n ℓ : ℕ}
    (left right : LowDegreeF₂Coefficients n ℓ) :
    lowDegreeF₂Eval (left + right) =
      lowDegreeF₂Eval left + lowDegreeF₂Eval right := by
  funext x
  simp [lowDegreeF₂Eval, add_mul, Finset.sum_add_distrib]

/-- The canonical ANF of a low-degree evaluator is its extension-by-zero coefficient family. -/
theorem anfCoeff_lowDegreeF₂Eval {n ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) :
    anfCoeff (lowDegreeF₂Eval coefficient) =
      extendLowDegreeF₂Coefficients coefficient := by
  apply anfEval_injective
  rw [anfEval_anfCoeff,
    anfEval_extendLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) coefficient]

/-- Every function represented by a low-degree coefficient vector has algebraic degree at most
`ℓ`. -/
theorem functionAlgebraicDegree_lowDegreeF₂Eval_le {n ℓ : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) :
    functionAlgebraicDegree (lowDegreeF₂Eval coefficient) ≤ ℓ := by
  rw [functionAlgebraicDegree,
    anfCoeff_lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient,
    algebraicDegree_le_iff]
  intro S hS
  by_contra hcard
  have hnot : ¬ S.card ≤ ℓ := by omega
  exact hS (by simp [extendLowDegreeF₂Coefficients, hnot])

/-- Restriction of the canonical ANF coefficients to degrees at most `ℓ`. -/
noncomputable def lowDegreeF₂CoefficientsOfFunction {n ℓ : ℕ}
    (f : F₂BooleanFunction n) : LowDegreeF₂Coefficients n ℓ :=
  fun S ↦ anfCoeff f S.1

/-- A function of algebraic degree at most `ℓ` is evaluated by its restricted coefficient
vector. -/
theorem lowDegreeF₂Eval_coefficientsOfFunction {n ℓ : ℕ}
    (f : F₂BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ ℓ) :
    lowDegreeF₂Eval (n := n) (ℓ := ℓ)
      (lowDegreeF₂CoefficientsOfFunction (n := n) (ℓ := ℓ) f) = f := by
  funext x
  unfold lowDegreeF₂Eval lowDegreeF₂CoefficientsOfFunction
  classical
  calc
    (∑ S : LowDegreeMonomial n ℓ, anfCoeff f S.1 * anfMonomial S.1 x) =
        ∑ S ∈ lowDegreeFourierFamily n ℓ, anfCoeff f S * anfMonomial S x := by
      symm
      exact Finset.sum_subtype (lowDegreeFourierFamily n ℓ)
        (fun S ↦ by simp) (fun S ↦ anfCoeff f S * anfMonomial S x)
    _ = ∑ S : Finset (Fin n), anfCoeff f S * anfMonomial S x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : ℓ < S.card := by simpa using hS
      have hzero : anfCoeff f S = 0 := by
        by_contra hne
        exact (not_le_of_gt hcard)
          ((algebraicDegree_le_iff (anfCoeff f) ℓ).mp hdegree S hne)
      simp [hzero]
    _ = f x := by
      simpa [anfEval] using congrFun (anfEval_anfCoeff f) x

/-- The linear equation contributed by one labeled binary-cube example. -/
def lowDegreeF₂SampleEquation {n ℓ : ℕ} (sample : F₂Cube n × 𝔽₂) :
    F₂LinearEquation (LowDegreeMonomial n ℓ) where
  coefficient S := anfMonomial S.1 sample.1
  constant := sample.2

/-- A coefficient vector satisfies its sample equation exactly when its ANF evaluation matches
the label. -/
theorem lowDegreeF₂SampleEquation_isSatisfied_iff {n ℓ : ℕ}
    (sample : F₂Cube n × 𝔽₂) (coefficient : LowDegreeF₂Coefficients n ℓ) :
    (lowDegreeF₂SampleEquation (n := n) (ℓ := ℓ) sample).IsSatisfied coefficient ↔
      lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient sample.1 = sample.2 := by
  unfold F₂LinearEquation.IsSatisfied F₂LinearEquation.eval
    lowDegreeF₂SampleEquation lowDegreeF₂Eval
  constructor <;> intro h <;> simpa only [mul_comm] using h

/-- The finite linear system supplied by a sample vector. -/
def lowDegreeF₂SampleRows {n ℓ m : ℕ}
    (samples : Fin m → F₂Cube n × 𝔽₂) :
    List (F₂LinearEquation (LowDegreeMonomial n ℓ)) :=
  List.ofFn fun i ↦ lowDegreeF₂SampleEquation (n := n) (ℓ := ℓ) (samples i)

/-- Labels generated by a low-degree target make its canonical coefficient vector a solution. -/
theorem coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows
    {n ℓ m : ℕ} (f : F₂BooleanFunction n)
    (hdegree : functionAlgebraicDegree f ≤ ℓ) (sampleInputs : Fin m → F₂Cube n) :
    F₂SatisfiesRows
      (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m)
        fun i ↦ (sampleInputs i, f (sampleInputs i)))
      (lowDegreeF₂CoefficientsOfFunction (n := n) (ℓ := ℓ) f) := by
  intro row hrow
  rw [lowDegreeF₂SampleRows, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  rw [lowDegreeF₂SampleEquation_isSatisfied_iff (n := n) (ℓ := ℓ),
    lowDegreeF₂Eval_coefficientsOfFunction (n := n) (ℓ := ℓ) f hdegree]

/-- A sample vector separates all low-degree coefficient vectors when evaluation on the vector is
injective. -/
def SeparatesLowDegreeF₂Coefficients {n ℓ m : ℕ}
    (sampleInputs : Fin m → F₂Cube n) : Prop :=
  Function.Injective fun coefficient : LowDegreeF₂Coefficients n ℓ ↦
    fun i ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient (sampleInputs i)

/-- Separation is equivalent to hitting the nonzero set of every nonzero low-degree ANF. -/
theorem separatesLowDegreeF₂Coefficients_iff {n ℓ m : ℕ}
    (sampleInputs : Fin m → F₂Cube n) :
    SeparatesLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) (m := m) sampleInputs ↔
      ∀ coefficient : LowDegreeF₂Coefficients n ℓ, coefficient ≠ 0 →
        ∃ i, lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient (sampleInputs i) ≠ 0 := by
  classical
  constructor
  · intro hinjective coefficient hcoefficient
    by_contra hmissed
    push Not at hmissed
    apply hcoefficient
    apply hinjective
    funext i
    change lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient (sampleInputs i) =
      lowDegreeF₂Eval (n := n) (ℓ := ℓ)
        (0 : LowDegreeF₂Coefficients n ℓ) (sampleInputs i)
    rw [hmissed i]
    simp [lowDegreeF₂Eval]
  · intro hhit left right hequal
    by_contra hne
    let difference : LowDegreeF₂Coefficients n ℓ := left + right
    have hdifference : difference ≠ 0 := by
      intro hzero
      apply hne
      funext S
      have hS : left S + right S = 0 := congrFun hzero S
      calc
        left S = left S + (right S + right S) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
        _ = (left S + right S) + right S := by rw [add_assoc]
        _ = right S := by rw [hS, zero_add]
    obtain ⟨i, hi⟩ := hhit difference hdifference
    apply hi
    change lowDegreeF₂Eval (n := n) (ℓ := ℓ) (left + right) (sampleInputs i) = 0
    rw [lowDegreeF₂Eval_add (n := n) (ℓ := ℓ)]
    have hpoint := congrFun hequal i
    change lowDegreeF₂Eval (n := n) (ℓ := ℓ) left (sampleInputs i) =
      lowDegreeF₂Eval (n := n) (ℓ := ℓ) right (sampleInputs i) at hpoint
    change lowDegreeF₂Eval (n := n) (ℓ := ℓ) left (sampleInputs i) +
      lowDegreeF₂Eval (n := n) (ℓ := ℓ) right (sampleInputs i) = 0
    rw [hpoint, CharTwo.add_self_eq_zero]

/-- The real measure of an event under the finite uniform PMF is its uniform probability. -/
theorem measure_uniformPMF_event_eq_uniformProbability
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (event : Set Ω) [DecidablePred (fun x ↦ x ∈ event)] :
    (uniformPMF Ω).toMeasure.real event =
      uniformProbability (fun x ↦ x ∈ event) := by
  classical
  rw [← integral_indicator_one event.toFinite.measurableSet,
    integral_uniformPMF_eq_expect]
  unfold uniformProbability
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : x ∈ event <;> simp [hx]

/-- Complementary decidable events have complementary uniform probabilities. -/
theorem uniformProbability_not
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (predicate : Ω → Prop) [DecidablePred predicate] :
    uniformProbability (fun x ↦ ¬ predicate x) =
      1 - uniformProbability predicate := by
  have hsum : uniformProbability predicate +
      uniformProbability (fun x ↦ ¬ predicate x) = 1 := by
    rw [uniformProbability, uniformProbability, ← Finset.expect_add_distrib]
    calc
      Finset.expect Finset.univ (fun x : Ω ↦
          (if predicate x then (1 : ℝ) else 0) +
            (if ¬ predicate x then (1 : ℝ) else 0)) =
          Finset.expect Finset.univ (fun _x : Ω ↦ (1 : ℝ)) := by
        apply Finset.expect_congr rfl
        intro x _
        by_cases hx : predicate x <;> simp [hx]
      _ = 1 := Fintype.expect_const 1
  linarith

/-- Samples which all miss the nonzero set of one low-degree coefficient vector. -/
def lowDegreeF₂MissSet {n ℓ m : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) : Set (Fin m → F₂Cube n) :=
  {sampleInputs | ∀ i,
    lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient (sampleInputs i) = 0}

/-- The probability of missing a fixed low-degree function is the `m`-th power of its zero
probability. -/
theorem measure_lowDegreeF₂MissSet_eq_pow {n ℓ m : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) :
    (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
        (lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient) =
      uniformProbability
        (fun x ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0) ^ m := by
  classical
  have hevent : lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient =
      Set.pi Set.univ
        (fun _ : Fin m ↦
          {x | lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0}) := by
    ext sampleInputs
    simp [lowDegreeF₂MissSet]
  rw [uniformSample_toMeasure_eq_pi (F₂Cube n) m, hevent,
    Measure.real_def, Measure.pi_pi,
    ENNReal.toReal_prod]
  simp_rw [← Measure.real_def,
    measure_uniformPMF_event_eq_uniformProbability]
  simp

/-- A fixed nonzero degree-at-most-`ℓ` polynomial is missed by `m` uniform samples with
probability at most `exp (-m 2⁻ℓ)`. -/
theorem measure_lowDegreeF₂MissSet_le_exp {n ℓ m : ℕ}
    (coefficient : LowDegreeF₂Coefficients n ℓ) (hcoefficient : coefficient ≠ 0) :
    (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
        (lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient) ≤
      Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
  have hfunction : lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient ≠ 0 := by
    intro hzero
    apply hcoefficient
    apply lowDegreeF₂Eval_injective (n := n) (ℓ := ℓ)
    rw [hzero]
    funext x
    simp [lowDegreeF₂Eval]
  have hnonzero :=
    inv_two_pow_le_uniformProbability_ne_zero_of_functionAlgebraicDegree_le
      (n := n) (k := ℓ)
      (lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient) hfunction
      (functionAlgebraicDegree_lowDegreeF₂Eval_le (n := n) (ℓ := ℓ) coefficient)
  have hzero : uniformProbability
      (fun x ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0) ≤
        1 - ((2 : ℝ)⁻¹) ^ ℓ := by
    rw [show uniformProbability
        (fun x ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0) =
      uniformProbability
        (fun x ↦ ¬ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x ≠ 0) by
        congr 1
        funext x
        simp]
    rw [uniformProbability_not]
    linarith
  have hprobabilityNonneg : 0 ≤ uniformProbability
      (fun x ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0) := by
    apply Finset.expect_nonneg
    intro x _
    positivity
  have honeSub : 1 - ((2 : ℝ)⁻¹) ^ ℓ ≤
      Real.exp (-((2 : ℝ)⁻¹) ^ ℓ) :=
    Real.one_sub_le_exp_neg _
  have honeSubNonneg : 0 ≤ 1 - ((2 : ℝ)⁻¹) ^ ℓ := by
    apply sub_nonneg.mpr
    exact pow_le_one₀ (a := (2 : ℝ)⁻¹) (n := ℓ) (by norm_num) (by norm_num)
  rw [measure_lowDegreeF₂MissSet_eq_pow (n := n) (ℓ := ℓ) (m := m)]
  calc
    uniformProbability
        (fun x ↦ lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient x = 0) ^ m ≤
        (1 - ((2 : ℝ)⁻¹) ^ ℓ) ^ m :=
      pow_le_pow_left₀ hprobabilityNonneg hzero m
    _ ≤ Real.exp (-((2 : ℝ)⁻¹) ^ ℓ) ^ m :=
      pow_le_pow_left₀ honeSubNonneg honeSub m
    _ = Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Nonzero coefficient vectors indexing the separation union bound. -/
abbrev NonzeroLowDegreeF₂Coefficients (n ℓ : ℕ) :=
  {coefficient : LowDegreeF₂Coefficients n ℓ // coefficient ≠ 0}

/-- Failure of a sample vector to separate the low-degree coefficient space. -/
def lowDegreeF₂SeparationFailureSet {n ℓ m : ℕ} : Set (Fin m → F₂Cube n) :=
  {sampleInputs |
    ¬ SeparatesLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) (m := m) sampleInputs}

/-- Every separation failure misses one nonzero low-degree polynomial. -/
theorem lowDegreeF₂SeparationFailureSet_subset_iUnion_missSet {n ℓ m : ℕ} :
    lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m) ⊆
      ⋃ coefficient : NonzeroLowDegreeF₂Coefficients n ℓ,
        lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient.1 := by
  intro sampleInputs hfailure
  rw [lowDegreeF₂SeparationFailureSet, Set.mem_setOf_eq,
    separatesLowDegreeF₂Coefficients_iff (n := n) (ℓ := ℓ) (m := m)] at hfailure
  push Not at hfailure
  obtain ⟨coefficient, hcoefficient, hmissed⟩ := hfailure
  exact Set.mem_iUnion.mpr
    ⟨⟨coefficient, hcoefficient⟩, by simpa [lowDegreeF₂MissSet] using hmissed⟩

/-- The coefficient space has `2ᴰ` elements, where `D` is the low-degree monomial count. -/
theorem card_lowDegreeF₂Coefficients (n ℓ : ℕ) :
    Fintype.card (LowDegreeF₂Coefficients n ℓ) =
      2 ^ lowDegreeF₂MonomialCount n ℓ := by
  simp [LowDegreeF₂Coefficients, lowDegreeF₂MonomialCount]

/-- Union bound for the probability that uniform samples fail to determine a low-degree ANF. -/
theorem measure_lowDegreeF₂SeparationFailureSet_le {n ℓ m : ℕ} :
    (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
        (lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)) ≤
      (2 : ℝ) ^ lowDegreeF₂MonomialCount n ℓ *
        Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
  calc
    (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
        (lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)) ≤
        (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
          (⋃ coefficient : NonzeroLowDegreeF₂Coefficients n ℓ,
            lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient.1) :=
      MeasureTheory.measureReal_mono
        (lowDegreeF₂SeparationFailureSet_subset_iUnion_missSet
          (n := n) (ℓ := ℓ) (m := m))
    _ ≤ ∑ coefficient : NonzeroLowDegreeF₂Coefficients n ℓ,
        (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
          (lowDegreeF₂MissSet (n := n) (ℓ := ℓ) (m := m) coefficient.1) :=
      MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _coefficient : NonzeroLowDegreeF₂Coefficients n ℓ,
        Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
      apply Finset.sum_le_sum
      intro coefficient _
      exact measure_lowDegreeF₂MissSet_le_exp
        (n := n) (ℓ := ℓ) (m := m) coefficient.1 coefficient.2
    _ = (Fintype.card (NonzeroLowDegreeF₂Coefficients n ℓ) : ℝ) *
        Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
      simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ lowDegreeF₂MonomialCount n ℓ *
        Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : Fintype.card (NonzeroLowDegreeF₂Coefficients n ℓ) ≤
            2 ^ lowDegreeF₂MonomialCount n ℓ := by
          calc
            Fintype.card (NonzeroLowDegreeF₂Coefficients n ℓ) ≤
                Fintype.card (LowDegreeF₂Coefficients n ℓ) :=
              Fintype.card_subtype_le _
            _ = 2 ^ lowDegreeF₂MonomialCount n ℓ :=
              card_lowDegreeF₂Coefficients n ℓ
        exact_mod_cast hcard
      · positivity

/-- Any sample count making the explicit union-bound expression at most `δ` gives failure
probability at most `δ`. -/
theorem measure_lowDegreeF₂SeparationFailureSet_le_of_budget
    {n ℓ m : ℕ} {δ : ℝ}
    (hbudget : (2 : ℝ) ^ lowDegreeF₂MonomialCount n ℓ *
      Real.exp (-(m : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ) ≤ δ) :
    (uniformPMF (Fin m → F₂Cube n)).toMeasure.real
        (lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)) ≤ δ :=
  (measure_lowDegreeF₂SeparationFailureSet_le (n := n) (ℓ := ℓ) (m := m)).trans
    hbudget

/-- Computable sample scheduler for Exercise 6.30(a).  It allocates one `2^ℓ` block for every
low-degree coefficient bit and every requested confidence bit. -/
def lowDegreeF₂LearningSampleCount (n ℓ : ℕ)
    (δ : PositiveLearningParameter) : ℕ :=
  2 ^ ℓ * (lowDegreeF₂MonomialCount n ℓ + fourierEstimatorFailureBits δ)

/-- Multiplying the scheduled sample count by `2⁻ℓ` leaves exactly the dimension plus the
confidence-bit count. -/
theorem lowDegreeF₂LearningSampleCount_mul_invTwoPow
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    (lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ =
      lowDegreeF₂MonomialCount n ℓ + fourierEstimatorFailureBits δ := by
  rw [lowDegreeF₂LearningSampleCount]
  push_cast
  rw [mul_assoc, inv_pow]
  field_simp

/-- The scheduled union-bound expression is at most the requested confidence parameter. -/
theorem lowDegreeF₂LearningSampleCount_budget_le
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    (2 : ℝ) ^ lowDegreeF₂MonomialCount n ℓ *
        Real.exp (-(lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) *
          ((2 : ℝ)⁻¹) ^ ℓ) ≤
      (δ.1 : ℝ) := by
  let dimension := lowDegreeF₂MonomialCount n ℓ
  let bits := fourierEstimatorFailureBits δ
  have hhalf : Real.exp (-1) ≤ (2 : ℝ)⁻¹ := by
    simpa [one_div] using (le_of_lt Real.exp_neg_one_lt_half)
  have hexpHalf : Real.exp (-(dimension + bits : ℝ)) ≤
      ((2 : ℝ)⁻¹) ^ (dimension + bits) := by
    calc
      Real.exp (-(dimension + bits : ℝ)) =
          Real.exp (-1) ^ (dimension + bits) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ ((2 : ℝ)⁻¹) ^ (dimension + bits) :=
        pow_le_pow_left₀ (Real.exp_nonneg _)
          hhalf _
  have hconfidence : ((2 : ℝ)⁻¹) ^ bits ≤ (δ.1 : ℝ) := by
    have hcast :
        (((2 : ℚ) / (2 : ℚ) ^ fourierEstimatorFailureBits δ : ℚ) : ℝ) ≤
          (δ.1 : ℝ) :=
      Rat.cast_le.mpr (two_div_pow_fourierEstimatorFailureBits_le δ)
    calc
      ((2 : ℝ)⁻¹) ^ bits = 1 / (2 : ℝ) ^ bits := by rw [inv_pow, one_div]
      _ ≤ 2 / (2 : ℝ) ^ bits := by
        gcongr
        norm_num
      _ ≤ (δ.1 : ℝ) := by
        simpa [bits] using hcast
  have hsampleExponent :
      -(lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ =
        -((dimension + bits : ℕ) : ℝ) := by
    calc
      -(lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) * ((2 : ℝ)⁻¹) ^ ℓ =
          -((lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) *
            ((2 : ℝ)⁻¹) ^ ℓ) := by ring
      _ = -((dimension + bits : ℕ) : ℝ) := by
        rw [lowDegreeF₂LearningSampleCount_mul_invTwoPow n ℓ δ]
        simp [dimension, bits]
  change (2 : ℝ) ^ dimension *
      Real.exp (-(lowDegreeF₂LearningSampleCount n ℓ δ : ℝ) *
        ((2 : ℝ)⁻¹) ^ ℓ) ≤ (δ.1 : ℝ)
  rw [hsampleExponent]
  norm_num only [Nat.cast_add]
  calc
    (2 : ℝ) ^ dimension * Real.exp (-(dimension + bits : ℝ)) ≤
        (2 : ℝ) ^ dimension * ((2 : ℝ)⁻¹) ^ (dimension + bits) := by
      gcongr
    _ = ((2 : ℝ)⁻¹) ^ bits := by
      rw [pow_add, inv_pow]
      field_simp
    _ ≤ (δ.1 : ℝ) := hconfidence

/-- Exercise 6.30(a): the scheduled uniform sample vector fails to identify the low-degree ANF
with probability at most `δ`. -/
theorem measure_lowDegreeF₂SeparationFailureSet_scheduled_le
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    (uniformPMF
      (Fin (lowDegreeF₂LearningSampleCount n ℓ δ) → F₂Cube n)).toMeasure.real
        (lowDegreeF₂SeparationFailureSet
          (n := n) (ℓ := ℓ) (m := lowDegreeF₂LearningSampleCount n ℓ δ)) ≤
      (δ.1 : ℝ) :=
  measure_lowDegreeF₂SeparationFailureSet_le_of_budget
    (lowDegreeF₂LearningSampleCount_budget_le n ℓ δ)

/-- The scheduler has the explicit `2^ℓ(D + clog₂⌈2/δ⌉)` form and inherits the Chapter 3
polynomial monomial-count bound. -/
theorem lowDegreeF₂LearningSampleCount_le
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    lowDegreeF₂LearningSampleCount n ℓ δ ≤
      2 ^ ℓ * ((ℓ + 1) * (n + 1) ^ ℓ + fourierEstimatorFailureBits δ) := by
  rw [lowDegreeF₂LearningSampleCount]
  exact Nat.mul_le_mul_left _
    (Nat.add_le_add_right (lowDegreeF₂MonomialCount_le n ℓ) _)

/-- Coordinatewise transport of a sign-cube sample vector to the binary cube. -/
def signSamplesF₂Equiv (n m : ℕ) :
    (Fin m → {−1,1}^[n]) ≃ (Fin m → F₂Cube n) :=
  Equiv.piCongrRight fun _ ↦ (binaryCubeSignEquiv n).symm

/-- Failure of a sign-cube sample vector to separate the low-degree ANF space after the explicit
binary-cube transport. -/
def signSampleLowDegreeF₂SeparationFailureSet {n ℓ m : ℕ} :
    Set (Fin m → {−1,1}^[n]) :=
  (signSamplesF₂Equiv n m) ⁻¹'
    lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)

/-- The scheduled separation bound is invariant under the sign/binary cube equivalence. -/
theorem measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    (uniformPMF
      (Fin (lowDegreeF₂LearningSampleCount n ℓ δ) → {−1,1}^[n])).toMeasure.real
        (signSampleLowDegreeF₂SeparationFailureSet
          (n := n) (ℓ := ℓ) (m := lowDegreeF₂LearningSampleCount n ℓ δ)) ≤
      (δ.1 : ℝ) := by
  let m := lowDegreeF₂LearningSampleCount n ℓ δ
  let e := signSamplesF₂Equiv n m
  have h := measure_lowDegreeF₂SeparationFailureSet_scheduled_le n ℓ δ
  have hmap : (uniformPMF (Fin m → {−1,1}^[n])).map e =
      uniformPMF (Fin m → F₂Cube n) :=
    map_uniformPMF_equiv e
  rw [← hmap] at h
  have hmeasure :
      ((uniformPMF (Fin m → {−1,1}^[n])).map e).toMeasure.real
          (lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)) =
        (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real
          (e ⁻¹' lowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m)) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply e _ _ (measurable_of_finite e)
        (Set.toFinite _).measurableSet)
  rw [hmeasure] at h
  simpa [m, e, signSampleLowDegreeF₂SeparationFailureSet] using h

/-- Separation turns consistency with all labels into exact coefficient recovery. -/
theorem coefficients_eq_of_separates_of_satisfies
    {n ℓ m : ℕ} (f : F₂BooleanFunction n)
    (hdegree : functionAlgebraicDegree f ≤ ℓ) (sampleInputs : Fin m → F₂Cube n)
    (hseparates : SeparatesLowDegreeF₂Coefficients
      (n := n) (ℓ := ℓ) (m := m) sampleInputs)
    (coefficient : LowDegreeF₂Coefficients n ℓ)
    (hsatisfies : F₂SatisfiesRows
      (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m)
        fun i ↦ (sampleInputs i, f (sampleInputs i))) coefficient) :
    coefficient = lowDegreeF₂CoefficientsOfFunction (n := n) (ℓ := ℓ) f := by
  apply hseparates
  funext i
  have hrow := hsatisfies
    (lowDegreeF₂SampleEquation (n := n) (ℓ := ℓ)
      (sampleInputs i, f (sampleInputs i)))
    (by simp [lowDegreeF₂SampleRows])
  rw [lowDegreeF₂SampleEquation_isSatisfied_iff (n := n) (ℓ := ℓ)] at hrow
  change lowDegreeF₂Eval (n := n) (ℓ := ℓ) coefficient (sampleInputs i) =
    lowDegreeF₂Eval (n := n) (ℓ := ℓ)
      (lowDegreeF₂CoefficientsOfFunction (n := n) (ℓ := ℓ) f) (sampleInputs i)
  rw [hrow,
    lowDegreeF₂Eval_coefficientsOfFunction (n := n) (ℓ := ℓ) f hdegree]

/-! ## The random-example learner -/

/-- A finite degree-at-most-`ℓ` ANF hypothesis. -/
structure LowDegreeF₂Hypothesis (n ℓ : ℕ) where
  coefficient : LowDegreeF₂Coefficients n ℓ

namespace LowDegreeF₂Hypothesis

/-- Evaluate a learned low-degree hypothesis. -/
def evaluate {n ℓ : ℕ} (hypothesis : LowDegreeF₂Hypothesis n ℓ) :
    F₂BooleanFunction n :=
  lowDegreeF₂Eval hypothesis.coefficient

end LowDegreeF₂Hypothesis

/-- Solve the ANF linear system represented by binary-cube labeled samples. -/
def solveLowDegreeF₂Samples {n ℓ m : ℕ}
    (samples : Fin m → F₂Cube n × 𝔽₂) : LowDegreeF₂Hypothesis n ℓ :=
  ⟨solveF₂Rows (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples)⟩

/-- The low-degree solver is consistent with every sample whenever the system has a solution. -/
theorem solveLowDegreeF₂Samples_satisfies_of_exists {n ℓ m : ℕ}
    (samples : Fin m → F₂Cube n × 𝔽₂)
    (hconsistent : ∃ coefficient : LowDegreeF₂Coefficients n ℓ,
      F₂SatisfiesRows
        (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples) coefficient) :
    F₂SatisfiesRows
      (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples)
      (solveLowDegreeF₂Samples (n := n) (ℓ := ℓ) (m := m) samples).coefficient := by
  exact solveF₂Rows_satisfies_of_exists
    (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples) hconsistent

/-- On a separating sample, the executable solver recovers the target ANF exactly. -/
theorem solveLowDegreeF₂Samples_evaluate_eq
    {n ℓ m : ℕ} (f : F₂BooleanFunction n)
    (hdegree : functionAlgebraicDegree f ≤ ℓ) (sampleInputs : Fin m → F₂Cube n)
    (hseparates : SeparatesLowDegreeF₂Coefficients
      (n := n) (ℓ := ℓ) (m := m) sampleInputs) :
    (solveLowDegreeF₂Samples (n := n) (ℓ := ℓ) (m := m)
      (fun i ↦ (sampleInputs i, f (sampleInputs i)))).evaluate = f := by
  have htarget := coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows
    (n := n) (ℓ := ℓ) (m := m) f hdegree sampleInputs
  have hsolver := solveLowDegreeF₂Samples_satisfies_of_exists
    (n := n) (ℓ := ℓ) (m := m)
    (fun i ↦ (sampleInputs i, f (sampleInputs i)))
    ⟨lowDegreeF₂CoefficientsOfFunction (n := n) (ℓ := ℓ) f, htarget⟩
  have hcoeff := coefficients_eq_of_separates_of_satisfies
    (n := n) (ℓ := ℓ) (m := m) f hdegree sampleInputs hseparates _ hsolver
  change lowDegreeF₂Eval (n := n) (ℓ := ℓ)
      (solveLowDegreeF₂Samples (n := n) (ℓ := ℓ) (m := m)
        (fun i ↦ (sampleInputs i, f (sampleInputs i)))).coefficient = f
  rw [hcoeff,
    lowDegreeF₂Eval_coefficientsOfFunction (n := n) (ℓ := ℓ) f hdegree]

/-- Convert one sign-cube labeled example to the canonical binary-cube representation. -/
def binaryLabeledSample {n : ℕ} (sample : {−1,1}^[n] × Sign) : F₂Cube n × 𝔽₂ :=
  ((binaryCubeSignEquiv n).symm sample.1, binarySignEquiv.symm sample.2)

/-- The executable low-degree output computed from a batch of sign-cube labeled examples. -/
def lowDegreeF₂PolynomialLearnerLabeledOutput (n ℓ m : ℕ)
    (samples : Fin m → ({−1,1}^[n] × Sign)) : LowDegreeF₂Hypothesis n ℓ :=
  solveLowDegreeF₂Samples fun i ↦ binaryLabeledSample (samples i)

/-- A target-generated labeled batch is converted to the corresponding labeled binary batch. -/
theorem binaryLabeledSample_target {n : ℕ} (target : BooleanFunction n)
    (x : {−1,1}^[n]) :
    binaryLabeledSample (x, target x) =
      ((binaryCubeSignEquiv n).symm x,
        booleanFunctionF₂Encoding target ((binaryCubeSignEquiv n).symm x)) := by
  apply Prod.ext
  · rfl
  · simp [binaryLabeledSample, booleanFunctionF₂Encoding]

/-- On a separating target-generated batch, the labeled output is the exact binary encoding of
the target. -/
theorem lowDegreeF₂PolynomialLearnerLabeledOutput_evaluate_eq
    {n ℓ m : ℕ} (target : BooleanFunction n)
    (hdegree : functionAlgebraicDegree (booleanFunctionF₂Encoding target) ≤ ℓ)
    (sampleInputs : Fin m → {−1,1}^[n])
    (hseparates : SeparatesLowDegreeF₂Coefficients
      (n := n) (ℓ := ℓ) (m := m)
      (fun i ↦ (binaryCubeSignEquiv n).symm (sampleInputs i))) :
    (lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m
      (fun i ↦ (sampleInputs i, target (sampleInputs i)))).evaluate =
        booleanFunctionF₂Encoding target := by
  unfold lowDegreeF₂PolynomialLearnerLabeledOutput
  simp_rw [binaryLabeledSample_target]
  exact solveLowDegreeF₂Samples_evaluate_eq
    (n := n) (ℓ := ℓ) (m := m)
    (booleanFunctionF₂Encoding target) hdegree _ hseparates

/-- The charged work of row construction, forward elimination, and back substitution on one
labeled batch. -/
def lowDegreeF₂PolynomialLearnerWork (n ℓ m : ℕ)
    (samples : Fin m → ({−1,1}^[n] × Sign)) : ℕ :=
  let rows : List (F₂LinearEquation (LowDegreeMonomial n ℓ)) :=
    lowDegreeF₂SampleRows fun i ↦ binaryLabeledSample (samples i)
  let elimination := eliminateF₂Rows
    (f₂LinearCoordinateList (LowDegreeMonomial n ℓ)) rows
  m * (lowDegreeF₂MonomialCount n ℓ + 1) + elimination.work +
    elimination.pivots.length * (lowDegreeF₂MonomialCount n ℓ + 1)

/-- Row construction, elimination, and back substitution have the advertised cubic finite
linear-algebra bound in the sample count and ANF dimension. -/
theorem lowDegreeF₂PolynomialLearnerWork_le
    (n ℓ m : ℕ) (samples : Fin m → ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWork n ℓ m samples ≤
      m * (lowDegreeF₂MonomialCount n ℓ + 1) +
        lowDegreeF₂MonomialCount n ℓ * m *
          (lowDegreeF₂MonomialCount n ℓ + 2) +
        lowDegreeF₂MonomialCount n ℓ *
          (lowDegreeF₂MonomialCount n ℓ + 1) := by
  classical
  let rows : List (F₂LinearEquation (LowDegreeMonomial n ℓ)) :=
    lowDegreeF₂SampleRows fun i ↦ binaryLabeledSample (samples i)
  let coordinates : List (LowDegreeMonomial n ℓ) :=
    f₂LinearCoordinateList (LowDegreeMonomial n ℓ)
  let elimination := eliminateF₂Rows coordinates rows
  change m * (lowDegreeF₂MonomialCount n ℓ + 1) + elimination.work +
      elimination.pivots.length * (lowDegreeF₂MonomialCount n ℓ + 1) ≤ _
  have hwork : elimination.work ≤
      lowDegreeF₂MonomialCount n ℓ * m *
        (lowDegreeF₂MonomialCount n ℓ + 2) := by
    simpa [elimination, coordinates, rows, lowDegreeF₂SampleRows,
      lowDegreeF₂MonomialCount] using eliminateF₂Rows_work_le coordinates rows
  have hpivots : elimination.pivots.length ≤ lowDegreeF₂MonomialCount n ℓ := by
    simpa [elimination, coordinates, lowDegreeF₂MonomialCount] using
      eliminateF₂Rows_pivots_length_le coordinates rows
  exact Nat.add_le_add
    (Nat.add_le_add_left hwork _)
    (Nat.mul_le_mul_right (lowDegreeF₂MonomialCount n ℓ + 1) hpivots)

/-- A single scale controlling the scheduled sample count, ANF dimension, and row width.  Its
cube is a degree-`3ℓ` polynomial in `n + 1` when `ℓ` and `δ` are fixed. -/
def lowDegreeF₂PolynomialLearnerCubicScale
    (n ℓ : ℕ) (δ : PositiveLearningParameter) : ℕ :=
  2 ^ ℓ * ((ℓ + 1) * (n + 1) ^ ℓ + fourierEstimatorFailureBits δ + 2)

/-- The scheduled learner's charged local work is bounded by three cubes of its common
dimension-confidence scale. -/
theorem scheduledLowDegreeF₂PolynomialLearnerWork_le_cubicScale
    (n ℓ : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n ℓ δ) →
      ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWork n ℓ
        (lowDegreeF₂LearningSampleCount n ℓ δ) samples ≤
      3 * (lowDegreeF₂PolynomialLearnerCubicScale n ℓ δ) ^ 3 := by
  let dimension := lowDegreeF₂MonomialCount n ℓ
  let dimensionBound := (ℓ + 1) * (n + 1) ^ ℓ
  let bits := fourierEstimatorFailureBits δ
  let sampleCount := lowDegreeF₂LearningSampleCount n ℓ δ
  let scale := lowDegreeF₂PolynomialLearnerCubicScale n ℓ δ
  have hdimension : dimension ≤ dimensionBound := by
    simpa [dimension, dimensionBound] using lowDegreeF₂MonomialCount_le n ℓ
  have hone : 1 ≤ 2 ^ ℓ := Nat.one_le_pow ℓ 2 (by omega)
  have hbase : dimensionBound + bits + 2 ≤ scale := by
    calc
      dimensionBound + bits + 2 = 1 * (dimensionBound + bits + 2) := by ring
      _ ≤ 2 ^ ℓ * (dimensionBound + bits + 2) :=
        Nat.mul_le_mul_right _ hone
      _ = scale := by rfl
  have hsample : sampleCount ≤ scale := by
    calc
      sampleCount = 2 ^ ℓ * (dimension + bits) := by rfl
      _ ≤ 2 ^ ℓ * (dimensionBound + bits) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hdimension bits)
      _ ≤ 2 ^ ℓ * (dimensionBound + bits + 2) := by
        apply Nat.mul_le_mul_left
        omega
      _ = scale := by rfl
  have hdimensionScale : dimension ≤ scale := by
    exact hdimension.trans ((show dimensionBound ≤ dimensionBound + bits + 2 by omega).trans hbase)
  have hdimensionSuccScale : dimension + 1 ≤ scale := by
    exact (show dimension + 1 ≤ dimensionBound + bits + 2 by omega).trans hbase
  have hdimensionTwoScale : dimension + 2 ≤ scale := by
    exact (show dimension + 2 ≤ dimensionBound + bits + 2 by omega).trans hbase
  have hscale : 1 ≤ scale := by omega
  have hwork := lowDegreeF₂PolynomialLearnerWork_le n ℓ sampleCount samples
  have hfirst : sampleCount * (dimension + 1) ≤ scale * scale :=
    Nat.mul_le_mul hsample hdimensionSuccScale
  have hmiddle : dimension * sampleCount * (dimension + 2) ≤
      scale * scale * scale :=
    Nat.mul_le_mul (Nat.mul_le_mul hdimensionScale hsample) hdimensionTwoScale
  have hlast : dimension * (dimension + 1) ≤ scale * scale :=
    Nat.mul_le_mul hdimensionScale hdimensionSuccScale
  have hsquare : scale * scale ≤ scale ^ 3 := by
    calc
      scale * scale = scale * scale * 1 := by ring
      _ ≤ scale * scale * scale := Nat.mul_le_mul_left (scale * scale) hscale
      _ = scale ^ 3 := by ring
  have hcube : scale * scale * scale ≤ scale ^ 3 := by
    exact (show scale * scale * scale = scale ^ 3 by ring).le
  calc
    lowDegreeF₂PolynomialLearnerWork n ℓ sampleCount samples ≤
        sampleCount * (dimension + 1) +
          dimension * sampleCount * (dimension + 2) +
          dimension * (dimension + 1) := by
      simpa [dimension, sampleCount] using hwork
    _ ≤ scale * scale + scale * scale * scale + scale * scale :=
      Nat.add_le_add (Nat.add_le_add hfirst hmiddle) hlast
    _ ≤ scale ^ 3 + scale ^ 3 + scale ^ 3 :=
      Nat.add_le_add (Nat.add_le_add hsquare hcube) hsquare
    _ = 3 * scale ^ 3 := by ring
    _ = 3 * (lowDegreeF₂PolynomialLearnerCubicScale n ℓ δ) ^ 3 := by rfl

/-- Explicit `O(n)^(3ℓ)` envelope: for fixed `ℓ` and `δ`, the coefficient is independent
of `n`, while the only `n`-dependent factor is `(n + 1)^(3ℓ)`. -/
theorem scheduledLowDegreeF₂PolynomialLearnerWork_le_fixedParameterEnvelope
    (n ℓ : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n ℓ δ) →
      ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWork n ℓ
        (lowDegreeF₂LearningSampleCount n ℓ δ) samples ≤
      3 * (2 ^ ℓ * (ℓ + fourierEstimatorFailureBits δ + 3)) ^ 3 *
        (n + 1) ^ (3 * ℓ) := by
  let bits := fourierEstimatorFailureBits δ
  let power := (n + 1) ^ ℓ
  let scale := lowDegreeF₂PolynomialLearnerCubicScale n ℓ δ
  let coefficient := 2 ^ ℓ * (ℓ + bits + 3)
  have hpower : 1 ≤ power := by
    dsimp [power]
    exact Nat.one_le_pow ℓ (n + 1) (by omega)
  have htail : bits + 2 ≤ (bits + 2) * power := by
    calc
      bits + 2 = (bits + 2) * 1 := by ring
      _ ≤ (bits + 2) * power := Nat.mul_le_mul_left _ hpower
  have hinner : (ℓ + 1) * power + bits + 2 ≤ (ℓ + bits + 3) * power := by
    calc
      (ℓ + 1) * power + bits + 2 = (ℓ + 1) * power + (bits + 2) := by ring
      _ ≤ (ℓ + 1) * power + (bits + 2) * power :=
        Nat.add_le_add_left htail _
      _ = (ℓ + bits + 3) * power := by ring
  have hscale : scale ≤ coefficient * power := by
    calc
      scale = 2 ^ ℓ * ((ℓ + 1) * power + bits + 2) := by rfl
      _ ≤ 2 ^ ℓ * ((ℓ + bits + 3) * power) :=
        Nat.mul_le_mul_left _ hinner
      _ = coefficient * power := by ring
  have hscaleCube : scale ^ 3 ≤ (coefficient * power) ^ 3 := by
    calc
      scale ^ 3 = scale * scale * scale := by ring
      _ ≤ (coefficient * power) * (coefficient * power) * (coefficient * power) :=
        Nat.mul_le_mul (Nat.mul_le_mul hscale hscale) hscale
      _ = (coefficient * power) ^ 3 := by ring
  have hpowerCube : power ^ 3 = (n + 1) ^ (3 * ℓ) := by
    dsimp [power]
    simpa [Nat.mul_comm] using (pow_mul (n + 1) ℓ 3).symm
  calc
    lowDegreeF₂PolynomialLearnerWork n ℓ
          (lowDegreeF₂LearningSampleCount n ℓ δ) samples ≤
        3 * scale ^ 3 := by
      simpa [scale] using
        scheduledLowDegreeF₂PolynomialLearnerWork_le_cubicScale n ℓ δ samples
    _ ≤ 3 * (coefficient * power) ^ 3 := Nat.mul_le_mul_left 3 hscaleCube
    _ = 3 * coefficient ^ 3 * power ^ 3 := by ring
    _ = 3 * coefficient ^ 3 * (n + 1) ^ (3 * ℓ) := by rw [hpowerCube]
    _ = 3 * (2 ^ ℓ * (ℓ + fourierEstimatorFailureBits δ + 3)) ^ 3 *
          (n + 1) ^ (3 * ℓ) := by rfl

/-- The finite random-example program for Exercise 6.30(b), with work read from the same
elimination trace that determines the output. -/
def lowDegreeF₂PolynomialLearnerProgram (n ℓ m : ℕ) :
    LearningProgram n .randomExamples (LowDegreeF₂Hypothesis n ℓ) :=
  .randomExampleBatch m fun samples ↦
    .tick (lowDegreeF₂PolynomialLearnerWork n ℓ m samples)
      (.pure (lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m samples))

/-- Exact output law and constructor-derived cost of the finite low-degree learner. -/
theorem runWithCost_lowDegreeF₂PolynomialLearnerProgram
    (n ℓ m : ℕ) (target : BooleanFunction n) :
    LearningProgram.runWithCost target (lowDegreeF₂PolynomialLearnerProgram n ℓ m) =
      (uniformPMF (Fin m → {−1,1}^[n])).map fun sampleInputs ↦
        let samples := fun i ↦ (sampleInputs i, target (sampleInputs i))
        (lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m samples,
          ⟨m, 0, m + lowDegreeF₂PolynomialLearnerWork n ℓ m samples⟩) := by
  unfold lowDegreeF₂PolynomialLearnerProgram LearningProgram.runWithCost
  simp only [LearningProgram.runWithCost, PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  congr 1

/-- Every learner execution uses exactly `m` random examples and no membership queries. -/
theorem lowDegreeF₂PolynomialLearnerProgram_oracleCost
    (n ℓ m : ℕ) (target : BooleanFunction n)
    (outcome : LowDegreeF₂Hypothesis n ℓ × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target
        (lowDegreeF₂PolynomialLearnerProgram n ℓ m)).support) :
    outcome.2.randomExamples = m ∧ outcome.2.queries = 0 := by
  rw [runWithCost_lowDegreeF₂PolynomialLearnerProgram] at houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  rcases houtcome with ⟨sampleInputs, _, rfl⟩
  exact ⟨rfl, rfl⟩

/-- The Exercise 6.30 learner with the computable confidence scheduler. -/
def scheduledLowDegreeF₂PolynomialLearnerProgram
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    LearningProgram n .randomExamples (LowDegreeF₂Hypothesis n ℓ) :=
  lowDegreeF₂PolynomialLearnerProgram n ℓ
    (lowDegreeF₂LearningSampleCount n ℓ δ)

/-- A wrong output on a low-degree target implies that the sampled inputs failed to separate the
low-degree coefficient space. -/
theorem lowDegreeF₂PolynomialLearner_failure_subset_separationFailure
    (n ℓ m : ℕ) (target : BooleanFunction n)
    (hdegree : functionAlgebraicDegree (booleanFunctionF₂Encoding target) ≤ ℓ) :
    {sampleInputs : Fin m → {−1,1}^[n] |
      (lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m
        (fun i ↦ (sampleInputs i, target (sampleInputs i)))).evaluate ≠
          booleanFunctionF₂Encoding target} ⊆
      signSampleLowDegreeF₂SeparationFailureSet (n := n) (ℓ := ℓ) (m := m) := by
  intro sampleInputs hfailure
  by_contra hseparates
  apply hfailure
  apply lowDegreeF₂PolynomialLearnerLabeledOutput_evaluate_eq
    (n := n) (ℓ := ℓ) (m := m) target hdegree
  change SeparatesLowDegreeF₂Coefficients (n := n) (ℓ := ℓ) (m := m)
    ((signSamplesF₂Equiv n m) sampleInputs)
  simpa [signSampleLowDegreeF₂SeparationFailureSet,
    lowDegreeF₂SeparationFailureSet] using hseparates

/-- Exercise 6.30(a)--(c): for `ℓ ≥ 1` and `0 < δ ≤ 1/2`, the scheduled finite
random-example program exactly learns every degree-at-most-`ℓ` target except with probability at
most `δ`. -/
theorem scheduledLowDegreeF₂PolynomialLearnerProgram_failureProbability_le
    (n ℓ : ℕ) (target : BooleanFunction n) (_hℓ : 1 ≤ ℓ)
    (δ : PositiveLearningParameter)
    (hdegree : functionAlgebraicDegree (booleanFunctionF₂Encoding target) ≤ ℓ) :
    LearningProgram.eventProbability
        (scheduledLowDegreeF₂PolynomialLearnerProgram n ℓ δ) target
        (fun outcome ↦ outcome.1.evaluate ≠ booleanFunctionF₂Encoding target) ≤
      (δ.1 : ℝ) := by
  let m := lowDegreeF₂LearningSampleCount n ℓ δ
  unfold LearningProgram.eventProbability scheduledLowDegreeF₂PolynomialLearnerProgram
  rw [runWithCost_lowDegreeF₂PolynomialLearnerProgram]
  rw [PMF.toOuterMeasure_map_apply]
  let failure : Set (Fin m → {−1,1}^[n]) :=
    {sampleInputs |
      (lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m
        (fun i ↦ (sampleInputs i, target (sampleInputs i)))).evaluate ≠
          booleanFunctionF₂Encoding target}
  change ((uniformPMF (Fin m → {−1,1}^[n])).toOuterMeasure failure).toReal ≤ _
  have hmeasure :
      ((uniformPMF (Fin m → {−1,1}^[n])).toOuterMeasure failure).toReal =
        (uniformPMF (Fin m → {−1,1}^[n])).toMeasure.real failure := by
    exact congrArg ENNReal.toReal
      ((uniformPMF (Fin m → {−1,1}^[n])).toMeasure_apply_eq_toOuterMeasure
        failure).symm
  rw [hmeasure]
  exact (MeasureTheory.measureReal_mono
    (lowDegreeF₂PolynomialLearner_failure_subset_separationFailure
      n ℓ m target hdegree)).trans
    (by simpa [m] using
      measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le n ℓ δ)

/-- The confidence scheduler simply amplifies the constant-confidence learner by adding
`clog₂ ⌈2/δ⌉` independent confidence blocks. -/
theorem scheduledLowDegreeF₂PolynomialLearnerProgram_sampleCount
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    lowDegreeF₂LearningSampleCount n ℓ δ =
      2 ^ ℓ * (lowDegreeF₂MonomialCount n ℓ +
        Nat.clog 2 (Nat.ceil ((2 : ℚ) / δ.1))) := by
  rfl

end FABL
