/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.Switching
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Set.PowersetCard

/-!
# Håstad's Switching Lemma

Book item: Håstad's Switching Lemma in Section 4.4.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

/-! ## Canonical decision tree for DNF formulas -/


variable {n : ℕ}

/-! ## Free literal positions -/

/-- Positions of the literals of `T` whose coordinates remain free under `ρ`. -/
noncomputable def DNFTerm.freeLiteralPositions (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) : Finset (Fin T.literals.length) :=
  Finset.univ.filter fun j ↦ ρ (T.literals.get j).index = .free

@[simp] theorem DNFTerm.mem_freeLiteralPositions_iff (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) (j : Fin T.literals.length) :
    j ∈ T.freeLiteralPositions ρ ↔ ρ (T.literals.get j).index = .free := by
  simp [DNFTerm.freeLiteralPositions]

theorem DNFTerm.freeLiteralPosition_coordinate_mem_support (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) {j : Fin T.literals.length}
    (_hj : j ∈ T.freeLiteralPositions ρ) :
    (T.literals.get j).index ∈ T.support := by
  exact T.mem_support_of_mem_literals (List.get_mem T.literals j)

theorem DNFTerm.eval_complete_eq_neg_one_of_compatible_of_no_free
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) (hcompat : T.Compatible ρ)
    (hfree : T.freeLiteralPositions ρ = ∅) (x : 𝔽₂^[n]) :
    T.eval (CoordRestriction.complete ρ x) = -1 := by
  obtain ⟨y, hy⟩ := hcompat
  rw [T.eval_eq_neg_one_iff]
  intro ℓ hℓ
  have hyℓ := (T.eval_eq_neg_one_iff _).1 hy ℓ hℓ
  obtain ⟨j, rfl⟩ := List.get_of_mem hℓ
  have hjnot : j ∉ T.freeLiteralPositions ρ := by simp [hfree]
  have hρ : ρ (T.literals.get j).index ≠ .free := by
    simpa using hjnot
  cases hstate : ρ (T.literals.get j).index with
  | free => exact False.elim (hρ hstate)
  | fixOne =>
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (y (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = _ at hyℓ
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = _
      rw [hstate] at hyℓ ⊢
      exact hyℓ
  | fixNegOne =>
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (y (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = _ at hyℓ
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = _
      rw [hstate] at hyℓ ⊢
      exact hyℓ

/-! ## Restriction updates -/

/-- Every free coordinate of a restriction is still available to the indexed decision tree. -/
def CoordRestriction.FreeWithin (ρ : Fin n → CoordRestriction)
    (available : Finset (Fin n)) : Prop :=
  ∀ i, ρ i = .free → i ∈ available

theorem CoordRestriction.freeWithin_univ (ρ : Fin n → CoordRestriction) :
    CoordRestriction.FreeWithin ρ Finset.univ := by
  intro i _
  simp

theorem CoordRestriction.fixedState_ne_free (s : Sign) :
    CoordRestriction.fixedState s ≠ .free := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    simp [CoordRestriction.fixedState]

theorem CoordRestriction.freeWithin_fixCoordinate
    (ρ : Fin n → CoordRestriction) (available : Finset (Fin n))
    (hρ : CoordRestriction.FreeWithin ρ available) (i : Fin n) (s : Sign) :
    CoordRestriction.FreeWithin (CoordRestriction.fixCoordinate ρ i s)
      (available.erase i) := by
  intro j hj
  by_cases hji : j = i
  · subst j
    exact False.elim (CoordRestriction.fixedState_ne_free s
      (by simpa using hj))
  · exact Finset.mem_erase.mpr ⟨hji, hρ j (by
      simpa [CoordRestriction.fixCoordinate_apply_of_ne ρ hji s] using hj)⟩

/-- Fix the listed coordinates to the signs supplied by a binary assignment. -/
def CoordRestriction.fixCoordinateList (ρ : Fin n → CoordRestriction)
    (coordinates : List (Fin n)) (x : 𝔽₂^[n]) : Fin n → CoordRestriction :=
  coordinates.foldl
    (fun η i ↦ CoordRestriction.fixCoordinate η i (signEncode (x i))) ρ

@[simp] theorem CoordRestriction.fixCoordinateList_nil
    (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n]) :
    CoordRestriction.fixCoordinateList ρ [] x = ρ := rfl

@[simp] theorem CoordRestriction.fixCoordinateList_cons
    (ρ : Fin n → CoordRestriction) (i : Fin n) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) :
    CoordRestriction.fixCoordinateList ρ (i :: coordinates) x =
      CoordRestriction.fixCoordinateList
        (CoordRestriction.fixCoordinate ρ i (signEncode (x i))) coordinates x := rfl

theorem CoordRestriction.complete_fixCoordinate_signEncode
    (ρ : Fin n → CoordRestriction) (i : Fin n) (hfree : ρ i = .free)
    (x : 𝔽₂^[n]) :
    CoordRestriction.complete (CoordRestriction.fixCoordinate ρ i (signEncode (x i))) x =
      CoordRestriction.complete ρ x := by
  apply CoordRestriction.complete_fixCoordinate_eq_of_value
  simp [CoordRestriction.complete, hfree]

theorem CoordRestriction.complete_fixCoordinateList
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) (hnodup : coordinates.Nodup)
    (hfree : ∀ i ∈ coordinates, ρ i = .free) :
    CoordRestriction.complete (CoordRestriction.fixCoordinateList ρ coordinates x) x =
      CoordRestriction.complete ρ x := by
  induction coordinates generalizing ρ with
  | nil => rfl
  | cons i coordinates ih =>
      rw [CoordRestriction.fixCoordinateList_cons, ih]
      · exact CoordRestriction.complete_fixCoordinate_signEncode ρ i
          (hfree i (by simp)) x
      · exact (List.nodup_cons.mp hnodup).2
      · intro j hj
        have hji : j ≠ i := by
          intro h
          subst j
          exact (List.nodup_cons.mp hnodup).1 hj
        rw [CoordRestriction.fixCoordinate_apply_of_ne ρ hji (signEncode (x i))]
        exact hfree j (by simp [hj])

theorem CoordRestriction.fixCoordinateList_apply_of_not_mem
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) {j : Fin n} (hj : j ∉ coordinates) :
    CoordRestriction.fixCoordinateList ρ coordinates x j = ρ j := by
  induction coordinates generalizing ρ with
  | nil => rfl
  | cons i coordinates ih =>
      simp only [List.mem_cons, not_or] at hj
      rw [CoordRestriction.fixCoordinateList_cons, ih _ hj.2]
      exact CoordRestriction.fixCoordinate_apply_of_ne ρ hj.1 (signEncode (x i))

theorem CoordRestriction.fixCoordinateList_ne_free_of_mem
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) {j : Fin n} (hj : j ∈ coordinates) :
    CoordRestriction.fixCoordinateList ρ coordinates x j ≠ CoordRestriction.free := by
  induction coordinates generalizing ρ with
  | nil => simp at hj
  | cons i coordinates ih =>
      rw [CoordRestriction.fixCoordinateList_cons]
      rcases List.mem_cons.mp hj with hji | hj
      · subst j
        by_cases hi : i ∈ coordinates
        · exact ih _ hi
        · rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi]
          simp [CoordRestriction.fixCoordinate_apply_self,
            CoordRestriction.fixedState_ne_free]
      · exact ih _ hj

theorem CoordRestriction.fixCoordinateList_free_imp_original_free
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) {j : Fin n}
    (hj : CoordRestriction.fixCoordinateList ρ coordinates x j = CoordRestriction.free) :
    ρ j = CoordRestriction.free := by
  by_cases hmem : j ∈ coordinates
  · exact False.elim
      (CoordRestriction.fixCoordinateList_ne_free_of_mem ρ coordinates x hmem hj)
  · rwa [CoordRestriction.fixCoordinateList_apply_of_not_mem ρ coordinates x hmem] at hj

theorem CoordRestriction.freeWithin_fixCoordinateList
    (ρ : Fin n → CoordRestriction) (available : Finset (Fin n))
    (hρ : CoordRestriction.FreeWithin ρ available)
    (coordinates : List (Fin n)) (x : 𝔽₂^[n]) :
    CoordRestriction.FreeWithin (CoordRestriction.fixCoordinateList ρ coordinates x)
      (available \ coordinates.toFinset) := by
  intro j hj
  have hjnot : j ∉ coordinates := by
    intro hmem
    exact (CoordRestriction.fixCoordinateList_ne_free_of_mem ρ coordinates x hmem) hj
  rw [Finset.mem_sdiff]
  exact ⟨hρ j (by
    rw [CoordRestriction.fixCoordinateList_apply_of_not_mem ρ coordinates x hjnot] at hj
    exact hj), by simpa using hjnot⟩

theorem CoordRestriction.card_freeCoordinates_fixCoordinateList_lt
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) (hnonempty : coordinates ≠ [])
    (hfree : ∀ i ∈ coordinates, ρ i = .free) :
    (CoordRestriction.freeCoordinates
      (CoordRestriction.fixCoordinateList ρ coordinates x)).card <
      (CoordRestriction.freeCoordinates ρ).card := by
  obtain ⟨i, tail, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
  have hi : i ∈ CoordRestriction.freeCoordinates ρ :=
    (CoordRestriction.mem_freeCoordinates_iff ρ i).2 (hfree i (by simp))
  apply lt_of_le_of_lt (Finset.card_le_card ?_) (Finset.card_erase_lt_of_mem hi)
  intro j hj
  rw [Finset.mem_erase]
  have hjfree := (CoordRestriction.mem_freeCoordinates_iff _ j).1 hj
  have hjnot : j ∉ i :: tail := by
    intro hmem
    exact (CoordRestriction.fixCoordinateList_ne_free_of_mem ρ (i :: tail) x hmem) hjfree
  exact ⟨by simpa using fun hji : j = i ↦ hjnot (by simp [hji]),
    (CoordRestriction.mem_freeCoordinates_iff ρ j).2 (by
      rw [CoordRestriction.fixCoordinateList_apply_of_not_mem ρ (i :: tail) x hjnot]
        at hjfree
      exact hjfree)⟩

/-- The first compatible term under an explicit nonemptiness witness. -/
noncomputable def DNFFormula.canonicalTermIndex (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    Fin φ.terms.length :=
  (φ.compatibleTermIndices ρ).min' hcompat

theorem DNFFormula.canonicalTerm_compatible (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    (φ.terms.get (φ.canonicalTermIndex ρ hcompat)).Compatible ρ := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hcompat)).2

/-! ## Unindexed trees and block queries -/

/-- A finite coordinate-query tree before the no-repeated-query invariant is packaged in its
dependent index. -/
inductive CoordinateDecisionTree (n : ℕ) (α : Type*) where
  | leaf (value : α)
  | query (coordinate : Fin n)
      (zeroChild oneChild : CoordinateDecisionTree n α)

namespace CoordinateDecisionTree

variable {α : Type*}

def eval : CoordinateDecisionTree n α → 𝔽₂^[n] → α
  | .leaf value, _ => value
  | .query coordinate zeroChild oneChild, x =>
      if x coordinate = 0 then zeroChild.eval x else oneChild.eval x

def depth : CoordinateDecisionTree n α → ℕ
  | .leaf _ => 0
  | .query _ zeroChild oneChild => max zeroChild.depth oneChild.depth + 1

/-- The tree queries only currently available coordinates. -/
def WellFormed : CoordinateDecisionTree n α → Finset (Fin n) → Prop
  | .leaf _, _ => True
  | .query coordinate zeroChild oneChild, available =>
      coordinate ∈ available ∧
        zeroChild.WellFormed (available.erase coordinate) ∧
        oneChild.WellFormed (available.erase coordinate)

/-- Package a well-formed unindexed tree as the project's indexed decision tree. -/
def toF₂DecisionTree (T : CoordinateDecisionTree n α) (available : Finset (Fin n))
    (hT : T.WellFormed available) : F₂DecisionTree n α available :=
  match T with
  | .leaf value => .leaf value
  | .query coordinate zeroChild oneChild =>
      .query coordinate hT.1
        (zeroChild.toF₂DecisionTree (available.erase coordinate) hT.2.1)
        (oneChild.toF₂DecisionTree (available.erase coordinate) hT.2.2)

@[simp] theorem eval_toF₂DecisionTree (T : CoordinateDecisionTree n α)
    (available : Finset (Fin n)) (hT : T.WellFormed available) :
    (T.toF₂DecisionTree available hT).eval = T.eval := by
  funext x
  induction T generalizing available with
  | leaf value => rfl
  | query coordinate zeroChild oneChild hzero hone =>
      simp only [toF₂DecisionTree, F₂DecisionTree.eval, eval]
      split_ifs <;> simp [hzero, hone]

@[simp] theorem depth_toF₂DecisionTree (T : CoordinateDecisionTree n α)
    (available : Finset (Fin n)) (hT : T.WellFormed available) :
    (T.toF₂DecisionTree available hT).depth = T.depth := by
  induction T generalizing available with
  | leaf value => rfl
  | query coordinate zeroChild oneChild hzero hone =>
      simp [toF₂DecisionTree, F₂DecisionTree.depth, depth, hzero, hone]

/-- Replace the values on `coordinates` by those from `x`, leaving the initial assignment
elsewhere. -/
def assignCoordinates (seed x : 𝔽₂^[n]) : List (Fin n) → 𝔽₂^[n]
  | [] => seed
  | coordinate :: coordinates =>
      assignCoordinates (Function.update seed coordinate (x coordinate)) x coordinates

/-- Query a list of coordinates, passing the accumulated branch assignment to the continuation. -/
def queryCoordinates (coordinates : List (Fin n)) (seed : 𝔽₂^[n])
    (finish : 𝔽₂^[n] → CoordinateDecisionTree n α) : CoordinateDecisionTree n α :=
  match coordinates with
  | [] => finish seed
  | coordinate :: rest =>
      .query coordinate
        (queryCoordinates rest (Function.update seed coordinate 0) finish)
        (queryCoordinates rest (Function.update seed coordinate 1) finish)

theorem eval_queryCoordinates (coordinates : List (Fin n)) (seed x : 𝔽₂^[n])
    (finish : 𝔽₂^[n] → CoordinateDecisionTree n α) :
    (queryCoordinates coordinates seed finish).eval x =
      (finish (assignCoordinates seed x coordinates)).eval x := by
  induction coordinates generalizing seed with
  | nil => rfl
  | cons coordinate coordinates ih =>
      simp only [queryCoordinates, eval]
      by_cases hx : x coordinate = 0
      · rw [if_pos hx, ih]
        simp [assignCoordinates, hx]
      · have hx1 : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
        rw [if_neg hx, ih]
        simp [assignCoordinates, hx1]

theorem assignCoordinates_apply_of_not_mem (coordinates : List (Fin n))
    (seed x : 𝔽₂^[n]) {i : Fin n} (hi : i ∉ coordinates) :
    assignCoordinates seed x coordinates i = seed i := by
  induction coordinates generalizing seed with
  | nil => rfl
  | cons coordinate coordinates ih =>
      simp only [List.mem_cons, not_or] at hi
      rw [assignCoordinates, ih _ hi.2]
      simp [Function.update, hi.1]

theorem assignCoordinates_eq_on_mem (coordinates : List (Fin n))
    (seed x : 𝔽₂^[n]) {i : Fin n} (hi : i ∈ coordinates) :
    assignCoordinates seed x coordinates i = x i := by
  induction coordinates generalizing seed with
  | nil => simp at hi
  | cons coordinate coordinates ih =>
      rw [assignCoordinates]
      rcases List.mem_cons.mp hi with h | hi
      · subst coordinate
        by_cases hmem : i ∈ coordinates
        · exact ih _ hmem
        · rw [assignCoordinates_apply_of_not_mem coordinates _ _ hmem]
          simp
      · exact ih _ hi

theorem fixCoordinateList_congr (ρ : Fin n → CoordRestriction)
    (coordinates : List (Fin n)) (x y : 𝔽₂^[n])
    (hxy : ∀ i ∈ coordinates, x i = y i) :
    CoordRestriction.fixCoordinateList ρ coordinates x =
      CoordRestriction.fixCoordinateList ρ coordinates y := by
  induction coordinates generalizing ρ with
  | nil => rfl
  | cons coordinate coordinates ih =>
      rw [CoordRestriction.fixCoordinateList_cons,
        CoordRestriction.fixCoordinateList_cons, hxy coordinate (by simp)]
      apply ih
      intro i hi
      exact hxy i (by simp [hi])

theorem fixCoordinateList_assignCoordinates (ρ : Fin n → CoordRestriction)
    (coordinates : List (Fin n)) (seed x : 𝔽₂^[n]) :
    CoordRestriction.fixCoordinateList ρ coordinates
        (assignCoordinates seed x coordinates) =
      CoordRestriction.fixCoordinateList ρ coordinates x := by
  apply fixCoordinateList_congr
  intro i hi
  exact assignCoordinates_eq_on_mem coordinates seed x hi

theorem wellFormed_queryCoordinates (coordinates : List (Fin n))
    (seed : 𝔽₂^[n]) (finish : 𝔽₂^[n] → CoordinateDecisionTree n α)
    (available : Finset (Fin n)) (hnodup : coordinates.Nodup)
    (hsubset : ∀ i ∈ coordinates, i ∈ available)
    (hfinish : ∀ x, (finish x).WellFormed (available \ coordinates.toFinset)) :
    (queryCoordinates coordinates seed finish).WellFormed available := by
  induction coordinates generalizing seed available with
  | nil =>
      change (finish seed).WellFormed available
      simpa using hfinish seed
  | cons coordinate coordinates ih =>
      rw [queryCoordinates, WellFormed]
      have hcoord : coordinate ∈ available := hsubset coordinate (by simp)
      refine ⟨hcoord, ?_, ?_⟩
      all_goals
        apply ih
        · exact (List.nodup_cons.mp hnodup).2
        · intro i hi
          exact Finset.mem_erase.mpr ⟨fun h ↦
            (List.nodup_cons.mp hnodup).1 (by simpa [h] using hi),
            hsubset i (by simp [hi])⟩
        · intro x
          have heq : available.erase coordinate \ coordinates.toFinset =
              available \ (coordinate :: coordinates).toFinset := by
            ext i
            simp [List.toFinset_cons, and_assoc, and_left_comm]
          rw [heq]
          exact hfinish x

end CoordinateDecisionTree

/-! ## Canonical block construction -/

/-- Literal coordinates selected by a set of positions, in term order. -/
noncomputable def DNFTerm.coordinatesAtPositions (T : DNFTerm n)
    (positions : Finset (Fin T.literals.length)) : List (Fin n) :=
  positions.toList.map fun j ↦ (T.literals.get j).index

theorem DNFTerm.coordinatesAtPositions_nodup (T : DNFTerm n)
    (positions : Finset (Fin T.literals.length)) :
    (T.coordinatesAtPositions positions).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj hij
    apply Fin.ext
    have hi' : (i : ℕ) < (T.literals.map Literal.index).length := by
      simp
    have hj' : (j : ℕ) < (T.literals.map Literal.index).length := by
      simp
    exact (List.getElem_inj (h₀ := hi') (h₁ := hj') T.nodupIndices).1
      (by simpa using hij)
  · exact positions.nodup_toList

theorem DNFTerm.mem_coordinatesAtPositions_iff (T : DNFTerm n)
    (positions : Finset (Fin T.literals.length)) (i : Fin n) :
    i ∈ T.coordinatesAtPositions positions ↔
      ∃ j ∈ positions, (T.literals.get j).index = i := by
  simp [DNFTerm.coordinatesAtPositions]

@[simp] theorem DNFTerm.coordinatesAtPositions_nonempty_iff (T : DNFTerm n)
    (positions : Finset (Fin T.literals.length)) :
    T.coordinatesAtPositions positions ≠ [] ↔ positions.Nonempty := by
  simp [DNFTerm.coordinatesAtPositions, Finset.nonempty_iff_ne_empty]

/-- Fuel-indexed canonical block tree. One unit of fuel is consumed only after a complete
nonempty term block has been queried. -/
noncomputable def DNFFormula.canonicalBlockTreeAux (φ : DNFFormula n) :
    ℕ → (Fin n → CoordRestriction) → CoordinateDecisionTree n Sign
  | 0, ρ => .leaf (φ.eval (CoordRestriction.complete ρ 0))
  | fuel + 1, ρ =>
      if hcompat : (φ.compatibleTermIndices ρ).Nonempty then
        let T := φ.terms.get (φ.canonicalTermIndex ρ hcompat)
        let positions := T.freeLiteralPositions ρ
        if _hfree : positions.Nonempty then
          let coordinates := T.coordinatesAtPositions positions
          CoordinateDecisionTree.queryCoordinates coordinates 0 fun x ↦
            let η := CoordRestriction.fixCoordinateList ρ coordinates x
            if T.Compatible η then .leaf (-1)
            else φ.canonicalBlockTreeAux fuel η
        else
          .leaf (-1)
      else
        .leaf 1

/-- Canonical block tree with enough fuel for every possible term block. -/
noncomputable def DNFFormula.canonicalBlockTreeRaw (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) : CoordinateDecisionTree n Sign :=
  φ.canonicalBlockTreeAux n ρ

theorem DNFFormula.eval_eq_one_of_no_compatible (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : ¬(φ.compatibleTermIndices ρ).Nonempty)
    (x : 𝔽₂^[n]) : φ.eval (CoordRestriction.complete ρ x) = 1 := by
  rcases Int.units_eq_one_or (φ.eval (CoordRestriction.complete ρ x)) with h | h
  · exact h
  · obtain ⟨T, hT, hTx⟩ := (φ.eval_eq_neg_one_iff _).1 h
    obtain ⟨i, rfl⟩ := List.get_of_mem hT
    apply False.elim
    apply hcompat
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨x, hTx⟩

theorem CoordRestriction.complete_eq_of_freeCoordinates_eq_empty
    (ρ : Fin n → CoordRestriction)
    (hρ : CoordRestriction.freeCoordinates ρ = ∅) (x y : 𝔽₂^[n]) :
    CoordRestriction.complete ρ x = CoordRestriction.complete ρ y := by
  funext i
  have hfixed : ρ i ≠ .free := by
    intro hfree
    have : i ∈ CoordRestriction.freeCoordinates ρ :=
      (CoordRestriction.mem_freeCoordinates_iff ρ i).2 hfree
    simp [hρ] at this
  cases hstate : ρ i with
  | free => exact False.elim (hfixed hstate)
  | fixOne => simp [CoordRestriction.complete, hstate]
  | fixNegOne => simp [CoordRestriction.complete, hstate]

theorem DNFTerm.coordinatesAt_freeLiteralPositions_all_free (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    ∀ i ∈ T.coordinatesAtPositions (T.freeLiteralPositions ρ), ρ i = .free := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff _ _).1 hi
  exact (T.mem_freeLiteralPositions_iff ρ j).1 hj

theorem DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n]) :
    T.freeLiteralPositions
      (CoordRestriction.fixCoordinateList ρ
        (T.coordinatesAtPositions (T.freeLiteralPositions ρ)) x) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨j, hj⟩
  let coordinates := T.coordinatesAtPositions (T.freeLiteralPositions ρ)
  have hjfree := (T.mem_freeLiteralPositions_iff _ j).1 hj
  have hjoriginal : ρ (T.literals.get j).index = .free :=
    CoordRestriction.fixCoordinateList_free_imp_original_free ρ coordinates x hjfree
  have hjpos : j ∈ T.freeLiteralPositions ρ :=
    (T.mem_freeLiteralPositions_iff ρ j).2 hjoriginal
  have hjcoord : (T.literals.get j).index ∈ coordinates :=
    (T.mem_coordinatesAtPositions_iff _ _).2 ⟨j, hjpos, rfl⟩
  exact (CoordRestriction.fixCoordinateList_ne_free_of_mem ρ coordinates x hjcoord) hjfree

/-- Correctness of the fuel-indexed canonical tree whenever the fuel covers the remaining free
coordinates. -/
theorem DNFFormula.eval_canonicalBlockTreeAux (φ : DNFFormula n)
    (fuel : ℕ) (ρ : Fin n → CoordRestriction)
    (hfuel : (CoordRestriction.freeCoordinates ρ).card ≤ fuel)
    (x : 𝔽₂^[n]) :
    (φ.canonicalBlockTreeAux fuel ρ).eval x =
      φ.eval (CoordRestriction.complete ρ x) := by
  induction fuel generalizing ρ with
  | zero =>
      have hfree : CoordRestriction.freeCoordinates ρ = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
      change φ.eval (CoordRestriction.complete ρ 0) =
        φ.eval (CoordRestriction.complete ρ x)
      exact congr_arg φ.eval
        (CoordRestriction.complete_eq_of_freeCoordinates_eq_empty ρ hfree 0 x)
  | succ fuel ih =>
      rw [DNFFormula.canonicalBlockTreeAux]
      by_cases hcompat : (φ.compatibleTermIndices ρ).Nonempty
      · rw [dif_pos hcompat]
        let T := φ.terms.get (φ.canonicalTermIndex ρ hcompat)
        let positions := T.freeLiteralPositions ρ
        by_cases hpositions : positions.Nonempty
        · rw [dif_pos hpositions]
          let coordinates := T.coordinatesAtPositions positions
          rw [CoordinateDecisionTree.eval_queryCoordinates]
          let branch := CoordinateDecisionTree.assignCoordinates 0 x coordinates
          let η := CoordRestriction.fixCoordinateList ρ coordinates branch
          have hηeq : η = CoordRestriction.fixCoordinateList ρ coordinates x := by
            exact CoordinateDecisionTree.fixCoordinateList_assignCoordinates
              ρ coordinates 0 x
          have hcoordinatesNodup : coordinates.Nodup :=
            T.coordinatesAtPositions_nodup positions
          have hcoordinatesFree : ∀ i ∈ coordinates, ρ i = .free := by
            simpa [coordinates, positions] using
              T.coordinatesAt_freeLiteralPositions_all_free ρ
          have hcomplete : CoordRestriction.complete η x =
              CoordRestriction.complete ρ x := by
            rw [hηeq]
            exact CoordRestriction.complete_fixCoordinateList ρ coordinates x
              hcoordinatesNodup hcoordinatesFree
          by_cases hTη : T.Compatible η
          · change (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                else φ.canonicalBlockTreeAux fuel η).eval x = _
            rw [if_pos hTη]
            have hTempty : T.freeLiteralPositions η = ∅ := by
              rw [hηeq]
              simpa [coordinates, positions] using
                T.freeLiteralPositions_fixCoordinateList_eq_empty ρ x
            have hTtrue :=
              T.eval_complete_eq_neg_one_of_compatible_of_no_free η hTη hTempty x
            rw [← hcomplete]
            exact ((φ.eval_eq_neg_one_iff _).2
              ⟨T, List.get_mem φ.terms (φ.canonicalTermIndex ρ hcompat), hTtrue⟩).symm
          · change (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                else φ.canonicalBlockTreeAux fuel η).eval x = _
            rw [if_neg hTη, ih]
            · rw [hcomplete]
            · have hcoordinatesNonempty : coordinates ≠ [] := by
                exact (T.coordinatesAtPositions_nonempty_iff positions).2 hpositions
              have hlt : (CoordRestriction.freeCoordinates η).card <
                  (CoordRestriction.freeCoordinates ρ).card := by
                rw [hηeq]
                exact CoordRestriction.card_freeCoordinates_fixCoordinateList_lt
                  ρ coordinates x hcoordinatesNonempty hcoordinatesFree
              omega
        · rw [dif_neg hpositions]
          have hTcompat : T.Compatible ρ := φ.canonicalTerm_compatible ρ hcompat
          have hTempty : T.freeLiteralPositions ρ = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hpositions
          have hTtrue :=
            T.eval_complete_eq_neg_one_of_compatible_of_no_free ρ hTcompat hTempty x
          exact ((φ.eval_eq_neg_one_iff _).2
            ⟨T, List.get_mem φ.terms (φ.canonicalTermIndex ρ hcompat), hTtrue⟩).symm
      · rw [dif_neg hcompat]
        exact (φ.eval_eq_one_of_no_compatible ρ hcompat x).symm

theorem DNFFormula.canonicalBlockTreeAux_wellFormed (φ : DNFFormula n)
    (fuel : ℕ) (ρ : Fin n → CoordRestriction) (available : Finset (Fin n))
    (hρ : CoordRestriction.FreeWithin ρ available) :
    (φ.canonicalBlockTreeAux fuel ρ).WellFormed available := by
  induction fuel generalizing ρ available with
  | zero => trivial
  | succ fuel ih =>
      rw [DNFFormula.canonicalBlockTreeAux]
      by_cases hcompat : (φ.compatibleTermIndices ρ).Nonempty
      · rw [dif_pos hcompat]
        let T := φ.terms.get (φ.canonicalTermIndex ρ hcompat)
        let positions := T.freeLiteralPositions ρ
        by_cases hpositions : positions.Nonempty
        · rw [dif_pos hpositions]
          let coordinates := T.coordinatesAtPositions positions
          apply CoordinateDecisionTree.wellFormed_queryCoordinates
          · exact T.coordinatesAtPositions_nodup positions
          · intro i hi
            exact hρ i (by
              simpa [coordinates, positions] using
                T.coordinatesAt_freeLiteralPositions_all_free ρ i hi)
          · intro x
            let η := CoordRestriction.fixCoordinateList ρ coordinates x
            have hη : CoordRestriction.FreeWithin η (available \ coordinates.toFinset) :=
              CoordRestriction.freeWithin_fixCoordinateList ρ available hρ coordinates x
            by_cases hTη : T.Compatible η
            · change (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                  else φ.canonicalBlockTreeAux fuel η).WellFormed
                (available \ coordinates.toFinset)
              rw [if_pos hTη]
              trivial
            · change (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                  else φ.canonicalBlockTreeAux fuel η).WellFormed
                (available \ coordinates.toFinset)
              rw [if_neg hTη]
              exact ih η (available \ coordinates.toFinset) hη
        · rw [dif_neg hpositions]
          trivial
      · rw [dif_neg hcompat]
        trivial

theorem DNFFormula.canonicalBlockTreeRaw_wellFormed (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) :
    (φ.canonicalBlockTreeRaw ρ).WellFormed Finset.univ :=
  φ.canonicalBlockTreeAux_wellFormed n ρ Finset.univ
    (CoordRestriction.freeWithin_univ ρ)

/-- The indexed canonical block tree. -/
noncomputable def DNFFormula.canonicalBlockTree (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) : DecisionTree n Sign :=
  (φ.canonicalBlockTreeRaw ρ).toF₂DecisionTree Finset.univ
    (φ.canonicalBlockTreeRaw_wellFormed ρ)

theorem DNFFormula.canonicalBlockTree_computes (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) :
    (φ.canonicalBlockTree ρ).Computes
      (CoordRestriction.restrict φ.toBooleanFunction ρ) := by
  apply (F₂DecisionTree.computes_iff _ _).2
  intro x
  rw [DNFFormula.canonicalBlockTree,
    CoordinateDecisionTree.eval_toF₂DecisionTree]
  simpa [DNFFormula.canonicalBlockTreeRaw, CoordRestriction.restrict,
    DNFFormula.toBooleanFunction] using
    φ.eval_canonicalBlockTreeAux n ρ
      (by simpa using (CoordRestriction.freeCoordinates ρ).card_le_univ) x

theorem DNFFormula.decisionTreeDepth_le_canonicalBlockTree_depth
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction) :
    F₂DecisionTree.decisionTreeDepth (CoordRestriction.restrict φ.toBooleanFunction ρ) ≤
      (φ.canonicalBlockTree ρ).depth :=
  F₂DecisionTree.decisionTreeDepth_le_of_computes _ _
    (φ.canonicalBlockTree_computes ρ)


/-! ## Finite switching codes and their cardinality -/


variable {w i k : ℕ}

/-! ## Block codes -/

/-- A block records literal positions below the width bound and the path assignment relative to
the unique satisfying assignment of the term. Bits outside `positions` are canonically zero. -/
structure SwitchingBlockCode (w : ℕ) where
  positions : Finset (Fin w)
  bits : Fin w → 𝔽₂
  deriving DecidableEq, Fintype

namespace SwitchingBlockCode

/-- The stored function has no information outside the selected positions. -/
def Canonical (B : SwitchingBlockCode w) : Prop :=
  ∀ i, i ∉ B.positions → B.bits i = 0

/-- At least one selected path bit differs from the satisfying assignment. -/
def Nonzero (B : SwitchingBlockCode w) : Prop :=
  ∃ i ∈ B.positions, B.bits i = 1

noncomputable instance (B : SwitchingBlockCode w) : Decidable B.Canonical :=
  Classical.propDecidable _

noncomputable instance (B : SwitchingBlockCode w) : Decidable B.Nonzero :=
  Classical.propDecidable _

/-- Codes for one final block of exact size `i`. -/
abbrev FinalOfSize (w i : ℕ) :=
  {B : SwitchingBlockCode w // B.Canonical ∧ B.positions.card = i}

/-- Codes for a completed, falsified nonfinal block of exact size `i`. -/
abbrev FullOfSize (w i : ℕ) :=
  {B : SwitchingBlockCode w //
    B.Canonical ∧ B.positions.card = i ∧ B.Nonzero}

/-- Sets of `i` literal positions below width `w`. -/
abbrev PositionSet (w i : ℕ) :=
  Set.powersetCard (Fin w) i

theorem card_positionSet (w i : ℕ) :
    Fintype.card (PositionSet w i) = Nat.choose w i := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]

/-- Restrict a canonical ambient bit function to its selected positions. -/
def restrictBits (B : SwitchingBlockCode w) : B.positions → 𝔽₂ :=
  fun i ↦ B.bits i

/-- Extend bits on a position set by zero. -/
def ofPositionBits (S : Finset (Fin w)) (bits : S → 𝔽₂) : SwitchingBlockCode w where
  positions := S
  bits := fun i ↦ if hi : i ∈ S then bits ⟨i, hi⟩ else 0

@[simp] theorem ofPositionBits_positions (S : Finset (Fin w)) (bits : S → 𝔽₂) :
    (ofPositionBits S bits).positions = S := rfl

theorem canonical_ofPositionBits (S : Finset (Fin w)) (bits : S → 𝔽₂) :
    (ofPositionBits S bits).Canonical := by
  intro i hi
  simp only [ofPositionBits_positions] at hi
  simp [ofPositionBits, hi]

@[simp] theorem restrictBits_ofPositionBits (S : Finset (Fin w)) (bits : S → 𝔽₂) :
    restrictBits (ofPositionBits S bits) = bits := by
  funext i
  simp [restrictBits, ofPositionBits]

theorem ofPositionBits_restrictBits (B : SwitchingBlockCode w) (hB : B.Canonical) :
    ofPositionBits B.positions B.restrictBits = B := by
  cases B with
  | mk positions bits =>
      simp only [ofPositionBits, restrictBits]
      congr 1
      funext i
      by_cases hi : i ∈ positions
      · simp [hi]
      · simp only [dif_neg hi]
        exact (hB i hi).symm

/-- Final block codes are exactly a position set together with arbitrary bits on it. -/
noncomputable def finalOfSizeEquiv (w i : ℕ) :
    FinalOfSize w i ≃ Σ S : PositionSet w i, S.1 → 𝔽₂ where
  toFun B := ⟨⟨B.1.positions, B.2.2⟩, B.1.restrictBits⟩
  invFun p :=
    ⟨ofPositionBits p.1.1 p.2, canonical_ofPositionBits p.1.1 p.2, p.1.2⟩
  left_inv B := by
    apply Subtype.ext
    exact ofPositionBits_restrictBits B.1 B.2.1
  right_inv p := by
    cases p with
    | mk S bits =>
        apply Sigma.ext
        · rfl
        · simp

theorem card_finalOfSize (w i : ℕ) :
    Fintype.card (FinalOfSize w i) = Nat.choose w i * 2 ^ i := by
  rw [Fintype.card_congr (finalOfSizeEquiv w i), Fintype.card_sigma]
  calc
    (∑ S : PositionSet w i, Fintype.card (S.1 → 𝔽₂)) =
        ∑ _S : PositionSet w i, 2 ^ i := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Fintype.card_fun, show Fintype.card 𝔽₂ = 2 by decide,
        Fintype.card_coe, S.2]
    _ = Fintype.card (PositionSet w i) * 2 ^ i := by simp
    _ = Nat.choose w i * 2 ^ i := by rw [card_positionSet]

/-- Nonzero functions on a finite binary cube are all functions except the zero function. -/
theorem card_nonzero_positionBits (S : Finset (Fin w)) :
    Fintype.card {bits : S → 𝔽₂ // bits ≠ 0} = 2 ^ S.card - 1 := by
  rw [Fintype.card_subtype_compl (fun bits : S → 𝔽₂ ↦ bits = 0)]
  simp

theorem nonzero_iff_restrictBits_ne_zero (B : SwitchingBlockCode w) :
    B.Nonzero ↔ B.restrictBits ≠ 0 := by
  constructor
  · rintro ⟨i, hi, hbit⟩ hzero
    have := congr_fun hzero ⟨i, hi⟩
    simp [restrictBits, hbit] at this
  · intro hbits
    by_contra hzero
    simp only [Nonzero, not_exists, not_and] at hzero
    apply hbits
    funext i
    have := hzero i i.property
    change B.bits i = 0
    apply (ZMod.val_eq_zero _).1
    have hlt := ZMod.val_lt (B.bits i)
    by_contra hzero
    have hpos : 0 < (B.bits i).val := Nat.pos_of_ne_zero hzero
    have hone : (B.bits i).val = 1 := by omega
    apply this
    apply ZMod.val_injective 2
    simpa [ZMod.val_one] using hone

/-- Full block codes are exactly a position set together with nonzero relative bits. -/
noncomputable def fullOfSizeEquiv (w i : ℕ) :
    FullOfSize w i ≃ Σ S : PositionSet w i, {bits : S.1 → 𝔽₂ // bits ≠ 0} where
  toFun B :=
    ⟨⟨B.1.positions, B.2.2.1⟩,
      ⟨B.1.restrictBits,
        (nonzero_iff_restrictBits_ne_zero B.1).1 B.2.2.2⟩⟩
  invFun p :=
    ⟨ofPositionBits p.1.1 p.2.1,
      canonical_ofPositionBits p.1.1 p.2.1,
      p.1.2,
      (nonzero_iff_restrictBits_ne_zero _).2 (by
        rw [restrictBits_ofPositionBits]
        exact p.2.2)⟩
  left_inv B := by
    apply Subtype.ext
    exact ofPositionBits_restrictBits B.1 B.2.1
  right_inv p := by
    cases p with
    | mk S bits =>
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Subtype.ext
          exact restrictBits_ofPositionBits S.1 bits.1

theorem card_fullOfSize (w i : ℕ) :
    Fintype.card (FullOfSize w i) = Nat.choose w i * (2 ^ i - 1) := by
  rw [Fintype.card_congr (fullOfSizeEquiv w i), Fintype.card_sigma]
  calc
    (∑ S : PositionSet w i,
        Fintype.card {bits : S.1 → 𝔽₂ // bits ≠ 0}) =
        ∑ _S : PositionSet w i, (2 ^ i - 1) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [card_nonzero_positionBits, S.2]
    _ = Fintype.card (PositionSet w i) * (2 ^ i - 1) := by simp
    _ = Nat.choose w i * (2 ^ i - 1) := by rw [card_positionSet]

end SwitchingBlockCode

/-! ## Recursive switching codes -/

/-- A switching code is a nonempty sequence of blocks of total size `k`. The final block carries
arbitrary relative bits; every earlier block carries a nonzero relative assignment. The indices
make both positivity of block sizes and total size true by construction. -/
inductive SwitchingCode (w : ℕ) : ℕ → Type
  | final {k : ℕ} (block : SwitchingBlockCode.FinalOfSize w (k + 1)) :
      SwitchingCode w (k + 1)
  | cons {k : ℕ} (i : Fin k) (block : SwitchingBlockCode.FullOfSize w (i + 1))
      (tail : SwitchingCode w (k - i)) : SwitchingCode w (k + 1)

namespace SwitchingCode

/-- No nonempty switching code has total size zero. -/
def zeroEquivEmpty (w : ℕ) : SwitchingCode w 0 ≃ Empty where
  toFun code := nomatch code
  invFun value := nomatch value
  left_inv code := nomatch code
  right_inv value := nomatch value

/-- Split a positive-size code into its final block or its first full block and remaining code. -/
def succEquiv (w k : ℕ) :
    SwitchingCode w (k + 1) ≃
      SwitchingBlockCode.FinalOfSize w (k + 1) ⊕
        Σ i : Fin k, SwitchingBlockCode.FullOfSize w (i + 1) × SwitchingCode w (k - i) where
  toFun
    | .final block => Sum.inl block
    | .cons i block tail => Sum.inr ⟨i, block, tail⟩
  invFun
    | Sum.inl block => .final block
    | Sum.inr ⟨i, block, tail⟩ => .cons i block tail
  left_inv
    | .final _ => rfl
    | .cons _ _ _ => rfl
  right_inv
    | Sum.inl _ => rfl
    | Sum.inr ⟨_, _, _⟩ => rfl

noncomputable def fintype (w : ℕ) : (k : ℕ) → Fintype (SwitchingCode w k)
  | 0 => Fintype.ofEquiv Empty (zeroEquivEmpty w).symm
  | k + 1 =>
      letI (i : Fin k) : Fintype (SwitchingCode w (k - i)) := fintype w (k - i)
      Fintype.ofEquiv
        (SwitchingBlockCode.FinalOfSize w (k + 1) ⊕
          Σ i : Fin k,
            SwitchingBlockCode.FullOfSize w (i + 1) × SwitchingCode w (k - i))
        (succEquiv w k).symm
termination_by k => k
decreasing_by omega

noncomputable instance (w k : ℕ) : Fintype (SwitchingCode w k) := fintype w k

/-- Exact cardinal recurrence for switching codes. -/
theorem card_succ (w k : ℕ) :
    Fintype.card (SwitchingCode w (k + 1)) =
      Nat.choose w (k + 1) * 2 ^ (k + 1) +
        ∑ i : Fin k,
          (Nat.choose w ((i : ℕ) + 1) * (2 ^ ((i : ℕ) + 1) - 1)) *
            Fintype.card (SwitchingCode w (k - (i : ℕ))) := by
  rw [Fintype.card_congr (succEquiv w k), Fintype.card_sum, Fintype.card_sigma]
  rw [SwitchingBlockCode.card_finalOfSize]
  apply congrArg (Nat.choose w (k + 1) * 2 ^ (k + 1) + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_prod, SwitchingBlockCode.card_fullOfSize]

end SwitchingCode


/-! ## Quantitative bounds for switching codes -/

namespace SwitchingCode

/-- Normalized contribution of a completed nonfinal block of size `i`. -/
noncomputable def fullCoefficient (i : ℕ) : ℝ :=
  ((2 ^ i - 1 : ℕ) : ℝ) * ((4 : ℝ) / 9) ^ i / i.factorial

/-- Difference between the final-block and full-block normalized contributions. -/
noncomputable def finalRemainder (i : ℕ) : ℝ :=
  ((4 : ℝ) / 9) ^ i / i.factorial

private theorem factorial_ge_twentyFour_mul_four_pow {i : ℕ} (hi : 4 ≤ i) :
    24 * 4 ^ (i - 4) ≤ i.factorial := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  simp only [Nat.add_sub_cancel_left]
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [show 4 + (t + 1) = (4 + t) + 1 by omega, Nat.factorial_succ, pow_succ]
      have ih' : 24 * 4 ^ t ≤ (4 + t).factorial := ih (by omega)
      have hfactor : 4 ≤ 4 + t + 1 := by omega
      nlinarith [Nat.factorial_pos (4 + t)]

private theorem fullCoefficient_tail {i : ℕ} (hi : 4 ≤ i) :
    fullCoefficient i ≤ (32 / 3 : ℝ) * ((2 : ℝ) / 9) ^ i := by
  have hpowNat : 2 ^ i - 1 ≤ 2 ^ i := Nat.sub_le _ _
  have hpow : (((2 ^ i - 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ i := by
    exact_mod_cast hpowNat
  have hfacNat := factorial_ge_twentyFour_mul_four_pow hi
  have hfac : (24 : ℝ) * 4 ^ (i - 4) ≤ (i.factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hdenpos : (0 : ℝ) < 24 * 4 ^ (i - 4) := by positivity
  calc
    fullCoefficient i ≤ (2 : ℝ) ^ i * ((4 : ℝ) / 9) ^ i / i.factorial := by
      unfold fullCoefficient
      gcongr
    _ ≤ (2 : ℝ) ^ i * ((4 : ℝ) / 9) ^ i /
        (24 * 4 ^ (i - 4)) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by positivity) (by positivity)) hdenpos hfac
    _ = (32 / 3 : ℝ) * ((2 : ℝ) / 9) ^ i := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
      simp only [Nat.add_sub_cancel_left]
      rw [show (2 : ℝ) ^ (4 + t) * ((4 : ℝ) / 9) ^ (4 + t) =
          ((8 : ℝ) / 9) ^ (4 + t) by
        rw [← mul_pow]
        congr 1
        norm_num]
      rw [pow_add, pow_add]
      have hratio : ((8 : ℝ) / 9) ^ t / (4 : ℝ) ^ t =
          ((2 : ℝ) / 9) ^ t := by
        rw [← div_pow]
        congr 1
        norm_num
      calc
        (8 / 9 : ℝ) ^ 4 * (8 / 9 : ℝ) ^ t / (24 * 4 ^ t) =
            ((8 / 9 : ℝ) ^ t / 4 ^ t) * ((8 / 9 : ℝ) ^ 4 / 24) := by ring
        _ = (32 / 3 : ℝ) * ((2 / 9 : ℝ) ^ 4 * (2 / 9 : ℝ) ^ t) := by
          rw [hratio]
          ring

private theorem geometric_two_ninths_bound (m : ℕ) :
    (∑ j ∈ Finset.range m, ((2 : ℝ) / 9) ^ j) ≤ 9 / 7 := by
  have hgeom := geom_sum_mul_neg ((2 : ℝ) / 9) m
  have hpow : 0 ≤ ((2 : ℝ) / 9) ^ m := by positivity
  nlinarith

private theorem sum_fullCoefficient_range (k : ℕ) :
    (∑ i ∈ Finset.range k, fullCoefficient (i + 1)) ≤
      (13420 : ℝ) / 15309 := by
  rcases k with _ | _ | _ | k
  · norm_num
  · norm_num [fullCoefficient]
  · norm_num [fullCoefficient]
  · rcases k with _ | k
    · norm_num [fullCoefficient]
    · rw [show k + 1 + 3 = 3 + (k + 1) by omega, Finset.sum_range_add]
      have htail :
          (∑ x ∈ Finset.range (k + 1), fullCoefficient (3 + x + 1)) ≤
            ∑ x ∈ Finset.range (k + 1),
              (32 / 3 : ℝ) * ((2 : ℝ) / 9) ^ (x + 4) := by
        gcongr with x hx
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          fullCoefficient_tail (i := x + 4) (by omega)
      have hgeom := geometric_two_ninths_bound (k + 1)
      calc
        (∑ x ∈ Finset.range 3, fullCoefficient (x + 1)) +
            ∑ x ∈ Finset.range (k + 1), fullCoefficient (3 + x + 1) ≤
          (4 / 9 + 8 / 27 + 224 / 2187 : ℝ) +
            ∑ x ∈ Finset.range (k + 1),
              (32 / 3 : ℝ) * ((2 : ℝ) / 9) ^ (x + 4) := by
                rw [show (∑ x ∈ Finset.range 3, fullCoefficient (x + 1)) =
                  (4 / 9 + 8 / 27 + 224 / 2187 : ℝ) by
                    norm_num [fullCoefficient]]
                gcongr
        _ = (4 / 9 + 8 / 27 + 224 / 2187 : ℝ) +
            (32 / 3) * ((2 / 9) ^ 4) *
              ∑ x ∈ Finset.range (k + 1), ((2 : ℝ) / 9) ^ x := by
                have hfactor :
                    (∑ x ∈ Finset.range (k + 1),
                      (32 / 3 : ℝ) * ((2 : ℝ) / 9) ^ (x + 4)) =
                    (32 / 3) * ((2 / 9) ^ 4) *
                      ∑ x ∈ Finset.range (k + 1), ((2 : ℝ) / 9) ^ x := by
                  rw [← Finset.mul_sum, mul_assoc]
                  apply congrArg ((32 / 3 : ℝ) * ·)
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [pow_add]
                  ring
                rw [hfactor]
        _ ≤ (13420 : ℝ) / 15309 := by nlinarith

private theorem finalRemainder_le {i : ℕ} (hi : 2 ≤ i) :
    finalRemainder i ≤ (8 : ℝ) / 81 := by
  have hpow : ((4 : ℝ) / 9) ^ i ≤ ((4 : ℝ) / 9) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
  have hfacNat : 2 ≤ i.factorial := by
    calc
      2 = Nat.factorial 2 := by norm_num
      _ ≤ i.factorial := Nat.factorial_le hi
  have hfac : (2 : ℝ) ≤ i.factorial := by exact_mod_cast hfacNat
  calc
    finalRemainder i ≤ ((4 : ℝ) / 9) ^ 2 / i.factorial := by
      unfold finalRemainder
      gcongr
    _ ≤ ((4 : ℝ) / 9) ^ 2 / 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hfac
    _ = (8 : ℝ) / 81 := by norm_num

private theorem scale_mul_fullCoefficient (w i : ℕ) :
    ((9 : ℝ) * w / 4) ^ i * fullCoefficient i =
      ((w : ℝ) ^ i / i.factorial) * ((2 ^ i - 1 : ℕ) : ℝ) := by
  unfold fullCoefficient
  rw [show (9 : ℝ) * w / 4 = (w : ℝ) * (9 / 4) by ring, mul_pow]
  have hcancel : ((9 : ℝ) / 4) ^ i * ((4 : ℝ) / 9) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((w : ℝ) ^ i * (9 / 4) ^ i) *
        (((2 ^ i - 1 : ℕ) : ℝ) * (4 / 9) ^ i / i.factorial) =
      ((w : ℝ) ^ i / i.factorial) * ((2 ^ i - 1 : ℕ) : ℝ) *
        ((9 / 4) ^ i * (4 / 9) ^ i) := by ring
    _ = _ := by rw [hcancel, mul_one]

private theorem scale_mul_finalCoefficient (w i : ℕ) :
    ((9 : ℝ) * w / 4) ^ i * (fullCoefficient i + finalRemainder i) =
      ((w : ℝ) ^ i / i.factorial) * (2 : ℝ) ^ i := by
  unfold fullCoefficient finalRemainder
  rw [show (9 : ℝ) * w / 4 = (w : ℝ) * (9 / 4) by ring, mul_pow]
  have hcancel : ((9 : ℝ) / 4) ^ i * ((4 : ℝ) / 9) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  have hcast : (((2 ^ i - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ i := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_num
  calc
    ((w : ℝ) ^ i * (9 / 4) ^ i) *
        (((2 ^ i - 1 : ℕ) : ℝ) * (4 / 9) ^ i / i.factorial +
          (4 / 9) ^ i / i.factorial) =
      ((w : ℝ) ^ i / i.factorial) * (((2 ^ i - 1 : ℕ) : ℝ) + 1) *
        ((9 / 4) ^ i * (4 / 9) ^ i) := by ring
    _ = _ := by rw [hcancel, mul_one, hcast]

private theorem choose_full_le (w i : ℕ) :
    ((Nat.choose w i * (2 ^ i - 1) : ℕ) : ℝ) ≤
      ((9 : ℝ) * w / 4) ^ i * fullCoefficient i := by
  have hchoose : (Nat.choose w i : ℝ) ≤ (w : ℝ) ^ i / i.factorial :=
    Nat.choose_le_pow_div i w
  calc
    ((Nat.choose w i * (2 ^ i - 1) : ℕ) : ℝ) =
        (Nat.choose w i : ℝ) * ((2 ^ i - 1 : ℕ) : ℝ) := by norm_num
    _ ≤ ((w : ℝ) ^ i / i.factorial) * ((2 ^ i - 1 : ℕ) : ℝ) := by gcongr
    _ = ((9 : ℝ) * w / 4) ^ i * fullCoefficient i :=
      (scale_mul_fullCoefficient w i).symm

private theorem choose_final_le (w i : ℕ) :
    ((Nat.choose w i * 2 ^ i : ℕ) : ℝ) ≤
      ((9 : ℝ) * w / 4) ^ i * (fullCoefficient i + finalRemainder i) := by
  have hchoose : (Nat.choose w i : ℝ) ≤ (w : ℝ) ^ i / i.factorial :=
    Nat.choose_le_pow_div i w
  calc
    ((Nat.choose w i * 2 ^ i : ℕ) : ℝ) =
        (Nat.choose w i : ℝ) * (2 : ℝ) ^ i := by norm_num
    _ ≤ ((w : ℝ) ^ i / i.factorial) * (2 : ℝ) ^ i := by gcongr
    _ = ((9 : ℝ) * w / 4) ^ i * (fullCoefficient i + finalRemainder i) :=
      (scale_mul_finalCoefficient w i).symm

/-- The sharp code-count estimate needed for the constant `5` in Håstad's Switching Lemma. -/
theorem card_le_scale_pow (w k : ℕ) :
    (Fintype.card (SwitchingCode w k) : ℝ) ≤ ((9 : ℝ) * w / 4) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | m
      · rw [Fintype.card_congr (zeroEquivEmpty w)]
        norm_num
      · rw [card_succ]
        push_cast
        let B : ℝ := 9 * w / 4
        have hfinal :
            (Nat.choose w (m + 1) : ℝ) * 2 ^ (m + 1) ≤
              B ^ (m + 1) * (fullCoefficient (m + 1) + finalRemainder (m + 1)) := by
          simpa [B] using choose_final_le w (m + 1)
        have hblocks :
            (∑ i : Fin m,
                (Nat.choose w ((i : ℕ) + 1) : ℝ) *
                  ((2 ^ ((i : ℕ) + 1) - 1 : ℕ) : ℝ) *
                    (Fintype.card (SwitchingCode w (m - (i : ℕ))) : ℝ)) ≤
              ∑ i : Fin m,
                (B ^ ((i : ℕ) + 1) * fullCoefficient ((i : ℕ) + 1)) *
                  B ^ (m - (i : ℕ)) := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (Nat.choose w ((i : ℕ) + 1) : ℝ) *
                ((2 ^ ((i : ℕ) + 1) - 1 : ℕ) : ℝ) *
                  (Fintype.card (SwitchingCode w (m - (i : ℕ))) : ℝ) ≤
              (B ^ ((i : ℕ) + 1) * fullCoefficient ((i : ℕ) + 1)) *
                (Fintype.card (SwitchingCode w (m - (i : ℕ))) : ℝ) := by
                  exact mul_le_mul_of_nonneg_right
                    (by simpa [B] using choose_full_le w ((i : ℕ) + 1)) (by positivity)
            _ ≤ (B ^ ((i : ℕ) + 1) * fullCoefficient ((i : ℕ) + 1)) *
                B ^ (m - (i : ℕ)) := by
                  gcongr
                  · exact mul_nonneg (by positivity) (by
                      unfold fullCoefficient
                      positivity)
                  · exact ih (m - (i : ℕ)) (by omega)
        have hsumPower :
            (∑ i : Fin m,
                (B ^ ((i : ℕ) + 1) * fullCoefficient ((i : ℕ) + 1)) *
                  B ^ (m - (i : ℕ))) =
              B ^ (m + 1) *
                ∑ i ∈ Finset.range m, fullCoefficient (i + 1) := by
          rw [Fin.sum_univ_eq_sum_range
            (fun i ↦ (B ^ (i + 1) * fullCoefficient (i + 1)) * B ^ (m - i)) m]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have him : i < m := Finset.mem_range.mp hi
          calc
            (B ^ (i + 1) * fullCoefficient (i + 1)) * B ^ (m - i) =
                (B ^ (i + 1) * B ^ (m - i)) * fullCoefficient (i + 1) := by ring
            _ = B ^ (i + 1 + (m - i)) * fullCoefficient (i + 1) := by
              congr 1
              exact (pow_add B (i + 1) (m - i)).symm
            _ = B ^ (m + 1) * fullCoefficient (i + 1) := by
              rw [show i + 1 + (m - i) = m + 1 by omega]
        have hcoefficient :
            (∑ i ∈ Finset.range (m + 1), fullCoefficient (i + 1)) +
                finalRemainder (m + 1) ≤ 1 := by
          rcases m with _ | m
          · norm_num [fullCoefficient, finalRemainder]
          · have hfull := sum_fullCoefficient_range (m + 2)
            have hremainder := finalRemainder_le (i := m + 2) (by omega)
            nlinarith
        calc
          (Nat.choose w (m + 1) : ℝ) * 2 ^ (m + 1) +
              ∑ i : Fin m,
                (Nat.choose w ((i : ℕ) + 1) : ℝ) *
                  ((2 ^ ((i : ℕ) + 1) - 1 : ℕ) : ℝ) *
                    (Fintype.card (SwitchingCode w (m - (i : ℕ))) : ℝ) ≤
            B ^ (m + 1) * (fullCoefficient (m + 1) + finalRemainder (m + 1)) +
              ∑ i : Fin m,
                (B ^ ((i : ℕ) + 1) * fullCoefficient ((i : ℕ) + 1)) *
                  B ^ (m - (i : ℕ)) := add_le_add hfinal hblocks
          _ = B ^ (m + 1) *
              ((∑ i ∈ Finset.range (m + 1), fullCoefficient (i + 1)) +
                finalRemainder (m + 1)) := by
                rw [hsumPower, Finset.sum_range_succ]
                ring
          _ ≤ B ^ (m + 1) * 1 := by gcongr
          _ = ((9 : ℝ) * w / 4) ^ (m + 1) := by simp [B]

end SwitchingCode


/-! ## Canonical trace encoder -/


variable {n w : ℕ}

/-! ## Extension order on restrictions -/

/-- `η` extends `ρ` when it only fixes coordinates that were free in `ρ`. -/
def CoordRestriction.Extends (ρ η : Fin n → CoordRestriction) : Prop :=
  ∀ i, ρ i ≠ .free → η i = ρ i

theorem CoordRestriction.extends_refl (ρ : Fin n → CoordRestriction) :
    CoordRestriction.Extends ρ ρ := by
  intro _ _
  rfl

theorem CoordRestriction.Extends.trans {ρ η τ : Fin n → CoordRestriction}
    (hρη : CoordRestriction.Extends ρ η) (hητ : CoordRestriction.Extends η τ) :
    CoordRestriction.Extends ρ τ := by
  intro i hρ
  have hη : η i ≠ .free := by rw [hρη i hρ]; exact hρ
  rw [hητ i hη, hρη i hρ]

theorem CoordRestriction.Extends.eq_of_ne_free {ρ η : Fin n → CoordRestriction}
    (hρη : CoordRestriction.Extends ρ η) {i : Fin n} (hρ : ρ i ≠ .free) : η i = ρ i :=
  hρη i hρ

theorem CoordRestriction.extends_fixCoordinateList
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n)) (x : 𝔽₂^[n])
    (hfree : ∀ i ∈ coordinates, ρ i = .free) :
    CoordRestriction.Extends ρ (CoordRestriction.fixCoordinateList ρ coordinates x) := by
  intro i hi
  have hinot : i ∉ coordinates := by
    intro himem
    exact hi (hfree i himem)
  rw [CoordRestriction.fixCoordinateList_apply_of_not_mem ρ coordinates x hinot]

theorem DNFTerm.compatible_of_extends (T : DNFTerm n)
    {ρ η : Fin n → CoordRestriction} (hρη : CoordRestriction.Extends ρ η)
    (hT : T.Compatible η) :
    T.Compatible ρ := by
  obtain ⟨x, hx⟩ := hT
  let y : 𝔽₂^[n] := fun i ↦ binarySignEquiv.symm (CoordRestriction.complete η x i)
  refine ⟨y, ?_⟩
  rw [← hx]
  congr 1
  funext i
  cases hρi : ρ i with
  | free =>
      simp only [CoordRestriction.complete, hρi]
      dsimp [y]
      change binarySignEquiv (binarySignEquiv.symm (CoordRestriction.complete η x i)) =
        CoordRestriction.complete η x i
      exact binarySignEquiv.apply_symm_apply _
  | fixOne =>
      have hηi := hρη i (by simp [hρi])
      simp [CoordRestriction.complete, hρi, hηi]
  | fixNegOne =>
      have hηi := hρη i (by simp [hρi])
      simp [CoordRestriction.complete, hρi, hηi]

/-- Once every literal coordinate is fixed, compatibility is preserved by every further
extension. -/
theorem DNFTerm.compatible_of_extends_of_no_free (T : DNFTerm n)
    {ρ η : Fin n → CoordRestriction} (hT : T.Compatible ρ)
    (hfree : T.freeLiteralPositions ρ = ∅)
    (hρη : CoordRestriction.Extends ρ η) : T.Compatible η := by
  obtain ⟨x, hx⟩ := hT
  refine ⟨x, ?_⟩
  rw [DNFTerm.eval_eq_neg_one_iff]
  intro ℓ hℓ
  have hxℓ := (T.eval_eq_neg_one_iff _).1 hx ℓ hℓ
  obtain ⟨j, rfl⟩ := List.get_of_mem hℓ
  have hρfixed : ρ (T.literals.get j).index ≠ .free := by
    intro hstate
    have hj : j ∈ T.freeLiteralPositions ρ :=
      (T.mem_freeLiteralPositions_iff ρ j).2 hstate
    simp [hfree] at hj
  have hη := hρη (T.literals.get j).index hρfixed
  cases hstate : ρ (T.literals.get j).index with
  | free => exact False.elim (hρfixed hstate)
  | fixOne =>
      change (match η (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = (T.literals.get j).required
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = (T.literals.get j).required at hxℓ
      rw [hη]
      exact hxℓ
  | fixNegOne =>
      change (match η (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = (T.literals.get j).required
      change (match ρ (T.literals.get j).index with
        | .free => signEncode (x (T.literals.get j).index)
        | .fixOne => 1
        | .fixNegOne => -1) = (T.literals.get j).required at hxℓ
      rw [hη]
      exact hxℓ

theorem DNFFormula.canonicalTermIndex_eq_of_extends
    (φ : DNFFormula n) {ρ η : Fin n → CoordRestriction}
    (hρ : (φ.compatibleTermIndices ρ).Nonempty)
    (hη : (φ.compatibleTermIndices η).Nonempty)
    (hρη : CoordRestriction.Extends ρ η)
    (hcanonicalη :
      (φ.terms.get (φ.canonicalTermIndex ρ hρ)).Compatible η) :
    φ.canonicalTermIndex η hη = φ.canonicalTermIndex ρ hρ := by
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcanonicalη⟩
  · apply Finset.min'_le
    have hminη := Finset.min'_mem (φ.compatibleTermIndices η) hη
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (φ.terms.get (φ.canonicalTermIndex η hη)).compatible_of_extends
        hρη (Finset.mem_filter.mp hminη).2⟩

/-! ## Coordinate updates and their inverses -/

/-- Free every coordinate in a list and leave all other states unchanged. -/
def CoordRestriction.freeCoordinateList (η : Fin n → CoordRestriction)
    (coordinates : List (Fin n)) : Fin n → CoordRestriction :=
  fun i ↦ if i ∈ coordinates then .free else η i

@[simp] theorem CoordRestriction.freeCoordinateList_apply_of_mem
    (η : Fin n → CoordRestriction) (coordinates : List (Fin n))
    {i : Fin n} (hi : i ∈ coordinates) :
    CoordRestriction.freeCoordinateList η coordinates i = CoordRestriction.free := by
  simp [CoordRestriction.freeCoordinateList, hi]

theorem CoordRestriction.freeCoordinateList_apply_of_not_mem
    (η : Fin n → CoordRestriction) (coordinates : List (Fin n))
    {i : Fin n} (hi : i ∉ coordinates) :
    CoordRestriction.freeCoordinateList η coordinates i = η i := by
  simp [CoordRestriction.freeCoordinateList, hi]

theorem CoordRestriction.freeCoordinateList_fixCoordinateList
    (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n)) (x : 𝔽₂^[n])
    (hfree : ∀ i ∈ coordinates, ρ i = .free) :
    CoordRestriction.freeCoordinateList
      (CoordRestriction.fixCoordinateList ρ coordinates x) coordinates = ρ := by
  funext i
  by_cases hi : i ∈ coordinates
  · rw [CoordRestriction.freeCoordinateList_apply_of_mem _ _ hi, hfree i hi]
  · rw [CoordRestriction.freeCoordinateList_apply_of_not_mem _ _ hi,
      CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi]

theorem CoordRestriction.fixCoordinateList_eq_self
    (η : Fin n → CoordRestriction) (coordinates : List (Fin n)) (x : 𝔽₂^[n])
    (hfixed : ∀ i ∈ coordinates,
      η i = CoordRestriction.fixedState (signEncode (x i))) :
    CoordRestriction.fixCoordinateList η coordinates x = η := by
  induction coordinates generalizing η with
  | nil => rfl
  | cons coordinate coordinates ih =>
      rw [CoordRestriction.fixCoordinateList_cons]
      have hhead := hfixed coordinate (by simp)
      have hupdate :
          CoordRestriction.fixCoordinate η coordinate (signEncode (x coordinate)) = η := by
        funext i
        by_cases hi : i = coordinate
        · subst i
          simp [hhead]
        · exact CoordRestriction.fixCoordinate_apply_of_ne η hi _
      rw [hupdate]
      apply ih
      intro i hi
      exact hfixed i (by simp [hi])

theorem CoordRestriction.fixCoordinateList_apply_of_mem
    (η : Fin n → CoordRestriction) (coordinates : List (Fin n)) (x : 𝔽₂^[n])
    (hnodup : coordinates.Nodup) {i : Fin n} (hi : i ∈ coordinates) :
    CoordRestriction.fixCoordinateList η coordinates x i =
      CoordRestriction.fixedState (signEncode (x i)) := by
  induction coordinates generalizing η with
  | nil => simp at hi
  | cons coordinate coordinates ih =>
      rw [CoordRestriction.fixCoordinateList_cons]
      have htailNodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [CoordRestriction.fixCoordinateList_apply_of_not_mem]
        · simp
        · exact (List.nodup_cons.mp hnodup).1
      · exact ih _ htailNodup hi

/-- Applying the same coordinate overwrite before and after an extension preserves the
extension order. -/
theorem CoordRestriction.Extends.parallel_fixCoordinateList
    {ρ τ : Fin n → CoordRestriction} (coordinates : List (Fin n)) (x y : 𝔽₂^[n])
    (hnodup : coordinates.Nodup)
    (hρτ : CoordRestriction.Extends
      (CoordRestriction.fixCoordinateList ρ coordinates x) τ) :
    CoordRestriction.Extends
      (CoordRestriction.fixCoordinateList ρ coordinates y)
      (CoordRestriction.fixCoordinateList τ coordinates y) := by
  intro i hi
  by_cases himem : i ∈ coordinates
  · rw [CoordRestriction.fixCoordinateList_apply_of_mem _ _ _ hnodup himem,
      CoordRestriction.fixCoordinateList_apply_of_mem _ _ _ hnodup himem]
  · rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ himem,
      CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ himem]
    have hρ : ρ i ≠ .free := by
      rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ himem] at hi
      exact hi
    have hsource : CoordRestriction.fixCoordinateList ρ coordinates x i ≠ .free := by
      rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ himem]
      exact hρ
    calc
      τ i = CoordRestriction.fixCoordinateList ρ coordinates x i := hρτ i hsource
      _ = ρ i := CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ himem

/-- A second assignment on the same duplicate-free coordinate list overwrites the first. -/
theorem CoordRestriction.fixCoordinateList_overwrite
    (η : Fin n → CoordRestriction) (coordinates : List (Fin n)) (x y : 𝔽₂^[n])
    (hnodup : coordinates.Nodup) :
    CoordRestriction.fixCoordinateList
      (CoordRestriction.fixCoordinateList η coordinates x) coordinates y =
        CoordRestriction.fixCoordinateList η coordinates y := by
  funext i
  by_cases hi : i ∈ coordinates
  · rw [CoordRestriction.fixCoordinateList_apply_of_mem _ _ _ hnodup hi,
      CoordRestriction.fixCoordinateList_apply_of_mem _ _ _ hnodup hi]
  · rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi,
      CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi,
      CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi]

/-! ## Literal-position codes -/

/-- Embed a literal position into the ambient width bound. -/
def DNFTerm.positionEmbedding (T : DNFTerm n) (hw : T.width ≤ w) :
    Fin T.literals.length ↪ Fin w where
  toFun j := ⟨j, lt_of_lt_of_le j.isLt hw⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

/-- Position of a support coordinate in the term's literal list. -/
noncomputable def DNFTerm.positionOfSupport (T : DNFTerm n)
    (i : Fin n) (hi : i ∈ T.support) : Fin T.literals.length :=
  Classical.choose (List.get_of_mem (T.literalAt_mem i hi))

theorem DNFTerm.get_positionOfSupport (T : DNFTerm n)
    (i : Fin n) (hi : i ∈ T.support) :
    T.literals.get (T.positionOfSupport i hi) = T.literalAt i hi :=
  Classical.choose_spec (List.get_of_mem (T.literalAt_mem i hi))

theorem DNFTerm.positionOfSupport_index (T : DNFTerm n)
    (i : Fin n) (hi : i ∈ T.support) :
    (T.literals.get (T.positionOfSupport i hi)).index = i := by
  rw [T.get_positionOfSupport i hi, T.literalAt_index i hi]

theorem DNFTerm.positionOfSupport_literal (T : DNFTerm n)
    (j : Fin T.literals.length) :
    T.positionOfSupport (T.literals.get j).index
      (T.mem_support_of_mem_literals (List.get_mem _ _)) = j := by
  apply Fin.ext
  have hleft :
      (T.positionOfSupport (T.literals.get j).index
        (T.mem_support_of_mem_literals (List.get_mem _ _)) : ℕ) <
        (T.literals.map Literal.index).length := by
    simp
  have hright : (j : ℕ) < (T.literals.map Literal.index).length := by
    simp
  exact (List.getElem_inj (h₀ := hleft) (h₁ := hright) T.nodupIndices).1
    (by simpa using (T.positionOfSupport_index (T.literals.get j).index
      (T.mem_support_of_mem_literals (List.get_mem _ _))))

/-- Pull a block's width-bounded positions back to positions of a particular term. -/
noncomputable def SwitchingBlockCode.termPositions (B : SwitchingBlockCode w)
    (T : DNFTerm n) (hw : T.width ≤ w) : Finset (Fin T.literals.length) :=
  B.positions.preimage (T.positionEmbedding hw) (T.positionEmbedding hw).injective.injOn

@[simp] theorem SwitchingBlockCode.termPositions_of_mapped
    (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length))
    (bits : positions.map (T.positionEmbedding hw) → 𝔽₂) :
    (SwitchingBlockCode.ofPositionBits (positions.map (T.positionEmbedding hw)) bits).termPositions
      T hw = positions := by
  exact Finset.preimage_map (T.positionEmbedding hw) positions

/-- Relative path bit at a literal position: zero is the satisfying value. -/
def DNFTerm.relativeBit (T : DNFTerm n) (x : 𝔽₂^[n])
    (j : Fin T.literals.length) : 𝔽₂ :=
  x (T.literals.get j).index + binarySignEquiv.symm (T.literals.get j).required

/-- A canonical width-bounded code for selected positions of one term. -/
noncomputable def DNFTerm.blockCode (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) : SwitchingBlockCode w :=
  SwitchingBlockCode.ofPositionBits (positions.map (T.positionEmbedding hw)) fun q ↦
    T.relativeBit x (Classical.choose (Finset.mem_map.mp q.property))

@[simp] theorem DNFTerm.blockCode_positions (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) :
    (T.blockCode hw positions x).positions = positions.map (T.positionEmbedding hw) := rfl

theorem DNFTerm.blockCode_canonical (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) :
    (T.blockCode hw positions x).Canonical :=
  SwitchingBlockCode.canonical_ofPositionBits _ _

@[simp] theorem DNFTerm.blockCode_termPositions (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) :
    (T.blockCode hw positions x).termPositions T hw = positions := by
  exact SwitchingBlockCode.termPositions_of_mapped T hw positions _

theorem DNFTerm.blockCode_card_positions (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) :
    (T.blockCode hw positions x).positions.card = positions.card := by
  rw [DNFTerm.blockCode_positions, Finset.card_map]

/-- Reconstruct the path assignment recorded by a block, relative to the term's satisfying
assignment. -/
noncomputable def DNFTerm.assignmentOfBlock (T : DNFTerm n) (hw : T.width ≤ w)
    (B : SwitchingBlockCode w) : 𝔽₂^[n] :=
  fun i ↦ if hi : i ∈ T.support then
    B.bits (T.positionEmbedding hw (T.positionOfSupport i hi)) +
      binarySignEquiv.symm (T.requiredAt i hi)
  else 0

theorem DNFTerm.assignmentOfBlock_literal (T : DNFTerm n) (hw : T.width ≤ w)
    (B : SwitchingBlockCode w) (j : Fin T.literals.length) :
    T.assignmentOfBlock hw B (T.literals.get j).index =
      B.bits (T.positionEmbedding hw j) +
        binarySignEquiv.symm (T.literals.get j).required := by
  let hj := T.mem_support_of_mem_literals (List.get_mem T.literals j)
  rw [DNFTerm.assignmentOfBlock, dif_pos hj]
  rw [T.positionOfSupport_literal j]
  have hrequired : T.requiredAt (T.literals.get j).index hj =
      (T.literals.get j).required := by
    unfold DNFTerm.requiredAt
    rw [T.literalAt_eq (List.get_mem T.literals j)]
  rw [hrequired]

theorem DNFTerm.blockCode_bits (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n])
    (j : Fin T.literals.length) (hj : j ∈ positions) :
    (T.blockCode hw positions x).bits (T.positionEmbedding hw j) = T.relativeBit x j := by
  unfold DNFTerm.blockCode SwitchingBlockCode.ofPositionBits
  change (if hi : T.positionEmbedding hw j ∈ positions.map (T.positionEmbedding hw) then
      T.relativeBit x (Classical.choose (Finset.mem_map.mp hi)) else 0) = T.relativeBit x j
  have hmem : T.positionEmbedding hw j ∈ positions.map (T.positionEmbedding hw) :=
    Finset.mem_map.mpr ⟨j, hj, rfl⟩
  rw [dif_pos hmem]
  let witness := Classical.choose (Finset.mem_map.mp hmem)
  have hwitness : witness = j := by
    apply (T.positionEmbedding hw).injective
    exact (Classical.choose_spec (Finset.mem_map.mp hmem)).2
  change T.relativeBit x witness = T.relativeBit x j
  rw [hwitness]

theorem DNFTerm.assignmentOfBlock_blockCode_literal
    (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n])
    (j : Fin T.literals.length) (hj : j ∈ positions) :
    T.assignmentOfBlock hw (T.blockCode hw positions x) (T.literals.get j).index =
      x (T.literals.get j).index := by
  rw [T.assignmentOfBlock_literal, T.blockCode_bits hw positions x j hj]
  unfold DNFTerm.relativeBit
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Read a block's selected literal coordinates without exposing a term-length-dependent type to
the decoder. -/
noncomputable def SwitchingBlockCode.termCoordinates (B : SwitchingBlockCode w)
    (T : DNFTerm n) : List (Fin n) :=
  T.coordinatesAtPositions <|
    Finset.univ.filter fun j : Fin T.literals.length ↦
      if hj : (j : ℕ) < w then (⟨j, hj⟩ : Fin w) ∈ B.positions else False

@[simp] theorem DNFTerm.termCoordinates_blockCode
    (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n]) :
    (T.blockCode hw positions x).termCoordinates T = T.coordinatesAtPositions positions := by
  unfold SwitchingBlockCode.termCoordinates
  congr 1
  ext j
  have hjw : (j : ℕ) < w := lt_of_lt_of_le j.isLt hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, dif_pos hjw,
    DNFTerm.blockCode_positions, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, haj⟩
    have haeq : a = j := by
      apply Fin.ext
      exact congrArg (fun q : Fin w ↦ (q : ℕ)) haj
    simpa [haeq] using ha
  · intro hj
    exact ⟨j, hj, by apply Fin.ext; rfl⟩

/-- Interpret a block as a relative assignment for a term, returning zero when an invalid block
position lies beyond the ambient width. -/
noncomputable def SwitchingBlockCode.assignmentForTerm (B : SwitchingBlockCode w)
    (T : DNFTerm n) : 𝔽₂^[n] :=
  fun i ↦ if hi : i ∈ T.support then
    let j := T.positionOfSupport i hi
    if hj : (j : ℕ) < w then
      B.bits ⟨j, hj⟩ + binarySignEquiv.symm (T.requiredAt i hi)
    else 0
  else 0

theorem SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock
    (B : SwitchingBlockCode w) (T : DNFTerm n) (hw : T.width ≤ w) :
    B.assignmentForTerm T = T.assignmentOfBlock hw B := by
  funext i
  by_cases hi : i ∈ T.support
  · simp only [SwitchingBlockCode.assignmentForTerm, DNFTerm.assignmentOfBlock,
      dif_pos hi]
    have hjw : (T.positionOfSupport i hi : ℕ) < w :=
      lt_of_lt_of_le (T.positionOfSupport i hi).isLt hw
    rw [dif_pos hjw]
    rfl
  · simp [SwitchingBlockCode.assignmentForTerm, DNFTerm.assignmentOfBlock, hi]

theorem DNFTerm.assignmentForTerm_blockCode_literal
    (T : DNFTerm n) (hw : T.width ≤ w)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n])
    (j : Fin T.literals.length) (hj : j ∈ positions) :
    (T.blockCode hw positions x).assignmentForTerm T (T.literals.get j).index =
      x (T.literals.get j).index := by
  rw [SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock _ T hw]
  exact T.assignmentOfBlock_blockCode_literal hw positions x j hj

/-- Canonical binary assignment satisfying every literal of a term. -/
noncomputable def DNFTerm.satisfyingAssignment (T : DNFTerm n) : 𝔽₂^[n] :=
  fun i ↦ if hi : i ∈ T.support then binarySignEquiv.symm (T.requiredAt i hi) else 0

theorem DNFTerm.satisfyingAssignment_literal (T : DNFTerm n)
    (j : Fin T.literals.length) :
    T.satisfyingAssignment (T.literals.get j).index =
      binarySignEquiv.symm (T.literals.get j).required := by
  have hjmem := List.get_mem T.literals j
  have hsupport := T.mem_support_of_mem_literals hjmem
  simp only [DNFTerm.satisfyingAssignment, dif_pos hsupport]
  rw [show T.requiredAt (T.literals.get j).index hsupport =
      (T.literals.get j).required by
    unfold DNFTerm.requiredAt
    rw [T.literalAt_eq hjmem]]

@[simp] theorem DNFTerm.relativeBit_satisfyingAssignment (T : DNFTerm n)
    (j : Fin T.literals.length) : T.relativeBit T.satisfyingAssignment j = 0 := by
  rw [DNFTerm.relativeBit, T.satisfyingAssignment_literal]
  exact CharTwo.add_self_eq_zero _

/-- Fix selected free literals to their satisfying values. -/
noncomputable def DNFTerm.satisfyingExtension (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) (positions : Finset (Fin T.literals.length)) :
    Fin n → CoordRestriction :=
  CoordRestriction.fixCoordinateList ρ (T.coordinatesAtPositions positions)
    T.satisfyingAssignment

/-- Fixing any selected free literals along an assignment that satisfies every free literal
preserves compatibility. -/
theorem DNFTerm.compatible_fix_positions
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction)
    (positions : Finset (Fin T.literals.length)) (x : 𝔽₂^[n])
    (hsubset : positions ⊆ T.freeLiteralPositions ρ) (hcompat : T.Compatible ρ)
    (hzero : ∀ j ∈ T.freeLiteralPositions ρ, T.relativeBit x j = 0) :
    T.Compatible
      (CoordRestriction.fixCoordinateList ρ (T.coordinatesAtPositions positions) x) := by
  obtain ⟨y, hy⟩ := hcompat
  refine ⟨x, ?_⟩
  rw [CoordRestriction.complete_fixCoordinateList ρ
    (T.coordinatesAtPositions positions) x
    (T.coordinatesAtPositions_nodup _)
    (fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff positions i).1 hi
      exact (T.mem_freeLiteralPositions_iff ρ j).1 (hsubset hj))]
  rw [DNFTerm.eval_eq_neg_one_iff]
  intro ℓ hℓ
  obtain ⟨j, rfl⟩ := List.get_of_mem hℓ
  have hyj := (T.eval_eq_neg_one_iff _).1 hy (T.literals.get j) (List.get_mem _ _)
  by_cases hfree : ρ (T.literals.get j).index = .free
  · have hj : j ∈ T.freeLiteralPositions ρ :=
      (T.mem_freeLiteralPositions_iff ρ j).2 hfree
    have hrelative := hzero j hj
    have hself := CharTwo.add_self_eq_zero
      (binarySignEquiv.symm (T.literals.get j).required)
    have hbit : x (T.literals.get j).index =
        binarySignEquiv.symm (T.literals.get j).required := by
      unfold DNFTerm.relativeBit at hrelative
      linear_combination hrelative - hself
    change (match ρ (T.literals.get j).index with
      | .free => signEncode (x (T.literals.get j).index)
      | .fixOne => 1
      | .fixNegOne => -1) = (T.literals.get j).required
    rw [hfree, hbit]
    exact binarySignEquiv.apply_symm_apply _
  · cases hstate : ρ (T.literals.get j).index with
    | free => exact False.elim (hfree hstate)
    | fixOne =>
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (x (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (y (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required at hyj
        rw [hstate] at hyj ⊢
        exact hyj
    | fixNegOne =>
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (x (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (y (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required at hyj
        rw [hstate] at hyj ⊢
        exact hyj

theorem DNFTerm.compatible_fix_freeLiteralPositions
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n])
    (hcompat : T.Compatible ρ)
    (hzero : ∀ j ∈ T.freeLiteralPositions ρ, T.relativeBit x j = 0) :
    T.Compatible
      (CoordRestriction.fixCoordinateList ρ
        (T.coordinatesAtPositions (T.freeLiteralPositions ρ)) x) := by
  obtain ⟨y, hy⟩ := hcompat
  refine ⟨x, ?_⟩
  rw [CoordRestriction.complete_fixCoordinateList ρ
    (T.coordinatesAtPositions (T.freeLiteralPositions ρ)) x
    (T.coordinatesAtPositions_nodup _)
    (T.coordinatesAt_freeLiteralPositions_all_free ρ)]
  rw [DNFTerm.eval_eq_neg_one_iff]
  intro ℓ hℓ
  obtain ⟨j, rfl⟩ := List.get_of_mem hℓ
  have hyj := (T.eval_eq_neg_one_iff _).1 hy (T.literals.get j) (List.get_mem _ _)
  by_cases hfree : ρ (T.literals.get j).index = .free
  · have hj : j ∈ T.freeLiteralPositions ρ :=
      (T.mem_freeLiteralPositions_iff ρ j).2 hfree
    have hrelative := hzero j hj
    have hself := CharTwo.add_self_eq_zero
      (binarySignEquiv.symm (T.literals.get j).required)
    have hbit : x (T.literals.get j).index =
        binarySignEquiv.symm (T.literals.get j).required := by
      unfold DNFTerm.relativeBit at hrelative
      linear_combination hrelative - hself
    change (match ρ (T.literals.get j).index with
      | .free => signEncode (x (T.literals.get j).index)
      | .fixOne => 1
      | .fixNegOne => -1) = (T.literals.get j).required
    rw [hfree, hbit]
    exact binarySignEquiv.apply_symm_apply _
  · cases hstate : ρ (T.literals.get j).index with
    | free => exact False.elim (hfree hstate)
    | fixOne =>
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (x (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (y (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required at hyj
        rw [hstate] at hyj ⊢
        exact hyj
    | fixNegOne =>
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (x (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required
        change (match ρ (T.literals.get j).index with
          | .free => signEncode (y (T.literals.get j).index)
          | .fixOne => 1
          | .fixNegOne => -1) = (T.literals.get j).required at hyj
        rw [hstate] at hyj ⊢
        exact hyj

theorem DNFTerm.blockCode_nonzero_of_not_compatible
    (T : DNFTerm n) (hw : T.width ≤ w) (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n])
    (hcompat : T.Compatible ρ)
    (hincompatible : ¬T.Compatible
      (CoordRestriction.fixCoordinateList ρ
        (T.coordinatesAtPositions (T.freeLiteralPositions ρ)) x)) :
    (T.blockCode hw (T.freeLiteralPositions ρ) x).Nonzero := by
  by_contra hnonzero
  apply hincompatible
  apply T.compatible_fix_freeLiteralPositions ρ x hcompat
  intro j hj
  by_contra hrelative
  have hone : T.relativeBit x j = 1 := Fin.eq_one_of_ne_zero _ hrelative
  apply hnonzero
  refine ⟨T.positionEmbedding hw j, ?_, ?_⟩
  · rw [T.blockCode_positions]
    exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
  · rw [T.blockCode_bits hw (T.freeLiteralPositions ρ) x j hj, hone]

theorem DNFTerm.satisfyingExtension_compatible
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) (hcompat : T.Compatible ρ) :
    T.Compatible (T.satisfyingExtension ρ (T.freeLiteralPositions ρ)) := by
  apply T.compatible_fix_freeLiteralPositions ρ T.satisfyingAssignment hcompat
  intro j hj
  exact T.relativeBit_satisfyingAssignment j


/-! ## Switching traces from deep restricted decision trees -/


variable {n w : ℕ}

namespace CoordinateDecisionTree

variable {α : Type*}

/-- If a list-query tree has depth beyond the queried list, one continuation has the
corresponding residual depth. -/
theorem exists_finish_depth_ge_sub_of_depth_queryCoordinates
    (coordinates : List (Fin n)) (seed : 𝔽₂^[n])
    (finish : 𝔽₂^[n] → CoordinateDecisionTree n α) (k : ℕ)
    (hdepth : k ≤ (queryCoordinates coordinates seed finish).depth)
    (hlength : coordinates.length < k) :
    ∃ x, k - coordinates.length ≤ (finish x).depth := by
  induction coordinates generalizing seed k with
  | nil =>
      exact ⟨seed, by simpa [queryCoordinates] using hdepth⟩
  | cons coordinate coordinates ih =>
      simp only [queryCoordinates, depth] at hdepth
      simp only [List.length_cons] at hlength
      have hk : 0 < k := by omega
      have hmax : k - 1 ≤
          max
            (queryCoordinates coordinates (Function.update seed coordinate 0) finish).depth
            (queryCoordinates coordinates (Function.update seed coordinate 1) finish).depth := by
        omega
      rcases le_max_iff.mp hmax with hzero | hone
      · obtain ⟨x, hx⟩ :=
          ih (Function.update seed coordinate 0) (k - 1) hzero (by omega)
        refine ⟨x, ?_⟩
        simp only [List.length_cons]
        have hsub : k - (coordinates.length + 1) = k - 1 - coordinates.length := by
          omega
        rw [hsub]
        exact hx
      · obtain ⟨x, hx⟩ :=
          ih (Function.update seed coordinate 1) (k - 1) hone (by omega)
        refine ⟨x, ?_⟩
        simp only [List.length_cons]
        have hsub : k - (coordinates.length + 1) = k - 1 - coordinates.length := by
          omega
        rw [hsub]
        exact hx

end CoordinateDecisionTree

/-! ## Traces through the canonical block tree -/

/-- The first compatible term, packaged for reuse in the switching trace. -/
noncomputable def DNFFormula.canonicalTerm (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    DNFTerm n :=
  φ.terms.get (φ.canonicalTermIndex ρ hcompat)

theorem DNFFormula.canonicalTerm_mem (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    φ.canonicalTerm ρ hcompat ∈ φ.terms :=
  List.get_mem φ.terms (φ.canonicalTermIndex ρ hcompat)

theorem DNFFormula.canonicalTerm_width_le (φ : DNFFormula n) {w : ℕ}
    (hw : φ.width ≤ w) (ρ : Fin n → CoordRestriction)
    (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    (φ.canonicalTerm ρ hcompat).width ≤ w :=
  (φ.width_le_of_mem (φ.canonicalTerm_mem ρ hcompat)).trans hw

theorem DNFFormula.canonicalTerm_compatible' (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hcompat : (φ.compatibleTermIndices ρ).Nonempty) :
    (φ.canonicalTerm ρ hcompat).Compatible ρ :=
  φ.canonicalTerm_compatible ρ hcompat

/-- A positive-length path through the canonical block tree. A final constructor stops inside
one term block; a `cons` constructor records a complete falsified block and continues. -/
inductive DNFFormula.SwitchingTrace (φ : DNFFormula n) :
    (Fin n → CoordRestriction) → ℕ → Type
  | final {ρ : Fin n → CoordRestriction} {k : ℕ}
      (hcompat : (φ.compatibleTermIndices ρ).Nonempty)
      (positions : Finset (Fin (φ.canonicalTerm ρ hcompat).literals.length))
      (hsubset : positions ⊆ (φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ)
      (hcard : positions.card = k + 1) :
      φ.SwitchingTrace ρ (k + 1)
  | cons {ρ : Fin n → CoordRestriction} {k : ℕ}
      (hcompat : (φ.compatibleTermIndices ρ).Nonempty) (i : Fin k) (x : 𝔽₂^[n])
      (hcard : ((φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ).card = i + 1)
      (hincompatible : ¬(φ.canonicalTerm ρ hcompat).Compatible
        (CoordRestriction.fixCoordinateList ρ
          ((φ.canonicalTerm ρ hcompat).coordinatesAtPositions
            ((φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ)) x))
      (tail : φ.SwitchingTrace
        (CoordRestriction.fixCoordinateList ρ
          ((φ.canonicalTerm ρ hcompat).coordinatesAtPositions
            ((φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ)) x)
        (k - i)) :
      φ.SwitchingTrace ρ (k + 1)

/-- A positive-depth path in the canonical block tree yields a switching trace of the same
length. -/
theorem DNFFormula.nonempty_switchingTrace_of_depth_canonicalBlockTreeAux
    (φ : DNFFormula n) (fuel : ℕ) (ρ : Fin n → CoordRestriction) (k : ℕ)
    (hdepth : k + 1 ≤ (φ.canonicalBlockTreeAux fuel ρ).depth) :
    Nonempty (φ.SwitchingTrace ρ (k + 1)) := by
  induction fuel generalizing ρ k with
  | zero =>
      simp [DNFFormula.canonicalBlockTreeAux, CoordinateDecisionTree.depth] at hdepth
  | succ fuel ih =>
      rw [DNFFormula.canonicalBlockTreeAux] at hdepth
      by_cases hcompat : (φ.compatibleTermIndices ρ).Nonempty
      · rw [dif_pos hcompat] at hdepth
        let T := φ.terms.get (φ.canonicalTermIndex ρ hcompat)
        let positions := T.freeLiteralPositions ρ
        by_cases hpositions : positions.Nonempty
        · rw [dif_pos hpositions] at hdepth
          let coordinates := T.coordinatesAtPositions positions
          by_cases hwithin : k + 1 ≤ positions.card
          · obtain ⟨selected, hselected, hcard⟩ :=
              Finset.exists_subset_card_eq hwithin
            exact ⟨DNFFormula.SwitchingTrace.final hcompat selected
              (by
                change selected ⊆ positions
                exact hselected) hcard⟩
          · have hlength : coordinates.length < k + 1 := by
              simpa [coordinates, DNFTerm.coordinatesAtPositions] using
                (lt_of_not_ge hwithin)
            obtain ⟨x, hx⟩ :=
              CoordinateDecisionTree.exists_finish_depth_ge_sub_of_depth_queryCoordinates
                coordinates 0
                  (fun x ↦
                    let η := CoordRestriction.fixCoordinateList ρ coordinates x
                    if T.Compatible η then .leaf (-1)
                    else φ.canonicalBlockTreeAux fuel η)
                  (k + 1) hdepth hlength
            let η := CoordRestriction.fixCoordinateList ρ coordinates x
            have hresidual : 0 < k + 1 - positions.card := by omega
            have hcoordinateLength : coordinates.length = positions.card := by
              simp [coordinates, DNFTerm.coordinatesAtPositions]
            have hincompatible : ¬T.Compatible η := by
              intro hT
              change k + 1 - coordinates.length ≤
                (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                  else φ.canonicalBlockTreeAux fuel η).depth at hx
              rw [if_pos hT] at hx
              simp only [CoordinateDecisionTree.depth] at hx
              omega
            have htailDepth : k + 1 - positions.card ≤
                (φ.canonicalBlockTreeAux fuel η).depth := by
              change k + 1 - coordinates.length ≤
                (if T.Compatible η then CoordinateDecisionTree.leaf (-1)
                  else φ.canonicalBlockTreeAux fuel η).depth at hx
              rw [if_neg hincompatible] at hx
              simpa [hcoordinateLength] using hx
            have hpositionsCard : 0 < positions.card := Finset.card_pos.mpr hpositions
            let i : Fin k := ⟨positions.card - 1, by omega⟩
            have hcard : positions.card = (i : ℕ) + 1 := by
              simp only [i]
              omega
            have htailIndex : k - (i : ℕ) = k + 1 - positions.card := by
              simp only [i]
              omega
            have htailPositive : 1 ≤ k - (i : ℕ) := by
              rw [htailIndex]
              exact hresidual
            have htailDepth' : k - (i : ℕ) ≤
                (φ.canonicalBlockTreeAux fuel η).depth := by
              rwa [htailIndex]
            have htail := ih η (k - (i : ℕ) - 1) (by
              rw [Nat.sub_add_cancel htailPositive]
              exact htailDepth')
            rw [Nat.sub_add_cancel htailPositive] at htail
            obtain ⟨tail⟩ := htail
            exact ⟨DNFFormula.SwitchingTrace.cons hcompat i x
              (by simpa [DNFFormula.canonicalTerm, T, positions] using hcard)
              (by simpa [DNFFormula.canonicalTerm, T, positions, coordinates, η]
                using hincompatible) tail⟩
        · rw [dif_neg hpositions] at hdepth
          simp only [CoordinateDecisionTree.depth] at hdepth
          omega
      · rw [dif_neg hcompat] at hdepth
        simp only [CoordinateDecisionTree.depth] at hdepth
        omega

/-- Every restriction whose restricted DNF has decision-tree depth at least `k + 1` carries a
canonical switching trace of that length. -/
theorem DNFFormula.nonempty_switchingTrace_of_decisionTreeDepth
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction) (k : ℕ)
    (hdepth : k + 1 ≤
      F₂DecisionTree.decisionTreeDepth (CoordRestriction.restrict φ.toBooleanFunction ρ)) :
    Nonempty (φ.SwitchingTrace ρ (k + 1)) := by
  apply φ.nonempty_switchingTrace_of_depth_canonicalBlockTreeAux n ρ k
  calc
    k + 1 ≤ F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict φ.toBooleanFunction ρ) := hdepth
    _ ≤ (φ.canonicalBlockTree ρ).depth :=
      φ.decisionTreeDepth_le_canonicalBlockTree_depth ρ
    _ = (φ.canonicalBlockTreeAux n ρ).depth := by
      simp [DNFFormula.canonicalBlockTree, DNFFormula.canonicalBlockTreeRaw]

namespace DNFFormula.SwitchingTrace

variable {φ : DNFFormula n}

/-- The restriction obtained by replacing every recorded path block by its satisfying values. -/
noncomputable def target : {k : ℕ} → {ρ : Fin n → CoordRestriction} →
    φ.SwitchingTrace ρ k → Fin n → CoordRestriction
  | _, ρ, .final hcompat positions _ _ =>
      (φ.canonicalTerm ρ hcompat).satisfyingExtension ρ positions
  | _, ρ, .cons hcompat _ _ _ _ tail =>
      (φ.canonicalTerm ρ hcompat).satisfyingExtension tail.target
        ((φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ)

/-- The finite block code carried by a trace. -/
noncomputable def code (hw : φ.width ≤ w) : {k : ℕ} →
    {ρ : Fin n → CoordRestriction} → φ.SwitchingTrace ρ k → SwitchingCode w k
  | _, ρ, .final hcompat positions _ hcard =>
      .final ⟨(φ.canonicalTerm ρ hcompat).blockCode
          (φ.canonicalTerm_width_le hw ρ hcompat) positions
          (φ.canonicalTerm ρ hcompat).satisfyingAssignment,
        (φ.canonicalTerm ρ hcompat).blockCode_canonical _ _ _,
        ((φ.canonicalTerm ρ hcompat).blockCode_card_positions
          (φ.canonicalTerm_width_le hw ρ hcompat) positions
          (φ.canonicalTerm ρ hcompat).satisfyingAssignment).trans hcard⟩
  | _, ρ, .cons hcompat i x hcard hincompatible tail =>
      .cons i ⟨(φ.canonicalTerm ρ hcompat).blockCode
          (φ.canonicalTerm_width_le hw ρ hcompat)
          ((φ.canonicalTerm ρ hcompat).freeLiteralPositions ρ) x,
        (φ.canonicalTerm ρ hcompat).blockCode_canonical _ _ _,
        by simpa using hcard,
        (φ.canonicalTerm ρ hcompat).blockCode_nonzero_of_not_compatible
          (φ.canonicalTerm_width_le hw ρ hcompat) ρ x
          (φ.canonicalTerm_compatible' ρ hcompat) hincompatible⟩
        (tail.code hw)

end DNFFormula.SwitchingTrace


/-! ## Decoder and encoder left inverse -/


variable {n w : ℕ}

/-- Decode a finite switching code against its target restriction. Invalid codes leave the
current restriction unchanged; codes produced by canonical traces are inverted exactly. -/
noncomputable def DNFFormula.decodeSwitchingCode (φ : DNFFormula n) (hw : φ.width ≤ w) :
    {k : ℕ} → (Fin n → CoordRestriction) → SwitchingCode w k →
      Fin n → CoordRestriction
  | _, η, .final block =>
      if hcompat : (φ.compatibleTermIndices η).Nonempty then
        let T := φ.canonicalTerm η hcompat
        CoordRestriction.freeCoordinateList η (block.1.termCoordinates T)
      else η
  | _, η, .cons _ block tail =>
      if hcompat : (φ.compatibleTermIndices η).Nonempty then
        let T := φ.canonicalTerm η hcompat
        let coordinates := block.1.termCoordinates T
        let τ := CoordRestriction.fixCoordinateList η coordinates
          (block.1.assignmentForTerm T)
        CoordRestriction.freeCoordinateList
          (φ.decodeSwitchingCode hw τ tail) coordinates
      else η

theorem DNFFormula.canonicalTerm_eq_of_extends (φ : DNFFormula n)
    {ρ η : Fin n → CoordRestriction}
    (hρ : (φ.compatibleTermIndices ρ).Nonempty)
    (hη : (φ.compatibleTermIndices η).Nonempty)
    (hρη : CoordRestriction.Extends ρ η)
    (hcanonicalη : (φ.canonicalTerm ρ hρ).Compatible η) :
    φ.canonicalTerm η hη = φ.canonicalTerm ρ hρ := by
  unfold DNFFormula.canonicalTerm
  rw [φ.canonicalTermIndex_eq_of_extends hρ hη hρη hcanonicalη]

namespace DNFFormula.SwitchingTrace

variable {φ : DNFFormula n} {ρ : Fin n → CoordRestriction} {k : ℕ}

/-- A trace target extends its source, and the source's first compatible term is compatible with
the target. -/
theorem target_extends_and_canonical_compatible (tr : φ.SwitchingTrace ρ k) :
    CoordRestriction.Extends ρ tr.target ∧
      ∃ hcompat : (φ.compatibleTermIndices ρ).Nonempty,
        (φ.canonicalTerm ρ hcompat).Compatible tr.target := by
  induction tr with
  | @final ρ k hcompat positions hsubset hcard =>
      let T := φ.canonicalTerm ρ hcompat
      let coordinates := T.coordinatesAtPositions positions
      have hfree : ∀ i ∈ coordinates, ρ i = .free := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff positions i).1 hi
        exact (T.mem_freeLiteralPositions_iff ρ j).1 (hsubset hj)
      constructor
      · simpa [target, DNFTerm.satisfyingExtension, T, coordinates] using
          CoordRestriction.extends_fixCoordinateList ρ coordinates
            T.satisfyingAssignment hfree
      · refine ⟨hcompat, ?_⟩
        simpa [target, DNFTerm.satisfyingExtension, T, coordinates] using
          T.compatible_fix_positions ρ positions T.satisfyingAssignment hsubset
            (φ.canonicalTerm_compatible' ρ hcompat)
            (fun j _ ↦ T.relativeBit_satisfyingAssignment j)
  | @cons ρ k hcompat i x hcard hincompatible tail ih =>
      let T := φ.canonicalTerm ρ hcompat
      let positions := T.freeLiteralPositions ρ
      let coordinates := T.coordinatesAtPositions positions
      let η := CoordRestriction.fixCoordinateList ρ coordinates x
      let σ := CoordRestriction.fixCoordinateList ρ coordinates T.satisfyingAssignment
      have hcoordinatesFree : ∀ j ∈ coordinates, ρ j = .free := by
        simpa [T, positions, coordinates] using
          T.coordinatesAt_freeLiteralPositions_all_free ρ
      have hρσ : CoordRestriction.Extends ρ σ := by
        exact CoordRestriction.extends_fixCoordinateList ρ coordinates
          T.satisfyingAssignment hcoordinatesFree
      have hηtarget : CoordRestriction.Extends η tail.target := by
        simpa [η] using ih.1
      have hσtarget : CoordRestriction.Extends σ
          (CoordRestriction.fixCoordinateList tail.target coordinates
            T.satisfyingAssignment) := by
        have hparallel := hηtarget.parallel_fixCoordinateList coordinates x
          T.satisfyingAssignment (T.coordinatesAtPositions_nodup positions)
        simpa [η, σ] using hparallel
      constructor
      · simpa [target, DNFTerm.satisfyingExtension, T, positions, coordinates] using
          hρσ.trans hσtarget
      · refine ⟨hcompat, ?_⟩
        have hTσ : T.Compatible σ := by
          simpa [σ, DNFTerm.satisfyingExtension, positions, coordinates] using
            T.satisfyingExtension_compatible ρ (φ.canonicalTerm_compatible' ρ hcompat)
        have hnoFree : T.freeLiteralPositions σ = ∅ := by
          simpa [σ, positions, coordinates] using
            T.freeLiteralPositions_fixCoordinateList_eq_empty ρ T.satisfyingAssignment
        simpa [target, DNFTerm.satisfyingExtension, T, positions, coordinates] using
          T.compatible_of_extends_of_no_free hTσ hnoFree hσtarget

theorem target_extends (tr : φ.SwitchingTrace ρ k) :
    CoordRestriction.Extends ρ tr.target :=
  tr.target_extends_and_canonical_compatible.1

theorem exists_canonical_compatible_target (tr : φ.SwitchingTrace ρ k) :
    ∃ hcompat : (φ.compatibleTermIndices ρ).Nonempty,
      (φ.canonicalTerm ρ hcompat).Compatible tr.target :=
  tr.target_extends_and_canonical_compatible.2

/-- The target restriction and finite code determine the source restriction exactly. -/
theorem decode_target_code (tr : φ.SwitchingTrace ρ k) (hw : φ.width ≤ w) :
    φ.decodeSwitchingCode hw tr.target (tr.code hw) = ρ := by
  induction tr with
  | @final ρ k hcompat positions hsubset hcard =>
      let T := φ.canonicalTerm ρ hcompat
      let coordinates := T.coordinatesAtPositions positions
      let η := CoordRestriction.fixCoordinateList ρ coordinates T.satisfyingAssignment
      have hfree : ∀ i ∈ coordinates, ρ i = .free := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff positions i).1 hi
        exact (T.mem_freeLiteralPositions_iff ρ j).1 (hsubset hj)
      have hρη : CoordRestriction.Extends ρ η :=
        CoordRestriction.extends_fixCoordinateList ρ coordinates
          T.satisfyingAssignment hfree
      have hTη : T.Compatible η := by
        exact T.compatible_fix_positions ρ positions T.satisfyingAssignment hsubset
          (φ.canonicalTerm_compatible' ρ hcompat)
          (fun j _ ↦ T.relativeBit_satisfyingAssignment j)
      have hηcompat : (φ.compatibleTermIndices η).Nonempty := by
        refine ⟨φ.canonicalTermIndex ρ hcompat, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa [T, DNFFormula.canonicalTerm] using hTη
      have hterm : φ.canonicalTerm η hηcompat = T := by
        simpa [T] using
          φ.canonicalTerm_eq_of_extends hcompat hηcompat hρη (by simpa [T] using hTη)
      simp only [target, code, DNFFormula.decodeSwitchingCode,
        DNFTerm.satisfyingExtension]
      rw [dif_pos (by simpa [η, coordinates, T] using hηcompat)]
      change CoordRestriction.freeCoordinateList η
        ((T.blockCode (φ.canonicalTerm_width_le hw ρ hcompat) positions
          T.satisfyingAssignment).termCoordinates
            (φ.canonicalTerm η hηcompat)) = ρ
      rw [hterm, DNFTerm.termCoordinates_blockCode]
      exact CoordRestriction.freeCoordinateList_fixCoordinateList ρ coordinates
        T.satisfyingAssignment hfree
  | @cons ρ k hcompat i x hcard hincompatible tail ih =>
      let T := φ.canonicalTerm ρ hcompat
      let positions := T.freeLiteralPositions ρ
      let coordinates := T.coordinatesAtPositions positions
      let η := CoordRestriction.fixCoordinateList ρ coordinates x
      let outer := CoordRestriction.fixCoordinateList tail.target coordinates
        T.satisfyingAssignment
      have hfree : ∀ j ∈ coordinates, ρ j = .free := by
        simpa [T, positions, coordinates] using
          T.coordinatesAt_freeLiteralPositions_all_free ρ
      have hηtail : CoordRestriction.Extends η tail.target := by
        simpa [η] using tail.target_extends
      have hρouter : CoordRestriction.Extends ρ outer := by
        have hρsat := CoordRestriction.extends_fixCoordinateList ρ coordinates
          T.satisfyingAssignment hfree
        have hparallel := hηtail.parallel_fixCoordinateList coordinates x
          T.satisfyingAssignment (T.coordinatesAtPositions_nodup positions)
        exact hρsat.trans (by simpa [η, outer] using hparallel)
      have hTouter : T.Compatible outer := by
        let sat := CoordRestriction.fixCoordinateList ρ coordinates T.satisfyingAssignment
        have hTsat : T.Compatible sat := by
          simpa [sat, positions, coordinates, DNFTerm.satisfyingExtension] using
            T.satisfyingExtension_compatible ρ (φ.canonicalTerm_compatible' ρ hcompat)
        have hnoFree : T.freeLiteralPositions sat = ∅ := by
          simpa [sat, positions, coordinates] using
            T.freeLiteralPositions_fixCoordinateList_eq_empty ρ T.satisfyingAssignment
        have hsattarget : CoordRestriction.Extends sat outer := by
          have hparallel := hηtail.parallel_fixCoordinateList coordinates x
            T.satisfyingAssignment (T.coordinatesAtPositions_nodup positions)
          simpa [sat, η, outer] using hparallel
        exact T.compatible_of_extends_of_no_free hTsat hnoFree hsattarget
      have houterCompat : (φ.compatibleTermIndices outer).Nonempty := by
        refine ⟨φ.canonicalTermIndex ρ hcompat, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa [T, DNFFormula.canonicalTerm] using hTouter
      have hterm : φ.canonicalTerm outer houterCompat = T := by
        simpa [T] using φ.canonicalTerm_eq_of_extends hcompat houterCompat hρouter
          (by simpa [T] using hTouter)
      let hT : T.width ≤ w := φ.canonicalTerm_width_le hw ρ hcompat
      let y := T.assignmentOfBlock hT (T.blockCode hT positions x)
      have hdecodeAssignment :
          (T.blockCode hT positions x).assignmentForTerm T = y := by
        rw [SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock _ T hT]
      have hy : ∀ q ∈ coordinates, y q = x q := by
        intro q hq
        obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff positions q).1 hq
        exact T.assignmentOfBlock_blockCode_literal hT positions x j hj
      have hfixedTail : ∀ q ∈ coordinates,
          tail.target q = CoordRestriction.fixedState (signEncode (y q)) := by
        intro q hq
        have hηq := CoordRestriction.fixCoordinateList_apply_of_mem ρ coordinates x
          (T.coordinatesAtPositions_nodup positions) hq
        have hηqFixed : η q ≠ .free := by
          change CoordRestriction.fixCoordinateList ρ coordinates x q ≠ .free
          rw [hηq]
          exact CoordRestriction.fixedState_ne_free _
        calc
          tail.target q = η q := hηtail q hηqFixed
          _ = CoordRestriction.fixedState (signEncode (x q)) := hηq
          _ = CoordRestriction.fixedState (signEncode (y q)) := by rw [hy q hq]
      have hrestore : CoordRestriction.fixCoordinateList outer coordinates y = tail.target := by
        change CoordRestriction.fixCoordinateList
          (CoordRestriction.fixCoordinateList tail.target coordinates T.satisfyingAssignment)
            coordinates y = tail.target
        rw [CoordRestriction.fixCoordinateList_overwrite tail.target coordinates
          T.satisfyingAssignment y (T.coordinatesAtPositions_nodup positions)]
        exact CoordRestriction.fixCoordinateList_eq_self tail.target coordinates y hfixedTail
      simp only [target, code, DNFFormula.decodeSwitchingCode,
        DNFTerm.satisfyingExtension]
      rw [dif_pos (by simpa [outer, coordinates, positions, T] using houterCompat)]
      change CoordRestriction.freeCoordinateList
        (φ.decodeSwitchingCode hw
          (CoordRestriction.fixCoordinateList outer
            ((T.blockCode hT positions x).termCoordinates
              (φ.canonicalTerm outer houterCompat))
            ((T.blockCode hT positions x).assignmentForTerm
              (φ.canonicalTerm outer houterCompat)))
          (tail.code hw))
        ((T.blockCode hT positions x).termCoordinates
          (φ.canonicalTerm outer houterCompat)) = ρ
      rw [hterm, DNFTerm.termCoordinates_blockCode, hdecodeAssignment]
      change CoordRestriction.freeCoordinateList
        (φ.decodeSwitchingCode hw
          (CoordRestriction.fixCoordinateList outer coordinates y) (tail.code hw))
        coordinates = ρ
      rw [hrestore, ih]
      exact CoordRestriction.freeCoordinateList_fixCoordinateList ρ coordinates x hfree

end DNFFormula.SwitchingTrace


/-! ## Exact restriction-weight identity -/


variable {n w : ℕ}

/-- Exact source-to-target atom ratio when one free coordinate is fixed. -/
noncomputable def switchingAtomRatio (δ : ℝ) : ℝ :=
  2 * δ / (1 - δ)

theorem restrictionAssignmentWeightAt_fixCoordinate
    {δ : ℝ} (hδ : δ < 1) (ρ : Fin n → CoordRestriction)
    (i : Fin n) (s : Sign) (hfree : ρ i = .free) :
    restrictionAssignmentWeightAt δ ρ =
      switchingAtomRatio δ *
        restrictionAssignmentWeightAt δ (CoordRestriction.fixCoordinate ρ i s) := by
  let P := ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    coordRestrictionWeightAt δ (ρ j)
  have hsource : restrictionAssignmentWeightAt δ ρ = δ * P := by
    rw [restrictionAssignmentWeightAt,
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j ↦ coordRestrictionWeightAt δ (ρ j)) (Finset.mem_univ i)]
    rw [hfree]
    rfl
  have htarget :
      restrictionAssignmentWeightAt δ (CoordRestriction.fixCoordinate ρ i s) =
        ((1 - δ) / 2) * P := by
    rw [restrictionAssignmentWeightAt,
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j ↦ coordRestrictionWeightAt δ (CoordRestriction.fixCoordinate ρ i s j))
        (Finset.mem_univ i)]
    rw [CoordRestriction.fixCoordinate_apply_self, coordRestrictionWeightAt_fixedState]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [CoordRestriction.fixCoordinate_apply_of_ne ρ (Finset.ne_of_mem_erase hj) s]
  rw [hsource, htarget]
  unfold switchingAtomRatio
  have hden : 1 - δ ≠ 0 := by linarith
  field_simp

theorem restrictionAssignmentWeightAt_fixCoordinateList
    {δ : ℝ} (hδ : δ < 1) (ρ : Fin n → CoordRestriction)
    (coordinates : List (Fin n)) (x : 𝔽₂^[n])
    (hnodup : coordinates.Nodup) (hfree : ∀ i ∈ coordinates, ρ i = .free) :
    restrictionAssignmentWeightAt δ ρ =
      switchingAtomRatio δ ^ coordinates.length *
        restrictionAssignmentWeightAt δ
          (CoordRestriction.fixCoordinateList ρ coordinates x) := by
  induction coordinates generalizing ρ with
  | nil => simp
  | cons i coordinates ih =>
      let η := CoordRestriction.fixCoordinate ρ i (signEncode (x i))
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have htailFree : ∀ j ∈ coordinates, η j = .free := by
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst j
          exact (List.nodup_cons.mp hnodup).1 hj
        change CoordRestriction.fixCoordinate ρ i (signEncode (x i)) j = .free
        rw [CoordRestriction.fixCoordinate_apply_of_ne ρ hji]
        exact hfree j (by simp [hj])
      calc
        restrictionAssignmentWeightAt δ ρ =
            switchingAtomRatio δ * restrictionAssignmentWeightAt δ η :=
          restrictionAssignmentWeightAt_fixCoordinate hδ ρ i
            (signEncode (x i)) (hfree i (by simp))
        _ = switchingAtomRatio δ *
            (switchingAtomRatio δ ^ coordinates.length *
              restrictionAssignmentWeightAt δ
                (CoordRestriction.fixCoordinateList η coordinates x)) := by
          rw [ih η htailNodup htailFree]
        _ = switchingAtomRatio δ ^ (i :: coordinates).length *
            restrictionAssignmentWeightAt δ
              (CoordRestriction.fixCoordinateList ρ (i :: coordinates) x) := by
          rw [CoordRestriction.fixCoordinateList_cons, List.length_cons, pow_succ']
          dsimp [η]
          ring

/-- Changing signs on coordinates that are already fixed preserves restriction weight. -/
theorem restrictionAssignmentWeightAt_fixCoordinateList_of_all_fixed
    (δ : ℝ) (ρ : Fin n → CoordRestriction) (coordinates : List (Fin n))
    (x : 𝔽₂^[n]) (hnodup : coordinates.Nodup)
    (hfixed : ∀ i ∈ coordinates, ρ i ≠ .free) :
    restrictionAssignmentWeightAt δ
      (CoordRestriction.fixCoordinateList ρ coordinates x) =
        restrictionAssignmentWeightAt δ ρ := by
  unfold restrictionAssignmentWeightAt
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ coordinates
  · have hvalue := CoordRestriction.fixCoordinateList_apply_of_mem ρ coordinates x
      hnodup hi
    rw [hvalue, coordRestrictionWeightAt_fixedState]
    cases hstate : ρ i with
    | free => exact False.elim (hfixed i hi hstate)
    | fixOne => rfl
    | fixNegOne => rfl
  · rw [CoordRestriction.fixCoordinateList_apply_of_not_mem _ _ _ hi]

namespace DNFFormula.SwitchingTrace

variable {φ : DNFFormula n} {ρ : Fin n → CoordRestriction} {k : ℕ}

/-- Exact atom-weight identity for a canonical switching trace. -/
theorem restrictionAssignmentWeightAt_eq_ratio_pow_target
    (tr : φ.SwitchingTrace ρ k) {δ : ℝ} (hδ : δ < 1) :
    restrictionAssignmentWeightAt δ ρ =
      switchingAtomRatio δ ^ k * restrictionAssignmentWeightAt δ tr.target := by
  induction tr with
  | @final ρ k hcompat positions hsubset hcard =>
      let T := φ.canonicalTerm ρ hcompat
      let coordinates := T.coordinatesAtPositions positions
      have hfree : ∀ i ∈ coordinates, ρ i = .free := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := (T.mem_coordinatesAtPositions_iff positions i).1 hi
        exact (T.mem_freeLiteralPositions_iff ρ j).1 (hsubset hj)
      have hweight := restrictionAssignmentWeightAt_fixCoordinateList hδ ρ coordinates
        T.satisfyingAssignment (T.coordinatesAtPositions_nodup positions) hfree
      simpa [target, DNFTerm.satisfyingExtension, T, coordinates,
        DNFTerm.coordinatesAtPositions, hcard] using hweight
  | @cons ρ k hcompat i x hcard hincompatible tail ih =>
      let T := φ.canonicalTerm ρ hcompat
      let positions := T.freeLiteralPositions ρ
      let coordinates := T.coordinatesAtPositions positions
      let η := CoordRestriction.fixCoordinateList ρ coordinates x
      let outer := CoordRestriction.fixCoordinateList tail.target coordinates
        T.satisfyingAssignment
      have hfree : ∀ q ∈ coordinates, ρ q = .free := by
        simpa [T, positions, coordinates] using
          T.coordinatesAt_freeLiteralPositions_all_free ρ
      have hsource := restrictionAssignmentWeightAt_fixCoordinateList hδ ρ coordinates x
        (T.coordinatesAtPositions_nodup positions) hfree
      have hηtail : CoordRestriction.Extends η tail.target := by
        simpa [η] using tail.target_extends
      have hfixed : ∀ q ∈ coordinates, tail.target q ≠ .free := by
        intro q hq
        have hηq := CoordRestriction.fixCoordinateList_apply_of_mem ρ coordinates x
          (T.coordinatesAtPositions_nodup positions) hq
        have hηqFixed : η q ≠ .free := by
          change CoordRestriction.fixCoordinateList ρ coordinates x q ≠ .free
          rw [hηq]
          exact CoordRestriction.fixedState_ne_free _
        rw [hηtail q hηqFixed]
        exact hηqFixed
      have houterWeight : restrictionAssignmentWeightAt δ outer =
          restrictionAssignmentWeightAt δ tail.target := by
        simpa [outer] using
          restrictionAssignmentWeightAt_fixCoordinateList_of_all_fixed δ tail.target
            coordinates T.satisfyingAssignment (T.coordinatesAtPositions_nodup positions) hfixed
      have hcoordinateLength : coordinates.length = (i : ℕ) + 1 := by
        simpa [coordinates, positions, DNFTerm.coordinatesAtPositions] using hcard
      have hsum : coordinates.length + (k - (i : ℕ)) = k + 1 := by
        rw [hcoordinateLength]
        omega
      calc
        restrictionAssignmentWeightAt δ ρ =
            switchingAtomRatio δ ^ coordinates.length *
              restrictionAssignmentWeightAt δ η := by simpa [η] using hsource
        _ = switchingAtomRatio δ ^ coordinates.length *
            (switchingAtomRatio δ ^ (k - (i : ℕ)) *
              restrictionAssignmentWeightAt δ tail.target) := by
          rw [show restrictionAssignmentWeightAt δ η =
              switchingAtomRatio δ ^ (k - (i : ℕ)) *
                restrictionAssignmentWeightAt δ tail.target by
            simpa [η] using ih]
        _ = switchingAtomRatio δ ^
              (coordinates.length + (k - (i : ℕ))) *
                restrictionAssignmentWeightAt δ outer := by
          rw [pow_add, houterWeight]
          ring
        _ = switchingAtomRatio δ ^ (k + 1) *
            restrictionAssignmentWeightAt δ outer := by rw [hsum]
        _ = switchingAtomRatio δ ^ (k + 1) *
            restrictionAssignmentWeightAt δ
              (DNFFormula.SwitchingTrace.target
                (DNFFormula.SwitchingTrace.cons hcompat i x hcard hincompatible tail)) := by
          rfl

end DNFFormula.SwitchingTrace


variable {n w : ℕ}

/-- Restrictions witnessing switching failure at a fixed depth. -/
abbrev DNFFormula.SwitchingBad (φ : DNFFormula n) (k : ℕ) :=
  {ρ : Fin n → CoordRestriction //
    k ≤ F₂DecisionTree.decisionTreeDepth
      (CoordRestriction.restrict φ.toBooleanFunction ρ)}

theorem DNFFormula.sum_switchingBadWeight_eq_coordSwitchingFailureProbability
    (φ : DNFFormula n) (δ : ℝ) (k : ℕ) :
    (∑ ρ : φ.SwitchingBad k, restrictionAssignmentWeightAt δ ρ.1) =
      coordSwitchingFailureProbability φ.toBooleanFunction δ k := by
  classical
  rw [coordSwitchingFailureProbability]
  simp_rw [coordSwitchingFailureIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

/-- Canonical trace chosen for a bad restriction of positive depth. -/
noncomputable def DNFFormula.traceOfSwitchingBad (φ : DNFFormula n) (k : ℕ)
    (ρ : φ.SwitchingBad (k + 1)) : φ.SwitchingTrace ρ.1 (k + 1) :=
  Classical.choice (φ.nonempty_switchingTrace_of_decisionTreeDepth ρ.1 k ρ.2)

/-- Injective source-to-target-and-code map underlying the switching argument. -/
noncomputable def DNFFormula.switchingEncoding (φ : DNFFormula n)
    (hw : φ.width ≤ w) (k : ℕ) :
    φ.SwitchingBad (k + 1) → (Fin n → CoordRestriction) × SwitchingCode w (k + 1) :=
  fun ρ ↦
    let tr := φ.traceOfSwitchingBad k ρ
    ⟨tr.target, tr.code hw⟩

theorem DNFFormula.switchingEncoding_injective (φ : DNFFormula n)
    (hw : φ.width ≤ w) (k : ℕ) :
    Function.Injective (φ.switchingEncoding hw k) := by
  intro ρ σ h
  apply Subtype.ext
  let trρ := φ.traceOfSwitchingBad k ρ
  let trσ := φ.traceOfSwitchingBad k σ
  have htarget : trρ.target = trσ.target := congrArg Prod.fst h
  have hcode : trρ.code hw = trσ.code hw := congrArg Prod.snd h
  calc
    ρ.1 = φ.decodeSwitchingCode hw trρ.target (trρ.code hw) :=
      (trρ.decode_target_code hw).symm
    _ = φ.decodeSwitchingCode hw trσ.target (trσ.code hw) := by
      rw [htarget, hcode]
    _ = σ.1 := trσ.decode_target_code hw

theorem switchingAtomRatio_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    0 ≤ switchingAtomRatio δ := by
  unfold switchingAtomRatio
  positivity

theorem DNFFormula.sum_switchingTraceTargetWeight_le_card
    (φ : DNFFormula n) (hw : φ.width ≤ w) (k : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∑ ρ : φ.SwitchingBad (k + 1),
      restrictionAssignmentWeightAt δ (φ.traceOfSwitchingBad k ρ).target) ≤
        (Fintype.card (SwitchingCode w (k + 1)) : ℝ) := by
  classical
  let encode := φ.switchingEncoding hw k
  have hinjective : Function.Injective encode := φ.switchingEncoding_injective hw k
  calc
    (∑ ρ : φ.SwitchingBad (k + 1),
        restrictionAssignmentWeightAt δ (φ.traceOfSwitchingBad k ρ).target) =
        ∑ p ∈ (Finset.univ.image encode), restrictionAssignmentWeightAt δ p.1 := by
      rw [Finset.sum_image hinjective.injOn]
      rfl
    _ ≤ ∑ p : (Fin n → CoordRestriction) × SwitchingCode w (k + 1),
        restrictionAssignmentWeightAt δ p.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _ _
      exact restrictionAssignmentWeightAt_nonneg hδ0 hδ1 p.1
    _ = (Fintype.card (SwitchingCode w (k + 1)) : ℝ) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, sum_restrictionAssignmentWeightAt, mul_one]

theorem DNFFormula.coordSwitchingFailureProbability_le_ratio_pow_card
    (φ : DNFFormula n) (hw : φ.width ≤ w) (k : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    coordSwitchingFailureProbability φ.toBooleanFunction δ (k + 1) ≤
      switchingAtomRatio δ ^ (k + 1) *
        Fintype.card (SwitchingCode w (k + 1)) := by
  rw [← φ.sum_switchingBadWeight_eq_coordSwitchingFailureProbability]
  calc
    (∑ ρ : φ.SwitchingBad (k + 1), restrictionAssignmentWeightAt δ ρ.1) =
        switchingAtomRatio δ ^ (k + 1) *
          ∑ ρ : φ.SwitchingBad (k + 1),
            restrictionAssignmentWeightAt δ (φ.traceOfSwitchingBad k ρ).target := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      exact (φ.traceOfSwitchingBad k ρ).restrictionAssignmentWeightAt_eq_ratio_pow_target hδ1
    _ ≤ switchingAtomRatio δ ^ (k + 1) *
        Fintype.card (SwitchingCode w (k + 1)) := by
      gcongr
      · exact pow_nonneg (switchingAtomRatio_nonneg hδ0 hδ1) _
      · exact φ.sum_switchingTraceTargetWeight_le_card hw k hδ0 hδ1.le

theorem DNFFormula.coordSwitchingFailureProbability_eq_zero_of_width_eq_zero
    (φ : DNFFormula n) (hwidth : φ.width = 0) (δ : ℝ) (k : ℕ) (hk : 0 < k) :
    coordSwitchingFailureProbability φ.toBooleanFunction δ k = 0 := by
  classical
  unfold coordSwitchingFailureProbability
  apply Finset.sum_eq_zero
  intro ρ _
  rw [mul_eq_zero]
  right
  unfold coordSwitchingFailureIndicator
  rw [if_neg]
  intro hdepth
  have hone : 1 ≤ F₂DecisionTree.decisionTreeDepth
      (CoordRestriction.restrict φ.toBooleanFunction ρ) := by omega
  obtain ⟨x, y, hxy⟩ :=
    (one_le_decisionTreeDepth_iff_nonconstant _).1 hone
  exact hxy (φ.toBooleanFunction_eq_of_width_eq_zero hwidth
    (CoordRestriction.complete ρ x) (CoordRestriction.complete ρ y))

theorem SwitchingCode.card_width_one (k : ℕ) (hk : 0 < k) :
    Fintype.card (SwitchingCode 1 k) = 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction m with
  | zero => simp [SwitchingCode.card_succ]
  | succ m ih =>
      calc
        Fintype.card (SwitchingCode 1 (m + 1).succ) =
            Fintype.card (SwitchingCode 1 (m + 1)) := by
          simpa [Nat.succ_eq_add_one] using
            (show Fintype.card (SwitchingCode 1 (m + 2)) =
              Fintype.card (SwitchingCode 1 (m + 1)) by
                rw [show m + 2 = (m + 1) + 1 by omega, SwitchingCode.card_succ]
                rw [Fin.sum_univ_succ]
                simp [Nat.choose])
        _ = 2 := ih (by omega)

/-- Håstad's Switching Lemma for a width-bounded DNF. -/
theorem hastadSwitchingLemma_dnf
    (φ : DNFFormula n) {w k : ℕ} (hw : φ.width ≤ w) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    switchingFailureProbability φ.toBooleanFunction δ k ≤ (5 * δ * w) ^ k := by
  rcases k with _ | m
  · simp
  · rw [← coordSwitchingFailureProbability_eq]
    by_cases hwzero : w = 0
    · have hφzero : φ.width = 0 := Nat.eq_zero_of_le_zero (hwzero ▸ hw)
      rw [φ.coordSwitchingFailureProbability_eq_zero_of_width_eq_zero
        hφzero δ (m + 1) (by omega), hwzero]
      simp
    · have hwoneNat : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr hwzero
      have hwone : (1 : ℝ) ≤ w := by exact_mod_cast hwoneNat
      by_cases hlarge : 1 ≤ (5 : ℝ) * δ * w
      · calc
          coordSwitchingFailureProbability φ.toBooleanFunction δ (m + 1) ≤ 1 :=
            coordSwitchingFailureProbability_le_one hδ0 hδ1
          _ ≤ (5 * δ * w) ^ (m + 1) := one_le_pow₀ hlarge
      · have hbase : (5 : ℝ) * δ * w < 1 := lt_of_not_ge hlarge
        have hδlt : δ < 1 := by nlinarith [mul_le_mul_of_nonneg_left hwone hδ0]
        have hratioNonneg := switchingAtomRatio_nonneg hδ0 hδlt
        calc
          coordSwitchingFailureProbability φ.toBooleanFunction δ (m + 1) ≤
              switchingAtomRatio δ ^ (m + 1) *
                Fintype.card (SwitchingCode w (m + 1)) :=
            φ.coordSwitchingFailureProbability_le_ratio_pow_card hw m hδ0 hδlt
          _ ≤ (5 * δ * w) ^ (m + 1) := by
            by_cases hwoneExact : w = 1
            · subst w
              rw [SwitchingCode.card_width_one (m + 1) (by omega)]
              push_cast
              norm_num only [Nat.cast_one, mul_one] at hbase ⊢
              have hδfifth : δ < (1 : ℝ) / 5 := by nlinarith
              have hratio : 2 * switchingAtomRatio δ ≤ 5 * δ := by
                unfold switchingAtomRatio
                calc
                  2 * (2 * δ / (1 - δ)) = 4 * δ / (1 - δ) := by ring
                  _ ≤ 5 * δ := by
                    apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).2
                    nlinarith
              have htwo : (2 : ℝ) ≤ 2 ^ (m + 1) := by
                rw [pow_succ']
                have hm : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
                nlinarith
              calc
                switchingAtomRatio δ ^ (m + 1) * 2 ≤
                    switchingAtomRatio δ ^ (m + 1) * 2 ^ (m + 1) := by
                  gcongr
                _ = (2 * switchingAtomRatio δ) ^ (m + 1) := by rw [mul_pow]; ring
                _ ≤ (5 * δ) ^ (m + 1) := by gcongr
            · have hwtwoNat : 2 ≤ w := by omega
              have hwtwo : (2 : ℝ) ≤ w := by exact_mod_cast hwtwoNat
              have hδtenth : δ < (1 : ℝ) / 10 := by
                nlinarith [mul_le_mul_of_nonneg_left hwtwo hδ0]
              have hratio : switchingAtomRatio δ ≤ 20 * δ / 9 := by
                unfold switchingAtomRatio
                apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).2
                nlinarith
              have hbaseCompare : switchingAtomRatio δ * ((9 : ℝ) * w / 4) ≤
                  5 * δ * w := by
                calc
                  switchingAtomRatio δ * ((9 : ℝ) * w / 4) ≤
                      (20 * δ / 9) * (9 * w / 4) :=
                    mul_le_mul_of_nonneg_right hratio (by positivity)
                  _ = 5 * δ * w := by ring
              calc
                switchingAtomRatio δ ^ (m + 1) *
                    Fintype.card (SwitchingCode w (m + 1)) ≤
                    switchingAtomRatio δ ^ (m + 1) *
                      ((9 : ℝ) * w / 4) ^ (m + 1) := by
                  exact mul_le_mul_of_nonneg_left
                    (SwitchingCode.card_le_scale_pow w (m + 1))
                    (pow_nonneg hratioNonneg _)
                _ = (switchingAtomRatio δ * ((9 : ℝ) * w / 4)) ^ (m + 1) := by
                  rw [mul_pow]
                _ ≤ (5 * δ * w) ^ (m + 1) := by gcongr

/-- Håstad's Switching Lemma, for either a DNF or a CNF of width at most `w`. -/
theorem hastadSwitchingLemma
    {f : BooleanFunction n} {w k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : HasDNFWidthLE f w ∨ HasCNFWidthLE f w) :
    switchingFailureProbability f δ k ≤ (5 * δ * w) ^ k := by
  rcases hf with ⟨φ, hw, rfl⟩ | ⟨ψ, hw, rfl⟩
  · exact hastadSwitchingLemma_dnf φ hw hδ0 hδ1
  · let φ := CNFFormula.switchAndOr ψ
    have hφwidth : φ.width ≤ w := by
      simpa [φ, CNFFormula.switchAndOr, CNFFormula.width] using hw
    calc
      switchingFailureProbability ψ.toBooleanFunction δ k =
          switchingFailureProbability
            (CNFFormula.booleanDual ψ.toBooleanFunction) δ k :=
        (switchingFailureProbability_booleanDual ψ.toBooleanFunction δ k).symm
      _ = switchingFailureProbability φ.toBooleanFunction δ k := by
        exact congrArg (fun g ↦ switchingFailureProbability g δ k)
          (CNFFormula.switchAndOr_toBooleanFunction ψ).symm
      _ ≤ (5 * δ * w) ^ k := hastadSwitchingLemma_dnf φ hφwidth hδ0 hδ1

end FABL
