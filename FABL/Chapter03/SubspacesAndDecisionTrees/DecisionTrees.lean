/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces

/-!
# Decision trees

Book items: Definition 3.13, Definition 3.14, Exercise 3.21, Exercise 3.22.

Finite decision trees, paths, and path subcubes from Section 3.2.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Decision trees -/

/-- O'Donnell, Definition 3.13: a binary decision tree whose index records the coordinates still
available for query. Removing the queried coordinate from both child indices enforces that no
coordinate occurs twice on a root-to-leaf path. -/
inductive F₂DecisionTree (n : ℕ) (α : Type*) : Finset (Fin n) → Type _ where
  /-- A leaf returns its stored value without querying another coordinate. -/
  | leaf {available} (value : α) : F₂DecisionTree n α available
  /-- Query one available coordinate, then remove it from both child indices. -/
  | query {available} (coordinate : Fin n) (mem_available : coordinate ∈ available)
      (zeroChild oneChild : F₂DecisionTree n α (available.erase coordinate)) :
      F₂DecisionTree n α available

/-- A complete decision tree starts with every coordinate available. -/
abbrev DecisionTree (n : ℕ) (α : Type*) :=
  F₂DecisionTree n α Finset.univ

namespace F₂DecisionTree

variable {α : Type*}

/-- Execute a decision tree on a binary-cube input. -/
def eval {available : Finset (Fin n)} : F₂DecisionTree n α available → 𝔽₂^[n] → α
  | .leaf value, _ => value
  | .query coordinate _ zeroChild oneChild, x =>
      if x coordinate = 0 then zeroChild.eval x else oneChild.eval x

/-- O'Donnell, Definition 3.14: the number of leaves. -/
def leafCount {available : Finset (Fin n)} : F₂DecisionTree n α available → ℕ
  | .leaf _ => 1
  | .query _ _ zeroChild oneChild => zeroChild.leafCount + oneChild.leafCount

/-- O'Donnell, Definition 3.14: maximum root-to-leaf path length. -/
def depth {available : Finset (Fin n)} : F₂DecisionTree n α available → ℕ
  | .leaf _ => 0
  | .query _ _ zeroChild oneChild => max zeroChild.depth oneChild.depth + 1

/-- The available-coordinate index bounds every root-to-leaf path length. -/
theorem depth_le_card_available {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) : T.depth ≤ available.card := by
  induction T with
  | leaf value => simp [depth]
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      rw [depth]
      have hcard := Finset.card_erase_of_mem hcoordinate
      have hmax : max zeroChild.depth oneChild.depth ≤ (available.erase coordinate).card :=
        max_le hzero hone
      have havailable : 0 < available.card :=
        Finset.card_pos.mpr ⟨coordinate, hcoordinate⟩
      omega

/-- Every decision tree over `n` coordinates has depth at most `n`. -/
theorem depth_le_dimension (T : DecisionTree n α) : T.depth ≤ n := by
  simpa using T.depth_le_card_available

/-- A binary tree of depth `k` has at most `2ᵏ` leaves. -/
theorem leafCount_le_two_pow_depth {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) : T.leafCount ≤ 2 ^ T.depth := by
  induction T with
  | leaf value => simp [leafCount, depth]
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      have hzeroMax : 2 ^ zeroChild.depth ≤ 2 ^ max zeroChild.depth oneChild.depth :=
        pow_le_pow_right' (by omega) (Nat.le_max_left _ _)
      have honeMax : 2 ^ oneChild.depth ≤ 2 ^ max zeroChild.depth oneChild.depth :=
        pow_le_pow_right' (by omega) (Nat.le_max_right _ _)
      rw [leafCount, depth]
      calc
        zeroChild.leafCount + oneChild.leafCount ≤
            2 ^ zeroChild.depth + 2 ^ oneChild.depth := Nat.add_le_add hzero hone
        _ ≤ 2 ^ max zeroChild.depth oneChild.depth +
            2 ^ max zeroChild.depth oneChild.depth := Nat.add_le_add hzeroMax honeMax
        _ = 2 ^ (max zeroChild.depth oneChild.depth + 1) := by
          rw [pow_succ]
          omega

/-- Truncate every root-to-leaf computation after at most `k` queries, labeling each newly
created leaf by `fallback`. Existing leaves are preserved. -/
def truncate (fallback : α) {available : Finset (Fin n)} :
    F₂DecisionTree n α available → ℕ → F₂DecisionTree n α available
  | .leaf value, _ => .leaf value
  | .query _ _ _ _, 0 => .leaf fallback
  | .query coordinate hcoordinate zeroChild oneChild, k + 1 =>
      .query coordinate hcoordinate
        (zeroChild.truncate fallback k) (oneChild.truncate fallback k)

/-- A depth-`k` truncation has depth at most `k`. -/
theorem depth_truncate_le {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (fallback : α) (k : ℕ) :
    (T.truncate fallback k).depth ≤ k := by
  induction T generalizing k with
  | leaf value => simp [truncate, depth]
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      cases k with
      | zero => simp [truncate, depth]
      | succ k =>
          rw [truncate, depth]
          exact Nat.succ_le_succ (max_le (hzero k) (hone k))

/-- On every input, a truncation returns either the original output or its fallback label. -/
theorem eval_truncate_eq_eval_or_eq_fallback {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (fallback : α) (k : ℕ) (x : 𝔽₂^[n]) :
    (T.truncate fallback k).eval x = T.eval x ∨
      (T.truncate fallback k).eval x = fallback := by
  induction T generalizing k with
  | leaf value =>
      exact Or.inl rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      cases k with
      | zero =>
          exact Or.inr rfl
      | succ k =>
          by_cases hx : x coordinate = 0
          · simpa [truncate, eval, hx] using hzero k
          · simpa [truncate, eval, hx] using hone k

/-- Full decision tree obtained by querying every still-available coordinate. -/
noncomputable def completeTreeAux (f : 𝔽₂^[n] → α) (partialInput : 𝔽₂^[n])
    (available : Finset (Fin n)) : F₂DecisionTree n α available :=
  if h : available.Nonempty then
    let coordinate := available.min' h
    .query coordinate (available.min'_mem h)
      (completeTreeAux f (Function.update partialInput coordinate 0) (available.erase coordinate))
      (completeTreeAux f (Function.update partialInput coordinate 1) (available.erase coordinate))
  else
    .leaf (f partialInput)
termination_by available.card
decreasing_by
  all_goals
    exact Finset.card_erase_lt_of_mem (available.min'_mem h)

/-- Canonical complete decision tree representing a function on the binary cube. -/
noncomputable def completeTree (f : 𝔽₂^[n] → α) : DecisionTree n α :=
  completeTreeAux f 0 Finset.univ

/-- The full tree agrees with `f` when its prefix already agrees with the input off the remaining
coordinate set. -/
theorem eval_completeTreeAux (f : 𝔽₂^[n] → α) (partialInput x : 𝔽₂^[n])
    (available : Finset (Fin n))
    (hagrees : ∀ i, i ∉ available → partialInput i = x i) :
    (completeTreeAux f partialInput available).eval x = f x := by
  rw [completeTreeAux]
  split_ifs with hnonempty
  · let coordinate := available.min' hnonempty
    have hcoordinate : coordinate ∈ available := available.min'_mem hnonempty
    change (if x coordinate = 0 then
        (completeTreeAux f (Function.update partialInput coordinate 0)
          (available.erase coordinate)).eval x
      else
        (completeTreeAux f (Function.update partialInput coordinate 1)
          (available.erase coordinate)).eval x) = f x
    by_cases hx : x coordinate = 0
    · rw [if_pos hx]
      apply eval_completeTreeAux
      intro i hi
      by_cases hic : i = coordinate
      · subst i
        simp [hx]
      · rw [Function.update_of_ne hic]
        apply hagrees i
        intro hmem
        exact hi (Finset.mem_erase.mpr ⟨hic, hmem⟩)
    · rw [if_neg hx]
      have hx_one : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
      apply eval_completeTreeAux
      intro i hi
      by_cases hic : i = coordinate
      · subst i
        simp [hx_one]
      · rw [Function.update_of_ne hic]
        apply hagrees i
        intro hmem
        exact hi (Finset.mem_erase.mpr ⟨hic, hmem⟩)
  · have hempty : available = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    change f partialInput = f x
    congr 1
    funext i
    apply hagrees i
    simp [hempty]
termination_by available.card
decreasing_by
  all_goals
    exact Finset.card_erase_lt_of_mem hcoordinate

/-- Execution of the complete tree agrees with its source function. -/
theorem eval_completeTree (f : 𝔽₂^[n] → α) : (completeTree f).eval = f := by
  apply funext
  intro x
  apply eval_completeTreeAux
  simp

/-- A tree computes `f` when execution agrees with `f` on every input. -/
def Computes {available : Finset (Fin n)} (T : F₂DecisionTree n α available)
    (f : 𝔽₂^[n] → α) : Prop :=
  T.eval = f

theorem computes_iff {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (f : 𝔽₂^[n] → α) :
    T.Computes f ↔ ∀ x, T.eval x = f x := by
  exact funext_iff

/-- Every function on the finite binary cube is represented by the complete decision tree. -/
theorem completeTree_computes (f : 𝔽₂^[n] → α) : (completeTree f).Computes f :=
  eval_completeTree f

/-- There is at least one depth attained by a decision tree computing `f`. -/
theorem exists_computingTree_with_depth (f : 𝔽₂^[n] → α) :
    ∃ k, ∃ T : DecisionTree n α, T.Computes f ∧ T.depth = k :=
  ⟨(completeTree f).depth, completeTree f, completeTree_computes f, rfl⟩

/-- There is at least one size attained by a decision tree computing `f`. -/
theorem exists_computingTree_with_size (f : 𝔽₂^[n] → α) :
    ∃ s, ∃ T : DecisionTree n α, T.Computes f ∧ T.leafCount = s :=
  ⟨(completeTree f).leafCount, completeTree f, completeTree_computes f, rfl⟩

/-- O'Donnell, Definition 3.14: the least depth of a decision tree computing `f`. -/
noncomputable def decisionTreeDepth (f : 𝔽₂^[n] → α) : ℕ :=
  by
    classical
    exact Nat.find (exists_computingTree_with_depth f)

/-- O'Donnell, Definition 3.14: the least number of leaves of a decision tree computing `f`. -/
noncomputable def decisionTreeSize (f : 𝔽₂^[n] → α) : ℕ :=
  by
    classical
    exact Nat.find (exists_computingTree_with_size f)

/-- A depth-optimal decision tree exists. -/
theorem exists_computingTree_depth_eq_decisionTreeDepth (f : 𝔽₂^[n] → α) :
    ∃ T : DecisionTree n α, T.Computes f ∧ T.depth = decisionTreeDepth f :=
  by
    classical
    exact Nat.find_spec (exists_computingTree_with_depth f)

/-- A size-optimal decision tree exists. -/
theorem exists_computingTree_leafCount_eq_decisionTreeSize (f : 𝔽₂^[n] → α) :
    ∃ T : DecisionTree n α, T.Computes f ∧ T.leafCount = decisionTreeSize f :=
  by
    classical
    exact Nat.find_spec (exists_computingTree_with_size f)

/-- `decisionTreeDepth` is no larger than the depth of any computing tree. -/
theorem decisionTreeDepth_le_of_computes (f : 𝔽₂^[n] → α) (T : DecisionTree n α)
    (hT : T.Computes f) : decisionTreeDepth f ≤ T.depth := by
  classical
  exact Nat.find_min' (exists_computingTree_with_depth f) ⟨T, hT, rfl⟩

/-- `decisionTreeSize` is no larger than the size of any computing tree. -/
theorem decisionTreeSize_le_of_computes (f : 𝔽₂^[n] → α) (T : DecisionTree n α)
    (hT : T.Computes f) : decisionTreeSize f ≤ T.leafCount := by
  classical
  exact Nat.find_min' (exists_computingTree_with_size f) ⟨T, hT, rfl⟩

/-- A root-to-leaf path records the queried partial assignment and the leaf label. -/
structure Path (n : ℕ) (α : Type*) where
  /-- The branch value fixed at each queried coordinate. -/
  assignment : Fin n → Option 𝔽₂
  /-- The label at the terminal leaf. -/
  output : α

namespace Path

/-- The empty root-to-leaf path. -/
def empty (value : α) : Path n α where
  assignment := fun _ ↦ none
  output := value

/-- Prepend a query outcome to a path. -/
def withQuery (path : Path n α) (coordinate : Fin n) (value : 𝔽₂) : Path n α where
  assignment := Function.update path.assignment coordinate (some value)
  output := path.output

/-- Coordinates queried along a path. -/
def support (path : Path n α) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ path.assignment i ≠ none

/-- Root-to-leaf path length. -/
def length (path : Path n α) : ℕ := path.support.card

@[simp] theorem mem_support (path : Path n α) (i : Fin n) :
    i ∈ path.support ↔ path.assignment i ≠ none := by
  simp [support]

@[simp] theorem empty_support (value : α) : (Path.empty (n := n) value).support = ∅ := by
  ext i
  simp [empty, support]

@[simp] theorem empty_length (value : α) : (Path.empty (n := n) value).length = 0 := by
  simp [length]

@[simp] theorem withQuery_output (path : Path n α) (coordinate : Fin n) (value : 𝔽₂) :
    (path.withQuery coordinate value).output = path.output := rfl

theorem mem_support_withQuery_iff (path : Path n α) (coordinate j : Fin n) (value : 𝔽₂) :
    j ∈ (path.withQuery coordinate value).support ↔ j = coordinate ∨ j ∈ path.support := by
  by_cases hj : j = coordinate
  · subst j
    simp [withQuery]
  · simp [withQuery, hj]

theorem support_withQuery (path : Path n α) (coordinate : Fin n) (value : 𝔽₂) :
    (path.withQuery coordinate value).support = insert coordinate path.support := by
  apply Finset.ext
  intro j
  rw [mem_support_withQuery_iff]
  simp

theorem length_withQuery_of_not_mem (path : Path n α) (coordinate : Fin n)
    (value : 𝔽₂) (hcoordinate : coordinate ∉ path.support) :
    (path.withQuery coordinate value).length = path.length + 1 := by
  rw [length, support_withQuery, Finset.card_insert_of_notMem hcoordinate, length]

/-- An input follows a path when it has every queried branch value. -/
def Matches (path : Path n α) (x : 𝔽₂^[n]) : Prop :=
  ∀ i value, path.assignment i = some value → x i = value

/-- The subcube of inputs following a root-to-leaf path. -/
def cylinder (path : Path n α) : Set 𝔽₂^[n] :=
  {x | path.Matches x}

/-- Indicator of a path subcube. -/
noncomputable def indicator (path : Path n α) : 𝔽₂^[n] → ℝ :=
  setIndicator path.cylinder

@[simp] theorem matches_empty (value : α) (x : 𝔽₂^[n]) :
    (Path.empty value).Matches x := by
  intro i branch h
  simp [empty] at h

theorem assignment_eq_none_of_not_mem_support (path : Path n α) (coordinate : Fin n)
    (hcoordinate : coordinate ∉ path.support) : path.assignment coordinate = none := by
  by_contra h
  exact hcoordinate ((Path.mem_support path coordinate).2 h)

/-- Prepending a fresh query intersects the old path subcube with one coordinate condition. -/
theorem matches_withQuery_iff (path : Path n α) (coordinate : Fin n) (value : 𝔽₂)
    (hcoordinate : coordinate ∉ path.support) (x : 𝔽₂^[n]) :
    (path.withQuery coordinate value).Matches x ↔ path.Matches x ∧ x coordinate = value := by
  have hnone := assignment_eq_none_of_not_mem_support path coordinate hcoordinate
  constructor
  · intro h
    constructor
    · intro i branch hbranch
      by_cases hi : i = coordinate
      · subst i
        rw [hnone] at hbranch
        simp at hbranch
      · apply h i branch
        simpa [withQuery, Function.update_of_ne hi] using hbranch
    · apply h coordinate value
      simp [withQuery]
  · rintro ⟨hpath, hvalue⟩ i branch hbranch
    by_cases hi : i = coordinate
    · subst i
      have hbranch' : value = branch := Option.some.inj (by simpa [withQuery] using hbranch)
      exact hvalue.trans hbranch'
    · apply hpath i branch
      simpa [withQuery, Function.update_of_ne hi] using hbranch

/-- A path indicator is one on a matching input. -/
theorem indicator_eq_one_of_matches (path : Path n α) (x : 𝔽₂^[n])
    (h : path.Matches x) : path.indicator x = 1 := by
  classical
  simp [indicator, cylinder, setIndicator, h]

/-- A path indicator is zero away from matching inputs. -/
theorem indicator_eq_zero_of_not_matches (path : Path n α) (x : 𝔽₂^[n])
    (h : ¬path.Matches x) : path.indicator x = 0 := by
  classical
  simp [indicator, cylinder, setIndicator, h]

/-- Indicator recursion when a fresh coordinate condition is prepended. -/
theorem indicator_withQuery (path : Path n α) (coordinate : Fin n) (value : 𝔽₂)
    (hcoordinate : coordinate ∉ path.support) (x : 𝔽₂^[n]) :
    (path.withQuery coordinate value).indicator x =
      if x coordinate = value then path.indicator x else 0 := by
  classical
  by_cases hpath : path.Matches x <;> by_cases hvalue : x coordinate = value
  · rw [if_pos hvalue, indicator_eq_one_of_matches _ _ hpath,
      indicator_eq_one_of_matches _ _
        ((matches_withQuery_iff path coordinate value hcoordinate x).2 ⟨hpath, hvalue⟩)]
  · rw [if_neg hvalue, indicator_eq_zero_of_not_matches]
    exact (matches_withQuery_iff path coordinate value hcoordinate x).not.mpr
      (not_and_or.mpr (Or.inr hvalue))
  · rw [if_pos hvalue, indicator_eq_zero_of_not_matches _ _ hpath,
      indicator_eq_zero_of_not_matches]
    exact (matches_withQuery_iff path coordinate value hcoordinate x).not.mpr
      (not_and_or.mpr (Or.inl hpath))
  · rw [if_neg hvalue, indicator_eq_zero_of_not_matches]
    exact (matches_withQuery_iff path coordinate value hcoordinate x).not.mpr
      (not_and_or.mpr (Or.inr hvalue))

end Path

/-- The finite list of root-to-leaf paths of a decision tree. -/
def paths {available : Finset (Fin n)} :
    F₂DecisionTree n α available → List (Path n α)
  | .leaf value => [Path.empty value]
  | .query coordinate _ zeroChild oneChild =>
      zeroChild.paths.map (fun path ↦ path.withQuery coordinate 0) ++
        oneChild.paths.map (fun path ↦ path.withQuery coordinate 1)

@[simp] theorem paths_leaf {available : Finset (Fin n)} (value : α) :
    paths (.leaf (available := available) value) = [Path.empty value] := rfl

@[simp] theorem paths_query {available : Finset (Fin n)} (coordinate : Fin n)
    (hcoordinate : coordinate ∈ available)
    (zeroChild oneChild : F₂DecisionTree n α (available.erase coordinate)) :
    paths (.query coordinate hcoordinate zeroChild oneChild) =
      zeroChild.paths.map (fun path ↦ path.withQuery coordinate 0) ++
        oneChild.paths.map (fun path ↦ path.withQuery coordinate 1) := rfl

/-- Every coordinate recorded by a path was available at the root of its tree. -/
theorem path_support_subset_available {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (path : Path n α) (hpath : path ∈ T.paths) :
    path.support ⊆ available := by
  induction T generalizing path with
  | leaf value =>
      simp only [paths_leaf, List.mem_singleton] at hpath
      subst path
      simp
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [paths_query, List.mem_append, List.mem_map] at hpath
      rcases hpath with ⟨childPath, hchild, rfl⟩ | ⟨childPath, hchild, rfl⟩
      · intro j hj
        rw [Path.mem_support_withQuery_iff] at hj
        rcases hj with rfl | hj
        · exact hcoordinate
        · exact Finset.mem_of_mem_erase (hzero childPath hchild hj)
      · intro j hj
        rw [Path.mem_support_withQuery_iff] at hj
        rcases hj with rfl | hj
        · exact hcoordinate
        · exact Finset.mem_of_mem_erase (hone childPath hchild hj)

/-- Every root-to-leaf path length is bounded by the tree depth. -/
theorem path_length_le_depth {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (path : Path n α) (hpath : path ∈ T.paths) :
    path.length ≤ T.depth := by
  induction T generalizing path with
  | leaf value =>
      simp only [paths_leaf, List.mem_singleton] at hpath
      subst path
      simp [depth]
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [paths_query, List.mem_append, List.mem_map] at hpath
      rcases hpath with ⟨childPath, hchild, rfl⟩ | ⟨childPath, hchild, rfl⟩
      · have hnot : coordinate ∉ childPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild childPath hchild hmem)
        rw [Path.length_withQuery_of_not_mem _ _ _ hnot, depth]
        exact Nat.succ_le_succ ((hzero childPath hchild).trans (Nat.le_max_left _ _))
      · have hnot : coordinate ∉ childPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild childPath hchild hmem)
        rw [Path.length_withQuery_of_not_mem _ _ _ hnot, depth]
        exact Nat.succ_le_succ ((hone childPath hchild).trans (Nat.le_max_right _ _))

/-- The number of enumerated paths is the number of leaves. -/
theorem length_paths_eq_leafCount {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) : T.paths.length = T.leafCount := by
  induction T with
  | leaf value => simp [paths, leafCount]
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp [paths, leafCount, hzero, hone]

/-- Summing indicators after prepending one branch condition restricts the old sum to that
branch. -/
theorem sum_withQuery_pathIndicators (pathList : List (Path n ℝ)) (coordinate : Fin n)
    (branch : 𝔽₂) (x : 𝔽₂^[n])
    (hfresh : ∀ path ∈ pathList, coordinate ∉ path.support) :
    (pathList.map fun path ↦
      (path.withQuery coordinate branch).output *
        (path.withQuery coordinate branch).indicator x).sum =
      if x coordinate = branch then
        (pathList.map fun path ↦ path.output * path.indicator x).sum
      else 0 := by
  classical
  by_cases hx : x coordinate = branch
  · rw [if_pos hx]
    congr 1
    apply List.map_congr_left
    intro path hpath
    rw [Path.withQuery_output,
      Path.indicator_withQuery path coordinate branch (hfresh path hpath) x, if_pos hx]
  · rw [if_neg hx]
    have hzero : pathList.map (fun path ↦
        (path.withQuery coordinate branch).output *
          (path.withQuery coordinate branch).indicator x) =
        pathList.map (fun _ ↦ (0 : ℝ)) := by
      apply List.map_congr_left
      intro path hpath
      rw [Path.withQuery_output,
        Path.indicator_withQuery path coordinate branch (hfresh path hpath) x, if_neg hx,
        mul_zero]
    rw [hzero]
    simp

/-- O'Donnell, Fact 3.15 at one input: execution is the sum of the leaf labels times their path
subcube indicators. -/
theorem eval_eq_sum_pathIndicators {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (x : 𝔽₂^[n]) :
    T.eval x = (T.paths.map fun path ↦ path.output * path.indicator x).sum := by
  induction T generalizing x with
  | leaf value =>
      rw [eval, paths]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      change value = value * (Path.empty value).indicator x
      rw [Path.indicator_eq_one_of_matches _ _ (Path.matches_empty _ _), mul_one]
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      have hzeroFresh : ∀ path ∈ zeroChild.paths, coordinate ∉ path.support := by
        intro path hpath hmem
        exact (Finset.notMem_erase coordinate available)
          (path_support_subset_available zeroChild path hpath hmem)
      have honeFresh : ∀ path ∈ oneChild.paths, coordinate ∉ path.support := by
        intro path hpath hmem
        exact (Finset.notMem_erase coordinate available)
          (path_support_subset_available oneChild path hpath hmem)
      rw [eval, paths_query, List.map_append, List.sum_append]
      rw [List.map_map, List.map_map]
      change (if x coordinate = 0 then zeroChild.eval x else oneChild.eval x) =
        (zeroChild.paths.map fun path ↦
          (path.withQuery coordinate 0).output *
            (path.withQuery coordinate 0).indicator x).sum +
        (oneChild.paths.map fun path ↦
          (path.withQuery coordinate 1).output *
            (path.withQuery coordinate 1).indicator x).sum
      rw [
        sum_withQuery_pathIndicators zeroChild.paths coordinate 0 x hzeroFresh,
        sum_withQuery_pathIndicators oneChild.paths coordinate 1 x honeFresh]
      by_cases hx : x coordinate = 0
      · have hx_one : x coordinate ≠ 1 := by simp [hx]
        rw [if_pos hx, if_pos hx, if_neg hx_one, add_zero, hzero]
      · have hx_one : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
        rw [if_neg hx, if_neg hx, if_pos hx_one, zero_add, hone]

/-- Functional form of Fact 3.15 for the function computed by a tree. -/
theorem eval_eq_sum_pathIndicators_function {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) :
    T.eval = fun x ↦ (T.paths.map fun path ↦ path.output * path.indicator x).sum := by
  funext x
  exact eval_eq_sum_pathIndicators T x

/-- O'Donnell, Fact 3.15 for a represented function. -/
theorem computes_eq_sum_pathIndicators {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    f = fun x ↦ (T.paths.map fun path ↦ path.output * path.indicator x).sum := by
  exact hT.symm.trans (eval_eq_sum_pathIndicators_function T)

/-- The tree output on an input following a listed path is that path's leaf label. -/
theorem eval_eq_path_output_of_mem_of_matches {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (path : Path n α) (x : 𝔽₂^[n])
    (hpath : path ∈ T.paths) (hmatches : path.Matches x) :
    T.eval x = path.output := by
  induction T generalizing path x with
  | leaf value =>
      simp only [paths_leaf, List.mem_singleton] at hpath
      subst path
      rfl
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [paths_query, List.mem_append, List.mem_map] at hpath
      rcases hpath with ⟨childPath, hchild, rfl⟩ | ⟨childPath, hchild, rfl⟩
      · have hfresh : coordinate ∉ childPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild childPath hchild hmem)
        have hm := (Path.matches_withQuery_iff childPath coordinate 0 hfresh x).1 hmatches
        rw [eval, if_pos hm.2]
        exact hzero childPath x hchild hm.1
      · have hfresh : coordinate ∉ childPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild childPath hchild hmem)
        have hm := (Path.matches_withQuery_iff childPath coordinate 1 hfresh x).1 hmatches
        have hne : x coordinate ≠ 0 := by rw [hm.2]; norm_num
        rw [eval, if_neg hne]
        exact hone childPath x hchild hm.1

/-- Every input follows at least one listed root-to-leaf path. -/
theorem exists_path_mem_and_matches {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (x : 𝔽₂^[n]) :
    ∃ path, path ∈ T.paths ∧ path.Matches x := by
  induction T with
  | leaf value =>
      exact ⟨Path.empty value, by simp, Path.matches_empty value x⟩
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      by_cases hx : x coordinate = 0
      · obtain ⟨path, hpath, hmatches⟩ := hzero
        have hfresh : coordinate ∉ path.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild path hpath hmem)
        refine ⟨path.withQuery coordinate 0, ?_,
          (Path.matches_withQuery_iff path coordinate 0 hfresh x).2 ⟨hmatches, hx⟩⟩
        rw [paths_query]
        exact List.mem_append.mpr <| Or.inl <| List.mem_map.mpr ⟨path, hpath, rfl⟩
      · have hx_one : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
        obtain ⟨path, hpath, hmatches⟩ := hone
        have hfresh : coordinate ∉ path.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild path hpath hmem)
        refine ⟨path.withQuery coordinate 1, ?_,
          (Path.matches_withQuery_iff path coordinate 1 hfresh x).2 ⟨hmatches, hx_one⟩⟩
        rw [paths_query]
        exact List.mem_append.mpr <| Or.inr <| List.mem_map.mpr ⟨path, hpath, rfl⟩

/-- If truncation changes the value at an input, that input follows an original path longer
than the truncation depth. -/
theorem exists_long_path_of_eval_truncate_ne {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (fallback : α) (k : ℕ) (x : 𝔽₂^[n])
    (hne : (T.truncate fallback k).eval x ≠ T.eval x) :
    ∃ path, path ∈ T.paths ∧ path.Matches x ∧ k < path.length := by
  induction T generalizing k x with
  | leaf value =>
      exact (hne rfl).elim
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      cases k with
      | zero =>
          by_cases hx : x coordinate = 0
          · obtain ⟨path, hpath, hmatches⟩ := exists_path_mem_and_matches zeroChild x
            have hfresh : coordinate ∉ path.support := by
              intro hmem
              exact (Finset.notMem_erase coordinate available)
                (path_support_subset_available zeroChild path hpath hmem)
            refine ⟨path.withQuery coordinate 0, ?_,
              (Path.matches_withQuery_iff path coordinate 0 hfresh x).2
                ⟨hmatches, hx⟩, ?_⟩
            · rw [paths_query]
              exact List.mem_append.mpr <| Or.inl <| List.mem_map.mpr ⟨path, hpath, rfl⟩
            · rw [Path.length_withQuery_of_not_mem path coordinate 0 hfresh]
              omega
          · have hx_one : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
            obtain ⟨path, hpath, hmatches⟩ := exists_path_mem_and_matches oneChild x
            have hfresh : coordinate ∉ path.support := by
              intro hmem
              exact (Finset.notMem_erase coordinate available)
                (path_support_subset_available oneChild path hpath hmem)
            refine ⟨path.withQuery coordinate 1, ?_,
              (Path.matches_withQuery_iff path coordinate 1 hfresh x).2
                ⟨hmatches, hx_one⟩, ?_⟩
            · rw [paths_query]
              exact List.mem_append.mpr <| Or.inr <| List.mem_map.mpr ⟨path, hpath, rfl⟩
            · rw [Path.length_withQuery_of_not_mem path coordinate 1 hfresh]
              omega
      | succ k =>
          by_cases hx : x coordinate = 0
          · have hchild : (zeroChild.truncate fallback k).eval x ≠ zeroChild.eval x := by
              simpa [truncate, eval, hx] using hne
            obtain ⟨path, hpath, hmatches, hlength⟩ := hzero k x hchild
            have hfresh : coordinate ∉ path.support := by
              intro hmem
              exact (Finset.notMem_erase coordinate available)
                (path_support_subset_available zeroChild path hpath hmem)
            refine ⟨path.withQuery coordinate 0, ?_,
              (Path.matches_withQuery_iff path coordinate 0 hfresh x).2
                ⟨hmatches, hx⟩, ?_⟩
            · rw [paths_query]
              exact List.mem_append.mpr <| Or.inl <| List.mem_map.mpr ⟨path, hpath, rfl⟩
            · rw [Path.length_withQuery_of_not_mem path coordinate 0 hfresh]
              exact Nat.succ_lt_succ hlength
          · have hx_one : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
            have hchild : (oneChild.truncate fallback k).eval x ≠ oneChild.eval x := by
              simpa [truncate, eval, hx] using hne
            obtain ⟨path, hpath, hmatches, hlength⟩ := hone k x hchild
            have hfresh : coordinate ∉ path.support := by
              intro hmem
              exact (Finset.notMem_erase coordinate available)
                (path_support_subset_available oneChild path hpath hmem)
            refine ⟨path.withQuery coordinate 1, ?_,
              (Path.matches_withQuery_iff path coordinate 1 hfresh x).2
                ⟨hmatches, hx_one⟩, ?_⟩
            · rw [paths_query]
              exact List.mem_append.mpr <| Or.inr <| List.mem_map.mpr ⟨path, hpath, rfl⟩
            · rw [Path.length_withQuery_of_not_mem path coordinate 1 hfresh]
              exact Nat.succ_lt_succ hlength

/-- No input follows two distinct listed root-to-leaf paths. -/
theorem path_eq_of_mem_of_matches {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (first second : Path n α) (x : 𝔽₂^[n])
    (hfirst : first ∈ T.paths) (hsecond : second ∈ T.paths)
    (hmatchesFirst : first.Matches x) (hmatchesSecond : second.Matches x) :
    first = second := by
  induction T generalizing first second x with
  | leaf value =>
      simp only [paths_leaf, List.mem_singleton] at hfirst hsecond
      exact hfirst.trans hsecond.symm
  | @query available coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [paths_query, List.mem_append, List.mem_map] at hfirst hsecond
      rcases hfirst with ⟨firstPath, hfirst, rfl⟩ | ⟨firstPath, hfirst, rfl⟩ <;>
        rcases hsecond with ⟨secondPath, hsecond, rfl⟩ | ⟨secondPath, hsecond, rfl⟩
      · have hfirstFresh : coordinate ∉ firstPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild firstPath hfirst hmem)
        have hsecondFresh : coordinate ∉ secondPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild secondPath hsecond hmem)
        have hmFirst :=
          (Path.matches_withQuery_iff firstPath coordinate 0 hfirstFresh x).1 hmatchesFirst
        have hmSecond :=
          (Path.matches_withQuery_iff secondPath coordinate 0 hsecondFresh x).1 hmatchesSecond
        exact congrArg (fun path ↦ Path.withQuery path coordinate 0)
          (hzero firstPath secondPath x hfirst hsecond hmFirst.1 hmSecond.1)
      · have hfirstFresh : coordinate ∉ firstPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild firstPath hfirst hmem)
        have hsecondFresh : coordinate ∉ secondPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild secondPath hsecond hmem)
        have hmFirst :=
          (Path.matches_withQuery_iff firstPath coordinate 0 hfirstFresh x).1 hmatchesFirst
        have hmSecond :=
          (Path.matches_withQuery_iff secondPath coordinate 1 hsecondFresh x).1 hmatchesSecond
        exfalso
        have : (0 : 𝔽₂) = 1 := hmFirst.2.symm.trans hmSecond.2
        norm_num at this
      · have hfirstFresh : coordinate ∉ firstPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild firstPath hfirst hmem)
        have hsecondFresh : coordinate ∉ secondPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available zeroChild secondPath hsecond hmem)
        have hmFirst :=
          (Path.matches_withQuery_iff firstPath coordinate 1 hfirstFresh x).1 hmatchesFirst
        have hmSecond :=
          (Path.matches_withQuery_iff secondPath coordinate 0 hsecondFresh x).1 hmatchesSecond
        exfalso
        have : (1 : 𝔽₂) = 0 := hmFirst.2.symm.trans hmSecond.2
        norm_num at this
      · have hfirstFresh : coordinate ∉ firstPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild firstPath hfirst hmem)
        have hsecondFresh : coordinate ∉ secondPath.support := by
          intro hmem
          exact (Finset.notMem_erase coordinate available)
            (path_support_subset_available oneChild secondPath hsecond hmem)
        have hmFirst :=
          (Path.matches_withQuery_iff firstPath coordinate 1 hfirstFresh x).1 hmatchesFirst
        have hmSecond :=
          (Path.matches_withQuery_iff secondPath coordinate 1 hsecondFresh x).1 hmatchesSecond
        exact congrArg (fun path ↦ Path.withQuery path coordinate 1)
          (hone firstPath secondPath x hfirst hsecond hmFirst.1 hmSecond.1)

/-- The path subcubes form a partition: every input follows exactly one listed path. -/
theorem existsUnique_path_mem_and_matches {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (x : 𝔽₂^[n]) :
    ∃! path, path ∈ T.paths ∧ path.Matches x := by
  obtain ⟨path, hpath, hmatches⟩ := exists_path_mem_and_matches T x
  refine ⟨path, ⟨hpath, hmatches⟩, ?_⟩
  rintro other ⟨hother, hmatchesOther⟩
  exact path_eq_of_mem_of_matches T other path x hother hpath hmatchesOther hmatches

/-- If `T` computes `f`, then `f` is constant on every path subcube, with the leaf label as its
value. -/
theorem computes_eq_path_output_of_matches {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (f : 𝔽₂^[n] → α) (hT : T.Computes f)
    (path : Path n α) (hpath : path ∈ T.paths) (x : 𝔽₂^[n]) (hmatches : path.Matches x) :
    f x = path.output := by
  exact (congrFun hT x).symm.trans
    (eval_eq_path_output_of_mem_of_matches T path x hpath hmatches)

/-! ### Path subcubes -/

/-- Restriction of a binary vector to a finite coordinate set. -/
def coordinateRestriction (coordinates : Finset (Fin n)) :
    𝔽₂^[n] →ₗ[𝔽₂] (coordinates → 𝔽₂) where
  toFun x i := x i.1
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

/-- The direction subspace of a coordinate subcube: all selected coordinates vanish. -/
def coordinateZeroSubspace (coordinates : Finset (Fin n)) : Submodule 𝔽₂ 𝔽₂^[n] :=
  LinearMap.ker (coordinateRestriction coordinates)

theorem mem_coordinateZeroSubspace_iff (coordinates : Finset (Fin n)) (x : 𝔽₂^[n]) :
    x ∈ coordinateZeroSubspace coordinates ↔ ∀ i ∈ coordinates, x i = 0 := by
  constructor
  · intro hx i hi
    have hzero : coordinateRestriction coordinates x = 0 :=
      LinearMap.mem_ker.mp hx
    exact congrFun hzero ⟨i, hi⟩
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext i
    exact hx i.1 i.2

/-- Coordinate restriction is onto: a partial coordinate vector extends by zero. -/
theorem coordinateRestriction_surjective (coordinates : Finset (Fin n)) :
    Function.Surjective (coordinateRestriction coordinates) := by
  intro y
  classical
  refine ⟨fun i ↦ if hi : i ∈ coordinates then y ⟨i, hi⟩ else 0, ?_⟩
  funext i
  simp [coordinateRestriction]

/-- Fixing `r` distinct coordinates defines a subspace of codimension `r`. -/
theorem f₂Codimension_coordinateZeroSubspace (coordinates : Finset (Fin n)) :
    f₂Codimension (coordinateZeroSubspace coordinates) = coordinates.card := by
  have hrange : LinearMap.range (coordinateRestriction coordinates) = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateRestriction_surjective coordinates)
  have hrank := LinearMap.finrank_range_add_finrank_ker (coordinateRestriction coordinates)
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [f₂Codimension, finrank_perpendicularSubspace]
  change n - Module.finrank 𝔽₂ (LinearMap.ker (coordinateRestriction coordinates)) =
    coordinates.card
  omega

/-- Standard basis vector at one binary coordinate. -/
def f₂UnitVector (coordinate : Fin n) : 𝔽₂^[n] :=
  fun i ↦ if i = coordinate then 1 else 0

@[simp] theorem f₂UnitVector_apply_self (coordinate : Fin n) :
    f₂UnitVector coordinate coordinate = 1 := by
  simp [f₂UnitVector]

/-- Dotting with a standard basis vector extracts the corresponding coordinate. -/
theorem f₂DotProduct_f₂UnitVector (x : 𝔽₂^[n]) (coordinate : Fin n) :
    f₂DotProduct x (f₂UnitVector coordinate) = x coordinate := by
  classical
  simp [f₂DotProduct, dotProduct, f₂UnitVector]

/-- The perpendicular of the coordinate-zero subspace is supported on the fixed coordinates. -/
theorem f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
    (coordinates : Finset (Fin n)) (γ : 𝔽₂^[n])
    (hγ : γ ∈ perpendicularSubspace (coordinateZeroSubspace coordinates)) :
    f₂Support γ ⊆ coordinates := by
  intro coordinate hcoordinate
  by_contra hnot
  have hunit : f₂UnitVector coordinate ∈ coordinateZeroSubspace coordinates := by
    rw [mem_coordinateZeroSubspace_iff]
    intro i hi
    have hne : i ≠ coordinate := by
      intro h
      subst i
      exact hnot hi
    simp [f₂UnitVector, hne]
  have hdot :=
    (mem_perpendicularSubspace_iff (coordinateZeroSubspace coordinates) γ).1 hγ
      (f₂UnitVector coordinate) hunit
  have hzero : γ coordinate = 0 := by
    simpa [f₂DotProduct_f₂UnitVector] using hdot
  exact (mem_f₂Support γ coordinate).1 hcoordinate hzero

/-- The coordinate subcube obtained by fixing the selected coordinates to a base point. -/
def coordinateSubcube (coordinates : Finset (Fin n)) (basePoint : 𝔽₂^[n]) : Set 𝔽₂^[n] :=
  {x | ∀ i ∈ coordinates, x i = basePoint i}

@[simp] theorem mem_coordinateSubcube (coordinates : Finset (Fin n))
    (basePoint x : 𝔽₂^[n]) :
    x ∈ coordinateSubcube coordinates basePoint ↔
      ∀ i ∈ coordinates, x i = basePoint i := by
  rfl

/-- Fixing coordinates is exactly the affine subspace with coordinate-zero direction. -/
theorem coordinateSubcube_eq_binaryAffineSubspace
    (coordinates : Finset (Fin n)) (basePoint : 𝔽₂^[n]) :
    coordinateSubcube coordinates basePoint =
      (binaryAffineSubspace (coordinateZeroSubspace coordinates) basePoint : Set 𝔽₂^[n]) := by
  ext x
  change (∀ i ∈ coordinates, x i = basePoint i) ↔
    x ∈ binaryAffineSubspace (coordinateZeroSubspace coordinates) basePoint
  rw [mem_binaryAffineSubspace_iff_add_mem, mem_coordinateZeroSubspace_iff]
  constructor
  · intro h i hi
    change x i + basePoint i = 0
    rw [h i hi]
    exact ZModModule.add_self _
  · intro h i hi
    have hzero := h i hi
    change x i + basePoint i = 0 at hzero
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans
      (ZMod.neg_eq_self_mod_two (basePoint i))

namespace Path

/-- Canonical base point of a path subcube, with zero on unqueried coordinates. -/
def base (path : Path n α) : 𝔽₂^[n] :=
  fun i ↦ (path.assignment i).getD 0

/-- Matching a path is equivalent to agreeing with its base point on the queried support. -/
theorem matches_iff_forall_mem_support_eq_base (path : Path n α) (x : 𝔽₂^[n]) :
    path.Matches x ↔ ∀ i ∈ path.support, x i = path.base i := by
  constructor
  · intro h i hi
    have hne : path.assignment i ≠ none := (mem_support path i).1 hi
    cases hassignment : path.assignment i with
    | none => exact (hne hassignment).elim
    | some branch =>
        have hx := h i branch hassignment
        simpa [base, hassignment] using hx
  · intro h i branch hassignment
    have hi : i ∈ path.support := (mem_support path i).2 (by simp [hassignment])
    have hx := h i hi
    simpa [base, hassignment] using hx

/-- The canonical base point follows its defining path. -/
theorem matches_base (path : Path n α) : path.Matches path.base := by
  rw [matches_iff_forall_mem_support_eq_base]
  intro i hi
  rfl

/-- A path cylinder is the coordinate subcube specified by its partial assignment. -/
theorem cylinder_eq_coordinateSubcube (path : Path n α) :
    path.cylinder = coordinateSubcube path.support path.base := by
  ext x
  exact path.matches_iff_forall_mem_support_eq_base x

/-- A path cylinder is the affine coordinate subcube obtained by fixing its queried coordinates. -/
theorem cylinder_eq_binaryAffineSubspace (path : Path n α) :
    path.cylinder =
      (binaryAffineSubspace (coordinateZeroSubspace path.support) path.base : Set 𝔽₂^[n]) := by
  ext x
  change path.Matches x ↔ x ∈ binaryAffineSubspace
    (coordinateZeroSubspace path.support) path.base
  rw [matches_iff_forall_mem_support_eq_base,
    mem_binaryAffineSubspace_iff_add_mem, mem_coordinateZeroSubspace_iff]
  constructor
  · intro h i hi
    change x i + path.base i = 0
    rw [h i hi]
    exact ZModModule.add_self _
  · intro h i hi
    have hzero := h i hi
    change x i + path.base i = 0 at hzero
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans (ZMod.neg_eq_self_mod_two _)

/-- A path subcube has codimension equal to its root-to-leaf path length. -/
theorem codimension_coordinateZeroSubspace_eq_length (path : Path n α) :
    f₂Codimension (coordinateZeroSubspace path.support) = path.length := by
  exact f₂Codimension_coordinateZeroSubspace path.support

/-- The path indicator is definitionally the indicator of its affine coordinate subcube. -/
theorem indicator_eq_binaryAffineSubspace (path : Path n α) :
    path.indicator =
      setIndicator
        (binaryAffineSubspace (coordinateZeroSubspace path.support) path.base : Set 𝔽₂^[n]) := by
  unfold indicator
  rw [cylinder_eq_binaryAffineSubspace]

/-- Fourier scale `2⁻ℓ` of a path of length `ℓ`. -/
noncomputable def inversePathSize (path : Path n α) : ℝ :=
  ((2 : ℝ) ^ path.length)⁻¹

theorem inversePerpendicularCard_coordinateZeroSubspace (path : Path n α) :
    inversePerpendicularCard (coordinateZeroSubspace path.support) = path.inversePathSize := by
  simp [inversePerpendicularCard, inversePathSize, codimension_coordinateZeroSubspace_eq_length]

/-- A path indicator has Fourier sparsity `2` raised to its path length. -/
theorem spectralSparsity_indicator (path : Path n α) :
    spectralSparsity path.indicator = 2 ^ path.length := by
  rw [indicator_eq_binaryAffineSubspace,
    spectralSparsity_setIndicator_binaryAffineSubspace,
    codimension_coordinateZeroSubspace_eq_length]

/-- The Fourier one-norm of a path indicator is one. -/
theorem spectralPNorm_one_indicator (path : Path n α) :
    spectralPNorm 1 path.indicator = 1 := by
  rw [indicator_eq_binaryAffineSubspace,
    spectralPNorm_one_setIndicator_binaryAffineSubspace]

/-- A path indicator is granular at the scale determined by its length. -/
theorem isVectorFourierGranular_indicator (path : Path n α) :
    IsVectorFourierGranular path.indicator path.inversePathSize := by
  rw [indicator_eq_binaryAffineSubspace, ← inversePerpendicularCard_coordinateZeroSubspace]
  exact isVectorFourierGranular_setIndicator_binaryAffineSubspace
    (coordinateZeroSubspace path.support) path.base

/-- A path-subcube indicator has Fourier degree at most the path length. -/
theorem vectorFourierDegree_indicator_le_length (path : Path n α) :
    vectorFourierDegree path.indicator ≤ path.length := by
  rw [vectorFourierDegree_le_iff]
  intro γ hweight
  by_contra hcoeff
  have hperp : γ ∈ perpendicularSubspace (coordinateZeroSubspace path.support) := by
    apply (vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff
      (coordinateZeroSubspace path.support) path.base γ).1
    simpa only [indicator_eq_binaryAffineSubspace] using hcoeff
  have hcard : (f₂Support γ).card ≤ path.support.card :=
    Finset.card_le_card
      (f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
        path.support γ hperp)
  exact (Nat.not_lt_of_ge hcard) (by simpa [length] using hweight)

end Path

end F₂DecisionTree

end FABL
