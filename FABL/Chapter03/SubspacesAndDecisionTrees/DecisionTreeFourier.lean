/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.SubspacesAndDecisionTrees.DecisionTrees

/-!
# Fourier bounds for decision trees

Book items: Fact 3.15, Proposition 3.16, Proposition 3.17, Exercise 3.21, Exercise 3.22.

Path expansions, Fourier bounds, and depth truncation for decision trees.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

namespace F₂DecisionTree

variable {α : Type*}

/-! ### Fourier bounds from the path expansion -/

/-- The linear combination of path-subcube indicators with their leaf labels. -/
noncomputable def pathExpansion (pathList : List (Path n ℝ)) : 𝔽₂^[n] → ℝ :=
  fun x ↦ (pathList.map fun path ↦ path.output * path.indicator x).sum

@[simp] theorem pathExpansion_nil :
    pathExpansion ([] : List (Path n ℝ)) = 0 := by
  funext x
  simp [pathExpansion]

@[simp] theorem pathExpansion_cons (path : Path n ℝ) (pathList : List (Path n ℝ)) :
    pathExpansion (path :: pathList) =
      (fun x ↦ path.output * path.indicator x) + pathExpansion pathList := by
  funext x
  simp [pathExpansion]

/-- Fact 3.15 expressed using the reusable path-expansion function. -/
theorem eval_eq_pathExpansion {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) :
    T.eval = pathExpansion T.paths := by
  exact eval_eq_sum_pathIndicators_function T

/-- Fact 3.15 for a function represented by a decision tree. -/
theorem computes_eq_pathExpansion {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    f = pathExpansion T.paths := by
  exact hT.symm.trans (eval_eq_pathExpansion T)

@[simp] theorem vectorFourierCoeff_zero (gamma : 𝔽₂^[n]) :
    vectorFourierCoeff (0 : 𝔽₂^[n] → ℝ) gamma = 0 := by
  rw [vectorFourierCoeff_eq_expect]
  simp

/-- Fourier coefficients of a path expansion are the corresponding finite linear combination. -/
theorem vectorFourierCoeff_pathExpansion (pathList : List (Path n ℝ)) (gamma : 𝔽₂^[n]) :
    vectorFourierCoeff (pathExpansion pathList) gamma =
      (pathList.map fun path ↦
        path.output * vectorFourierCoeff path.indicator gamma).sum := by
  induction pathList with
  | nil => simp
  | cons path pathList ih =>
      rw [pathExpansion_cons, vectorFourierCoeff_add,
        vectorFourierCoeff_const_mul, ih]
      simp

/-- A sum of path indicators of length at most `k` has Fourier degree at most `k`. -/
theorem vectorFourierDegree_pathExpansion_le (pathList : List (Path n ℝ)) (k : ℕ)
    (hlength : ∀ path ∈ pathList, path.length ≤ k) :
    vectorFourierDegree (pathExpansion pathList) ≤ k := by
  rw [vectorFourierDegree_le_iff]
  intro gamma hweight
  rw [vectorFourierCoeff_pathExpansion]
  apply List.sum_eq_zero
  intro coefficient hcoefficient
  obtain ⟨path, hpath, rfl⟩ := List.mem_map.mp hcoefficient
  have hzero : vectorFourierCoeff path.indicator gamma = 0 := by
    apply (vectorFourierDegree_le_iff path.indicator path.length).1
      path.vectorFourierDegree_indicator_le_length gamma
    exact Nat.lt_of_le_of_lt (hlength path hpath) hweight
  rw [hzero, mul_zero]

/-- Exercise 3.21: the function executed by a tree has degree at most the tree depth. -/
theorem vectorFourierDegree_eval_le_depth {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) :
    vectorFourierDegree T.eval ≤ T.depth := by
  rw [eval_eq_pathExpansion]
  apply vectorFourierDegree_pathExpansion_le
  intro path hpath
  exact path_length_le_depth T path hpath

/-- Exercise 3.21: a function computed by a tree has degree at most that tree's depth. -/
theorem vectorFourierDegree_le_depth_of_computes {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    vectorFourierDegree f ≤ T.depth := by
  rw [← hT]
  exact vectorFourierDegree_eval_le_depth T

/-- The sparsity of a path expansion is bounded by the sum of the sparsities of its path
indicators. -/
theorem spectralSparsity_pathExpansion_le_sum (pathList : List (Path n ℝ)) :
    spectralSparsity (pathExpansion pathList) ≤
      (pathList.map fun path ↦ 2 ^ path.length).sum := by
  induction pathList with
  | nil =>
      simp [spectralSparsity, vectorFourierCoeff_eq_expect]
  | cons path pathList ih =>
      rw [pathExpansion_cons]
      calc
        spectralSparsity
            ((fun x ↦ path.output * path.indicator x) + pathExpansion pathList) ≤
            spectralSparsity (fun x ↦ path.output * path.indicator x) +
              spectralSparsity (pathExpansion pathList) :=
          spectralSparsity_add_le _ _
        _ ≤ spectralSparsity path.indicator +
              spectralSparsity (pathExpansion pathList) :=
          Nat.add_le_add_right
            (spectralSparsity_const_mul_le path.output path.indicator) _
        _ ≤ 2 ^ path.length +
              (pathList.map fun childPath ↦ 2 ^ childPath.length).sum :=
          Nat.add_le_add (Nat.le_of_eq path.spectralSparsity_indicator) ih
        _ = ((path :: pathList).map fun childPath ↦ 2 ^ childPath.length).sum := by
          rfl

/-- If every listed path has length at most `k`, its total indicator sparsity is at most the
number of paths times `2^k`. -/
theorem sum_two_pow_pathLength_le (pathList : List (Path n ℝ)) (k : ℕ)
    (hlength : ∀ path ∈ pathList, path.length ≤ k) :
    (pathList.map fun path ↦ 2 ^ path.length).sum ≤ pathList.length * 2 ^ k := by
  induction pathList with
  | nil => simp
  | cons path pathList ih =>
      have hpath : path.length ≤ k := hlength path (by simp)
      have htail : ∀ childPath ∈ pathList, childPath.length ≤ k := by
        intro childPath hchild
        exact hlength childPath (by simp [hchild])
      have hpow : 2 ^ path.length ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hpath
      have hsum := ih htail
      have hrhs : (path :: pathList).length * 2 ^ k =
          2 ^ k + pathList.length * 2 ^ k := by
        simp [Nat.add_mul, Nat.add_comm]
      rw [hrhs]
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add hpow hsum

/-- Exercise 3.21: a tree with size `s` and depth `k` has spectral sparsity at most `s 2^k`. -/
theorem spectralSparsity_eval_le_leafCount_mul_two_pow_depth
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available) :
    spectralSparsity T.eval ≤ T.leafCount * 2 ^ T.depth := by
  rw [eval_eq_pathExpansion]
  exact (spectralSparsity_pathExpansion_le_sum T.paths).trans
    (by
      rw [← length_paths_eq_leafCount T]
      apply sum_two_pow_pathLength_le
      intro path hpath
      exact path_length_le_depth T path hpath)

/-- Exercise 3.21: the size/depth sparsity bound is at most `4^k`. -/
theorem spectralSparsity_eval_le_four_pow_depth
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available) :
    spectralSparsity T.eval ≤ 4 ^ T.depth := by
  calc
    spectralSparsity T.eval ≤ T.leafCount * 2 ^ T.depth :=
      spectralSparsity_eval_le_leafCount_mul_two_pow_depth T
    _ ≤ 2 ^ T.depth * 2 ^ T.depth :=
      Nat.mul_le_mul_right (2 ^ T.depth) T.leafCount_le_two_pow_depth
    _ = 4 ^ T.depth := by
      rw [← mul_pow]
      norm_num

/-- Exercise 3.21 spectral-sparsity bounds for a represented function. -/
theorem spectralSparsity_le_of_computes {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    spectralSparsity f ≤ T.leafCount * 2 ^ T.depth ∧
      spectralSparsity f ≤ 4 ^ T.depth := by
  rw [← hT]
  exact ⟨spectralSparsity_eval_le_leafCount_mul_two_pow_depth T,
    spectralSparsity_eval_le_four_pow_depth T⟩

/-- The Fourier one-norm of a path expansion is bounded by the sum of the absolute leaf
labels. -/
theorem spectralPNorm_one_pathExpansion_le_sum_abs_output
    (pathList : List (Path n ℝ)) :
    spectralPNorm 1 (pathExpansion pathList) ≤
      (pathList.map fun path ↦ |path.output|).sum := by
  induction pathList with
  | nil =>
      simp [spectralPNorm, vectorFourierCoeff_eq_expect]
  | cons path pathList ih =>
      rw [pathExpansion_cons]
      calc
        spectralPNorm 1
            ((fun x ↦ path.output * path.indicator x) + pathExpansion pathList) ≤
            spectralPNorm 1 (fun x ↦ path.output * path.indicator x) +
              spectralPNorm 1 (pathExpansion pathList) :=
          spectralPNorm_one_add_le _ _
        _ = |path.output| + spectralPNorm 1 (pathExpansion pathList) := by
          rw [spectralPNorm_one_const_mul, Path.spectralPNorm_one_indicator, mul_one]
        _ ≤ |path.output| + (pathList.map fun childPath ↦ |childPath.output|).sum :=
          add_le_add (le_refl |path.output|) ih
        _ = ((path :: pathList).map fun childPath ↦ |childPath.output|).sum := by
          rfl

/-- A finite sum of terms bounded by `bound` is bounded by the list length times `bound`. -/
theorem sum_map_le_length_mul {beta : Type*} (items : List beta) (weight : beta → ℝ)
    (bound : ℝ) (hweight : ∀ item ∈ items, weight item ≤ bound) :
    (items.map weight).sum ≤ (items.length : ℝ) * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have hitem : weight item ≤ bound := hweight item (by simp)
      have htail : ∀ child ∈ items, weight child ≤ bound := by
        intro child hchild
        exact hweight child (by simp [hchild])
      calc
        ((item :: items).map weight).sum = weight item + (items.map weight).sum := by
          rfl
        _ ≤ bound + (items.length : ℝ) * bound :=
          add_le_add hitem (ih htail)
        _ = ((item :: items).length : ℝ) * bound := by
          simp
          ring

/-- A path label in a computing tree is bounded by the infinity norm of the represented
function. -/
theorem abs_path_output_le_binaryFunctionInfinityNorm {available : Finset (Fin n)}
    (T : F₂DecisionTree n ℝ available) (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f)
    (path : Path n ℝ) (hpath : path ∈ T.paths) :
    |path.output| ≤ binaryFunctionInfinityNorm f := by
  have hvalue : f path.base = path.output :=
    computes_eq_path_output_of_matches T f hT path hpath path.base path.matches_base
  rw [← hvalue]
  exact abs_le_binaryFunctionInfinityNorm f path.base

/-- The sum of absolute leaf labels is bounded by tree size times the represented function's
infinity norm. -/
theorem sum_abs_pathOutput_le_leafCount_mul_infinityNorm
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    (T.paths.map fun path ↦ |path.output|).sum ≤
      (T.leafCount : ℝ) * binaryFunctionInfinityNorm f := by
  rw [← length_paths_eq_leafCount T]
  exact sum_map_le_length_mul T.paths (fun path ↦ |path.output|)
    (binaryFunctionInfinityNorm f)
    (fun path hpath ↦ abs_path_output_le_binaryFunctionInfinityNorm T f hT path hpath)

/-- Exercise 3.21: the Fourier one-norm is at most the infinity norm times tree size. -/
theorem spectralPNorm_one_le_infinityNorm_mul_leafCount_of_computes
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    spectralPNorm 1 f ≤ binaryFunctionInfinityNorm f * (T.leafCount : ℝ) := by
  rw [computes_eq_pathExpansion T f hT]
  calc
    spectralPNorm 1 (pathExpansion T.paths) ≤
        (T.paths.map fun path ↦ |path.output|).sum :=
      spectralPNorm_one_pathExpansion_le_sum_abs_output T.paths
    _ ≤ (T.leafCount : ℝ) *
        binaryFunctionInfinityNorm (pathExpansion T.paths) :=
      sum_abs_pathOutput_le_leafCount_mul_infinityNorm T
        (pathExpansion T.paths) (eval_eq_pathExpansion T)
    _ = binaryFunctionInfinityNorm (pathExpansion T.paths) * (T.leafCount : ℝ) := by
      ring

/-- Exercise 3.21: replacing size by `2^depth` in the Fourier one-norm bound. -/
theorem spectralPNorm_one_le_infinityNorm_mul_two_pow_depth_of_computes
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f) :
    spectralPNorm 1 f ≤ binaryFunctionInfinityNorm f * ((2 ^ T.depth : ℕ) : ℝ) := by
  calc
    spectralPNorm 1 f ≤ binaryFunctionInfinityNorm f * (T.leafCount : ℝ) :=
      spectralPNorm_one_le_infinityNorm_mul_leafCount_of_computes T f hT
    _ ≤ binaryFunctionInfinityNorm f * ((2 ^ T.depth : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (binaryFunctionInfinityNorm_nonneg f)
      exact_mod_cast T.leafCount_le_two_pow_depth

/-- An integer multiple of a path indicator is granular at the scale of any upper bound on the
path length. -/
theorem isVectorFourierGranular_intCast_mul_pathIndicator
    (path : Path n ℝ) (k : ℕ) (hlength : path.length ≤ k) (z : ℤ) :
    IsVectorFourierGranular
      (fun x ↦ (z : ℝ) * path.indicator x) (((2 : ℝ) ^ k)⁻¹) := by
  have hscale : path.inversePathSize =
      ((Int.ofNat (2 ^ (k - path.length)) : ℤ) : ℝ) * (((2 : ℝ) ^ k)⁻¹) := by
    simpa [Path.inversePathSize] using
      (inverse_two_pow_eq_natCast_mul_inverse_two_pow hlength)
  exact (path.isVectorFourierGranular_indicator.refine
    (Int.ofNat (2 ^ (k - path.length))) hscale).intCast_mul z

/-- A path expansion with integer leaf labels and path length at most `k` is `2⁻ᵏ`-granular. -/
theorem isVectorFourierGranular_pathExpansion (pathList : List (Path n ℝ)) (k : ℕ)
    (hlength : ∀ path ∈ pathList, path.length ≤ k)
    (hinteger : ∀ path ∈ pathList, ∃ z : ℤ, path.output = (z : ℝ)) :
    IsVectorFourierGranular (pathExpansion pathList) (((2 : ℝ) ^ k)⁻¹) := by
  induction pathList with
  | nil =>
      simpa using (isVectorFourierGranular_zero (n := n) (((2 : ℝ) ^ k)⁻¹))
  | cons path pathList ih =>
      obtain ⟨z, hz⟩ := hinteger path (by simp)
      have hpathLength : path.length ≤ k := hlength path (by simp)
      have htailLength : ∀ childPath ∈ pathList, childPath.length ≤ k := by
        intro childPath hchild
        exact hlength childPath (by simp [hchild])
      have htailInteger : ∀ childPath ∈ pathList,
          ∃ childZ : ℤ, childPath.output = (childZ : ℝ) := by
        intro childPath hchild
        exact hinteger childPath (by simp [hchild])
      rw [pathExpansion_cons, hz]
      exact (isVectorFourierGranular_intCast_mul_pathIndicator path k hpathLength z).add
        (ih htailLength htailInteger)

/-- Exercise 3.21: an integer-valued function computed by a depth-`k` tree has a
`2⁻ᵏ`-granular Fourier transform. -/
theorem isVectorFourierGranular_inverseTwoPowDepth_of_computes_int
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (f : 𝔽₂^[n] → ℤ) (hT : T.Computes (fun x ↦ (f x : ℝ))) :
    IsVectorFourierGranular (fun x ↦ (f x : ℝ)) (((2 : ℝ) ^ T.depth)⁻¹) := by
  rw [computes_eq_pathExpansion T (fun x ↦ (f x : ℝ)) hT]
  apply isVectorFourierGranular_pathExpansion T.paths T.depth
  · intro path hpath
    exact path_length_le_depth T path hpath
  · intro path hpath
    refine ⟨f path.base, ?_⟩
    exact (computes_eq_path_output_of_matches T (fun x ↦ (f x : ℝ)) hT
      path hpath path.base path.matches_base).symm

/-! ### Depth truncation and Fourier concentration -/

namespace Path

/-- A path indicator is pointwise nonnegative. -/
theorem indicator_nonneg (path : Path n α) (x : 𝔽₂^[n]) :
    0 ≤ path.indicator x := by
  by_cases hmatches : path.Matches x
  · rw [path.indicator_eq_one_of_matches x hmatches]
    norm_num
  · rw [path.indicator_eq_zero_of_not_matches x hmatches]

/-- The uniform expectation of a path indicator is `2` to the negative path length. -/
theorem expect_indicator (path : Path n α) :
    (𝔼 x, path.indicator x) = path.inversePathSize := by
  calc
    (𝔼 x, path.indicator x) = vectorFourierCoeff path.indicator 0 := by
      rw [vectorFourierCoeff_eq_expect]
      simp
    _ = inversePerpendicularCard (coordinateZeroSubspace path.support) := by
      rw [path.indicator_eq_binaryAffineSubspace,
        vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem]
      · simp
      · exact (perpendicularSubspace (coordinateZeroSubspace path.support)).zero_mem
    _ = path.inversePathSize := path.inversePerpendicularCard_coordinateZeroSubspace

end Path

/-- Sum of the indicators of paths whose length is strictly larger than `k`. -/
noncomputable def longPathIndicatorSum (pathList : List (Path n α)) (k : ℕ) :
    𝔽₂^[n] → ℝ :=
  fun x ↦ (pathList.map fun path ↦
    if k < path.length then path.indicator x else 0).sum

/-- The long-path indicator sum is nonnegative. -/
theorem longPathIndicatorSum_nonneg (pathList : List (Path n α)) (k : ℕ)
    (x : 𝔽₂^[n]) :
    0 ≤ longPathIndicatorSum pathList k x := by
  unfold longPathIndicatorSum
  apply List.sum_nonneg
  intro value hvalue
  obtain ⟨path, hpath, rfl⟩ := List.mem_map.mp hvalue
  split_ifs
  · exact path.indicator_nonneg x
  · exact le_rfl

/-- A matching long path contributes one to the long-path indicator sum. -/
theorem one_le_longPathIndicatorSum_of_mem_of_matches
    (pathList : List (Path n α)) (k : ℕ) (path : Path n α)
    (hpath : path ∈ pathList) (hlong : k < path.length) (x : 𝔽₂^[n])
    (hmatches : path.Matches x) :
    1 ≤ longPathIndicatorSum pathList k x := by
  induction pathList with
  | nil => simp at hpath
  | cons head tail ih =>
      rw [longPathIndicatorSum]
      simp only [List.map_cons, List.sum_cons]
      by_cases hhead : head = path
      · subst head
        rw [if_pos hlong, path.indicator_eq_one_of_matches x hmatches]
        exact le_add_of_nonneg_right (longPathIndicatorSum_nonneg tail k x)
      · have htail : path ∈ tail := by
          have hne : path ≠ head := Ne.symm hhead
          simpa [hne] using hpath
        have hih := ih htail
        change 1 ≤ (if k < head.length then head.indicator x else 0) +
          longPathIndicatorSum tail k x
        have hterm : 0 ≤ (if k < head.length then head.indicator x else 0) := by
          split_ifs
          · exact head.indicator_nonneg x
          · exact le_rfl
        linarith

/-- Expectation of the long-path indicator sum is the sum of the path-subcube probabilities. -/
theorem expect_longPathIndicatorSum (pathList : List (Path n α)) (k : ℕ) :
    (𝔼 x, longPathIndicatorSum pathList k x) =
      (pathList.map fun path ↦
        if k < path.length then path.inversePathSize else 0).sum := by
  induction pathList with
  | nil => simp [longPathIndicatorSum]
  | cons path pathList ih =>
      change (𝔼 x, (
          (if k < path.length then path.indicator x else 0) +
            longPathIndicatorSum pathList k x)) =
        (if k < path.length then path.inversePathSize else 0) +
          (pathList.map fun childPath ↦
            if k < childPath.length then childPath.inversePathSize else 0).sum
      rw [Finset.expect_add_distrib, ih]
      by_cases hlong : k < path.length
      · simp [hlong, path.expect_indicator]
      · simp [hlong]

/-- Longer paths have no more uniform mass than the depth-`k` scale. -/
theorem inversePathSize_le_inverseTwoPow (path : Path n α) (k : ℕ)
    (hlength : k ≤ path.length) :
    path.inversePathSize ≤ ((2 : ℝ) ^ k)⁻¹ := by
  unfold Path.inversePathSize
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact pow_le_pow_right₀ (by norm_num) hlength

/-- The total probability mass of paths longer than `k` is at most the number of paths times
`2⁻ᵏ`. -/
theorem sum_longPath_inversePathSize_le (pathList : List (Path n α)) (k : ℕ) :
    (pathList.map fun path ↦
      if k < path.length then path.inversePathSize else 0).sum ≤
      (pathList.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  apply sum_map_le_length_mul pathList
    (fun path ↦ if k < path.length then path.inversePathSize else 0)
    (((2 : ℝ) ^ k)⁻¹)
  intro path hpath
  by_cases hlong : k < path.length
  · rw [if_pos hlong]
    exact inversePathSize_le_inverseTwoPow path k hlong.le
  · rw [if_neg hlong]
    positivity

/-- Fourier weight strictly above a natural cutoff, in vector indexing. -/
noncomputable def vectorFourierWeightAbove (k : ℕ) (f : 𝔽₂^[n] → ℝ) : ℝ :=
  ∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦ k < (f₂Support γ).card),
    vectorFourierCoeff f γ ^ 2

/-- The vector-indexed tail agrees with the Chapter 1 tail after the canonical cube bridge. -/
theorem vectorFourierWeightAbove_eq_fourierWeightAbove_binaryFunctionOnSignCube
    (k : ℕ) (f : 𝔽₂^[n] → ℝ) :
    vectorFourierWeightAbove k f =
      fourierWeightAbove k (binaryFunctionOnSignCube f) := by
  classical
  unfold vectorFourierWeightAbove fourierWeightAbove fourierWeight
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (f₂CubeEquivFinset n)
  intro γ
  simp only [f₂CubeEquivFinset_apply]
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]

/-- Vector Fourier coefficients commute with subtraction. -/
theorem vectorFourierCoeff_sub (f g : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (fun x ↦ f x - g x) γ =
      vectorFourierCoeff f γ - vectorFourierCoeff g γ := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect,
    vectorFourierCoeff_eq_expect]
  simp only [sub_mul]
  exact Finset.expect_sub_distrib _ _ _

/-- Parseval: the tail above `k` is controlled by squared approximation error to any function
of degree at most `k`. -/
theorem vectorFourierWeightAbove_le_expect_sq_sub_of_degree_le
    (f g : 𝔽₂^[n] → ℝ) (k : ℕ) (hdegree : vectorFourierDegree g ≤ k) :
    vectorFourierWeightAbove k f ≤ 𝔼 x, (f x - g x) ^ 2 := by
  classical
  let residual : 𝔽₂^[n] → ℝ := fun x ↦ f x - g x
  calc
    vectorFourierWeightAbove k f =
        ∑ γ ∈ (Finset.univ.filter fun γ : 𝔽₂^[n] ↦
          k < (f₂Support γ).card), vectorFourierCoeff residual γ ^ 2 := by
      unfold vectorFourierWeightAbove
      apply Finset.sum_congr rfl
      intro γ hγ
      have hg : vectorFourierCoeff g γ = 0 :=
        (vectorFourierDegree_le_iff g k).1 hdegree γ (Finset.mem_filter.mp hγ).2
      rw [show vectorFourierCoeff residual γ =
          vectorFourierCoeff f γ - vectorFourierCoeff g γ by
        exact vectorFourierCoeff_sub f g γ, hg, sub_zero]
    _ ≤ ∑ γ, vectorFourierCoeff residual γ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun γ _ _ ↦ sq_nonneg (vectorFourierCoeff residual γ))
    _ = 𝔼 x, residual x * residual x := by
      simpa [pow_two] using (vector_plancherel residual residual).symm
    _ = 𝔼 x, (f x - g x) ^ 2 := by
      apply Finset.expect_congr rfl
      intro x hx
      simp only [residual]
      ring

/-- Every decision tree has at least one leaf. -/
theorem leafCount_pos {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) :
    0 < T.leafCount := by
  induction T with
  | leaf value => simp [leafCount]
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [leafCount]
      omega

/-- Union-bound form of Exercise 3.22: depth-`k` truncation changes the original function on at
most `s 2⁻ᵏ` of the cube, independently of the chosen fallback label. -/
theorem relativeHammingDist_eval_truncate_le [DecidableEq α]
    {available : Finset (Fin n)} (T : F₂DecisionTree n α available)
    (fallback : α) (k : ℕ) :
    relativeHammingDist T.eval (T.truncate fallback k).eval ≤
      (T.leafCount : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  classical
  rw [← uniformProbability_ne_eq_relativeHammingDist]
  unfold uniformProbability
  calc
    (𝔼 x, if T.eval x ≠ (T.truncate fallback k).eval x then (1 : ℝ) else 0) ≤
        𝔼 x, longPathIndicatorSum T.paths k x := by
      apply Finset.expect_le_expect
      intro x hx
      by_cases hne : T.eval x ≠ (T.truncate fallback k).eval x
      · rw [if_pos hne]
        obtain ⟨path, hpath, hmatches, hlong⟩ :=
          exists_long_path_of_eval_truncate_ne T fallback k x hne.symm
        exact one_le_longPathIndicatorSum_of_mem_of_matches
          T.paths k path hpath hlong x hmatches
      · rw [if_neg hne]
        exact longPathIndicatorSum_nonneg T.paths k x
    _ = (T.paths.map fun path ↦
          if k < path.length then path.inversePathSize else 0).sum :=
      expect_longPathIndicatorSum T.paths k
    _ ≤ (T.paths.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ :=
      sum_longPath_inversePathSize_le T.paths k
    _ = (T.leafCount : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
      rw [length_paths_eq_leafCount]

/-- Explicit base-two cutoff `⌈log₂(s / ε)⌉`. -/
noncomputable def decisionTreeTruncationDegree (s : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((s : ℝ) / ε)⌉₊

/-- The explicit cutoff satisfies `s 2⁻ᵏ ≤ ε`. -/
theorem mul_inverseTwoPow_decisionTreeTruncationDegree_le
    (s : ℕ) {ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    (s : ℝ) * ((2 : ℝ) ^ decisionTreeTruncationDegree s ε)⁻¹ ≤ ε := by
  let ratio : ℝ := (s : ℝ) / ε
  have hratio : 0 < ratio := div_pos (by exact_mod_cast hs) hε
  have hlog : Real.logb 2 ratio ≤ (decisionTreeTruncationDegree s ε : ℝ) := by
    exact Nat.le_ceil _
  have hratioPow : ratio ≤ (2 : ℝ) ^ decisionTreeTruncationDegree s ε := by
    have hrpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hratio).1 hlog
    simpa [Real.rpow_natCast] using hrpow
  have hsPow : (s : ℝ) ≤ ε * (2 : ℝ) ^ decisionTreeTruncationDegree s ε := by
    have := (div_le_iff₀ hε).1 hratioPow
    simpa [ratio, mul_comm] using this
  rw [← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^
    decisionTreeTruncationDegree s ε)).2 hsPow

/-- Exercise 3.22 with its explicit cutoff: arbitrary fallback labels give an `ε`-close
truncation. -/
theorem relativeHammingDist_eval_truncate_decisionTreeTruncationDegree_le
    [DecidableEq α] {available : Finset (Fin n)}
    (T : F₂DecisionTree n α available) (fallback : α) {ε : ℝ} (hε : 0 < ε) :
    relativeHammingDist T.eval
      (T.truncate fallback (decisionTreeTruncationDegree T.leafCount ε)).eval ≤ ε := by
  exact (relativeHammingDist_eval_truncate_le T fallback
    (decisionTreeTruncationDegree T.leafCount ε)).trans
      (mul_inverseTwoPow_decisionTreeTruncationDegree_le T.leafCount T.leafCount_pos hε)

/-- Exercise 3.22 in existential form, including the depth guarantee on the truncated tree. -/
theorem exists_truncatedTree_close {available : Finset (Fin n)} [DecidableEq α]
    (T : F₂DecisionTree n α available) (fallback : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ T' : F₂DecisionTree n α available,
      T'.depth ≤ decisionTreeTruncationDegree T.leafCount ε ∧
        relativeHammingDist T.eval T'.eval ≤ ε := by
  exact ⟨T.truncate fallback (decisionTreeTruncationDegree T.leafCount ε),
    T.depth_truncate_le fallback (decisionTreeTruncationDegree T.leafCount ε),
    relativeHammingDist_eval_truncate_decisionTreeTruncationDegree_le T fallback hε⟩

/-- For a sign-valued real function, the squared error of zero-labeled truncation is bounded
pointwise by the long-path union bound. -/
theorem sq_sub_eval_truncate_zero_le_longPathIndicatorSum
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available) (k : ℕ)
    (hsign : ∀ x, T.eval x = -1 ∨ T.eval x = 1) (x : 𝔽₂^[n]) :
    (T.eval x - (T.truncate 0 k).eval x) ^ 2 ≤
      longPathIndicatorSum T.paths k x := by
  rcases eval_truncate_eq_eval_or_eq_fallback T 0 k x with hsame | hzero
  · rw [hsame, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact longPathIndicatorSum_nonneg T.paths k x
  · have hne : (T.truncate 0 k).eval x ≠ T.eval x := by
      intro heq
      have hevalZero : T.eval x = 0 := heq.symm.trans hzero
      rcases hsign x with heval | heval <;> rw [heval] at hevalZero <;> norm_num at hevalZero
    obtain ⟨path, hpath, hmatches, hlong⟩ :=
      exists_long_path_of_eval_truncate_ne T 0 k x hne
    have hone := one_le_longPathIndicatorSum_of_mem_of_matches
      T.paths k path hpath hlong x hmatches
    rcases hsign x with heval | heval <;> simpa [hzero, heval] using hone

/-- The mean squared error of zero-labeled depth truncation is at most `s 2⁻ᵏ`. -/
theorem expect_sq_sub_eval_truncate_zero_le
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available) (k : ℕ)
    (hsign : ∀ x, T.eval x = -1 ∨ T.eval x = 1) :
    (𝔼 x, (T.eval x - (T.truncate 0 k).eval x) ^ 2) ≤
      (T.leafCount : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  calc
    (𝔼 x, (T.eval x - (T.truncate 0 k).eval x) ^ 2) ≤
        𝔼 x, longPathIndicatorSum T.paths k x := by
      apply Finset.expect_le_expect
      intro x hx
      exact sq_sub_eval_truncate_zero_le_longPathIndicatorSum T k hsign x
    _ = (T.paths.map fun path ↦
          if k < path.length then path.inversePathSize else 0).sum :=
      expect_longPathIndicatorSum T.paths k
    _ ≤ (T.paths.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ :=
      sum_longPath_inversePathSize_le T.paths k
    _ = (T.leafCount : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
      rw [length_paths_eq_leafCount]

/-- Fourier-tail form of depth truncation: a sign-valued size-`s` tree has weight above `k`
at most `s 2⁻ᵏ`. -/
theorem vectorFourierWeightAbove_eval_le_leafCount_mul_inverseTwoPow
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available) (k : ℕ)
    (hsign : ∀ x, T.eval x = -1 ∨ T.eval x = 1) :
    vectorFourierWeightAbove k T.eval ≤
      (T.leafCount : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  let truncatedTree := T.truncate 0 k
  have hdegree : vectorFourierDegree truncatedTree.eval ≤ k :=
    (vectorFourierDegree_eval_le_depth truncatedTree).trans (T.depth_truncate_le 0 k)
  exact (vectorFourierWeightAbove_le_expect_sq_sub_of_degree_le
    T.eval truncatedTree.eval k hdegree).trans
      (expect_sq_sub_eval_truncate_zero_le T k hsign)

/-- Proposition 3.17 in vector indexing at the exact integer cutoff. The book writes
`log(s / ε)` and suppresses the integer rounding; the executable convention here is
`k = ⌈log₂(s / ε)⌉`. -/
theorem vectorFourierWeightAbove_decisionTreeTruncationDegree_le
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hsign : ∀ x, T.eval x = -1 ∨ T.eval x = 1) :
    vectorFourierWeightAbove (decisionTreeTruncationDegree T.leafCount ε) T.eval ≤ ε := by
  have htail := vectorFourierWeightAbove_eval_le_leafCount_mul_inverseTwoPow T
    (decisionTreeTruncationDegree T.leafCount ε) hsign
  exact htail.trans (mul_inverseTwoPow_decisionTreeTruncationDegree_le
    T.leafCount T.leafCount_pos hε.1)

/-- Proposition 3.17 in the Chapter 3 spectral-concentration API, with explicit base-two
ceiling and the book's boundary condition `ε ∈ (0, 1]`. -/
theorem isFourierSpectrumConcentratedUpTo_of_decisionTree
    {available : Finset (Fin n)} (T : F₂DecisionTree n ℝ available)
    (f : 𝔽₂^[n] → ℝ) (hT : T.Computes f)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hsign : ∀ x, f x = -1 ∨ f x = 1) :
    IsFourierSpectrumConcentratedUpTo
      (binaryFunctionOnSignCube f) ε
      (decisionTreeTruncationDegree T.leafCount ε : ℝ) := by
  unfold IsFourierSpectrumConcentratedUpTo
  rw [fourierWeightAboveReal_natCast,
    ← vectorFourierWeightAbove_eq_fourierWeightAbove_binaryFunctionOnSignCube]
  have hsignEval : ∀ x, T.eval x = -1 ∨ T.eval x = 1 := by
    intro x
    rw [hT]
    exact hsign x
  have htail := vectorFourierWeightAbove_decisionTreeTruncationDegree_le
    T hε hsignEval
  rw [← hT]
  exact htail

end F₂DecisionTree

end FABL
