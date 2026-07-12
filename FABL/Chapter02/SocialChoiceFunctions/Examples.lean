/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.SocialChoiceFunctions.MayTheorem

/-!
# Social choice examples

Book items: Definition 2.10, Definition 2.11, Example 2.9.

Structural properties of majority, dictators, recursive majority, tribes, and the impartial-culture
law from Section 2.1 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 2.10: every two coordinates are equivalent under a symmetry of `f`. -/
def IsTransitiveSymmetric {β : Type*} (f : {−1,1}^[n] → β) : Prop :=
  ∀ i i' : Fin n, ∃ π : Equiv.Perm (Fin n),
    π i = i' ∧ ∀ x : {−1,1}^[n], f (permuteInput π x) = f x

/-- Full coordinate symmetry implies transitive symmetry. -/
theorem IsSymmetric.isTransitiveSymmetric {β : Type*} {f : {−1,1}^[n] → β}
    (hf : IsSymmetric f) : IsTransitiveSymmetric f := by
  intro i i'
  refine ⟨Equiv.swap i i', Equiv.swap_apply_left i i', ?_⟩
  exact hf (Equiv.swap i i')

/-- Majority is monotone. -/
theorem majority_monotone (n : ℕ) : Monotone (majority n) := by
  intro x y hxy
  apply monotone_thresholdSign
  apply Finset.sum_le_sum
  intro i hi
  exact monotone_signValue (hxy i)

/-- Majority is odd when its arity is odd. -/
theorem majority_odd (hn : Odd n) : Function.Odd (majority n) := by
  intro x
  have hsum := sum_signValue_ne_zero_of_odd hn x
  simp only [majority, Pi.neg_apply, signValue]
  rw [show (∑ i, ((-x i : Sign) : ℤ) : ℝ) = -(∑ i, ((x i : Sign) : ℤ) : ℝ) by
    simp]
  exact thresholdSign_neg _ hsum

/-- Majority is invariant under every coordinate permutation. -/
theorem majority_symmetric (n : ℕ) : IsSymmetric (majority n) := by
  intro π x
  simp only [majority, permuteInput]
  congr 1
  exact Equiv.sum_comp π (fun i ↦ signValue (x i))

/-- Majority is transitive-symmetric. -/
theorem majority_transitiveSymmetric (n : ℕ) : IsTransitiveSymmetric (majority n) :=
  (majority_symmetric n).isTransitiveSymmetric

/-- A nonempty majority function is unanimous. -/
theorem majority_unanimous (n : ℕ) (hn : 0 < n) : IsUnanimous (majority n) := by
  constructor
  · simp [majority, thresholdSign]
  · simp [majority, thresholdSign, hn.ne']

/-- Recursive majority is monotone at every depth. -/
theorem recursiveMajority_monotone (n : ℕ) :
    ∀ d, Monotone (recursiveMajority n d)
  | 0 => by
      intro x y hxy
      exact hxy 0
  | d + 1 => by
      intro x y hxy
      apply majority_monotone
      intro i
      apply recursiveMajority_monotone n d
      intro j
      exact hxy _

/-- Recursive majority of odd arity is odd at every depth. -/
theorem recursiveMajority_odd (hn : Odd n) :
    ∀ d, Function.Odd (recursiveMajority n d)
  | 0 => by
      intro x
      rfl
  | d + 1 => by
      intro x
      simp only [recursiveMajority_succ]
      rw [show (fun i ↦ recursiveMajority n d (recursiveInputBlock (-x) i)) =
          -(fun i ↦ recursiveMajority n d (recursiveInputBlock x i)) by
        funext i
        rw [show recursiveInputBlock (-x) i = -(recursiveInputBlock x i) by rfl]
        exact recursiveMajority_odd hn d (recursiveInputBlock x i)]
      exact majority_odd hn _

/-- Recursive majority of positive arity is unanimous at every depth. -/
theorem recursiveMajority_unanimous (n : ℕ) (hn : 0 < n) :
    ∀ d, IsUnanimous (recursiveMajority n d)
  | 0 => by
      constructor <;> rfl
  | d + 1 => by
      rcases recursiveMajority_unanimous n hn d with ⟨hp, hm⟩
      constructor
      · simp only [recursiveMajority_succ]
        rw [show (fun i ↦ recursiveMajority n d
            (recursiveInputBlock (fun _ ↦ 1) i)) = (fun _ ↦ 1) by
          funext i
          simpa [recursiveInputBlock] using hp]
        exact (majority_unanimous n hn).1
      · simp only [recursiveMajority_succ]
        rw [show (fun i ↦ recursiveMajority n d
            (recursiveInputBlock (fun _ ↦ -1) i)) = (fun _ ↦ -1) by
          funext i
          simpa [recursiveInputBlock] using hm]
        exact (majority_unanimous n hn).2

/-- A dictator is monotone. -/
theorem dictator_monotone (i : Fin n) : Monotone (dictator i) := by
  intro x y hxy
  exact hxy i

/-- A dictator is odd. -/
theorem dictator_odd (i : Fin n) : Function.Odd (dictator i) := by
  intro x
  rfl

/-- A dictator is unanimous. -/
theorem dictator_unanimous (i : Fin n) : IsUnanimous (dictator i) := by
  simp [IsUnanimous, dictator]

/-- The AND function is monotone. -/
theorem andFunction_monotone (n : ℕ) : Monotone (andFunction n) := by
  intro x y hxy
  by_cases hx : ∀ i, x i = -1
  · simp only [andFunction, if_pos hx]
    exact neg_one_le_sign _
  · have hy : ¬∀ i, y i = -1 := by
      intro hy
      apply hx
      intro i
      apply sign_eq_neg_one_of_le_neg_one
      simpa [hy i] using hxy i
    simp [andFunction, hx, hy]

/-- The OR function is monotone. -/
theorem orFunction_monotone (n : ℕ) : Monotone (orFunction n) := by
  intro x y hxy
  by_cases hy : ∀ i, y i = 1
  · simp only [orFunction, if_pos hy]
    exact sign_le_one _
  · have hx : ¬∀ i, x i = 1 := by
      intro hx
      apply hy
      intro i
      apply sign_eq_one_of_one_le
      simpa [hx i] using hxy i
    simp [orFunction, hx, hy]

/-- For arity at least two, AND is not odd. -/
theorem andFunction_not_odd (n : ℕ) (hn : 1 < n) : ¬Function.Odd (andFunction n) := by
  intro hodd
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, hn⟩
  let x : {−1,1}^[n] := fun i ↦ if i = i₀ then 1 else -1
  have hxi : x i₀ = 1 := by simp [x]
  have hxj : x i₁ = -1 := by
    simp [x, i₀, i₁, Fin.ext_iff]
  have hxnot : ¬∀ i, x i = -1 := by
    intro h
    have := h i₀
    rw [hxi] at this
    norm_num at this
  have hnegnot : ¬∀ i, (-x) i = -1 := by
    intro h
    have := h i₁
    simp [hxj] at this
  have hxval : andFunction n x = 1 := by simp [andFunction, hxnot]
  have hnegval : andFunction n (-x) = 1 := by
    change (if ∀ i, (-x) i = -1 then -1 else 1) = 1
    rw [if_neg hnegnot]
  have := hodd x
  rw [hxval, hnegval] at this
  norm_num at this

/-- For arity at least two, OR is not odd. -/
theorem orFunction_not_odd (n : ℕ) (hn : 1 < n) : ¬Function.Odd (orFunction n) := by
  intro hodd
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, hn⟩
  let x : {−1,1}^[n] := fun i ↦ if i = i₀ then -1 else 1
  have hxi : x i₀ = -1 := by simp [x]
  have hxj : x i₁ = 1 := by
    simp [x, i₀, i₁, Fin.ext_iff]
  have hxnot : ¬∀ i, x i = 1 := by
    intro h
    have := h i₀
    rw [hxi] at this
    norm_num at this
  have hnegnot : ¬∀ i, (-x) i = 1 := by
    intro h
    have := h i₁
    simp [hxj] at this
  have hxval : orFunction n x = -1 := by simp [orFunction, hxnot]
  have hnegval : orFunction n (-x) = -1 := by
    change (if ∀ i, (-x) i = 1 then 1 else -1) = -1
    rw [if_neg hnegnot]
  have := hodd x
  rw [hxval, hnegval] at this
  norm_num at this

/-- AND is unanimous on a nonempty cube. -/
theorem andFunction_unanimous (n : ℕ) (hn : 0 < n) : IsUnanimous (andFunction n) := by
  constructor
  · have h : ¬∀ i : Fin n, (1 : Sign) = -1 := by
      intro h'
      have := h' ⟨0, hn⟩
      norm_num at this
    change (if ∀ i : Fin n, (1 : Sign) = -1 then -1 else 1) = 1
    rw [if_neg h]
  · change (if ∀ i : Fin n, (-1 : Sign) = -1 then -1 else 1) = -1
    rw [if_pos (by simp)]

/-- OR is unanimous on a nonempty cube. -/
theorem orFunction_unanimous (n : ℕ) (hn : 0 < n) : IsUnanimous (orFunction n) := by
  constructor
  · change (if ∀ i : Fin n, (1 : Sign) = 1 then 1 else -1) = 1
    rw [if_pos (by simp)]
  · have h : ¬∀ i : Fin n, (-1 : Sign) = 1 := by
      intro h'
      have := h' ⟨0, hn⟩
      norm_num at this
    change (if ∀ i : Fin n, (-1 : Sign) = 1 then 1 else -1) = -1
    rw [if_neg h]

/-- AND is invariant under coordinate permutations. -/
theorem andFunction_symmetric (n : ℕ) : IsSymmetric (andFunction n) := by
  intro π x
  simp only [andFunction, permuteInput]
  congr 1
  apply propext
  constructor <;> intro h i
  · simpa using h (π.symm i)
  · exact h (π i)

/-- AND is transitive-symmetric. -/
theorem andFunction_transitiveSymmetric (n : ℕ) :
    IsTransitiveSymmetric (andFunction n) :=
  (andFunction_symmetric n).isTransitiveSymmetric

/-- OR is invariant under coordinate permutations. -/
theorem orFunction_symmetric (n : ℕ) : IsSymmetric (orFunction n) := by
  intro π x
  simp only [orFunction, permuteInput]
  congr 1
  apply propext
  constructor <;> intro h i
  · simpa using h (π.symm i)
  · exact h (π i)

/-- OR is transitive-symmetric. -/
theorem orFunction_transitiveSymmetric (n : ℕ) :
    IsTransitiveSymmetric (orFunction n) :=
  (orFunction_symmetric n).isTransitiveSymmetric

/-- Tribes is monotone. -/
theorem tribes_monotone (w s : ℕ) : Monotone (tribes w s) := by
  intro x y hxy
  apply orFunction_monotone
  intro i
  apply andFunction_monotone
  intro j
  exact hxy _

/-- Tribes is unanimous when both its block width and number of blocks are positive. -/
theorem tribes_unanimous (w s : ℕ) (hw : 0 < w) (hs : 0 < s) :
    IsUnanimous (tribes w s) := by
  rcases andFunction_unanimous w hw with ⟨handPos, handNeg⟩
  rcases orFunction_unanimous s hs with ⟨horPos, horNeg⟩
  constructor
  · change orFunction s (fun i ↦ andFunction w (inputBlock (fun _ ↦ 1) i)) = 1
    rw [show (fun i ↦ andFunction w (inputBlock (fun _ ↦ 1) i)) = (fun _ ↦ 1) by
      funext i
      simpa [inputBlock] using handPos]
    exact horPos
  · change orFunction s (fun i ↦ andFunction w (inputBlock (fun _ ↦ -1) i)) = -1
    rw [show (fun i ↦ andFunction w (inputBlock (fun _ ↦ -1) i)) = (fun _ ↦ -1) by
      funext i
      simpa [inputBlock] using handNeg]
    exact horNeg

/-- Permute the blocks and, uniformly, the positions within each block. -/
def blockCoordinatePermutation {s w : ℕ} (σ : Equiv.Perm (Fin s))
    (τ : Equiv.Perm (Fin w)) : Equiv.Perm (Fin (s * w)) :=
  finProdFinEquiv.symm.trans ((σ.prodCongr τ).trans finProdFinEquiv)

@[simp] theorem blockCoordinatePermutation_apply {s w : ℕ} (σ : Equiv.Perm (Fin s))
    (τ : Equiv.Perm (Fin w)) (i : Fin s) (j : Fin w) :
    blockCoordinatePermutation σ τ (finProdFinEquiv (i, j)) =
      finProdFinEquiv (σ i, τ j) := by
  simp [blockCoordinatePermutation]

/-- Tribes is invariant under block permutations and uniform within-block permutations. -/
theorem tribes_blockCoordinatePermutation (w s : ℕ) (σ : Equiv.Perm (Fin s))
    (τ : Equiv.Perm (Fin w)) (x : {−1,1}^[s * w]) :
    tribes w s (permuteInput (blockCoordinatePermutation σ τ) x) = tribes w s x := by
  change orFunction s
      (fun i ↦ andFunction w
        (inputBlock (permuteInput (blockCoordinatePermutation σ τ) x) i)) =
    orFunction s (fun i ↦ andFunction w (inputBlock x i))
  rw [show (fun i ↦ andFunction w
      (inputBlock (permuteInput (blockCoordinatePermutation σ τ) x) i)) =
      permuteInput σ (fun i ↦ andFunction w (inputBlock x i)) by
    funext i
    have hblock : inputBlock (permuteInput (blockCoordinatePermutation σ τ) x) i =
        permuteInput τ (inputBlock x (σ i)) := by
      funext j
      simp [inputBlock, permuteInput]
    rw [hblock]
    exact andFunction_symmetric w τ (inputBlock x (σ i))]
  exact orFunction_symmetric s σ _

/-- O'Donnell, Example 2.9: every tribes function is transitive-symmetric. -/
theorem tribes_transitiveSymmetric (w s : ℕ) : IsTransitiveSymmetric (tribes w s) := by
  intro p q
  let σ := Equiv.swap (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
  let τ := Equiv.swap (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2
  refine ⟨blockCoordinatePermutation σ τ, ?_, ?_⟩
  · change finProdFinEquiv
      (σ (finProdFinEquiv.symm p).1, τ (finProdFinEquiv.symm p).2) = q
    rw [show σ (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm q).1 by
      exact Equiv.swap_apply_left _ _]
    rw [show τ (finProdFinEquiv.symm p).2 = (finProdFinEquiv.symm q).2 by
      exact Equiv.swap_apply_left _ _]
    exact finProdFinEquiv.apply_symm_apply q
  · exact tribes_blockCoordinatePermutation w s σ τ

/-- For at least two blocks of width at least two, tribes is not fully symmetric.

The counterexample swaps one coordinate of the first block with the corresponding coordinate of
the second block. Before the swap the first block is unanimously `-1`; afterwards no block is. -/
theorem tribes_not_symmetric (w s : ℕ) (hw : 1 < w) (hs : 1 < s) :
    ¬IsSymmetric (tribes w s) := by
  intro hsym
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, hs⟩
  let j₀ : Fin w := ⟨0, by omega⟩
  let j₁ : Fin w := ⟨1, hw⟩
  let p : Fin (s * w) := finProdFinEquiv (i₀, j₀)
  let q : Fin (s * w) := finProdFinEquiv (i₁, j₀)
  let π : Equiv.Perm (Fin (s * w)) := Equiv.swap p q
  let x : {−1,1}^[s * w] := fun k ↦
    if (finProdFinEquiv.symm k).1 = i₀ then -1 else 1
  have hi_ne : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hx_q : x q = 1 := by
    change (if (finProdFinEquiv.symm (finProdFinEquiv (i₁, j₀))).1 = i₀
      then -1 else 1) = 1
    rw [finProdFinEquiv.symm_apply_apply]
    simp [hi_ne.symm]
  have hx : tribes w s x = -1 := by
    change orFunction s (fun i ↦ andFunction w (inputBlock x i)) = -1
    have hblock : andFunction w (inputBlock x i₀) = -1 := by
      apply if_pos
      intro j
      change (if (finProdFinEquiv.symm (finProdFinEquiv (i₀, j))).1 = i₀
        then -1 else 1) = -1
      rw [finProdFinEquiv.symm_apply_apply]
      rfl
    apply if_neg
    intro hall
    have := hall i₀
    change andFunction w (inputBlock x i₀) = 1 at this
    rw [hblock] at this
    norm_num at this
  have hπx : tribes w s (permuteInput π x) = 1 := by
    change orFunction s
      (fun i ↦ andFunction w (inputBlock (permuteInput π x) i)) = 1
    apply if_pos
    intro i
    apply if_neg
    intro hall
    by_cases hi : i = i₀
    · have := hall j₀
      subst i
      simp only [inputBlock, permuteInput] at this
      rw [show π (finProdFinEquiv (i₀, j₀)) = q by
        change Equiv.swap p q p = q
        exact Equiv.swap_apply_left p q] at this
      rw [hx_q] at this
      norm_num at this
    · have := hall j₁
      have hcoord_ne_p : finProdFinEquiv (i, j₁) ≠ p := by
        intro h
        have hpair := finProdFinEquiv.injective h
        have := congrArg Prod.snd hpair
        simp [j₀, j₁, Fin.ext_iff] at this
      have hcoord_ne_q : finProdFinEquiv (i, j₁) ≠ q := by
        intro h
        have hpair := finProdFinEquiv.injective h
        have := congrArg Prod.snd hpair
        simp [j₀, j₁, Fin.ext_iff] at this
      simp only [inputBlock, permuteInput] at this
      rw [show π (finProdFinEquiv (i, j₁)) = finProdFinEquiv (i, j₁) by
        change Equiv.swap p q (finProdFinEquiv (i, j₁)) = finProdFinEquiv (i, j₁)
        exact Equiv.swap_apply_of_ne_of_ne hcoord_ne_p hcoord_ne_q] at this
      have hx_coord : x (finProdFinEquiv (i, j₁)) = 1 := by
        change (if (finProdFinEquiv.symm (finProdFinEquiv (i, j₁))).1 = i₀
          then -1 else 1) = 1
        rw [finProdFinEquiv.symm_apply_apply]
        simp [hi]
      rw [hx_coord] at this
      norm_num at this
  have hinvariant := hsym π x
  rw [hx, hπx] at hinvariant
  norm_num at hinvariant

/-- O'Donnell, Example 2.9: the stated properties of the standard social-choice functions.

The hypotheses record the nondegenerate cases suppressed in the prose: AND and OR are non-odd
only from arity two onward, and tribes is non-symmetric only with at least two blocks of width at
least two. -/
theorem example2_9 (hn : Odd n) (i : Fin n) (d m w s : ℕ)
    (hm : 1 < m) (hw : 1 < w) (hs : 1 < s) :
    (Monotone (majority n) ∧ Function.Odd (majority n) ∧
      IsUnanimous (majority n) ∧ IsSymmetric (majority n)) ∧
    (∀ f : BooleanFunction n,
      IsSymmetric f → Monotone f → Function.Odd f → f = majority n) ∧
    (Monotone (dictator i) ∧ Function.Odd (dictator i) ∧ IsUnanimous (dictator i)) ∧
    (Monotone (recursiveMajority n d) ∧ Function.Odd (recursiveMajority n d) ∧
      IsUnanimous (recursiveMajority n d)) ∧
    (Monotone (andFunction m) ∧ IsUnanimous (andFunction m) ∧
      IsSymmetric (andFunction m) ∧ ¬Function.Odd (andFunction m)) ∧
    (Monotone (orFunction m) ∧ IsUnanimous (orFunction m) ∧
      IsSymmetric (orFunction m) ∧ ¬Function.Odd (orFunction m)) ∧
    (Monotone (tribes w s) ∧ IsUnanimous (tribes w s) ∧
      ¬IsSymmetric (tribes w s) ∧ IsTransitiveSymmetric (tribes w s)) := by
  have hnpos : 0 < n := by
    rcases hn with ⟨k, hk⟩
    omega
  have hmpos : 0 < m := by omega
  have hwpos : 0 < w := by omega
  have hspos : 0 < s := by omega
  refine ⟨⟨majority_monotone n, majority_odd hn, majority_unanimous n hnpos,
    majority_symmetric n⟩, ?_,
    ⟨dictator_monotone i, dictator_odd i, dictator_unanimous i⟩,
    ⟨recursiveMajority_monotone n d, recursiveMajority_odd hn d,
      recursiveMajority_unanimous n hnpos d⟩,
    ⟨andFunction_monotone m, andFunction_unanimous m hmpos,
      andFunction_symmetric m, andFunction_not_odd m hm⟩,
    ⟨orFunction_monotone m, orFunction_unanimous m hmpos,
      orFunction_symmetric m, orFunction_not_odd m hm⟩,
    ⟨tribes_monotone w s, tribes_unanimous w s hwpos hspos,
      tribes_not_symmetric w s hw hs, tribes_transitiveSymmetric w s⟩⟩
  intro f hsym hmono hodd
  exact (may_theorem f hsym hmono hodd).2

/-- O'Donnell, Definition 2.11: impartial culture is the uniform distribution on vote profiles. -/
noncomputable def impartialCulture (n : ℕ) : PMF {−1,1}^[n] :=
  uniformPMF {−1,1}^[n]


end FABL
