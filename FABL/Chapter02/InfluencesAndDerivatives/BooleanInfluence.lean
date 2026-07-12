/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.SocialChoiceFunctions

/-!
# Boolean influence

Book items: Definition 2.12, Definition 2.13, Fact 2.14, Example 2.15.

Pivotal coordinates, cube edges, and Boolean influences from Section 2.2 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Set coordinate `i` of a sign-cube input to `b`, using Mathlib's `Function.update`. -/
def setCoordinate (x : {−1,1}^[n]) (i : Fin n) (b : Sign) : {−1,1}^[n] :=
  Function.update x i b

/-- Reading the coordinate just set returns its new value. -/
@[simp] theorem setCoordinate_apply_self (x : {−1,1}^[n]) (i : Fin n) (b : Sign) :
    setCoordinate x i b i = b := by
  simp [setCoordinate, Function.update_self]

/-- Setting one coordinate leaves every other coordinate unchanged. -/
@[simp] theorem setCoordinate_apply_of_ne (x : {−1,1}^[n]) {i j : Fin n} (h : j ≠ i)
    (b : Sign) : setCoordinate x i b j = x j := by
  simp [setCoordinate, Function.update_of_ne h]

/-- Setting a coordinate to its present value leaves the input unchanged. -/
@[simp] theorem setCoordinate_eq_self (x : {−1,1}^[n]) (i : Fin n) :
    setCoordinate x i (x i) = x := by
  exact Function.update_eq_self i x

/-- Repeatedly setting the same coordinate retains only the final value. -/
@[simp] theorem setCoordinate_setCoordinate (x : {−1,1}^[n]) (i : Fin n) (a b : Sign) :
    setCoordinate (setCoordinate x i a) i b = setCoordinate x i b := by
  exact Function.update_idem (a := i) a b x

/-- O'Donnell, Definition 2.12: flip coordinate `i` of a sign-cube input. -/
def flipCoordinate (x : {−1,1}^[n]) (i : Fin n) : {−1,1}^[n] :=
  setCoordinate x i (-x i)

/-- Flipping a coordinate twice restores the input. -/
@[simp] theorem flipCoordinate_flipCoordinate (x : {−1,1}^[n]) (i : Fin n) :
    flipCoordinate (flipCoordinate x i) i = x := by
  rw [flipCoordinate, flipCoordinate, setCoordinate_apply_self]
  simp

/-- O'Donnell, Definition 2.12: coordinate `i` is pivotal for `f` at `x`. -/
def IsPivotal {β : Type*} (f : {−1,1}^[n] → β) (i : Fin n) (x : {−1,1}^[n]) : Prop :=
  f x ≠ f (flipCoordinate x i)

/-- Pivotality is equivalently disagreement between the two restrictions of one coordinate. -/
theorem isPivotal_iff_setCoordinate_ne {β : Type*} (f : {−1,1}^[n] → β)
    (i : Fin n) (x : {−1,1}^[n]) :
    IsPivotal f i x ↔
      f (setCoordinate x i 1) ≠ f (setCoordinate x i (-1)) := by
  rcases Int.units_eq_one_or (x i) with hi | hi
  · have hplus : setCoordinate x i 1 = x := by
      simpa [hi] using setCoordinate_eq_self x i
    have hflip : flipCoordinate x i = setCoordinate x i (-1) := by
      simp [flipCoordinate, hi]
    rw [IsPivotal, hplus, hflip]
  · have hminus : setCoordinate x i (-1) = x := by
      simpa [hi] using setCoordinate_eq_self x i
    have hflip : flipCoordinate x i = setCoordinate x i 1 := by
      simp [flipCoordinate, hi]
    rw [IsPivotal, hminus, hflip, ne_comm]

/-- O'Donnell, Definition 2.13: pivotal probability for a Boolean-valued function. -/
noncomputable def booleanInfluence (f : BooleanFunction n) (i : Fin n) : ℝ :=
  by
    classical
    exact uniformProbability (IsPivotal f i)

/-- The canonical endpoint model for an undirected dimension-`i` edge: the endpoint whose
`i`th coordinate is `+1`. -/
abbrev DimensionEdge (i : Fin n) := {x : {−1,1}^[n] // x i = 1}

instance dimensionEdgeNonempty (i : Fin n) : Nonempty (DimensionEdge i) :=
  ⟨⟨fun _ ↦ 1, rfl⟩⟩

/-- Split a cube vertex into its `i`th sign and the canonical endpoint of its dimension-`i`
edge. This identifies vertices with the two orientations of undirected dimension-`i` edges. -/
def signProdDimensionEdgeEquiv (i : Fin n) :
    Sign × DimensionEdge i ≃ {−1,1}^[n] where
  toFun p := setCoordinate p.2.1 i p.1
  invFun x := (x i, ⟨setCoordinate x i 1, setCoordinate_apply_self x i 1⟩)
  left_inv p := by
    apply Prod.ext
    · change setCoordinate p.2.1 i p.1 i = p.1
      simp
    · apply Subtype.ext
      change setCoordinate (setCoordinate p.2.1 i p.1) i 1 = p.2.1
      rw [setCoordinate_setCoordinate]
      simpa [p.2.2] using setCoordinate_eq_self p.2.1 i
  right_inv x := by
    change setCoordinate (setCoordinate x i 1) i (x i) = x
    rw [setCoordinate_setCoordinate, setCoordinate_eq_self]

/-- There are `2^(n-1)` undirected edges in each dimension of the `n`-cube. -/
theorem card_dimensionEdge (i : Fin n) :
    Fintype.card (DimensionEdge i) = 2 ^ (n - 1) := by
  have hcard := Fintype.card_congr (signProdDimensionEdgeEquiv i)
  simp only [Fintype.card_prod] at hcard
  have hsign : Fintype.card Sign = 2 := by decide
  rw [hsign] at hcard
  simp only [SignCube, Fintype.card_fun, Fintype.card_fin] at hcard
  rw [hsign] at hcard
  cases n with
  | zero => exact Fin.elim0 i
  | succ k =>
      simp only [Nat.succ_sub_one]
      rw [pow_succ] at hcard
      omega

/-- The uniform probability of a singleton in a finite nonempty type. -/
theorem uniformProbability_eq_singleton {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (a : Ω) :
    uniformProbability (fun x : Ω ↦ x = a) = 1 / Fintype.card Ω := by
  rw [uniformProbability, Fintype.expect_eq_sum_div_card]
  simp

/-- Boundary status of the undirected dimension-`i` edge represented by its canonical
endpoint. -/
def IsBoundaryDimensionEdge (f : BooleanFunction n) (i : Fin n)
    (e : DimensionEdge i) : Prop :=
  f e.1 ≠ f (flipCoordinate e.1 i)

/-- The fraction of undirected dimension-`i` edges crossing the boundary of a Boolean
function. -/
noncomputable def dimensionEdgeBoundaryFraction (f : BooleanFunction n) (i : Fin n) : ℝ :=
  by
    classical
    exact uniformProbability (IsBoundaryDimensionEdge f i)

/-- Pivotality is constant on the two orientations of a dimension-`i` edge. -/
theorem isPivotal_signProdDimensionEdgeEquiv_iff
    (f : BooleanFunction n) (i : Fin n) (p : Sign × DimensionEdge i) :
    IsPivotal f i (signProdDimensionEdgeEquiv i p) ↔
      IsBoundaryDimensionEdge f i p.2 := by
  rcases p with ⟨b, e⟩
  rcases Int.units_eq_one_or b with rfl | rfl
  · change IsPivotal f i (setCoordinate e.1 i 1) ↔ IsBoundaryDimensionEdge f i e
    have hedge : setCoordinate e.1 i 1 = e.1 := by
      simpa [e.2] using setCoordinate_eq_self e.1 i
    rw [hedge]
    rfl
  · change IsPivotal f i (setCoordinate e.1 i (-1)) ↔ IsBoundaryDimensionEdge f i e
    have hminus : setCoordinate e.1 i (-1) = flipCoordinate e.1 i := by
      rw [flipCoordinate, e.2]
    rw [hminus]
    simp only [IsPivotal, IsBoundaryDimensionEdge, flipCoordinate_flipCoordinate, ne_comm]

/-- O'Donnell, Fact 2.14: Boolean influence is exactly the fraction of undirected
dimension-`i` edges which are boundary edges. -/
theorem booleanInfluence_eq_dimensionEdgeBoundaryFraction
    (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence f i = dimensionEdgeBoundaryFraction f i := by
  classical
  rw [booleanInfluence, dimensionEdgeBoundaryFraction, uniformProbability, uniformProbability]
  calc
    (𝔼 x : {−1,1}^[n], if IsPivotal f i x then (1 : ℝ) else 0) =
        𝔼 p : Sign × DimensionEdge i,
          if IsPivotal f i (signProdDimensionEdgeEquiv i p) then (1 : ℝ) else 0 := by
      symm
      exact Fintype.expect_equiv (signProdDimensionEdgeEquiv i)
        (fun p ↦ if IsPivotal f i (signProdDimensionEdgeEquiv i p) then (1 : ℝ) else 0)
        (fun x ↦ if IsPivotal f i x then (1 : ℝ) else 0) (fun _ ↦ rfl)
    _ = 𝔼 p : Sign × DimensionEdge i,
          if IsBoundaryDimensionEdge f i p.2 then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro p _
      rw [isPivotal_signProdDimensionEdgeEquiv_iff]
    _ = 𝔼 e : DimensionEdge i,
          if IsBoundaryDimensionEdge f i e then (1 : ℝ) else 0 := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_const
      simp

/-- A coordinate is pivotal for a dictator exactly when it is the dictated coordinate. -/
theorem isPivotal_dictator_iff (i j : Fin n) (x : {−1,1}^[n]) :
    IsPivotal (dictator i) j x ↔ j = i := by
  by_cases hji : j = i
  · subst j
    simp only [IsPivotal, dictator, flipCoordinate, setCoordinate,
      Function.update_self, ne_eq, iff_true]
    rcases Int.units_eq_one_or (x i) with hi | hi <;> simp [hi]
  · simp [IsPivotal, dictator, flipCoordinate, setCoordinate,
      Function.update_of_ne (Ne.symm hji),
      hji]

/-- O'Donnell, Example 2.15: the dictated coordinate has influence one. -/
theorem booleanInfluence_dictator_self (i : Fin n) :
    booleanInfluence (dictator i) i = 1 := by
  rw [booleanInfluence, uniformProbability]
  simp_rw [isPivotal_dictator_iff]
  simp

/-- O'Donnell, Example 2.15: every other coordinate has influence zero on a dictator. -/
theorem booleanInfluence_dictator_of_ne (i j : Fin n) (hji : j ≠ i) :
    booleanInfluence (dictator i) j = 0 := by
  rw [booleanInfluence, uniformProbability]
  simp_rw [isPivotal_dictator_iff]
  simp [hji]

/-- Negating a Boolean function does not change its pivotal coordinates. -/
theorem isPivotal_neg_iff (f : BooleanFunction n) (i : Fin n) (x : {−1,1}^[n]) :
    IsPivotal (fun y ↦ -f y) i x ↔ IsPivotal f i x := by
  simp only [IsPivotal, ne_eq, neg_inj]

/-- Negating a Boolean function preserves every Boolean influence. -/
theorem booleanInfluence_neg (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence (fun x ↦ -f x) i = booleanInfluence f i := by
  rw [booleanInfluence, booleanInfluence, uniformProbability, uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  rw [isPivotal_neg_iff]

/-- O'Donnell, Example 2.15: a negated dictator has the same exact influence profile as a
dictator. -/
theorem booleanInfluence_neg_dictator (i j : Fin n) :
    booleanInfluence (fun x ↦ -dictator i x) j = if j = i then 1 else 0 := by
  rw [booleanInfluence_neg]
  split_ifs with hji
  · subst j
    exact booleanInfluence_dictator_self i
  · exact booleanInfluence_dictator_of_ne i j hji

/-- O'Donnell, Example 2.15: every coordinate influence of a constant function is zero. -/
theorem booleanInfluence_const (c : Sign) (i : Fin n) :
    booleanInfluence (fun _ ↦ c) i = 0 := by
  rw [booleanInfluence, uniformProbability]
  simp [IsPivotal]

/-- The unique canonical dimension-`i` edge whose other endpoint differs from the all-`+1`
vertex. -/
def allOneDimensionEdge (i : Fin n) : DimensionEdge i :=
  ⟨fun _ ↦ 1, rfl⟩

/-- The unique canonical dimension-`i` edge whose other endpoint is the all-`-1` vertex. -/
def allNegOneDimensionEdge (i : Fin n) : DimensionEdge i :=
  ⟨fun j ↦ if j = i then 1 else -1, by simp⟩

/-- A dimension-`i` edge crosses the OR boundary exactly when its canonical endpoint is the
all-`+1` vertex. -/
theorem isBoundaryDimensionEdge_orFunction_iff (i : Fin n) (e : DimensionEdge i) :
    IsBoundaryDimensionEdge (orFunction n) i e ↔ e = allOneDimensionEdge i := by
  have hflipAll : ¬∀ j, flipCoordinate e.1 i j = 1 := by
    intro h
    have hi := h i
    simp [flipCoordinate, setCoordinate, e.2] at hi
  simp only [IsBoundaryDimensionEdge, orFunction]
  rw [if_neg hflipAll]
  by_cases hall : ∀ j, e.1 j = 1
  · rw [if_pos hall]
    constructor
    · intro _
      apply Subtype.ext
      funext j
      exact hall j
    · intro _
      decide
  · rw [if_neg hall]
    constructor
    · simp
    · intro heq
      exfalso
      apply hall
      intro j
      have hj := congrArg (fun q : DimensionEdge i ↦ q.1 j) heq
      simpa [allOneDimensionEdge] using hj

/-- A dimension-`i` edge crosses the AND boundary exactly when its canonical endpoint has
`+1` in coordinate `i` and `-1` everywhere else. -/
theorem isBoundaryDimensionEdge_andFunction_iff (i : Fin n) (e : DimensionEdge i) :
    IsBoundaryDimensionEdge (andFunction n) i e ↔ e = allNegOneDimensionEdge i := by
  have heNot : ¬∀ j, e.1 j = -1 := by
    intro h
    have hi := h i
    rw [e.2] at hi
    exact (by decide : (1 : Sign) ≠ -1) hi
  simp only [IsBoundaryDimensionEdge, andFunction]
  rw [if_neg heNot]
  by_cases hflip : ∀ j, flipCoordinate e.1 i j = -1
  · rw [if_pos hflip]
    constructor
    · intro _
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [allNegOneDimensionEdge, e.2]
      · have hj := hflip j
        simpa [allNegOneDimensionEdge, flipCoordinate, setCoordinate, hji,
          Function.update_of_ne hji] using hj
    · intro _
      decide
  · rw [if_neg hflip]
    constructor
    · simp
    · intro heq
      exfalso
      apply hflip
      intro j
      have hj := congrArg (fun q : DimensionEdge i ↦ q.1 j) heq
      by_cases hji : j = i
      · subst j
        simp [flipCoordinate, setCoordinate, e.2]
      · simpa [allNegOneDimensionEdge, flipCoordinate, setCoordinate, hji,
          Function.update_of_ne hji] using hj

/-- O'Donnell, Example 2.15: every coordinate of `ORₙ` has influence `2^(1-n)`. -/
theorem booleanInfluence_orFunction (i : Fin n) :
    booleanInfluence (orFunction n) i = 1 / (2 ^ (n - 1) : ℝ) := by
  classical
  rw [booleanInfluence_eq_dimensionEdgeBoundaryFraction]
  unfold dimensionEdgeBoundaryFraction
  calc
    uniformProbability (IsBoundaryDimensionEdge (orFunction n) i) =
        uniformProbability (fun e : DimensionEdge i ↦ e = allOneDimensionEdge i) := by
      unfold uniformProbability
      apply Finset.expect_congr rfl
      intro e _
      simp only [isBoundaryDimensionEdge_orFunction_iff]
    _ = 1 / Fintype.card (DimensionEdge i) :=
      uniformProbability_eq_singleton (allOneDimensionEdge i)
    _ = 1 / (2 ^ (n - 1) : ℝ) := by
      rw [card_dimensionEdge]
      norm_num

/-- O'Donnell, Example 2.15: every coordinate of `ANDₙ` has influence `2^(1-n)`. -/
theorem booleanInfluence_andFunction (i : Fin n) :
    booleanInfluence (andFunction n) i = 1 / (2 ^ (n - 1) : ℝ) := by
  classical
  rw [booleanInfluence_eq_dimensionEdgeBoundaryFraction]
  unfold dimensionEdgeBoundaryFraction
  calc
    uniformProbability (IsBoundaryDimensionEdge (andFunction n) i) =
        uniformProbability (fun e : DimensionEdge i ↦ e = allNegOneDimensionEdge i) := by
      unfold uniformProbability
      apply Finset.expect_congr rfl
      intro e _
      simp only [isBoundaryDimensionEdge_andFunction_iff]
    _ = 1 / Fintype.card (DimensionEdge i) :=
      uniformProbability_eq_singleton (allNegOneDimensionEdge i)
    _ = 1 / (2 ^ (n - 1) : ℝ) := by
      rw [card_dimensionEdge]
      norm_num

/-- Removing the fixed coordinate identifies dimension-`i` edges in the `(k+1)`-cube with
the `k`-cube. Mathlib's `Fin.insertNth` and `Fin.succAbove` provide the reindexing. -/
def dimensionEdgeRemoveEquiv {k : ℕ} (i : Fin (k + 1)) :
    DimensionEdge i ≃ {−1,1}^[k] where
  toFun e := fun j ↦ e.1 (i.succAbove j)
  invFun y := ⟨i.insertNth 1 y, by simp⟩
  left_inv e := by
    apply Subtype.ext
    funext j
    exact Fin.succAboveCases i (by simpa using e.2.symm) (fun q ↦ by simp) j
  right_inv y := by
    funext j
    simp

/-- A sign-cube input is equivalently the finite set of its positive coordinates. -/
def signCubeEquivFinset (k : ℕ) : {−1,1}^[k] ≃ Finset (Fin k) where
  toFun := positiveCoordinateSet
  invFun S := fun i ↦ if i ∈ S then 1 else -1
  left_inv x := by
    funext i
    rcases Int.units_eq_one_or (x i) with hi | hi <;>
      simp [positiveCoordinateSet, hi]
  right_inv S := by
    ext i
    simp [positiveCoordinateSet]

@[simp] theorem signCubeEquivFinset_apply_card {k : ℕ} (x : {−1,1}^[k]) :
    (signCubeEquivFinset k x).card = positiveCoordinateCount x := rfl

/-- The exact binomial distribution of the number of positive coordinates on the sign cube. -/
theorem uniformProbability_positiveCoordinateCount_eq (k r : ℕ) :
    uniformProbability (fun x : {−1,1}^[k] ↦ positiveCoordinateCount x = r) =
      (Nat.choose k r : ℝ) / (2 ^ k : ℝ) := by
  classical
  rw [uniformProbability, Fintype.expect_eq_sum_div_card]
  calc
    (∑ x : {−1,1}^[k], if positiveCoordinateCount x = r then (1 : ℝ) else 0) /
        Fintype.card ({−1,1}^[k]) =
      (∑ S : Finset (Fin k), if S.card = r then (1 : ℝ) else 0) /
        Fintype.card (Finset (Fin k)) := by
      congr 1
      · apply Fintype.sum_equiv (signCubeEquivFinset k)
        intro x
        simp [signCubeEquivFinset_apply_card]
      · exact_mod_cast Fintype.card_congr (signCubeEquivFinset k)
    _ = (Nat.choose k r : ℝ) / (2 ^ k : ℝ) := by
      rw [Finset.sum_boole]
      have hfilter : (Finset.univ.filter fun S : Finset (Fin k) ↦ S.card = r) =
          Finset.univ.powersetCard r := by
        ext S
        simp
      rw [hfilter, Finset.card_powersetCard]
      simp

/-- For majority on `2m+1` coordinates, a dimension edge is a boundary edge exactly when
the remaining `2m` coordinates split evenly. -/
theorem isBoundaryDimensionEdge_majority_odd_iff (m : ℕ) (i : Fin (2 * m + 1))
    (e : DimensionEdge i) :
    IsBoundaryDimensionEdge (majority (2 * m + 1)) i e ↔
      positiveCoordinateCount (dimensionEdgeRemoveEquiv i e) = m := by
  let y := dimensionEdgeRemoveEquiv i e
  let c := positiveCoordinateCount y
  have hsumY : (∑ j, signValue (y j)) = 2 * c - 2 * m := by
    simpa [y, c] using sum_signValue_eq_two_mul_positiveCoordinateCount_sub y
  have hsumPlus : (∑ j, signValue (e.1 j)) = 1 + ∑ j, signValue (y j) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [y, dimensionEdgeRemoveEquiv, e.2]
  have hsumMinus : (∑ j, signValue (flipCoordinate e.1 i j)) =
      -1 + ∑ j, signValue (y j) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [y, dimensionEdgeRemoveEquiv, flipCoordinate, setCoordinate, e.2,
      Fin.succAbove_ne]
  change thresholdSign (∑ j, signValue (e.1 j)) ≠
      thresholdSign (∑ j, signValue (flipCoordinate e.1 i j)) ↔ c = m
  rw [hsumPlus, hsumMinus, hsumY]
  rcases lt_trichotomy c m with hlt | heq | hgt
  · have hltR : (c : ℝ) < m := by exact_mod_cast hlt
    have hstep : (c : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    have hp : 1 + ((2 : ℝ) * c - 2 * m) < 0 := by linarith
    have hm : -1 + ((2 : ℝ) * c - 2 * m) < 0 := by linarith
    simp [thresholdSign_of_neg hp, thresholdSign_of_neg hm, hlt.ne]
  · rw [heq]
    norm_num [thresholdSign]
  · have hgtR : (m : ℝ) < c := by exact_mod_cast hgt
    have hp : 0 ≤ 1 + ((2 : ℝ) * c - 2 * m) := by linarith
    have hm : 0 ≤ -1 + ((2 : ℝ) * c - 2 * m) := by
      have hstep : (m : ℝ) + 1 ≤ c := by exact_mod_cast hgt
      linarith
    simp [thresholdSign_of_nonneg hp, thresholdSign_of_nonneg hm, hgt.ne']

/-- O'Donnell, Example 2.15 and Exercise 2.22(a): the exact influence of every coordinate
of odd-arity majority. -/
theorem booleanInfluence_majority_odd (m : ℕ) (i : Fin (2 * m + 1)) :
    booleanInfluence (majority (2 * m + 1)) i =
      (Nat.choose (2 * m) m : ℝ) / (2 ^ (2 * m) : ℝ) := by
  classical
  rw [booleanInfluence_eq_dimensionEdgeBoundaryFraction]
  unfold dimensionEdgeBoundaryFraction
  calc
    uniformProbability (IsBoundaryDimensionEdge (majority (2 * m + 1)) i) =
        uniformProbability (fun y : {−1,1}^[2 * m] ↦ positiveCoordinateCount y = m) := by
      unfold uniformProbability
      exact Fintype.expect_equiv (dimensionEdgeRemoveEquiv i)
        (fun e ↦ if IsBoundaryDimensionEdge (majority (2 * m + 1)) i e then (1 : ℝ)
          else 0)
        (fun y ↦ if positiveCoordinateCount y = m then (1 : ℝ) else 0)
        (fun e ↦ by simp only [isBoundaryDimensionEdge_majority_odd_iff])
    _ = (Nat.choose (2 * m) m : ℝ) / (2 ^ (2 * m) : ℝ) := by
      exact uniformProbability_positiveCoordinateCount_eq (k := 2 * m) m

/-- O'Donnell, Example 2.15: every coordinate of three-bit majority has influence `1/2`. -/
theorem booleanInfluence_majority_three (i : Fin 3) :
    booleanInfluence (majority 3) i = (1 : ℝ) / 2 := by
  have h := booleanInfluence_majority_odd 1 i
  norm_num at h ⊢
  exact h


end FABL
