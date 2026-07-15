/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5 and Gemini 3.1 Pro
-/
module

public import FABL.Chapter04.RandomRestrictions

/-!
# Random-restriction switching events

Book items: Exercise 4.19 and the Baby Switching Lemma. The same restriction algebra is reused
by Håstad's Switching Lemma and the recursive circuit argument.

The pure core defines the decision-tree failure event in both the book's `(J | z)` presentation
and an equivalent independent-coordinate presentation.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Decision-tree failure under a random restriction -/

/-- The restriction `f_{J|z}`, transported to the binary cube on which the project's
decision-tree API is defined. -/
def restrictedBinaryFunction (f : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) : 𝔽₂^[n] → Sign :=
  fun x ↦ extendedSignRestriction f J z (binaryCubeSignEquiv n x)

/-- The decision-tree depth of a restricted Boolean function. Fixed coordinates remain in the
ambient cube, but do not affect the minimum depth. -/
noncomputable def restrictedDecisionTreeDepth (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) : ℕ :=
  F₂DecisionTree.decisionTreeDepth (restrictedBinaryFunction f J z)

/-- Indicator of the event `DT(f_{J|z}) ≥ k`. -/
noncomputable def switchingFailureIndicator (f : BooleanFunction n) (k : ℕ)
    (J : Finset (Fin n)) (z : FixedSignCube J) : ℝ :=
  if k ≤ restrictedDecisionTreeDepth f J z then 1 else 0

/-- Probability of the event `DT(f_{J|z}) ≥ k` under a `δ`-random restriction. -/
noncomputable def switchingFailureProbability (f : BooleanFunction n) (δ : ℝ) (k : ℕ) : ℝ :=
  expectRandomRestriction n δ (switchingFailureIndicator f k)

theorem switchingFailureIndicator_nonneg (f : BooleanFunction n) (k : ℕ)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    0 ≤ switchingFailureIndicator f k J z := by
  unfold switchingFailureIndicator
  split_ifs <;> norm_num

theorem switchingFailureIndicator_le_one (f : BooleanFunction n) (k : ℕ)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    switchingFailureIndicator f k J z ≤ 1 := by
  unfold switchingFailureIndicator
  split_ifs <;> norm_num

@[simp] theorem switchingFailureIndicator_zero (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    switchingFailureIndicator f 0 J z = 1 := by
  simp [switchingFailureIndicator]

@[simp] theorem switchingFailureProbability_zero (f : BooleanFunction n) (δ : ℝ) :
    switchingFailureProbability f δ 0 = 1 := by
  simp [switchingFailureProbability, switchingFailureIndicator,
    expectRandomRestriction, sum_deltaRandomSubsetWeight]

theorem switchingFailureProbability_nonneg {f : BooleanFunction n} {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ switchingFailureProbability f δ k := by
  classical
  unfold switchingFailureProbability expectRandomRestriction
  exact Finset.sum_nonneg fun J _ ↦ mul_nonneg
    (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)
    (Finset.expect_nonneg fun z _ ↦ switchingFailureIndicator_nonneg f k J z)

theorem switchingFailureProbability_le_one {f : BooleanFunction n} {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    switchingFailureProbability f δ k ≤ 1 := by
  classical
  unfold switchingFailureProbability expectRandomRestriction
  calc
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
        (𝔼 z : FixedSignCube J, switchingFailureIndicator f k J z) ≤
        ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J * 1 := by
      refine Finset.sum_le_sum fun J _ ↦
        mul_le_mul_of_nonneg_left ?_ (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)
      exact Finset.expect_le Finset.univ_nonempty fun z _ ↦
        switchingFailureIndicator_le_one f k J z
    _ = 1 := by simp [sum_deltaRandomSubsetWeight]

/-! ## Independent coordinate presentation of restrictions -/

/-- The coordinate weight for a `δ`-random restriction. -/
noncomputable def coordRestrictionWeightAt (δ : ℝ) : CoordRestriction → ℝ
  | .free => δ
  | .fixOne => (1 - δ) / 2
  | .fixNegOne => (1 - δ) / 2

theorem sum_coordRestrictionWeightAt (δ : ℝ) :
    ∑ c : CoordRestriction, coordRestrictionWeightAt δ c = 1 := by
  have hset : (Finset.univ : Finset CoordRestriction) =
      insert .free (insert .fixOne {CoordRestriction.fixNegOne}) := by
    ext c
    cases c <;> simp
  rw [hset, Finset.sum_insert (by decide : CoordRestriction.free ∉ insert .fixOne {.fixNegOne}),
    Finset.sum_insert (by decide : CoordRestriction.fixOne ∉ ({.fixNegOne} : Finset _)),
    Finset.sum_singleton]
  simp only [coordRestrictionWeightAt]
  ring

theorem coordRestrictionWeightAt_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (c : CoordRestriction) : 0 ≤ coordRestrictionWeightAt δ c := by
  cases c <;> simp only [coordRestrictionWeightAt] <;> linarith

/-- Product weight of an independent coordinate restriction. -/
noncomputable def restrictionAssignmentWeightAt (δ : ℝ)
    (ρ : Fin n → CoordRestriction) : ℝ :=
  ∏ i, coordRestrictionWeightAt δ (ρ i)

theorem restrictionAssignmentWeightAt_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ρ : Fin n → CoordRestriction) : 0 ≤ restrictionAssignmentWeightAt δ ρ :=
  Finset.prod_nonneg fun i _ ↦ coordRestrictionWeightAt_nonneg hδ0 hδ1 (ρ i)

theorem sum_restrictionAssignmentWeightAt (δ : ℝ) :
    ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ ρ = 1 := by
  classical
  have hprod := Fintype.prod_sum
    (f := fun (_ : Fin n) (c : CoordRestriction) ↦ coordRestrictionWeightAt δ c)
  simpa [restrictionAssignmentWeightAt, sum_coordRestrictionWeightAt] using hprod.symm

/-- Coordinates left free by a coordinate restriction. -/
def CoordRestriction.freeCoordinates (ρ : Fin n → CoordRestriction) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ρ i = .free

@[simp] theorem CoordRestriction.mem_freeCoordinates_iff
    (ρ : Fin n → CoordRestriction) (i : Fin n) :
    i ∈ CoordRestriction.freeCoordinates ρ ↔ ρ i = .free := by
  simp [CoordRestriction.freeCoordinates]

/-- Complete a coordinate restriction with a binary-cube input on its free coordinates. -/
def CoordRestriction.complete (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n]) : {−1,1}^[n] :=
  fun i ↦ match ρ i with
    | .free => signEncode (x i)
    | .fixOne => 1
    | .fixNegOne => -1

/-- Restrict a Boolean function using the coordinate-wise presentation. -/
def CoordRestriction.restrict (f : BooleanFunction n)
    (ρ : Fin n → CoordRestriction) : 𝔽₂^[n] → Sign :=
  fun x ↦ f (CoordRestriction.complete ρ x)

/-- Indicator that the coordinate-wise restricted function has decision-tree depth at least `k`. -/
noncomputable def coordSwitchingFailureIndicator (f : BooleanFunction n) (k : ℕ)
    (ρ : Fin n → CoordRestriction) : ℝ :=
  if k ≤ F₂DecisionTree.decisionTreeDepth (CoordRestriction.restrict f ρ) then 1 else 0

/-- Coordinate-wise presentation of the switching-failure probability. -/
noncomputable def coordSwitchingFailureProbability (f : BooleanFunction n)
    (δ : ℝ) (k : ℕ) : ℝ :=
  ∑ ρ : Fin n → CoordRestriction,
    restrictionAssignmentWeightAt δ ρ * coordSwitchingFailureIndicator f k ρ

theorem coordSwitchingFailureIndicator_nonneg (f : BooleanFunction n) (k : ℕ)
    (ρ : Fin n → CoordRestriction) : 0 ≤ coordSwitchingFailureIndicator f k ρ := by
  unfold coordSwitchingFailureIndicator
  split_ifs <;> norm_num

theorem coordSwitchingFailureProbability_nonneg {f : BooleanFunction n} {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : 0 ≤ coordSwitchingFailureProbability f δ k := by
  unfold coordSwitchingFailureProbability
  exact Finset.sum_nonneg fun ρ _ ↦ mul_nonneg
    (restrictionAssignmentWeightAt_nonneg hδ0 hδ1 ρ)
    (coordSwitchingFailureIndicator_nonneg f k ρ)

theorem coordSwitchingFailureProbability_le_one {f : BooleanFunction n} {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : coordSwitchingFailureProbability f δ k ≤ 1 := by
  classical
  calc
    coordSwitchingFailureProbability f δ k ≤
        ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ ρ := by
      unfold coordSwitchingFailureProbability
      refine Finset.sum_le_sum fun ρ _ ↦ ?_
      refine mul_le_of_le_one_right (restrictionAssignmentWeightAt_nonneg hδ0 hδ1 ρ) ?_
      unfold coordSwitchingFailureIndicator
      split_ifs <;> norm_num
    _ = 1 := sum_restrictionAssignmentWeightAt δ

/-- Coordinate restriction associated to a free set and an assignment to its complement. -/
noncomputable def coordRestrictionOf (J : Finset (Fin n)) (z : FixedSignCube J) :
    Fin n → CoordRestriction :=
  fun i ↦ if hi : i ∈ J then .free
    else if z ⟨i, hi⟩ = (1 : Sign) then .fixOne else .fixNegOne

@[simp] theorem coordRestrictionOf_apply_of_mem (J : Finset (Fin n))
    (z : FixedSignCube J) {i : Fin n} (hi : i ∈ J) :
    coordRestrictionOf J z i = .free := by
  simp [coordRestrictionOf, hi]

theorem coordRestrictionOf_apply_of_not_mem (J : Finset (Fin n))
    (z : FixedSignCube J) {i : Fin n} (hi : i ∉ J) :
    coordRestrictionOf J z i =
      if z ⟨i, hi⟩ = (1 : Sign) then .fixOne else .fixNegOne := by
  simp [coordRestrictionOf, hi]

@[simp] theorem freeCoordinates_coordRestrictionOf (J : Finset (Fin n))
    (z : FixedSignCube J) :
    CoordRestriction.freeCoordinates (coordRestrictionOf J z) = J := by
  ext i
  by_cases hi : i ∈ J
  · simp [CoordRestriction.freeCoordinates, coordRestrictionOf, hi]
  · have hne : coordRestrictionOf J z i ≠ .free := by
      rw [coordRestrictionOf_apply_of_not_mem J z hi]
      split_ifs <;> decide
    simp [CoordRestriction.freeCoordinates, hi, hne]

theorem complete_coordRestrictionOf (J : Finset (Fin n)) (z : FixedSignCube J)
    (x : 𝔽₂^[n]) :
    CoordRestriction.complete (coordRestrictionOf J z) x =
      combineSignCube J (fun i : J ↦ signEncode (x i)) z := by
  funext i
  by_cases hi : i ∈ J
  · rw [combineSignCube_apply_free J (fun j : J ↦ signEncode (x j)) z ⟨i, hi⟩]
    simp [CoordRestriction.complete, coordRestrictionOf, hi]
  · rw [combineSignCube_apply_fixed J (fun j : J ↦ signEncode (x j)) z ⟨i, hi⟩]
    rcases Int.units_eq_one_or (z ⟨i, hi⟩) with hz | hz
    · simp [CoordRestriction.complete, coordRestrictionOf, hi, hz]
    · simp [CoordRestriction.complete, coordRestrictionOf, hi, hz]

theorem restrict_coordRestrictionOf (f : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) :
    CoordRestriction.restrict f (coordRestrictionOf J z) = restrictedBinaryFunction f J z := by
  funext x
  simp only [CoordRestriction.restrict, restrictedBinaryFunction, extendedSignRestriction]
  rw [complete_coordRestrictionOf]
  congr 2

theorem coordSwitchingFailureIndicator_coordRestrictionOf
    (f : BooleanFunction n) (k : ℕ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    coordSwitchingFailureIndicator f k (coordRestrictionOf J z) =
      switchingFailureIndicator f k J z := by
  simp [coordSwitchingFailureIndicator, switchingFailureIndicator,
    restrictedDecisionTreeDepth, restrict_coordRestrictionOf]

theorem restrictionAssignmentWeightAt_coordRestrictionOf (δ : ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictionAssignmentWeightAt δ (coordRestrictionOf J z) =
      δ ^ J.card * ((1 - δ) / 2) ^ (n - J.card) := by
  classical
  rw [restrictionAssignmentWeightAt]
  have hfactor (i : Fin n) :
      coordRestrictionWeightAt δ (coordRestrictionOf J z i) =
        if i ∈ J then δ else (1 - δ) / 2 := by
    by_cases hi : i ∈ J
    · simp [coordRestrictionOf, coordRestrictionWeightAt, hi]
    · rw [coordRestrictionOf_apply_of_not_mem J z hi]
      split_ifs <;> rfl
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  have hpos : (Finset.univ.filter fun i : Fin n ↦ i ∈ J).card = J.card := by
    congr 1
    ext i
    simp
  have hneg : (Finset.univ.filter fun i : Fin n ↦ i ∉ J).card = n - J.card := by
    have heq : (Finset.univ.filter fun i : Fin n ↦ i ∉ J) = Finset.univ \ J := by
      ext i
      simp
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ,
      Fintype.card_fin]
  rw [Finset.prod_const, Finset.prod_const, hpos, hneg]

/-- Fixed assignment carried by a coordinate restriction on the complement of its free set. -/
noncomputable def CoordRestriction.fixedSign (ρ : Fin n → CoordRestriction) :
    FixedSignCube (CoordRestriction.freeCoordinates ρ) :=
  fun i ↦ if ρ i = .fixOne then 1 else -1

theorem coordRestrictionOf_freeCoordinates_fixedSign
    (ρ : Fin n → CoordRestriction) :
    coordRestrictionOf (CoordRestriction.freeCoordinates ρ)
      (CoordRestriction.fixedSign ρ) = ρ := by
  funext i
  cases hρ : ρ i with
  | free =>
      have hi : i ∈ CoordRestriction.freeCoordinates ρ :=
        (CoordRestriction.mem_freeCoordinates_iff ρ i).2 hρ
      simp [coordRestrictionOf, hi]
  | fixOne =>
      have hi : i ∉ CoordRestriction.freeCoordinates ρ := by
        simp [CoordRestriction.mem_freeCoordinates_iff, hρ]
      simp [coordRestrictionOf, CoordRestriction.fixedSign, hi, hρ]
  | fixNegOne =>
      have hi : i ∉ CoordRestriction.freeCoordinates ρ := by
        simp [CoordRestriction.mem_freeCoordinates_iff, hρ]
      simp [coordRestrictionOf, CoordRestriction.fixedSign, hi, hρ]

/-- Atoms of the `(J | z)` presentation of random restrictions. -/
abbrev RandomRestrictionAtom (n : ℕ) := Σ J : Finset (Fin n), FixedSignCube J

/-- The two presentations of a restriction are canonically equivalent. -/
noncomputable def randomRestrictionAtomEquiv :
    RandomRestrictionAtom n ≃ (Fin n → CoordRestriction) := by
  classical
  let toCoord : RandomRestrictionAtom n → (Fin n → CoordRestriction) :=
    fun R ↦ coordRestrictionOf R.1 R.2
  refine Equiv.ofBijective toCoord ⟨?_, ?_⟩
  · rintro ⟨J, z⟩ ⟨K, y⟩ h
    change coordRestrictionOf J z = coordRestrictionOf K y at h
    have hJK : J = K := by
      rw [← freeCoordinates_coordRestrictionOf J z,
        ← freeCoordinates_coordRestrictionOf K y, h]
    subst K
    congr 1
    funext i
    have hi := i.property
    have hcoord := congrFun h (i : Fin n)
    rcases Int.units_eq_one_or (z i) with hz | hz <;>
      rcases Int.units_eq_one_or (y i) with hy | hy <;>
      simp [coordRestrictionOf, hi, hz, hy] at hcoord ⊢
  · intro ρ
    refine ⟨⟨CoordRestriction.freeCoordinates ρ, CoordRestriction.fixedSign ρ⟩, ?_⟩
    exact coordRestrictionOf_freeCoordinates_fixedSign ρ

theorem card_fixedSignCube (J : Finset (Fin n)) :
    Fintype.card (FixedSignCube J) = 2 ^ (n - J.card) := by
  change Fintype.card (FixedIndex J → Sign) = _
  rw [Fintype.card_fun, Fintype.card_units_int]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

theorem restrictionAssignmentWeightAt_coordRestrictionOf_eq_div (δ : ℝ)
    (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictionAssignmentWeightAt δ (coordRestrictionOf J z) =
      deltaRandomSubsetWeight n δ J / Fintype.card (FixedSignCube J) := by
  rw [restrictionAssignmentWeightAt_coordRestrictionOf, deltaRandomSubsetWeight,
    card_fixedSignCube]
  push_cast
  rw [div_pow]
  ring

/-- The coordinate-product model and `(J | z)` model give the same failure probability. -/
theorem coordSwitchingFailureProbability_eq (f : BooleanFunction n) (δ : ℝ) (k : ℕ) :
    coordSwitchingFailureProbability f δ k = switchingFailureProbability f δ k := by
  classical
  unfold coordSwitchingFailureProbability switchingFailureProbability expectRandomRestriction
  simp_rw [Fintype.expect_eq_sum_div_card]
  have hdistribute :
      ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          ((∑ z : FixedSignCube J, switchingFailureIndicator f k J z) /
            Fintype.card (FixedSignCube J)) =
        ∑ J : Finset (Fin n), ∑ z : FixedSignCube J,
          deltaRandomSubsetWeight n δ J / Fintype.card (FixedSignCube J) *
            switchingFailureIndicator f k J z := by
    refine Finset.sum_congr rfl fun J _ ↦ ?_
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  rw [hdistribute]
  let g : RandomRestrictionAtom n → ℝ := fun R ↦
    deltaRandomSubsetWeight n δ R.1 / Fintype.card (FixedSignCube R.1) *
      switchingFailureIndicator f k R.1 R.2
  change (∑ ρ, restrictionAssignmentWeightAt δ ρ *
    coordSwitchingFailureIndicator f k ρ) = ∑ J, ∑ z, g ⟨J, z⟩
  rw [← Fintype.sum_sigma]
  symm
  apply Fintype.sum_equiv randomRestrictionAtomEquiv
  rintro ⟨J, z⟩
  simp only [randomRestrictionAtomEquiv, Equiv.ofBijective_apply]
  rw [coordSwitchingFailureIndicator_coordRestrictionOf,
    restrictionAssignmentWeightAt_coordRestrictionOf_eq_div]

/-! ## The Baby Switching Lemma -/


variable {n : ℕ}

/-! ## Exercise 4.19: the size-independent constant-three bound -/

/-- A term is compatible with a partial restriction when some completion satisfies it. -/
def DNFTerm.Compatible (T : DNFTerm n) (ρ : Fin n → CoordRestriction) : Prop :=
  ∃ x : 𝔽₂^[n], T.eval (CoordRestriction.complete ρ x) = -1

noncomputable instance DNFTerm.decidableCompatible (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) : Decidable (T.Compatible ρ) := by
  classical infer_instance

/-- A restricted DNF is bad when its computed function is not constant. -/
def DNFFormula.IsBadRestriction (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) : Prop :=
  ∃ x y : 𝔽₂^[n],
    CoordRestriction.restrict φ.toBooleanFunction ρ x ≠
      CoordRestriction.restrict φ.toBooleanFunction ρ y

noncomputable instance DNFFormula.decidableIsBadRestriction (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) : Decidable (φ.IsBadRestriction ρ) := by
  classical infer_instance

theorem DNFFormula.exists_compatible_of_badRestriction
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    ∃ i : Fin φ.terms.length, (φ.terms.get i).Compatible ρ := by
  rcases hbad with ⟨x, y, hxy⟩
  have hneg : φ.eval (CoordRestriction.complete ρ x) = -1 ∨
      φ.eval (CoordRestriction.complete ρ y) = -1 := by
    rcases Int.units_eq_one_or (φ.eval (CoordRestriction.complete ρ x)) with hx | hx
    · rcases Int.units_eq_one_or (φ.eval (CoordRestriction.complete ρ y)) with hy | hy
      · exact False.elim (hxy (by simp [CoordRestriction.restrict, DNFFormula.toBooleanFunction,
          hx, hy]))
      · exact Or.inr hy
    · exact Or.inl hx
  rcases hneg with hx | hy
  · obtain ⟨T, hT, hTx⟩ := (φ.eval_eq_neg_one_iff _).1 hx
    obtain ⟨i, rfl⟩ := List.get_of_mem hT
    exact ⟨i, x, hTx⟩
  · obtain ⟨T, hT, hTy⟩ := (φ.eval_eq_neg_one_iff _).1 hy
    obtain ⟨i, rfl⟩ := List.get_of_mem hT
    exact ⟨i, y, hTy⟩

theorem DNFTerm.exists_free_literal_of_compatible_of_badRestriction
    (φ : DNFFormula n) (T : DNFTerm n) (ρ : Fin n → CoordRestriction)
    (hT : T ∈ φ.terms) (hcompat : T.Compatible ρ) (hbad : φ.IsBadRestriction ρ) :
    ∃ ℓ ∈ T.literals, ρ ℓ.index = .free := by
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  obtain ⟨x, hTx⟩ := hcompat
  have hfixed (y : 𝔽₂^[n]) : T.eval (CoordRestriction.complete ρ y) = -1 := by
    rw [T.eval_eq_neg_one_iff]
    intro ℓ hℓ
    have hx := (T.eval_eq_neg_one_iff _).1 hTx ℓ hℓ
    cases hρ : ρ ℓ.index with
    | free => exact False.elim (hnone ℓ hℓ hρ)
    | fixOne => simpa [CoordRestriction.complete, hρ] using hx
    | fixNegOne => simpa [CoordRestriction.complete, hρ] using hx
  rcases hbad with ⟨y, z, hyz⟩
  have htrue (u : 𝔽₂^[n]) : φ.eval (CoordRestriction.complete ρ u) = -1 :=
    (φ.eval_eq_neg_one_iff _).2 ⟨T, hT, hfixed u⟩
  exact hyz (by simp [CoordRestriction.restrict, DNFFormula.toBooleanFunction, htrue])

/-- Indices of terms compatible with a partial restriction. -/
noncomputable def DNFFormula.compatibleTermIndices (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) : Finset (Fin φ.terms.length) :=
  Finset.univ.filter fun i ↦ (φ.terms.get i).Compatible ρ

theorem DNFFormula.compatibleTermIndices_nonempty_of_badRestriction
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    (φ.compatibleTermIndices ρ).Nonempty := by
  obtain ⟨i, hi⟩ := φ.exists_compatible_of_badRestriction ρ hbad
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- The first compatible term, using the formula's book order. -/
noncomputable def DNFFormula.firstCompatibleTermIndex (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    Fin φ.terms.length :=
  (φ.compatibleTermIndices ρ).min'
    (φ.compatibleTermIndices_nonempty_of_badRestriction ρ hbad)

theorem DNFFormula.firstCompatibleTermIndex_mem (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    φ.firstCompatibleTermIndex ρ hbad ∈ φ.compatibleTermIndices ρ :=
  Finset.min'_mem _ _

theorem DNFFormula.firstCompatibleTerm_compatible (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    (φ.terms.get (φ.firstCompatibleTermIndex ρ hbad)).Compatible ρ := by
  exact (Finset.mem_filter.mp (φ.firstCompatibleTermIndex_mem ρ hbad)).2

/-- Free support of the first compatible term of a bad restriction. -/
noncomputable def DNFFormula.firstCompatibleFreeSupport (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) : Finset (Fin n) :=
  (φ.terms.get (φ.firstCompatibleTermIndex ρ hbad)).support ∩
    CoordRestriction.freeCoordinates ρ

theorem DNFFormula.firstCompatibleFreeSupport_nonempty (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    (φ.firstCompatibleFreeSupport ρ hbad).Nonempty := by
  let i := φ.firstCompatibleTermIndex ρ hbad
  let T := φ.terms.get i
  have hT : T ∈ φ.terms := List.get_mem φ.terms i
  have hcompat : T.Compatible ρ := φ.firstCompatibleTerm_compatible ρ hbad
  obtain ⟨ℓ, hℓT, hℓfree⟩ :=
    T.exists_free_literal_of_compatible_of_badRestriction φ ρ hT hcompat hbad
  refine ⟨ℓ.index, ?_⟩
  change ℓ.index ∈ T.support ∩ CoordRestriction.freeCoordinates ρ
  rw [Finset.mem_inter]
  exact ⟨T.mem_support_of_mem_literals hℓT,
    (CoordRestriction.mem_freeCoordinates_iff ρ ℓ.index).2 hℓfree⟩

/-- Minimal free variable in the first compatible term, as in Exercise 4.19(a). -/
noncomputable def DNFFormula.firstBadCoordinate (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) : Fin n :=
  (φ.firstCompatibleFreeSupport ρ hbad).min'
    (φ.firstCompatibleFreeSupport_nonempty ρ hbad)

theorem DNFFormula.firstBadCoordinate_mem (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    φ.firstBadCoordinate ρ hbad ∈ φ.firstCompatibleFreeSupport ρ hbad :=
  Finset.min'_mem _ _

theorem DNFFormula.firstBadCoordinate_free (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    ρ (φ.firstBadCoordinate ρ hbad) = .free := by
  exact (CoordRestriction.mem_freeCoordinates_iff ρ _).1
    (Finset.mem_inter.mp (φ.firstBadCoordinate_mem ρ hbad)).2

/-- Coordinate state fixing a variable to a specified sign. -/
def CoordRestriction.fixedState (s : Sign) : CoordRestriction :=
  if s = 1 then .fixOne else .fixNegOne

/-- Extend a restriction by fixing one coordinate. -/
def CoordRestriction.fixCoordinate (ρ : Fin n → CoordRestriction)
    (i : Fin n) (s : Sign) : Fin n → CoordRestriction :=
  Function.update ρ i (CoordRestriction.fixedState s)

@[simp] theorem CoordRestriction.fixCoordinate_apply_self
    (ρ : Fin n → CoordRestriction) (i : Fin n) (s : Sign) :
    CoordRestriction.fixCoordinate ρ i s i = CoordRestriction.fixedState s := by
  simp [CoordRestriction.fixCoordinate]

theorem CoordRestriction.fixCoordinate_apply_of_ne
    (ρ : Fin n → CoordRestriction) {i j : Fin n} (hij : j ≠ i) (s : Sign) :
    CoordRestriction.fixCoordinate ρ i s j = ρ j := by
  simp [CoordRestriction.fixCoordinate, hij]

theorem CoordRestriction.complete_fixCoordinate_of_free
    (ρ : Fin n → CoordRestriction) (i : Fin n) (s : Sign) (hfree : ρ i = .free)
    (x : 𝔽₂^[n]) :
    CoordRestriction.complete (CoordRestriction.fixCoordinate ρ i s) x =
      CoordRestriction.complete ρ (Function.update x i (binarySignEquiv.symm s)) := by
  funext j
  by_cases hji : j = i
  · subst j
    rcases Int.units_eq_one_or s with rfl | rfl <;>
      simp [CoordRestriction.complete, CoordRestriction.fixCoordinate,
        CoordRestriction.fixedState, binarySignEquiv, signEncode, hfree]
  · simp [CoordRestriction.complete, CoordRestriction.fixCoordinate, hji]

theorem CoordRestriction.complete_fixCoordinate_eq_of_value
    (ρ : Fin n → CoordRestriction) (i : Fin n) (s : Sign)
    (x : 𝔽₂^[n]) (hx : CoordRestriction.complete ρ x i = s) :
    CoordRestriction.complete (CoordRestriction.fixCoordinate ρ i s) x =
      CoordRestriction.complete ρ x := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [hx]
    rcases Int.units_eq_one_or s with hs | hs <;>
      simp [CoordRestriction.complete, CoordRestriction.fixCoordinate,
        CoordRestriction.fixedState, hs]
  · simp [CoordRestriction.complete, CoordRestriction.fixCoordinate, hji]

theorem DNFTerm.compatible_of_fixCoordinate
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) (i : Fin n) (s : Sign)
    (hfree : ρ i = .free)
    (hcompat : T.Compatible (CoordRestriction.fixCoordinate ρ i s)) :
    T.Compatible ρ := by
  obtain ⟨x, hx⟩ := hcompat
  refine ⟨Function.update x i (binarySignEquiv.symm s), ?_⟩
  rwa [← CoordRestriction.complete_fixCoordinate_of_free ρ i s hfree x]

/-- Minimal compatible term under an explicit nonemptiness witness. -/
noncomputable def DNFFormula.firstCompatibleTermIndexOf (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (h : (φ.compatibleTermIndices ρ).Nonempty) :
    Fin φ.terms.length :=
  (φ.compatibleTermIndices ρ).min' h

theorem DNFFormula.firstCompatibleTermIndex_eq_firstCompatibleTermIndexOf
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction)
    (hbad : φ.IsBadRestriction ρ) :
    φ.firstCompatibleTermIndex ρ hbad =
      φ.firstCompatibleTermIndexOf ρ
        (φ.compatibleTermIndices_nonempty_of_badRestriction ρ hbad) := rfl

/-- Sign which uniquely extends a bad restriction without falsifying its first nontrivial term. -/
noncomputable def DNFFormula.firstBadRequiredSign (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) : Sign :=
  let T := φ.terms.get (φ.firstCompatibleTermIndex ρ hbad)
  let j := φ.firstBadCoordinate ρ hbad
  T.requiredAt j (Finset.mem_inter.mp (φ.firstBadCoordinate_mem ρ hbad)).1

/-- Exercise 4.19(a)'s extension `R'`. -/
noncomputable def DNFFormula.badExtension (φ : DNFFormula n)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    Fin n → CoordRestriction :=
  CoordRestriction.fixCoordinate ρ (φ.firstBadCoordinate ρ hbad)
    (φ.firstBadRequiredSign ρ hbad)

theorem DNFFormula.firstCompatibleTerm_compatible_badExtension
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction)
    (hbad : φ.IsBadRestriction ρ) :
    (φ.terms.get (φ.firstCompatibleTermIndex ρ hbad)).Compatible
      (φ.badExtension ρ hbad) := by
  let i := φ.firstCompatibleTermIndex ρ hbad
  let T := φ.terms.get i
  let j := φ.firstBadCoordinate ρ hbad
  have hjT : j ∈ T.support :=
    (Finset.mem_inter.mp (φ.firstBadCoordinate_mem ρ hbad)).1
  obtain ⟨x, hx⟩ := φ.firstCompatibleTerm_compatible ρ hbad
  have hxj : CoordRestriction.complete ρ x j = T.requiredAt j hjT :=
    (T.eval_eq_neg_one_iff_requiredAt _).1 hx j hjT
  refine ⟨x, ?_⟩
  unfold DNFFormula.badExtension DNFFormula.firstBadRequiredSign
  rwa [CoordRestriction.complete_fixCoordinate_eq_of_value ρ j
    (T.requiredAt j hjT) x hxj]

theorem DNFFormula.compatible_of_badExtension
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction)
    (hbad : φ.IsBadRestriction ρ) (T : DNFTerm n)
    (hT : T.Compatible (φ.badExtension ρ hbad)) : T.Compatible ρ := by
  exact T.compatible_of_fixCoordinate ρ (φ.firstBadCoordinate ρ hbad)
    (φ.firstBadRequiredSign ρ hbad) (φ.firstBadCoordinate_free ρ hbad) hT

theorem DNFFormula.compatibleTermIndices_badExtension_nonempty
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction)
    (hbad : φ.IsBadRestriction ρ) :
    (φ.compatibleTermIndices (φ.badExtension ρ hbad)).Nonempty := by
  refine ⟨φ.firstCompatibleTermIndex ρ hbad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact φ.firstCompatibleTerm_compatible_badExtension ρ hbad

theorem DNFFormula.firstCompatibleTermIndexOf_badExtension
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction)
    (hbad : φ.IsBadRestriction ρ) :
    φ.firstCompatibleTermIndexOf (φ.badExtension ρ hbad)
        (φ.compatibleTermIndices_badExtension_nonempty ρ hbad) =
      φ.firstCompatibleTermIndex ρ hbad := by
  apply le_antisymm
  · exact Finset.min'_le (s := φ.compatibleTermIndices (φ.badExtension ρ hbad))
      (φ.firstCompatibleTermIndex ρ hbad)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        φ.firstCompatibleTerm_compatible_badExtension ρ hbad⟩)
  · apply Finset.min'_le (s := φ.compatibleTermIndices ρ)
      (φ.firstCompatibleTermIndexOf (φ.badExtension ρ hbad)
        (φ.compatibleTermIndices_badExtension_nonempty ρ hbad))
    have htarget := Finset.min'_mem
      (φ.compatibleTermIndices (φ.badExtension ρ hbad))
      (φ.compatibleTermIndices_badExtension_nonempty ρ hbad)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact φ.compatible_of_badExtension ρ hbad _ (Finset.mem_filter.mp htarget).2

/-- Bad restrictions as a finite set. -/
noncomputable def DNFFormula.badRestrictions (φ : DNFFormula n) :
    Finset (Fin n → CoordRestriction) :=
  Finset.univ.filter φ.IsBadRestriction

/-- Exercise 4.19's encoding map, defined on the bad-restriction subtype. -/
noncomputable def DNFFormula.badExtensionMap (φ : DNFFormula n) :
    { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ } →
      (Fin n → CoordRestriction) :=
  fun ρ ↦ φ.badExtension ρ.1 ρ.2

noncomputable def DNFFormula.badCoordinateMap (φ : DNFFormula n) :
    { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ } → Fin n :=
  fun ρ ↦ φ.firstBadCoordinate ρ.1 ρ.2

theorem DNFFormula.recover_badRestriction (φ : DNFFormula n)
    (ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ }) :
    Function.update (φ.badExtensionMap ρ) (φ.badCoordinateMap ρ) .free = ρ.1 := by
  funext i
  by_cases hi : i = φ.badCoordinateMap ρ
  · subst i
    simp [DNFFormula.badExtensionMap, DNFFormula.badCoordinateMap,
      DNFFormula.badExtension, DNFFormula.firstBadCoordinate_free]
  · change i ≠ φ.firstBadCoordinate ρ.1 ρ.2 at hi
    simp [DNFFormula.badExtensionMap, DNFFormula.badCoordinateMap,
      DNFFormula.badExtension, CoordRestriction.fixCoordinate, hi]

theorem DNFFormula.badCoordinateMap_injective_on_fiber (φ : DNFFormula n)
    (η : Fin n → CoordRestriction) :
    Set.InjOn φ.badCoordinateMap { ρ | φ.badExtensionMap ρ = η } := by
  intro ρ hρ σ hσ hj
  apply Subtype.ext
  rw [← φ.recover_badRestriction ρ, ← φ.recover_badRestriction σ,
    hρ, hσ, hj]

/-- Fiber of the Exercise 4.19 encoding over a fixed extended restriction. -/
noncomputable def DNFFormula.badExtensionFiber (φ : DNFFormula n)
    (η : Fin n → CoordRestriction) :
    Finset { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ } :=
  Finset.univ.filter fun ρ ↦ φ.badExtensionMap ρ = η

theorem DNFFormula.badExtensionFiber_card_le_width (φ : DNFFormula n)
    {w : ℕ} (hw : φ.width ≤ w) (η : Fin n → CoordRestriction) :
    (φ.badExtensionFiber η).card ≤ w := by
  classical
  by_cases hempty : φ.badExtensionFiber η = ∅
  · simp [hempty]
  · obtain ⟨ρ₀, hρ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hρ₀ext : φ.badExtensionMap ρ₀ = η :=
      (Finset.mem_filter.mp hρ₀).2
    let i₀ := φ.firstCompatibleTermIndex ρ₀.1 ρ₀.2
    let T₀ := φ.terms.get i₀
    have himage :
        (φ.badExtensionFiber η).image φ.badCoordinateMap ⊆ T₀.support := by
      intro j hj
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
      have hρext : φ.badExtensionMap ρ = η := (Finset.mem_filter.mp hρ).2
      have hext : φ.badExtension ρ.1 ρ.2 = φ.badExtension ρ₀.1 ρ₀.2 := by
        exact hρext.trans hρ₀ext.symm
      have hi : φ.firstCompatibleTermIndex ρ.1 ρ.2 = i₀ := by
        change φ.firstCompatibleTermIndex ρ.1 ρ.2 =
          φ.firstCompatibleTermIndex ρ₀.1 ρ₀.2
        apply le_antisymm
        · apply Finset.min'_le (s := φ.compatibleTermIndices ρ.1)
            (φ.firstCompatibleTermIndex ρ₀.1 ρ₀.2)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          apply φ.compatible_of_badExtension ρ.1 ρ.2
          rw [hext]
          exact φ.firstCompatibleTerm_compatible_badExtension ρ₀.1 ρ₀.2
        · apply Finset.min'_le (s := φ.compatibleTermIndices ρ₀.1)
            (φ.firstCompatibleTermIndex ρ.1 ρ.2)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          apply φ.compatible_of_badExtension ρ₀.1 ρ₀.2
          rw [← hext]
          exact φ.firstCompatibleTerm_compatible_badExtension ρ.1 ρ.2
      have hjSupport :=
        (Finset.mem_inter.mp (φ.firstBadCoordinate_mem ρ.1 ρ.2)).1
      simpa [DNFFormula.badCoordinateMap, T₀, i₀, hi] using hjSupport
    calc
      (φ.badExtensionFiber η).card =
          ((φ.badExtensionFiber η).image φ.badCoordinateMap).card := by
        symm
        apply Finset.card_image_of_injOn
        intro ρ hρ σ hσ
        exact φ.badCoordinateMap_injective_on_fiber η
          (Finset.mem_filter.mp hρ).2 (Finset.mem_filter.mp hσ).2
      _ ≤ T₀.support.card := Finset.card_le_card himage
      _ = T₀.width := T₀.card_support
      _ ≤ φ.width := φ.width_le_of_mem (List.get_mem φ.terms i₀)
      _ ≤ w := hw

@[simp] theorem coordRestrictionWeightAt_fixedState (δ : ℝ) (s : Sign) :
    coordRestrictionWeightAt δ (CoordRestriction.fixedState s) = (1 - δ) / 2 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    simp [CoordRestriction.fixedState, coordRestrictionWeightAt]

/-- Exercise 4.19(c): exact weight ratio between a bad restriction and its one-coordinate
extension. -/
theorem DNFFormula.restrictionAssignmentWeightAt_badExtension_eq
    (φ : DNFFormula n) (δ : ℝ) (hδ : δ ≠ 1)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    restrictionAssignmentWeightAt δ ρ =
      (2 * δ / (1 - δ)) *
        restrictionAssignmentWeightAt δ (φ.badExtension ρ hbad) := by
  classical
  let j := φ.firstBadCoordinate ρ hbad
  let s := φ.firstBadRequiredSign ρ hbad
  let P := ∏ i ∈ (Finset.univ : Finset (Fin n)).erase j,
    coordRestrictionWeightAt δ (ρ i)
  have hsource : restrictionAssignmentWeightAt δ ρ = δ * P := by
    rw [restrictionAssignmentWeightAt,
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun i ↦ coordRestrictionWeightAt δ (ρ i)) (Finset.mem_univ j)]
    rw [φ.firstBadCoordinate_free ρ hbad]
    rfl
  have htarget : restrictionAssignmentWeightAt δ (φ.badExtension ρ hbad) =
      ((1 - δ) / 2) * P := by
    rw [restrictionAssignmentWeightAt,
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun i ↦ coordRestrictionWeightAt δ ((φ.badExtension ρ hbad) i))
        (Finset.mem_univ j)]
    have hj : φ.badExtension ρ hbad j = CoordRestriction.fixedState s := by
      simp [DNFFormula.badExtension, j, s]
    rw [hj, coordRestrictionWeightAt_fixedState]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [DNFFormula.badExtension, CoordRestriction.fixCoordinate_apply_of_ne ρ hij s]
  rw [hsource, htarget]
  have hone : 1 - δ ≠ 0 := sub_ne_zero.mpr hδ.symm
  field_simp [hone]

theorem DNFFormula.restrictionAssignmentWeightAt_badExtension_le
    (φ : DNFFormula n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 3)
    (ρ : Fin n → CoordRestriction) (hbad : φ.IsBadRestriction ρ) :
    restrictionAssignmentWeightAt δ ρ ≤
      3 * δ * restrictionAssignmentWeightAt δ (φ.badExtension ρ hbad) := by
  rw [φ.restrictionAssignmentWeightAt_badExtension_eq δ (by linarith) ρ hbad]
  have hweight :
      0 ≤ restrictionAssignmentWeightAt δ (φ.badExtension ρ hbad) :=
    restrictionAssignmentWeightAt_nonneg hδ0 (hδ.trans (by norm_num)) _
  apply mul_le_mul_of_nonneg_right _ hweight
  have hdenom : 0 < 1 - δ := by linarith
  apply (div_le_iff₀ hdenom).2
  nlinarith

/-- Total weight of bad restrictions in the independent-coordinate model. -/
noncomputable def DNFFormula.badRestrictionWeight (φ : DNFFormula n) (δ : ℝ) : ℝ :=
  ∑ ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ },
    restrictionAssignmentWeightAt δ ρ.1

theorem DNFFormula.sum_weight_badExtension_le
    (φ : DNFFormula n) {w : ℕ} (hw : φ.width ≤ w)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∑ ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ },
      restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ)) ≤ w := by
  classical
  calc
    (∑ ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ },
        restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ)) =
        ∑ η : Fin n → CoordRestriction,
          ∑ ρ ∈ φ.badExtensionFiber η,
            restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro ρ _
      exact Finset.mem_univ _
    _ = ∑ η : Fin n → CoordRestriction,
          ((φ.badExtensionFiber η).card : ℝ) * restrictionAssignmentWeightAt δ η := by
      apply Finset.sum_congr rfl
      intro η _
      calc
        (∑ ρ ∈ φ.badExtensionFiber η,
            restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ)) =
            ∑ _ρ ∈ φ.badExtensionFiber η, restrictionAssignmentWeightAt δ η := by
          apply Finset.sum_congr rfl
          intro ρ hρ
          rw [(Finset.mem_filter.mp hρ).2]
        _ = ((φ.badExtensionFiber η).card : ℝ) *
            restrictionAssignmentWeightAt δ η := by simp
    _ ≤ ∑ η : Fin n → CoordRestriction,
          (w : ℝ) * restrictionAssignmentWeightAt δ η := by
      refine Finset.sum_le_sum fun η _ ↦ ?_
      apply mul_le_mul_of_nonneg_right _ (restrictionAssignmentWeightAt_nonneg hδ0 hδ1 η)
      exact_mod_cast φ.badExtensionFiber_card_le_width hw η
    _ = (w : ℝ) * ∑ η : Fin n → CoordRestriction,
          restrictionAssignmentWeightAt δ η := by rw [Finset.mul_sum]
    _ = w := by rw [sum_restrictionAssignmentWeightAt, mul_one]

/-- Exercise 4.19(d): the Baby Switching bound with constant `3`, independent of DNF size. -/
theorem exercise4_19
    (φ : DNFFormula n) {w : ℕ} (hw : φ.width ≤ w) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 3) :
    φ.badRestrictionWeight δ ≤ 3 * δ * w := by
  have hδ1 : δ ≤ 1 := hδ.trans (by norm_num)
  calc
    φ.badRestrictionWeight δ ≤
        ∑ ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ },
          3 * δ * restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ) := by
      unfold DNFFormula.badRestrictionWeight
      exact Finset.sum_le_sum fun ρ _ ↦
        φ.restrictionAssignmentWeightAt_badExtension_le δ hδ0 hδ ρ.1 ρ.2
    _ = 3 * δ * ∑ ρ : { ρ : Fin n → CoordRestriction // φ.IsBadRestriction ρ },
          restrictionAssignmentWeightAt δ (φ.badExtensionMap ρ) := by
      rw [Finset.mul_sum]
    _ ≤ 3 * δ * w := by
      exact mul_le_mul_of_nonneg_left (φ.sum_weight_badExtension_le hw δ hδ0 hδ1)
        (mul_nonneg (by norm_num) hδ0)

/-! ## The exact depth-one switching event -/

theorem F₂DecisionTree.eval_eq_of_depth_eq_zero
    (T : DecisionTree n Sign) (hT : T.depth = 0) (x y : 𝔽₂^[n]) :
    T.eval x = T.eval y := by
  cases T with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild =>
      simp [F₂DecisionTree.depth] at hT

theorem one_le_decisionTreeDepth_iff_nonconstant (f : 𝔽₂^[n] → Sign) :
    1 ≤ F₂DecisionTree.decisionTreeDepth f ↔ ∃ x y, f x ≠ f y := by
  constructor
  · intro hdepth
    by_contra hconstant
    push Not at hconstant
    let T : DecisionTree n Sign := .leaf (f 0)
    have hcomputes : T.Computes f := by
      apply (F₂DecisionTree.computes_iff T f).2
      intro x
      simpa [T, F₂DecisionTree.eval] using hconstant 0 x
    have hle := F₂DecisionTree.decisionTreeDepth_le_of_computes f T hcomputes
    simp [T, F₂DecisionTree.depth] at hle
    omega
  · rintro ⟨x, y, hxy⟩
    obtain ⟨T, hcomputes, hdepth⟩ :=
      F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth f
    by_contra hlt
    have hzero : T.depth = 0 := by
      rw [hdepth]
      omega
    apply hxy
    rw [← (F₂DecisionTree.computes_iff T f).1 hcomputes x,
      ← (F₂DecisionTree.computes_iff T f).1 hcomputes y]
    exact T.eval_eq_of_depth_eq_zero hzero x y

theorem coordSwitchingFailureIndicator_one_eq_badRestriction
    (φ : DNFFormula n) (ρ : Fin n → CoordRestriction) :
    coordSwitchingFailureIndicator φ.toBooleanFunction 1 ρ =
      if φ.IsBadRestriction ρ then 1 else 0 := by
  simp only [coordSwitchingFailureIndicator, one_le_decisionTreeDepth_iff_nonconstant,
    DNFFormula.IsBadRestriction]
  by_cases hbad : ∃ x y,
      CoordRestriction.restrict φ.toBooleanFunction ρ x ≠
        CoordRestriction.restrict φ.toBooleanFunction ρ y <;> simp [hbad]

theorem DNFFormula.badRestrictionWeight_eq_coordSwitchingFailureProbability
    (φ : DNFFormula n) (δ : ℝ) :
    φ.badRestrictionWeight δ =
      coordSwitchingFailureProbability φ.toBooleanFunction δ 1 := by
  classical
  rw [DNFFormula.badRestrictionWeight, coordSwitchingFailureProbability]
  simp_rw [coordSwitchingFailureIndicator_one_eq_badRestriction, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

/-- Exercise 4.19 in the canonical switching-probability presentation. -/
theorem exercise4_19_switchingFailureProbability
    (φ : DNFFormula n) {w : ℕ} (hw : φ.width ≤ w) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 3) :
    switchingFailureProbability φ.toBooleanFunction δ 1 ≤ 3 * δ * w := by
  rw [← coordSwitchingFailureProbability_eq,
    ← φ.badRestrictionWeight_eq_coordSwitchingFailureProbability]
  exact exercise4_19 φ hw hδ0 hδ

theorem DNFFormula.toBooleanFunction_eq_of_width_eq_zero
    (φ : DNFFormula n) (hw : φ.width = 0) (x y : {−1,1}^[n]) :
    φ.toBooleanFunction x = φ.toBooleanFunction y := by
  by_cases hnil : φ.terms = []
  · simp [DNFFormula.toBooleanFunction, DNFFormula.eval, hnil]
  · obtain ⟨T, hT⟩ := List.exists_mem_of_ne_nil φ.terms hnil
    have hTwidth : T.width = 0 :=
      Nat.eq_zero_of_le_zero ((φ.width_le_of_mem hT).trans_eq hw)
    have hTliterals : T.literals = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [DNFTerm.width] using hTwidth)
    have hTx : T.eval x = -1 := by
      rw [T.eval_eq_neg_one_iff]
      simp [hTliterals]
    have hTy : T.eval y = -1 := by
      rw [T.eval_eq_neg_one_iff]
      simp [hTliterals]
    rw [DNFFormula.toBooleanFunction,
      (φ.eval_eq_neg_one_iff x).2 ⟨T, hT, hTx⟩,
      (φ.eval_eq_neg_one_iff y).2 ⟨T, hT, hTy⟩]

theorem DNFFormula.badRestrictionWeight_eq_zero_of_width_eq_zero
    (φ : DNFFormula n) (hw : φ.width = 0) (δ : ℝ) :
    φ.badRestrictionWeight δ = 0 := by
  classical
  unfold DNFFormula.badRestrictionWeight
  apply Finset.sum_eq_zero
  rintro ⟨ρ, hbad⟩ _
  exact False.elim (by
    obtain ⟨x, y, hxy⟩ := hbad
    exact hxy (φ.toBooleanFunction_eq_of_width_eq_zero hw
      (CoordRestriction.complete ρ x) (CoordRestriction.complete ρ y)))

/-- The exact size-independent Baby Switching bound for a width-bounded DNF. -/
theorem babySwitchingLemma_dnf
    (φ : DNFFormula n) {w : ℕ} (hw : φ.width ≤ w) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    switchingFailureProbability φ.toBooleanFunction δ 1 ≤ 5 * δ * w := by
  by_cases hsmall : δ ≤ 1 / 3
  · calc
      switchingFailureProbability φ.toBooleanFunction δ 1 ≤ 3 * δ * w :=
        exercise4_19_switchingFailureProbability φ hw hδ0 hsmall
      _ ≤ 5 * δ * w := by
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith
  · by_cases hwzero : w = 0
    · have hφzero : φ.width = 0 := Nat.eq_zero_of_le_zero (hwzero ▸ hw)
      rw [← coordSwitchingFailureProbability_eq,
        ← φ.badRestrictionWeight_eq_coordSwitchingFailureProbability,
        φ.badRestrictionWeight_eq_zero_of_width_eq_zero hφzero]
      positivity
    · calc
        switchingFailureProbability φ.toBooleanFunction δ 1 ≤ 1 :=
          switchingFailureProbability_le_one hδ0 hδ1
        _ ≤ 5 * δ * w := by
          have hδ : 1 / 3 < δ := lt_of_not_ge hsmall
          have hwone : (1 : ℝ) ≤ w := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hwzero
          nlinarith

/-! ## Boolean duality preserves switching failure -/

/-- Complement every bit of a binary-cube input. -/
def binaryCubeComplement (x : 𝔽₂^[n]) : 𝔽₂^[n] :=
  fun i ↦ x i + 1

@[simp] theorem f₂_one_add_one : (1 : 𝔽₂) + 1 = 0 := by
  decide

@[simp] theorem binaryCubeComplement_involutive (x : 𝔽₂^[n]) :
    binaryCubeComplement (binaryCubeComplement x) = x := by
  funext i
  simp [binaryCubeComplement, add_assoc]

theorem signEncode_binaryCubeComplement (x : 𝔽₂^[n]) (i : Fin n) :
    signEncode (binaryCubeComplement x i) = -signEncode (x i) := by
  rw [binaryCubeComplement, signEncode_add]
  simp

/-- Swap every query's children, thereby complementing every queried input bit. -/
def F₂DecisionTree.complementInputs {α : Type*} {available : Finset (Fin n)} :
    F₂DecisionTree n α available → F₂DecisionTree n α available
  | .leaf value => .leaf value
  | .query coordinate hcoordinate zeroChild oneChild =>
      .query coordinate hcoordinate (complementInputs oneChild) (complementInputs zeroChild)

theorem F₂DecisionTree.eval_complementInputs {α : Type*}
    {available : Finset (Fin n)} (T : F₂DecisionTree n α available) (x : 𝔽₂^[n]) :
    T.complementInputs.eval x = T.eval (binaryCubeComplement x) := by
  induction T with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      by_cases hx : x coordinate = 0
      · simp [F₂DecisionTree.complementInputs, F₂DecisionTree.eval,
          binaryCubeComplement, hx, hone]
      · have hxone : x coordinate = 1 := Fin.eq_one_of_ne_zero _ hx
        simp [F₂DecisionTree.complementInputs, F₂DecisionTree.eval,
          binaryCubeComplement, hxone, hzero]

@[simp] theorem F₂DecisionTree.depth_complementInputs {α : Type*}
    {available : Finset (Fin n)} (T : F₂DecisionTree n α available) :
    T.complementInputs.depth = T.depth := by
  induction T with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp [F₂DecisionTree.complementInputs, F₂DecisionTree.depth, hzero, hone, max_comm]

/-- Apply a pure output map at every leaf. -/
def F₂DecisionTree.mapOutputs {α β : Type*} (g : α → β)
    {available : Finset (Fin n)} :
    F₂DecisionTree n α available → F₂DecisionTree n β available
  | .leaf value => .leaf (g value)
  | .query coordinate hcoordinate zeroChild oneChild =>
      .query coordinate hcoordinate (mapOutputs g zeroChild) (mapOutputs g oneChild)

theorem F₂DecisionTree.eval_mapOutputs {α β : Type*} (g : α → β)
    {available : Finset (Fin n)} (T : F₂DecisionTree n α available) (x : 𝔽₂^[n]) :
    (T.mapOutputs g).eval x = g (T.eval x) := by
  induction T with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp only [F₂DecisionTree.mapOutputs, F₂DecisionTree.eval]
      split <;> simp_all

@[simp] theorem F₂DecisionTree.depth_mapOutputs {α β : Type*} (g : α → β)
    {available : Finset (Fin n)} (T : F₂DecisionTree n α available) :
    (T.mapOutputs g).depth = T.depth := by
  induction T with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      simp [F₂DecisionTree.mapOutputs, F₂DecisionTree.depth, hzero, hone]

/-- Binary-cube form of Boolean duality. -/
def binaryBooleanDual (f : 𝔽₂^[n] → Sign) : 𝔽₂^[n] → Sign :=
  fun x ↦ -f (binaryCubeComplement x)

theorem decisionTreeDepth_binaryBooleanDual_le (f : 𝔽₂^[n] → Sign) :
    F₂DecisionTree.decisionTreeDepth (binaryBooleanDual f) ≤
      F₂DecisionTree.decisionTreeDepth f := by
  obtain ⟨T, hcomputes, hdepth⟩ :=
    F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth f
  let S : DecisionTree n Sign := T.complementInputs.mapOutputs Neg.neg
  have hS : S.Computes (binaryBooleanDual f) := by
    apply (F₂DecisionTree.computes_iff S (binaryBooleanDual f)).2
    intro x
    rw [F₂DecisionTree.eval_mapOutputs, F₂DecisionTree.eval_complementInputs,
      (F₂DecisionTree.computes_iff T f).1 hcomputes]
    rfl
  calc
    F₂DecisionTree.decisionTreeDepth (binaryBooleanDual f) ≤ S.depth :=
      F₂DecisionTree.decisionTreeDepth_le_of_computes _ S hS
    _ = T.depth := by simp [S]
    _ = F₂DecisionTree.decisionTreeDepth f := hdepth

theorem binaryBooleanDual_involutive (f : 𝔽₂^[n] → Sign) :
    binaryBooleanDual (binaryBooleanDual f) = f := by
  funext x
  simp [binaryBooleanDual]

theorem decisionTreeDepth_binaryBooleanDual (f : 𝔽₂^[n] → Sign) :
    F₂DecisionTree.decisionTreeDepth (binaryBooleanDual f) =
      F₂DecisionTree.decisionTreeDepth f := by
  apply le_antisymm
  · exact decisionTreeDepth_binaryBooleanDual_le f
  · have h := decisionTreeDepth_binaryBooleanDual_le (binaryBooleanDual f)
    rwa [binaryBooleanDual_involutive] at h

/-- Negate the fixed sign of a coordinate restriction, leaving free coordinates free. -/
def CoordRestriction.negateState : CoordRestriction → CoordRestriction
  | .free => .free
  | .fixOne => .fixNegOne
  | .fixNegOne => .fixOne

@[simp] theorem CoordRestriction.negateState_involutive (c : CoordRestriction) :
    c.negateState.negateState = c := by
  cases c <;> rfl

/-- Coordinatewise sign negation of a restriction. -/
def CoordRestriction.negateAssignment
    (ρ : Fin n → CoordRestriction) : Fin n → CoordRestriction :=
  fun i ↦ (ρ i).negateState

@[simp] theorem CoordRestriction.negateAssignment_involutive
    (ρ : Fin n → CoordRestriction) :
    CoordRestriction.negateAssignment (CoordRestriction.negateAssignment ρ) = ρ := by
  funext i
  simp [CoordRestriction.negateAssignment]

/-- Negating all fixed signs is an involutive equivalence on restrictions. -/
def coordRestrictionNegationEquiv :
    (Fin n → CoordRestriction) ≃ (Fin n → CoordRestriction) where
  toFun := CoordRestriction.negateAssignment
  invFun := CoordRestriction.negateAssignment
  left_inv := CoordRestriction.negateAssignment_involutive
  right_inv := CoordRestriction.negateAssignment_involutive

@[simp] theorem coordRestrictionWeightAt_negateState (δ : ℝ) (c : CoordRestriction) :
    coordRestrictionWeightAt δ c.negateState = coordRestrictionWeightAt δ c := by
  cases c <;> rfl

@[simp] theorem restrictionAssignmentWeightAt_negateAssignment
    (δ : ℝ) (ρ : Fin n → CoordRestriction) :
    restrictionAssignmentWeightAt δ (CoordRestriction.negateAssignment ρ) =
      restrictionAssignmentWeightAt δ ρ := by
  simp [restrictionAssignmentWeightAt, CoordRestriction.negateAssignment]

theorem CoordRestriction.complete_negateAssignment
    (ρ : Fin n → CoordRestriction) (x : 𝔽₂^[n]) :
    CoordRestriction.complete (CoordRestriction.negateAssignment ρ)
        (binaryCubeComplement x) =
      fun i ↦ -CoordRestriction.complete ρ x i := by
  funext i
  cases hρ : ρ i <;>
    simp [CoordRestriction.complete, CoordRestriction.negateAssignment,
      CoordRestriction.negateState, hρ, signEncode_binaryCubeComplement]

theorem CoordRestriction.restrict_booleanDual
    (f : BooleanFunction n) (ρ : Fin n → CoordRestriction) :
    CoordRestriction.restrict (CNFFormula.booleanDual f) ρ =
      binaryBooleanDual
        (CoordRestriction.restrict f (CoordRestriction.negateAssignment ρ)) := by
  funext x
  unfold CoordRestriction.restrict CNFFormula.booleanDual binaryBooleanDual
  congr 2
  exact (CoordRestriction.complete_negateAssignment ρ x).symm

theorem decisionTreeDepth_restrict_booleanDual
    (f : BooleanFunction n) (ρ : Fin n → CoordRestriction) :
    F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict (CNFFormula.booleanDual f) ρ) =
      F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict f (CoordRestriction.negateAssignment ρ)) := by
  rw [CoordRestriction.restrict_booleanDual, decisionTreeDepth_binaryBooleanDual]

theorem coordSwitchingFailureIndicator_booleanDual
    (f : BooleanFunction n) (k : ℕ) (ρ : Fin n → CoordRestriction) :
    coordSwitchingFailureIndicator (CNFFormula.booleanDual f) k ρ =
      coordSwitchingFailureIndicator f k (CoordRestriction.negateAssignment ρ) := by
  simp [coordSwitchingFailureIndicator, decisionTreeDepth_restrict_booleanDual]

theorem coordSwitchingFailureProbability_booleanDual
    (f : BooleanFunction n) (δ : ℝ) (k : ℕ) :
    coordSwitchingFailureProbability (CNFFormula.booleanDual f) δ k =
      coordSwitchingFailureProbability f δ k := by
  classical
  unfold coordSwitchingFailureProbability
  calc
    (∑ ρ : Fin n → CoordRestriction,
        restrictionAssignmentWeightAt δ ρ *
          coordSwitchingFailureIndicator (CNFFormula.booleanDual f) k ρ) =
        ∑ ρ : Fin n → CoordRestriction,
          restrictionAssignmentWeightAt δ (CoordRestriction.negateAssignment ρ) *
            coordSwitchingFailureIndicator f k (CoordRestriction.negateAssignment ρ) := by
      apply Finset.sum_congr rfl
      intro ρ _
      rw [restrictionAssignmentWeightAt_negateAssignment,
        coordSwitchingFailureIndicator_booleanDual]
    _ = ∑ ρ : Fin n → CoordRestriction,
          restrictionAssignmentWeightAt δ ρ * coordSwitchingFailureIndicator f k ρ :=
      by
        simpa [coordRestrictionNegationEquiv] using
          coordRestrictionNegationEquiv.sum_comp
            (fun ρ ↦ restrictionAssignmentWeightAt δ ρ *
              coordSwitchingFailureIndicator f k ρ)

theorem switchingFailureProbability_booleanDual
    (f : BooleanFunction n) (δ : ℝ) (k : ℕ) :
    switchingFailureProbability (CNFFormula.booleanDual f) δ k =
      switchingFailureProbability f δ k := by
  rw [← coordSwitchingFailureProbability_eq,
    ← coordSwitchingFailureProbability_eq,
    coordSwitchingFailureProbability_booleanDual]

/-- The exact Baby Switching Lemma, for either a DNF or a CNF of width at most `w`. -/
theorem babySwitchingLemma
    {f : BooleanFunction n} {w : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : HasDNFWidthLE f w ∨ HasCNFWidthLE f w) :
    switchingFailureProbability f δ 1 ≤ 5 * δ * w := by
  rcases hf with ⟨φ, hw, rfl⟩ | ⟨ψ, hw, rfl⟩
  · exact babySwitchingLemma_dnf φ hw hδ0 hδ1
  · let φ := CNFFormula.switchAndOr ψ
    have hφwidth : φ.width ≤ w := by
      simpa [φ, CNFFormula.switchAndOr, CNFFormula.width] using hw
    calc
      switchingFailureProbability ψ.toBooleanFunction δ 1 =
          switchingFailureProbability
            (CNFFormula.booleanDual ψ.toBooleanFunction) δ 1 :=
        (switchingFailureProbability_booleanDual ψ.toBooleanFunction δ 1).symm
      _ = switchingFailureProbability φ.toBooleanFunction δ 1 := by
        exact congrArg (fun g ↦ switchingFailureProbability g δ 1)
          (CNFFormula.switchAndOr_toBooleanFunction ψ).symm
      _ ≤ 5 * δ * w := babySwitchingLemma_dnf φ hφwidth hδ0 hδ1



/-! ## Exact composition of independent random restrictions -/


variable {m n : ℕ}

/-! ## Decision-tree depth under coordinate embeddings -/

namespace F₂DecisionTree

variable {α : Type*}

/-- Transport a decision tree along an injective renaming of its queried coordinates. -/
def pushEmbedding (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i ∈ source, e i ∈ target) :
    F₂DecisionTree m α source → F₂DecisionTree n α target
  | .leaf value => .leaf value
  | .query coordinate hcoordinate zeroChild oneChild =>
      .query (e coordinate) (h coordinate hcoordinate)
        (pushEmbedding e (fun i hi ↦ by
          rw [Finset.mem_erase] at hi ⊢
          exact ⟨fun hei ↦ hi.1 (e.injective hei), h i hi.2⟩) zeroChild)
        (pushEmbedding e (fun i hi ↦ by
          rw [Finset.mem_erase] at hi ⊢
          exact ⟨fun hei ↦ hi.1 (e.injective hei), h i hi.2⟩) oneChild)

@[simp] theorem depth_pushEmbedding (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i ∈ source, e i ∈ target)
    (T : F₂DecisionTree m α source) : (T.pushEmbedding e h).depth = T.depth := by
  induction T generalizing target with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      change max (pushEmbedding e _ zeroChild).depth (pushEmbedding e _ oneChild).depth + 1 =
        max zeroChild.depth oneChild.depth + 1
      congr 2
      · exact hzero _
      · exact hone _

@[simp] theorem eval_pushEmbedding (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i ∈ source, e i ∈ target)
    (T : F₂DecisionTree m α source) (x : 𝔽₂^[n]) :
    (T.pushEmbedding e h).eval x = T.eval (fun i ↦ x (e i)) := by
  induction T generalizing target with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      change (if x (e coordinate) = 0 then (pushEmbedding e _ zeroChild).eval x
        else (pushEmbedding e _ oneChild).eval x) =
          if x (e coordinate) = 0 then zeroChild.eval (fun i ↦ x (e i))
          else oneChild.eval (fun i ↦ x (e i))
      by_cases hx : x (e coordinate) = 0
      · rw [if_pos hx, if_pos hx]
        exact hzero _
      · rw [if_neg hx, if_neg hx]
        exact hone _

/-- Pull a decision tree back along an embedding, pruning every query outside its image by
following the zero branch. -/
noncomputable def pullEmbedding (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i, i ∈ source ↔ e i ∈ target) :
    F₂DecisionTree n α target → F₂DecisionTree m α source
  | .leaf value => .leaf value
  | .query coordinate hcoordinate zeroChild oneChild =>
      if hcoordinateImage : ∃ i, e i = coordinate then
        let i := Classical.choose hcoordinateImage
        let hi : i ∈ source := (h i).2 (Classical.choose_spec hcoordinateImage ▸ hcoordinate)
        .query i hi
          (pullEmbedding e (fun j ↦ by
            rw [Finset.mem_erase, Finset.mem_erase, h j]
            constructor
            · rintro ⟨hji, hj⟩
              exact ⟨fun hej ↦ hji (e.injective (hej.trans
                (Classical.choose_spec hcoordinateImage).symm)), hj⟩
            · rintro ⟨hej, hj⟩
              exact ⟨fun hji ↦ hej (congrArg e hji ▸
                Classical.choose_spec hcoordinateImage), hj⟩) zeroChild)
          (pullEmbedding e (fun j ↦ by
            rw [Finset.mem_erase, Finset.mem_erase, h j]
            constructor
            · rintro ⟨hji, hj⟩
              exact ⟨fun hej ↦ hji (e.injective (hej.trans
                (Classical.choose_spec hcoordinateImage).symm)), hj⟩
            · rintro ⟨hej, hj⟩
              exact ⟨fun hji ↦ hej (congrArg e hji ▸
                Classical.choose_spec hcoordinateImage), hj⟩) oneChild)
      else
        pullEmbedding e (fun i ↦ by
          rw [Finset.mem_erase, h i]
          exact ⟨fun hi ↦ ⟨fun hei ↦ hcoordinateImage ⟨i, hei⟩, hi⟩, And.right⟩) zeroChild

theorem depth_pullEmbedding_le (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i, i ∈ source ↔ e i ∈ target)
    (T : F₂DecisionTree n α target) : (T.pullEmbedding e h).depth ≤ T.depth := by
  induction T generalizing source with
  | leaf value => simp [pullEmbedding, depth]
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      rw [pullEmbedding]
      split_ifs with hcoordinateImage
      · simp only [depth]
        apply Nat.add_le_add_right
        apply max_le_max
        · apply hzero
        · apply hone
      · exact ((hzero _).trans (Nat.le_max_left _ _)).trans (Nat.le_add_right _ _)

theorem eval_pullEmbedding (e : Fin m ↪ Fin n) {source : Finset (Fin m)}
    {target : Finset (Fin n)} (h : ∀ i, i ∈ source ↔ e i ∈ target)
    (T : F₂DecisionTree n α target) (x : 𝔽₂^[m]) :
    (T.pullEmbedding e h).eval x = T.eval (Function.extend e x 0) := by
  induction T generalizing source with
  | leaf value => rfl
  | query coordinate hcoordinate zeroChild oneChild hzero hone =>
      rw [pullEmbedding]
      split_ifs with hcoordinateImage
      · let i := Classical.choose hcoordinateImage
        have hei : e i = coordinate := Classical.choose_spec hcoordinateImage
        have heval : Function.extend e x 0 coordinate = x i := by
          rw [← hei, e.injective.extend_apply]
        simp only [eval, heval]
        dsimp only [i]
        by_cases hx : x (Classical.choose hcoordinateImage) = 0
        · rw [if_pos hx, if_pos hx]
          exact hzero _
        · rw [if_neg hx, if_neg hx]
          exact hone _
      · have heval : Function.extend e x 0 coordinate = 0 :=
          Function.extend_apply' (f := e) x 0 coordinate hcoordinateImage
        simp only [eval, heval, if_pos, hzero _]

/-- Adding coordinates on which a function does not depend preserves minimum decision-tree depth. -/
theorem decisionTreeDepth_comp_embedding (e : Fin m ↪ Fin n) (f : 𝔽₂^[m] → α) :
    decisionTreeDepth (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i))) = decisionTreeDepth f := by
  apply Nat.le_antisymm
  · obtain ⟨T, hT, hdepth⟩ := exists_computingTree_depth_eq_decisionTreeDepth f
    let pushed : DecisionTree n α := T.pushEmbedding e (by simp)
    have hpushed : pushed.Computes (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i))) := by
      rw [computes_iff]
      intro x
      rw [show pushed.eval x = T.eval (fun i ↦ x (e i)) by
        exact eval_pushEmbedding e (by simp) T x]
      exact congrFun hT (fun i ↦ x (e i))
    calc
      decisionTreeDepth (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i))) ≤ pushed.depth :=
        decisionTreeDepth_le_of_computes _ pushed hpushed
      _ = T.depth := depth_pushEmbedding e (by simp) T
      _ = decisionTreeDepth f := hdepth
  · obtain ⟨T, hT, hdepth⟩ :=
      exists_computingTree_depth_eq_decisionTreeDepth
        (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i)))
    let pulled : DecisionTree m α := T.pullEmbedding e (by simp)
    have hpulled : pulled.Computes f := by
      rw [computes_iff]
      intro x
      calc
        pulled.eval x = T.eval (Function.extend e x 0) := eval_pullEmbedding e (by simp) T x
        _ = f (fun i ↦ Function.extend e x 0 (e i)) := congrFun hT _
        _ = f x := by simp [e.injective.extend_apply]
    calc
      decisionTreeDepth f ≤ pulled.depth := decisionTreeDepth_le_of_computes f pulled hpulled
      _ ≤ T.depth := depth_pullEmbedding_le e (by simp) T
      _ = decisionTreeDepth (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i))) := hdepth

/-- Minimum decision-tree depth is invariant under an equivalence of coordinates. -/
theorem decisionTreeDepth_comp_equiv (e : Fin m ≃ Fin n) (f : 𝔽₂^[m] → α) :
    decisionTreeDepth (fun x : 𝔽₂^[n] ↦ f (fun i ↦ x (e i))) = decisionTreeDepth f :=
  decisionTreeDepth_comp_embedding e.toEmbedding f

end F₂DecisionTree

/-! ## Coordinate-equivariant switching events -/

/-- Rename the coordinates of a Boolean function along an equivalence. -/
def reindexBooleanFunction (e : Fin m ≃ Fin n) (f : BooleanFunction m) : BooleanFunction n :=
  fun x ↦ f (fun i ↦ x (e i))

@[simp] theorem reindexBooleanFunction_apply (e : Fin m ≃ Fin n) (f : BooleanFunction m)
    (x : {−1,1}^[n]) : reindexBooleanFunction e f x = f (fun i ↦ x (e i)) := rfl

theorem CoordRestriction.restrict_reindexBooleanFunction (e : Fin m ≃ Fin n)
    (f : BooleanFunction m) (ρ : Fin n → CoordRestriction) :
    CoordRestriction.restrict (reindexBooleanFunction e f) ρ =
      fun x : 𝔽₂^[n] ↦
        CoordRestriction.restrict f (fun i ↦ ρ (e i)) (fun i ↦ x (e i)) := rfl

/-- Renaming coordinates preserves the decision-tree depth of every coordinate restriction. -/
theorem restrictedDecisionTreeDepth_reindexBooleanFunction (e : Fin m ≃ Fin n)
    (f : BooleanFunction m) (ρ : Fin n → CoordRestriction) :
    F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict (reindexBooleanFunction e f) ρ) =
      F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict f (fun i ↦ ρ (e i))) := by
  rw [CoordRestriction.restrict_reindexBooleanFunction]
  exact F₂DecisionTree.decisionTreeDepth_comp_equiv e
    (CoordRestriction.restrict f (fun i ↦ ρ (e i)))

theorem coordSwitchingFailureIndicator_reindexBooleanFunction (e : Fin m ≃ Fin n)
    (f : BooleanFunction m) (k : ℕ) (ρ : Fin n → CoordRestriction) :
    coordSwitchingFailureIndicator (reindexBooleanFunction e f) k ρ =
      coordSwitchingFailureIndicator f k (fun i ↦ ρ (e i)) := by
  unfold coordSwitchingFailureIndicator
  rw [restrictedDecisionTreeDepth_reindexBooleanFunction]

theorem restrictionAssignmentWeightAt_reindex (e : Fin m ≃ Fin n) (δ : ℝ)
    (ρ : Fin n → CoordRestriction) :
    restrictionAssignmentWeightAt δ (fun i ↦ ρ (e i)) =
      restrictionAssignmentWeightAt δ ρ := by
  unfold restrictionAssignmentWeightAt
  simpa using e.prod_comp (fun j ↦ coordRestrictionWeightAt δ (ρ j))

/-- The coordinate-product switching probability is invariant under a coordinate equivalence. -/
theorem coordSwitchingFailureProbability_reindexBooleanFunction (e : Fin m ≃ Fin n)
    (f : BooleanFunction m) (δ : ℝ) (k : ℕ) :
    coordSwitchingFailureProbability (reindexBooleanFunction e f) δ k =
      coordSwitchingFailureProbability f δ k := by
  classical
  unfold coordSwitchingFailureProbability
  let pull := Equiv.arrowCongr e.symm (Equiv.refl CoordRestriction)
  apply Fintype.sum_equiv pull
  intro ρ
  change restrictionAssignmentWeightAt δ ρ *
      coordSwitchingFailureIndicator (reindexBooleanFunction e f) k ρ =
    restrictionAssignmentWeightAt δ (fun i ↦ ρ (e i)) *
      coordSwitchingFailureIndicator f k (fun i ↦ ρ (e i))
  rw [coordSwitchingFailureIndicator_reindexBooleanFunction,
    restrictionAssignmentWeightAt_reindex]

/-- Switching-failure probability is invariant under an equivalence of coordinates. -/
theorem switchingFailureProbability_reindexBooleanFunction (e : Fin m ≃ Fin n)
    (f : BooleanFunction m) (δ : ℝ) (k : ℕ) :
    switchingFailureProbability (reindexBooleanFunction e f) δ k =
      switchingFailureProbability f δ k := by
  calc
    switchingFailureProbability (reindexBooleanFunction e f) δ k =
        coordSwitchingFailureProbability (reindexBooleanFunction e f) δ k :=
      (coordSwitchingFailureProbability_eq _ _ _).symm
    _ = coordSwitchingFailureProbability f δ k :=
      coordSwitchingFailureProbability_reindexBooleanFunction e f δ k
    _ = switchingFailureProbability f δ k := coordSwitchingFailureProbability_eq _ _ _

/-! ## Canonical finite-coordinate restriction -/

/-- The canonical embedding of the enumerated free coordinates back into the ambient cube. -/
noncomputable def freeCoordinateEmbedding (J : Finset (Fin n)) : Fin J.card ↪ Fin n :=
  J.equivFin.symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem freeCoordinateEmbedding_equivFin (J : Finset (Fin n)) (i : J) :
    freeCoordinateEmbedding J (J.equivFin i) = i := by
  simp [freeCoordinateEmbedding]

/-- Restrict to `J` and enumerate its coordinates canonically by `Fin J.card`. -/
noncomputable def reindexedSignRestriction (f : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) : BooleanFunction J.card :=
  fun x ↦ signRestriction f J z (fun i ↦ x (J.equivFin i))

@[simp] theorem reindexedSignRestriction_apply (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) (x : {−1,1}^[J.card]) :
    reindexedSignRestriction f J z x =
      f (combineSignCube J (fun i ↦ x (J.equivFin i)) z) := rfl

theorem restrictedBinaryFunction_eq_comp_reindexedSignRestriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictedBinaryFunction f J z = fun x : 𝔽₂^[n] ↦
      reindexedSignRestriction f J z
        (binaryCubeSignEquiv J.card (fun i ↦ x (freeCoordinateEmbedding J i))) := by
  funext x
  apply congrArg f
  funext i
  simp [freeCoordinateEmbedding]

/-- The ambient and canonically reindexed presentations of a restriction have the same
decision-tree depth. -/
theorem restrictedDecisionTreeDepth_eq_reindexedSignRestriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictedDecisionTreeDepth f J z =
      F₂DecisionTree.decisionTreeDepth
        (fun x ↦ reindexedSignRestriction f J z (binaryCubeSignEquiv J.card x)) := by
  rw [restrictedDecisionTreeDepth, restrictedBinaryFunction_eq_comp_reindexedSignRestriction]
  exact F₂DecisionTree.decisionTreeDepth_comp_embedding (freeCoordinateEmbedding J)
    (fun x ↦ reindexedSignRestriction f J z (binaryCubeSignEquiv J.card x))

/-! ## Product kernels for coordinate restrictions -/

/-- Apply a second coordinate restriction only when the first restriction left the coordinate
free. -/
def CoordRestriction.compose : CoordRestriction → CoordRestriction → CoordRestriction
  | .free, second => second
  | .fixOne, _ => .fixOne
  | .fixNegOne, _ => .fixNegOne

/-- Coordinatewise composition of two restrictions. -/
def composeCoordRestrictions (first second : Fin n → CoordRestriction) :
    Fin n → CoordRestriction :=
  fun i ↦ CoordRestriction.compose (first i) (second i)

/-- Product weight of coordinate restrictions over an arbitrary finite coordinate type. -/
noncomputable def coordRestrictionProductWeight {ι : Type*} [Fintype ι]
    (δ : ℝ) (ρ : ι → CoordRestriction) : ℝ :=
  ∏ i, coordRestrictionWeightAt δ (ρ i)

@[simp] theorem coordRestrictionProductWeight_fin (δ : ℝ)
    (ρ : Fin n → CoordRestriction) :
    coordRestrictionProductWeight δ ρ = restrictionAssignmentWeightAt δ ρ := rfl

theorem sum_coordRestrictionProductWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (δ : ℝ) :
    ∑ ρ : ι → CoordRestriction, coordRestrictionProductWeight δ ρ = 1 := by
  classical
  have hproduct := Fintype.prod_sum
    (f := fun (_ : ι) (c : CoordRestriction) ↦ coordRestrictionWeightAt δ c)
  simpa [coordRestrictionProductWeight, sum_coordRestrictionWeightAt] using hproduct.symm

theorem coordRestrictionProductWeight_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (δ : ℝ) (ρ : ι → CoordRestriction) :
    coordRestrictionProductWeight δ (fun j ↦ ρ (e.symm j)) =
      coordRestrictionProductWeight δ ρ := by
  unfold coordRestrictionProductWeight
  simpa using (e.prod_comp fun j ↦ coordRestrictionWeightAt δ (ρ (e.symm j))).symm

theorem coordRestrictionProductWeight_split (δ : ℝ) (J : Finset (Fin n))
    (free : J → CoordRestriction) (fixed : FixedIndex J → CoordRestriction) :
    coordRestrictionProductWeight δ
        ((Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ i ∈ J)
          (fun _ ↦ CoordRestriction)).symm (free, fixed)) =
      coordRestrictionProductWeight δ free * coordRestrictionProductWeight δ fixed := by
  classical
  let splitCoordinates := Equiv.sumCompl (fun i : Fin n ↦ i ∈ J)
  unfold coordRestrictionProductWeight
  calc
    ∏ i : Fin n, coordRestrictionWeightAt δ
        ((Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ i ∈ J)
          (fun _ ↦ CoordRestriction)).symm (free, fixed) i) =
        ∏ i : J ⊕ FixedIndex J, coordRestrictionWeightAt δ
          ((Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ i ∈ J)
            (fun _ ↦ CoordRestriction)).symm (free, fixed) (splitCoordinates i)) :=
      (splitCoordinates.prod_comp _).symm
    _ = (∏ i : J, coordRestrictionWeightAt δ (free i)) *
        ∏ i : FixedIndex J, coordRestrictionWeightAt δ (fixed i) := by
      rw [Fintype.prod_sum_type]
      congr 1 <;> apply Fintype.prod_congr <;> intro i <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

/-- Marginalizing a product restriction over coordinates outside `J` leaves the product
restriction on `J`. -/
theorem sum_coordRestrictionProductWeight_restrict (δ : ℝ) (J : Finset (Fin n))
    (g : (J → CoordRestriction) → ℝ) :
    (∑ ρ : Fin n → CoordRestriction,
      restrictionAssignmentWeightAt δ ρ * g (fun i ↦ ρ i)) =
      ∑ free : J → CoordRestriction, coordRestrictionProductWeight δ free * g free := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ i ∈ J)
    (fun _ ↦ CoordRestriction)
  calc
    ∑ ρ : Fin n → CoordRestriction,
        restrictionAssignmentWeightAt δ ρ * g (fun i ↦ ρ i) =
        ∑ p : (J → CoordRestriction) × (FixedIndex J → CoordRestriction),
          coordRestrictionProductWeight δ (split.symm p) * g p.1 := by
      apply Fintype.sum_equiv split
      intro ρ
      change restrictionAssignmentWeightAt δ ρ * g (fun i ↦ ρ i) =
        coordRestrictionProductWeight δ (split.symm (split ρ)) * g (split ρ).1
      rw [split.symm_apply_apply]
      rfl
    _ = ∑ free : J → CoordRestriction,
        ∑ fixed : FixedIndex J → CoordRestriction,
          (coordRestrictionProductWeight δ free * coordRestrictionProductWeight δ fixed) *
            g free := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro free
      apply Fintype.sum_congr
      intro fixed
      rw [coordRestrictionProductWeight_split]
    _ = ∑ free : J → CoordRestriction,
        coordRestrictionProductWeight δ free * g free := by
      apply Fintype.sum_congr
      intro free
      calc
        ∑ fixed : FixedIndex J → CoordRestriction,
            (coordRestrictionProductWeight δ free * coordRestrictionProductWeight δ fixed) *
              g free =
            (coordRestrictionProductWeight δ free * g free) *
              ∑ fixed : FixedIndex J → CoordRestriction,
                coordRestrictionProductWeight δ fixed := by
          rw [Finset.mul_sum]
          apply Fintype.sum_congr
          intro fixed
          ring
        _ = coordRestrictionProductWeight δ free * g free := by
          rw [sum_coordRestrictionProductWeight, mul_one]

/-- The same marginal law after canonically enumerating `J` by `Fin J.card`. -/
theorem sum_restrictionAssignmentWeightAt_comp_freeCoordinateEmbedding
    (δ : ℝ) (J : Finset (Fin n)) (g : (Fin J.card → CoordRestriction) → ℝ) :
    (∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ ρ *
      g (fun i ↦ ρ (freeCoordinateEmbedding J i))) =
      ∑ τ : Fin J.card → CoordRestriction, restrictionAssignmentWeightAt δ τ * g τ := by
  classical
  let enumerate := Equiv.arrowCongr J.equivFin (Equiv.refl CoordRestriction)
  calc
    ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ ρ *
        g (fun i ↦ ρ (freeCoordinateEmbedding J i)) =
        ∑ free : J → CoordRestriction,
          coordRestrictionProductWeight δ free * g (enumerate free) := by
      simpa [enumerate, freeCoordinateEmbedding] using
        sum_coordRestrictionProductWeight_restrict δ J (fun free ↦ g (enumerate free))
    _ = ∑ τ : Fin J.card → CoordRestriction,
        restrictionAssignmentWeightAt δ τ * g τ := by
      apply Fintype.sum_equiv enumerate
      intro free
      rw [← coordRestrictionProductWeight_fin]
      congr 1
      exact (coordRestrictionProductWeight_reindex J.equivFin δ free).symm

/-- A two-stage restriction records both local stages before composing them. -/
def twoStageCoordRestriction (stages : Fin n → CoordRestriction × CoordRestriction) :
    Fin n → CoordRestriction :=
  fun i ↦ CoordRestriction.compose (stages i).1 (stages i).2

/-- Product weight of all local choices in a two-stage restriction. -/
noncomputable def twoStageCoordRestrictionWeight (δ₁ δ₂ : ℝ)
    (stages : Fin n → CoordRestriction × CoordRestriction) : ℝ :=
  ∏ i, coordRestrictionWeightAt δ₁ (stages i).1 *
    coordRestrictionWeightAt δ₂ (stages i).2

theorem sum_twoStageCoordRestrictionWeight_localFiber (δ₁ δ₂ : ℝ)
    (target : CoordRestriction) :
    (∑ stages : CoordRestriction × CoordRestriction with
      CoordRestriction.compose stages.1 stages.2 = target,
        coordRestrictionWeightAt δ₁ stages.1 * coordRestrictionWeightAt δ₂ stages.2) =
      coordRestrictionWeightAt (δ₁ * δ₂) target := by
  classical
  have hstates : (Finset.univ : Finset CoordRestriction) =
      insert .free (insert .fixOne {.fixNegOne}) := by
    ext state
    cases state <;> simp
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  cases target <;> simp [hstates, CoordRestriction.compose, coordRestrictionWeightAt] <;> ring

theorem sum_twoStageCoordRestrictionWeight_fiber (δ₁ δ₂ : ℝ)
    (target : Fin n → CoordRestriction) :
    (∑ stages : {stages : Fin n → CoordRestriction × CoordRestriction //
        twoStageCoordRestriction stages = target},
      twoStageCoordRestrictionWeight δ₁ δ₂ stages.1) =
      restrictionAssignmentWeightAt (δ₁ * δ₂) target := by
  classical
  let allowed (i : Fin n) := (Finset.univ : Finset (CoordRestriction × CoordRestriction)).filter
    fun stages ↦ CoordRestriction.compose stages.1 stages.2 = target i
  have hfiber : (Finset.univ : Finset (Fin n → CoordRestriction × CoordRestriction)).filter
      (fun stages ↦ twoStageCoordRestriction stages = target) = Fintype.piFinset allowed := by
    ext stages
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, allowed,
      twoStageCoordRestriction, funext_iff]
  calc
    ∑ stages : {stages : Fin n → CoordRestriction × CoordRestriction //
        twoStageCoordRestriction stages = target},
        twoStageCoordRestrictionWeight δ₁ δ₂ stages.1 =
        ∑ stages : Fin n → CoordRestriction × CoordRestriction with
          twoStageCoordRestriction stages = target,
            twoStageCoordRestrictionWeight δ₁ δ₂ stages := by
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin n → CoordRestriction × CoordRestriction)))
        (p := fun stages ↦ twoStageCoordRestriction stages = target)
        (twoStageCoordRestrictionWeight δ₁ δ₂))
    _ = ∑ stages ∈ Fintype.piFinset allowed,
        ∏ i, coordRestrictionWeightAt δ₁ (stages i).1 *
          coordRestrictionWeightAt δ₂ (stages i).2 := by
      rw [hfiber]
      rfl
    _ = ∏ i, ∑ stages ∈ allowed i,
        coordRestrictionWeightAt δ₁ stages.1 * coordRestrictionWeightAt δ₂ stages.2 :=
      (Finset.prod_univ_sum allowed fun i stages ↦
        coordRestrictionWeightAt δ₁ stages.1 * coordRestrictionWeightAt δ₂ stages.2).symm
    _ = ∏ i, coordRestrictionWeightAt (δ₁ * δ₂) (target i) := by
      apply Fintype.prod_congr
      intro i
      exact sum_twoStageCoordRestrictionWeight_localFiber δ₁ δ₂ (target i)
    _ = restrictionAssignmentWeightAt (δ₁ * δ₂) target := rfl

/-- Independent coordinate restrictions compose by multiplying their free-coordinate
probabilities. -/
theorem sum_restrictionAssignmentWeightAt_compose (δ₁ δ₂ : ℝ)
    (g : (Fin n → CoordRestriction) → ℝ) :
    (∑ first : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ₁ first *
      ∑ second : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ₂ second *
        g (composeCoordRestrictions first second)) =
      ∑ target : Fin n → CoordRestriction,
        restrictionAssignmentWeightAt (δ₁ * δ₂) target * g target := by
  classical
  let pairStages := Equiv.arrowProdEquivProdArrow (Fin n)
    (fun _ ↦ CoordRestriction) (fun _ ↦ CoordRestriction)
  calc
    ∑ first : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ₁ first *
        ∑ second : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ₂ second *
          g (composeCoordRestrictions first second) =
        ∑ pair : (Fin n → CoordRestriction) × (Fin n → CoordRestriction),
          restrictionAssignmentWeightAt δ₁ pair.1 * restrictionAssignmentWeightAt δ₂ pair.2 *
            g (composeCoordRestrictions pair.1 pair.2) := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro first
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro second
      ring
    _ = ∑ stages : Fin n → CoordRestriction × CoordRestriction,
        twoStageCoordRestrictionWeight δ₁ δ₂ stages *
          g (twoStageCoordRestriction stages) := by
      apply Fintype.sum_equiv pairStages.symm
      intro pair
      simp only [pairStages]
      unfold twoStageCoordRestrictionWeight twoStageCoordRestriction composeCoordRestrictions
      unfold restrictionAssignmentWeightAt
      simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
      rw [Finset.prod_mul_distrib]
    _ = ∑ target : Fin n → CoordRestriction,
        (∑ stages : {stages : Fin n → CoordRestriction × CoordRestriction //
          twoStageCoordRestriction stages = target},
            twoStageCoordRestrictionWeight δ₁ δ₂ stages.1) * g target := by
      rw [← Fintype.sum_fiberwise twoStageCoordRestriction]
      apply Fintype.sum_congr
      intro target
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro stages
      rw [stages.property]
    _ = ∑ target : Fin n → CoordRestriction,
        restrictionAssignmentWeightAt (δ₁ * δ₂) target * g target := by
      apply Fintype.sum_congr
      intro target
      rw [sum_twoStageCoordRestrictionWeight_fiber]

/-! ## Restriction composition and the switching observable -/

theorem complete_compose_coordRestrictionOf (J : Finset (Fin n)) (z : FixedSignCube J)
    (second : Fin n → CoordRestriction) (x : 𝔽₂^[n]) :
    CoordRestriction.complete
        (composeCoordRestrictions (coordRestrictionOf J z) second) x =
      combineSignCube J
        (fun j : J ↦ CoordRestriction.complete
          (fun q ↦ second (freeCoordinateEmbedding J q))
          (fun q ↦ x (freeCoordinateEmbedding J q)) (J.equivFin j)) z := by
  funext i
  by_cases hi : i ∈ J
  · rw [combineSignCube_apply_free J _ z ⟨i, hi⟩]
    cases hsecond : second i <;>
      simp [composeCoordRestrictions, CoordRestriction.compose, CoordRestriction.complete,
        coordRestrictionOf, hi, hsecond]
  · rw [combineSignCube_apply_fixed J _ z ⟨i, hi⟩]
    rcases Int.units_eq_one_or (z ⟨i, hi⟩) with hz | hz <;>
      simp [composeCoordRestrictions, CoordRestriction.compose, CoordRestriction.complete,
        coordRestrictionOf, hi, hz]

theorem restrict_compose_coordRestrictionOf (f : BooleanFunction n)
    (J : Finset (Fin n)) (z : FixedSignCube J) (second : Fin n → CoordRestriction) :
    CoordRestriction.restrict f (composeCoordRestrictions (coordRestrictionOf J z) second) =
      fun x : 𝔽₂^[n] ↦ CoordRestriction.restrict (reindexedSignRestriction f J z)
        (fun q ↦ second (freeCoordinateEmbedding J q))
        (fun q ↦ x (freeCoordinateEmbedding J q)) := by
  funext x
  simp only [CoordRestriction.restrict, reindexedSignRestriction_apply]
  rw [complete_compose_coordRestrictionOf]

theorem decisionTreeDepth_restrict_compose_coordRestrictionOf
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J)
    (second : Fin n → CoordRestriction) :
    F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict f (composeCoordRestrictions (coordRestrictionOf J z) second)) =
      F₂DecisionTree.decisionTreeDepth
        (CoordRestriction.restrict (reindexedSignRestriction f J z)
          (fun q ↦ second (freeCoordinateEmbedding J q))) := by
  rw [restrict_compose_coordRestrictionOf]
  exact F₂DecisionTree.decisionTreeDepth_comp_embedding (freeCoordinateEmbedding J)
    (CoordRestriction.restrict (reindexedSignRestriction f J z)
      (fun q ↦ second (freeCoordinateEmbedding J q)))

theorem coordSwitchingFailureIndicator_compose_coordRestrictionOf
    (f : BooleanFunction n) (k : ℕ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (second : Fin n → CoordRestriction) :
    coordSwitchingFailureIndicator f k
        (composeCoordRestrictions (coordRestrictionOf J z) second) =
      coordSwitchingFailureIndicator (reindexedSignRestriction f J z) k
        (fun q ↦ second (freeCoordinateEmbedding J q)) := by
  unfold coordSwitchingFailureIndicator
  rw [decisionTreeDepth_restrict_compose_coordRestrictionOf]

/-- A second random restriction of a canonically reindexed restriction is the corresponding
conditional second stage in the ambient coordinate model. -/
theorem switchingFailureProbability_reindexedSignRestriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J)
    (δ : ℝ) (k : ℕ) :
    switchingFailureProbability (reindexedSignRestriction f J z) δ k =
      ∑ second : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ second *
        coordSwitchingFailureIndicator f k
          (composeCoordRestrictions (coordRestrictionOf J z) second) := by
  rw [← coordSwitchingFailureProbability_eq]
  unfold coordSwitchingFailureProbability
  rw [← sum_restrictionAssignmentWeightAt_comp_freeCoordinateEmbedding δ J
    (fun second ↦ coordSwitchingFailureIndicator (reindexedSignRestriction f J z) k second)]
  apply Fintype.sum_congr
  intro second
  rw [coordSwitchingFailureIndicator_compose_coordRestrictionOf]

/-- The random-restriction atom canonically associated to a coordinate assignment. -/
noncomputable def restrictionAtomOfAssignment (ρ : Fin n → CoordRestriction) :
    RandomRestrictionAtom n :=
  randomRestrictionAtomEquiv.symm ρ

@[simp] theorem coordRestrictionOf_restrictionAtomOfAssignment
    (ρ : Fin n → CoordRestriction) :
    coordRestrictionOf (restrictionAtomOfAssignment ρ).1
      (restrictionAtomOfAssignment ρ).2 = ρ := by
  exact randomRestrictionAtomEquiv.apply_symm_apply ρ

/-- Rewrite an expectation over `(J | z)` as the equivalent independent-coordinate sum. -/
theorem expectRandomRestriction_eq_sum_assignment (δ : ℝ)
    (g : (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    expectRandomRestriction n δ g =
      ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeightAt δ ρ *
        g (restrictionAtomOfAssignment ρ).1 (restrictionAtomOfAssignment ρ).2 := by
  classical
  unfold expectRandomRestriction
  simp_rw [Fintype.expect_eq_sum_div_card]
  have hdistribute :
      ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          ((∑ z : FixedSignCube J, g J z) / Fintype.card (FixedSignCube J)) =
        ∑ J : Finset (Fin n), ∑ z : FixedSignCube J,
          deltaRandomSubsetWeight n δ J / Fintype.card (FixedSignCube J) * g J z := by
    apply Fintype.sum_congr
    intro J
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum]
    ring
  rw [hdistribute]
  let atomTerm : RandomRestrictionAtom n → ℝ := fun R ↦
    deltaRandomSubsetWeight n δ R.1 / Fintype.card (FixedSignCube R.1) * g R.1 R.2
  change (∑ J, ∑ z, atomTerm ⟨J, z⟩) = _
  rw [← Fintype.sum_sigma]
  apply Fintype.sum_equiv randomRestrictionAtomEquiv
  rintro ⟨J, z⟩
  simp only [restrictionAtomOfAssignment]
  rw [randomRestrictionAtomEquiv.symm_apply_apply]
  simp only [atomTerm, randomRestrictionAtomEquiv, Equiv.ofBijective_apply]
  rw [restrictionAssignmentWeightAt_coordRestrictionOf_eq_div]

/-- Algebraic two-stage composition law for switching-failure weights. The probabilistic
corollary below records the interval hypotheses used in the book. -/
theorem switchingFailureProbability_mul_algebraic (f : BooleanFunction n)
    (δ₁ δ₂ : ℝ) (k : ℕ) :
    switchingFailureProbability f (δ₁ * δ₂) k =
      expectRandomRestriction n δ₁ (fun J z ↦
        switchingFailureProbability (reindexedSignRestriction f J z) δ₂ k) := by
  rw [← coordSwitchingFailureProbability_eq]
  unfold coordSwitchingFailureProbability
  rw [← sum_restrictionAssignmentWeightAt_compose δ₁ δ₂
    (coordSwitchingFailureIndicator f k)]
  rw [expectRandomRestriction_eq_sum_assignment]
  apply Fintype.sum_congr
  intro first
  rw [switchingFailureProbability_reindexedSignRestriction,
    coordRestrictionOf_restrictionAtomOfAssignment]

/-- Two independent random restrictions with free-coordinate probabilities `δ₁` and `δ₂`
compose to a random restriction with free-coordinate probability `δ₁ * δ₂`. -/
theorem switchingFailureProbability_mul (f : BooleanFunction n)
    {δ₁ δ₂ : ℝ} (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1)
    (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1) (k : ℕ) :
    switchingFailureProbability f (δ₁ * δ₂) k =
      expectRandomRestriction n δ₁ (fun J z ↦
        switchingFailureProbability (reindexedSignRestriction f J z) δ₂ k) := by
  have _hproduct0 : 0 ≤ δ₁ * δ₂ := mul_nonneg hδ₁0 hδ₂0
  have _hproduct1 : δ₁ * δ₂ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ₁1) hδ₂0]
  exact switchingFailureProbability_mul_algebraic f δ₁ δ₂ k


end FABL
