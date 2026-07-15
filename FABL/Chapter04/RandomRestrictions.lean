/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5 and Gemini 3.1 Pro
-/
module

public import FABL.Chapter03.Restrictions
public import FABL.Chapter04.DNFFormulas

/-!
# Random restrictions

Book items: Definition 4.15, Definition 4.16, Proposition 4.17, Corollary 4.18,
Lemma 4.19, and Theorem 4.20.

Formalization of Section 4.3 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Definition 4.15 -/

/-- Probability weight of a free set under a `δ`-random subset model. -/
noncomputable def deltaRandomSubsetWeight (n : ℕ) (δ : ℝ) (J : Finset (Fin n)) : ℝ :=
  δ ^ J.card * (1 - δ) ^ (n - J.card)

theorem deltaRandomSubsetWeight_nonneg (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (J : Finset (Fin n)) : 0 ≤ deltaRandomSubsetWeight n δ J :=
  mul_nonneg (pow_nonneg hδ0 _) (pow_nonneg (sub_nonneg.mpr hδ1) _)

/-- The `δ`-random subset weights form a probability distribution. -/
theorem sum_deltaRandomSubsetWeight (n : ℕ) (δ : ℝ) :
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J = 1 := by
  classical
  calc
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J =
        ∑ J ∈ (univ : Finset (Fin n)).powerset,
          (∏ i ∈ J, δ) * ∏ i ∈ univ \ J, (1 - δ) := by
      refine Finset.sum_congr ?_ ?_
      · ext J; simp
      · intro J _
        dsimp [deltaRandomSubsetWeight]
        rw [prod_const, prod_const]
        have hcard : ((univ : Finset (Fin n)) \ J).card = n - J.card := by
          rw [card_sdiff_of_subset (subset_univ J), card_univ, Fintype.card_fin]
        rw [← hcard]
    _ = ∏ i ∈ univ, (δ + (1 - δ)) :=
      (prod_add (fun _ : Fin n ↦ δ) (fun _ : Fin n ↦ 1 - δ) univ).symm
    _ = 1 := by simp

/-- Expectation under a `δ`-random free set. -/
noncomputable def expectDeltaRandomSubset (n : ℕ) (δ : ℝ) (g : Finset (Fin n) → ℝ) : ℝ :=
  ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J * g J

/-- O'Donnell, Definition 4.15: expectation over a `δ`-random restriction `(J | z)`. -/
noncomputable def expectRandomRestriction (n : ℕ) (δ : ℝ)
    (g : (J : Finset (Fin n)) → FixedSignCube J → ℝ) : ℝ :=
  ∑ J : Finset (Fin n),
    deltaRandomSubsetWeight n δ J * (𝔼 z : FixedSignCube J, g J z)

/-! ## Definition 4.16 -/

/-- O'Donnell, Definition 4.16: restricted function extended to the full cube. -/
def extendedSignRestriction {α : Type*} (f : {−1,1}^[n] → α)
    (J : Finset (Fin n)) (z : FixedSignCube J) : {−1,1}^[n] → α :=
  fun x ↦ f (combineSignCube J (fun i : J ↦ x (i : Fin n)) z)

@[simp] theorem extendedSignRestriction_apply {α : Type*} (f : {−1,1}^[n] → α)
    (J : Finset (Fin n)) (z : FixedSignCube J) (x : {−1,1}^[n]) :
    extendedSignRestriction f J z x =
      f (combineSignCube J (fun i : J ↦ x (i : Fin n)) z) := rfl

theorem extendedSignRestriction_setCoordinate_of_not_mem {α : Type*}
    (f : {−1,1}^[n] → α) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin n) (hi : i ∉ J) (x : {−1,1}^[n]) (b : Sign) :
    extendedSignRestriction f J z (setCoordinate x i b) =
      extendedSignRestriction f J z x := by
  dsimp [extendedSignRestriction]
  congr 1
  funext k
  by_cases hk : k ∈ J
  · have hne : k ≠ i := fun h ↦ hi (h ▸ hk)
    have h1 := combineSignCube_apply_free J
      (fun j : J ↦ setCoordinate x i b (j : Fin n)) z ⟨k, hk⟩
    have h2 := combineSignCube_apply_free J
      (fun j : J ↦ x (j : Fin n)) z ⟨k, hk⟩
    dsimp at h1 h2
    rw [h1, h2, setCoordinate, Function.update_of_ne hne]
  · have h1 := combineSignCube_apply_fixed J
      (fun j : J ↦ setCoordinate x i b (j : Fin n)) z ⟨k, hk⟩
    have h2 := combineSignCube_apply_fixed J
      (fun j : J ↦ x (j : Fin n)) z ⟨k, hk⟩
    dsimp at h1 h2
    rw [h1, h2]

theorem discreteDerivative_extendedSignRestriction_of_not_mem
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin n) (hi : i ∉ J) (x : {−1,1}^[n]) :
    discreteDerivative i (extendedSignRestriction f J z) x = 0 := by
  change (extendedSignRestriction f J z (setCoordinate x i 1) -
      extendedSignRestriction f J z (setCoordinate x i (-1))) / 2 = 0
  rw [extendedSignRestriction_setCoordinate_of_not_mem f J z i hi,
    extendedSignRestriction_setCoordinate_of_not_mem f J z i hi]
  ring

theorem influence_extendedSignRestriction_of_not_mem
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin n) (hi : i ∉ J) :
    influence (extendedSignRestriction f J z) i = 0 := by
  simp only [influence]
  simp [discreteDerivative_extendedSignRestriction_of_not_mem f J z i hi]

/-! ## Coordinate-wise restriction model (for Lemma 4.19) -/

/-- Local restriction state of one coordinate. -/
inductive CoordRestriction
  | free
  | fixOne
  | fixNegOne
  deriving DecidableEq, Fintype, Repr

noncomputable def coordRestrictionWeight : CoordRestriction → ℝ
  | .free => (1 : ℝ) / 2
  | .fixOne => (1 : ℝ) / 4
  | .fixNegOne => (1 : ℝ) / 4

theorem sum_coordRestrictionWeight :
    ∑ c : CoordRestriction, coordRestrictionWeight c = 1 := by
  have hset : (Finset.univ : Finset CoordRestriction) =
      insert .free (insert .fixOne {CoordRestriction.fixNegOne}) := by
    ext c; cases c <;> simp
  rw [hset, Finset.sum_insert (by decide : CoordRestriction.free ∉ insert .fixOne {.fixNegOne}),
    Finset.sum_insert (by decide : CoordRestriction.fixOne ∉ ({.fixNegOne} : Finset _)),
    Finset.sum_singleton]
  simp only [coordRestrictionWeight]
  norm_num

theorem coordRestrictionWeight_nonneg (c : CoordRestriction) :
    0 ≤ coordRestrictionWeight c := by
  cases c <;> (simp only [coordRestrictionWeight]; norm_num)

noncomputable def restrictionAssignmentWeight (ρ : Fin n → CoordRestriction) : ℝ :=
  ∏ i, coordRestrictionWeight (ρ i)

theorem restrictionAssignmentWeight_nonneg (ρ : Fin n → CoordRestriction) :
    0 ≤ restrictionAssignmentWeight ρ :=
  Finset.prod_nonneg fun i _ ↦ coordRestrictionWeight_nonneg (ρ i)

theorem sum_restrictionAssignmentWeight :
    ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ = 1 := by
  classical
  have hprod :=
    Fintype.prod_sum (f := fun (_ : Fin n) (c : CoordRestriction) ↦
      coordRestrictionWeight c)
  simpa [restrictionAssignmentWeight, sum_coordRestrictionWeight] using hprod.symm

def Literal.isFalsified (ℓ : Literal n) (ρ : Fin n → CoordRestriction) : Bool :=
  match ρ ℓ.index with
  | .free => false
  | .fixOne => decide (ℓ.required ≠ (1 : Sign))
  | .fixNegOne => decide (ℓ.required ≠ (-1 : Sign))

noncomputable def DNFTerm.restrictedWidthOf (T : DNFTerm n) (ρ : Fin n → CoordRestriction) : ℕ :=
  if T.literals.any fun ℓ ↦ ℓ.isFalsified ρ then 0
  else (T.literals.filter fun ℓ ↦ decide (ρ ℓ.index = .free)).length

theorem DNFTerm.restrictedWidthOf_le_width (T : DNFTerm n) (ρ : Fin n → CoordRestriction) :
    T.restrictedWidthOf ρ ≤ T.width := by
  dsimp [restrictedWidthOf, width]
  split_ifs
  · exact Nat.zero_le _
  · exact List.length_filter_le _ _

/-- Indicator that no literal of a term is falsified. -/
def DNFTerm.notFalsified (T : DNFTerm n) (ρ : Fin n → CoordRestriction) : Bool :=
  !(T.literals.any fun ℓ ↦ ℓ.isFalsified ρ)

theorem DNFTerm.notFalsified_iff (T : DNFTerm n) (ρ : Fin n → CoordRestriction) :
    T.notFalsified ρ = true ↔ ∀ ℓ ∈ T.literals, ℓ.isFalsified ρ = false := by
  simp [notFalsified, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem DNFTerm.restrictedWidthOf_ge_implies_notFalsified
    (T : DNFTerm n) (ρ : Fin n → CoordRestriction) {w : ℕ}
    (h : w ≤ T.restrictedWidthOf ρ) (hw : 0 < w) : T.notFalsified ρ = true := by
  dsimp [restrictedWidthOf] at h
  split_ifs at h with hf
  · omega
  · simp [notFalsified, hf]

/-! ## Proposition 4.17 -/

/-- O'Donnell, Proposition 4.17 (empty-set first moment). -/
theorem expect_fourierCoeff_empty_randomRestriction (f : {−1,1}^[n] → ℝ) (δ : ℝ) :
    expectRandomRestriction n δ (fun J z ↦
      restrictionFourierCoeff f J (∅ : Finset J) z) =
      fourierCoeff f ∅ := by
  classical
  simp only [expectRandomRestriction]
  have hpoint (J : Finset (Fin n)) :
      (𝔼 z : FixedSignCube J, restrictionFourierCoeff f J (∅ : Finset J) z) =
        fourierCoeff f ∅ := by
    have := expect_restrictionFourierCoeff f J (∅ : Finset J)
    simpa [liftFreeFrequency, Finset.map_empty] using this
  simp_rw [hpoint]
  calc
    ∑ J, deltaRandomSubsetWeight n δ J * fourierCoeff f ∅ =
        fourierCoeff f ∅ * ∑ J, deltaRandomSubsetWeight n δ J := by
      simp [mul_comm, Finset.mul_sum]
    _ = fourierCoeff f ∅ * 1 := by rw [sum_deltaRandomSubsetWeight]
    _ = fourierCoeff f ∅ := by ring




/-- Weight of free sets containing a fixed set `S` equals `δ ^ |S|`. -/
theorem sum_deltaRandomSubsetWeight_supset (n : ℕ) (δ : ℝ) (S : Finset (Fin n)) :
    ∑ J : Finset (Fin n),
      (if S ⊆ J then deltaRandomSubsetWeight n δ J else 0) = δ ^ S.card := by
  classical
  let rest := (univ : Finset (Fin n)) \ S
  have hfilter :
      (∑ J : Finset (Fin n), (if S ⊆ J then deltaRandomSubsetWeight n δ J else 0)) =
        ∑ J ∈ Finset.univ.filter (S ⊆ ·), deltaRandomSubsetWeight n δ J := by
    simp only [Finset.sum_filter]
  rw [hfilter]
  calc
    ∑ J ∈ Finset.univ.filter (S ⊆ ·), deltaRandomSubsetWeight n δ J =
        ∑ K ∈ rest.powerset, deltaRandomSubsetWeight n δ (S ∪ K) := by
      refine Finset.sum_bij (fun J _ ↦ J \ S)
        (fun J _ ↦ by
          rw [Finset.mem_powerset, Finset.subset_sdiff]
          exact ⟨(Finset.sdiff_subset).trans (subset_univ J), disjoint_sdiff.symm⟩)
        (fun J₁ hJ₁ J₂ hJ₂ hEq ↦ by
          have hS1 : S ⊆ J₁ := (Finset.mem_filter.mp hJ₁).2
          have hS2 : S ⊆ J₂ := (Finset.mem_filter.mp hJ₂).2
          change J₁ \ S = J₂ \ S at hEq
          rw [← Finset.union_sdiff_of_subset hS1, ← Finset.union_sdiff_of_subset hS2, hEq])
        (fun K hK ↦ by
          refine ⟨S ∪ K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩, ?_⟩
          rw [Finset.mem_powerset, Finset.subset_sdiff] at hK
          exact Finset.union_sdiff_cancel_left hK.2.symm)
        (fun J hJ ↦ by
          have hS : S ⊆ J := (Finset.mem_filter.mp hJ).2
          rw [Finset.union_sdiff_of_subset hS])
    _ = ∑ K ∈ rest.powerset,
          δ ^ (S.card + K.card) * (1 - δ) ^ (rest.card - K.card) := by
      refine Finset.sum_congr rfl ?_
      intro K hK
      have hKsub : K ⊆ rest := Finset.mem_powerset.mp hK
      have hdisj : Disjoint S K := by
        rw [Finset.disjoint_left]
        intro i hiS hiK
        exact (Finset.mem_sdiff.mp (hKsub hiK)).2 hiS
      have hcard : (S ∪ K).card = S.card + K.card := by
        rw [Finset.card_union_of_disjoint hdisj]
      have hrest : rest.card = n - S.card := by
        simp only [rest]
        rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
      have hKle : K.card ≤ rest.card := Finset.card_le_card hKsub
      have hdiff : n - (S.card + K.card) = rest.card - K.card := by
        rw [hrest]; omega
      dsimp [deltaRandomSubsetWeight]
      rw [hcard, hdiff]
    _ = δ ^ S.card *
          ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) := by
      have hform (K : Finset (Fin n)) :
          δ ^ (S.card + K.card) * (1 - δ) ^ (rest.card - K.card) =
            δ ^ S.card * (δ ^ K.card * (1 - δ) ^ (rest.card - K.card)) := by
        rw [pow_add]; ring
      simp_rw [hform]
      exact (Finset.mul_sum _ _ (δ ^ S.card)).symm
    _ = δ ^ S.card * 1 := by
      have hbin :
          ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) = 1 := by
        calc
          ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) =
              ∑ K ∈ rest.powerset, (∏ j ∈ K, δ) * ∏ j ∈ rest \ K, (1 - δ) := by
            refine Finset.sum_congr rfl ?_
            intro K hK
            have hKsub : K ⊆ rest := Finset.mem_powerset.mp hK
            rw [prod_const, prod_const, card_sdiff_of_subset hKsub]
          _ = ∏ j ∈ rest, (δ + (1 - δ)) :=
            (prod_add (fun _ : Fin n ↦ δ) (fun _ : Fin n ↦ 1 - δ) rest).symm
          _ = 1 := by simp
      rw [hbin]
    _ = δ ^ S.card := by ring

/-- Free-cube Fourier coefficient of a restriction, zero unless `S ⊆ J`.

This is the book’s first-moment input for Proposition 4.17 under the convention that
frequencies outside the free set do not contribute.
-/
noncomputable def ambientRestrictionFourierCoeff (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset (Fin n)) (z : FixedSignCube J) : ℝ :=
  if S ⊆ J then
    restrictionFourierCoeff f J (freeFrequencyPart J S) z
  else
    0

theorem ambientRestrictionFourierCoeff_eq (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset (Fin n)) (z : FixedSignCube J) :
    ambientRestrictionFourierCoeff f J S z =
      if S ⊆ J then restrictionFourierCoeff f J (freeFrequencyPart J S) z else 0 := by
  unfold ambientRestrictionFourierCoeff
  split_ifs <;> rfl

/-- Conditional first moment: free-set Fourier recovers ambient when `S ⊆ J`. -/
theorem expect_ambientRestrictionFourierCoeff (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset (Fin n)) :
    (𝔼 z : FixedSignCube J, ambientRestrictionFourierCoeff f J S z) =
      (if S ⊆ J then (1 : ℝ) else 0) * fourierCoeff f S := by
  classical
  simp only [ambientRestrictionFourierCoeff]
  split_ifs with hS
  · have h := expect_restrictionFourierCoeff f J (freeFrequencyPart J S)
    have hlift : liftFreeFrequency (freeFrequencyPart J S) = S := by
      ext i
      simp only [liftFreeFrequency, Finset.mem_map, Function.Embedding.coe_subtype,
        freeFrequencyPart, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj
      · intro hi
        exact ⟨⟨i, hS hi⟩, hi, rfl⟩
    -- E_z restrictionFourier = ̂f(lift free) = ̂f(S)
    calc
      (𝔼 z, restrictionFourierCoeff f J (freeFrequencyPart J S) z) =
          fourierCoeff f (liftFreeFrequency (freeFrequencyPart J S)) := h
      _ = fourierCoeff f S := by rw [hlift]
      _ = (1 : ℝ) * fourierCoeff f S := by ring
  · simp

/-- O'Donnell, Proposition 4.17 (general first moment).

`E[̂f_{J|z}(S)] = δ^{|S|} ̂f(S)`, with frequencies outside the free set treated as zero.
-/
theorem expect_fourierCoeff_randomRestriction
    (f : {−1,1}^[n] → ℝ) (δ : ℝ) (S : Finset (Fin n)) :
    expectRandomRestriction n δ (fun J z ↦
      ambientRestrictionFourierCoeff f J S z) =
      δ ^ S.card * fourierCoeff f S := by
  classical
  simp only [expectRandomRestriction]
  simp_rw [expect_ambientRestrictionFourierCoeff]
  have hterm (J : Finset (Fin n)) :
      deltaRandomSubsetWeight n δ J *
          ((if S ⊆ J then (1 : ℝ) else 0) * fourierCoeff f S) =
        (if S ⊆ J then deltaRandomSubsetWeight n δ J else 0) *
          fourierCoeff f S := by
    split_ifs <;> ring
  simp_rw [hterm]
  -- ∑_J (1[S⊆J] w_δ(J)) * ̂f(S) = δ^{|S|} ̂f(S)
  have hsum :
      ∑ J : Finset (Fin n),
          (if S ⊆ J then deltaRandomSubsetWeight n δ J else 0) * fourierCoeff f S =
        (∑ J : Finset (Fin n),
          if S ⊆ J then deltaRandomSubsetWeight n δ J else 0) *
          fourierCoeff f S :=
    (Finset.sum_mul (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun J : Finset (Fin n) ↦
        if S ⊆ J then deltaRandomSubsetWeight n δ J else (0 : ℝ))
      (a := fourierCoeff f S)).symm
  rw [hsum, sum_deltaRandomSubsetWeight_supset, mul_comm]


/-! ### Proposition 4.17 second moment -/

/-- Lift of the free part of `S` recovers `S` when `S ⊆ J`. -/
theorem liftFreeFrequency_freeFrequencyPart_of_subset
    {J S : Finset (Fin n)} (hS : S ⊆ J) :
    liftFreeFrequency (freeFrequencyPart J S) = S := by
  ext i
  simp only [liftFreeFrequency, Finset.mem_map, Function.Embedding.coe_subtype,
    freeFrequencyPart, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i, hS hi⟩, hi, rfl⟩

/-- Conditional second moment via Corollary 3.22. -/
theorem expect_sq_ambientRestrictionFourierCoeff (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset (Fin n)) :
    (𝔼 z : FixedSignCube J, ambientRestrictionFourierCoeff f J S z ^ 2) =
      if S ⊆ J then
        ∑ T : Finset (FixedIndex J),
          fourierCoeff f
            (liftFreeFrequency (freeFrequencyPart J S) ∪ liftFixedFrequency T) ^ 2
      else
        0 := by
  classical
  simp only [ambientRestrictionFourierCoeff]
  split_ifs with _hS
  · simpa using expect_sq_restrictionFourierCoeff f J (freeFrequencyPart J S)
  · simp

theorem subset_of_inter_eq {S U J : Finset (Fin n)} (h : U ∩ J = S) : S ⊆ J := by
  intro x hx
  have : x ∈ U ∩ J := by rw [h]; exact hx
  exact (Finset.mem_inter.mp this).2

theorem subset_of_inter_eq_left {S U J : Finset (Fin n)} (h : U ∩ J = S) : S ⊆ U := by
  intro x hx
  have : x ∈ U ∩ J := by rw [h]; exact hx
  exact (Finset.mem_inter.mp this).1

/-- Weight of free sets with fixed intersection `U ∩ J = S`. -/
theorem sum_deltaRandomSubsetWeight_inter_eq
    (n : ℕ) (δ : ℝ) (S U : Finset (Fin n)) :
    ∑ J : Finset (Fin n),
      (if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0) =
      if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0 := by
  classical
  by_cases hSU : S ⊆ U
  · rw [if_pos hSU]
    let B := U \ S
    let R := (univ : Finset (Fin n)) \ U
    have hS_disj_B : Disjoint S B := by simp only [B]; exact Finset.disjoint_sdiff
    have hS_disj_R : Disjoint S R := by
      simp only [R]; rw [Finset.disjoint_left]
      intro i hiS hiR
      exact (Finset.mem_sdiff.mp hiR).2 (hSU hiS)
    have hB_disj_R : Disjoint B R := by
      simp only [B, R]; rw [Finset.disjoint_left]
      intro i hiB hiR
      exact (Finset.mem_sdiff.mp hiR).2 (Finset.mem_sdiff.mp hiB).1
    have hcover : S ∪ B ∪ R = univ := by
      simp only [B, R]
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      by_cases hiU : i ∈ U
      · by_cases hiS : i ∈ S <;> simp [hiU, hiS]
      · simp [hiU]
    have hfilter :
        (∑ J : Finset (Fin n),
            (if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0)) =
          ∑ J ∈ Finset.univ.filter (fun J ↦ U ∩ J = S),
            deltaRandomSubsetWeight n δ J := by
      simp only [Finset.sum_filter]
    rw [hfilter]
    calc
      ∑ J ∈ Finset.univ.filter (fun J ↦ U ∩ J = S), deltaRandomSubsetWeight n δ J =
          ∑ L ∈ R.powerset, deltaRandomSubsetWeight n δ (S ∪ L) := by
        refine Finset.sum_bij (fun J _ ↦ J \ S)
          (fun J hJ ↦ by
            have hJS : U ∩ J = S := (Finset.mem_filter.mp hJ).2
            rw [Finset.mem_powerset, Finset.subset_sdiff]
            refine ⟨(Finset.sdiff_subset).trans (subset_univ J), ?_⟩
            rw [Finset.disjoint_left]
            intro x hxJ hxU
            have : x ∈ S := hJS ▸ Finset.mem_inter.mpr ⟨hxU, (Finset.mem_sdiff.mp hxJ).1⟩
            exact (Finset.mem_sdiff.mp hxJ).2 this)
          (fun J₁ hJ₁ J₂ hJ₂ hEq ↦ by
            have h1 : U ∩ J₁ = S := (Finset.mem_filter.mp hJ₁).2
            have h2 : U ∩ J₂ = S := (Finset.mem_filter.mp hJ₂).2
            have hS1 : S ⊆ J₁ := subset_of_inter_eq h1
            have hS2 : S ⊆ J₂ := subset_of_inter_eq h2
            change J₁ \ S = J₂ \ S at hEq
            rw [← Finset.union_sdiff_of_subset hS1, ← Finset.union_sdiff_of_subset hS2, hEq])
          (fun L hL ↦ by
            rw [Finset.mem_powerset, Finset.subset_sdiff] at hL
            refine ⟨S ∪ L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hSU]
              have hUL : Disjoint U L := hL.2.symm
              rw [Finset.disjoint_iff_inter_eq_empty.mp hUL, Finset.union_empty]
            · exact Finset.union_sdiff_cancel_left (Disjoint.symm (Disjoint.mono_right hSU hL.2)))
          (fun J hJ ↦ by
            have hSsub : S ⊆ J := subset_of_inter_eq (Finset.mem_filter.mp hJ).2
            rw [Finset.union_sdiff_of_subset hSsub])
      _ = δ ^ S.card * (1 - δ) ^ B.card := by
        calc
          ∑ L ∈ R.powerset, deltaRandomSubsetWeight n δ (S ∪ L) =
              ∑ L ∈ R.powerset,
                δ ^ (S.card + L.card) *
                  (1 - δ) ^ (B.card + (R.card - L.card)) := by
            refine Finset.sum_congr rfl ?_
            intro L hL
            have hLsub : L ⊆ R := Finset.mem_powerset.mp hL
            have hdisjSL : Disjoint S L := by
              rw [Finset.disjoint_left]
              intro i hiS hiL
              exact (Finset.mem_sdiff.mp (hLsub hiL)).2 (hSU hiS)
            have hcard : (S ∪ L).card = S.card + L.card :=
              Finset.card_union_of_disjoint hdisjSL
            have hn : n = S.card + B.card + R.card := by
              have h1 : (S ∪ B ∪ R).card = n := by
                rw [hcover, card_univ, Fintype.card_fin]
              have hSBR : Disjoint (S ∪ B) R := by
                rw [Finset.disjoint_union_left]
                exact ⟨hS_disj_R, hB_disj_R⟩
              rw [Finset.card_union_of_disjoint hSBR,
                Finset.card_union_of_disjoint hS_disj_B] at h1
              simpa [add_assoc] using h1.symm
            have hdiff : n - (S.card + L.card) = B.card + (R.card - L.card) := by
              have hLle : L.card ≤ R.card := Finset.card_le_card hLsub
              have hn' : n = S.card + B.card + R.card := hn
              omega
            dsimp [deltaRandomSubsetWeight]
            rw [hcard, hdiff]
          _ = ∑ L ∈ R.powerset,
                (δ ^ S.card * (1 - δ) ^ B.card) *
                  (δ ^ L.card * (1 - δ) ^ (R.card - L.card)) := by
            refine Finset.sum_congr rfl ?_
            intro L _
            rw [pow_add, pow_add]; ring
          _ = (δ ^ S.card * (1 - δ) ^ B.card) *
                ∑ L ∈ R.powerset, δ ^ L.card * (1 - δ) ^ (R.card - L.card) := by
            exact (Finset.mul_sum _ _ (δ ^ S.card * (1 - δ) ^ B.card)).symm
          _ = δ ^ S.card * (1 - δ) ^ B.card := by
            have hbin :
                ∑ L ∈ R.powerset, δ ^ L.card * (1 - δ) ^ (R.card - L.card) = 1 := by
              calc
                ∑ L ∈ R.powerset, δ ^ L.card * (1 - δ) ^ (R.card - L.card) =
                    ∑ L ∈ R.powerset, (∏ j ∈ L, δ) * ∏ j ∈ R \ L, (1 - δ) := by
                  refine Finset.sum_congr rfl ?_
                  intro L hL
                  have hLsub : L ⊆ R := Finset.mem_powerset.mp hL
                  rw [prod_const, prod_const, card_sdiff_of_subset hLsub]
                _ = ∏ j ∈ R, (δ + (1 - δ)) :=
                  (prod_add (fun _ : Fin n ↦ δ) (fun _ : Fin n ↦ 1 - δ) R).symm
                _ = 1 := by simp
            rw [hbin]; ring
      _ = δ ^ S.card * (1 - δ) ^ (U \ S).card := by rfl
  · rw [if_neg hSU]
    have himp (J : Finset (Fin n)) : U ∩ J ≠ S := fun h ↦
      hSU (subset_of_inter_eq_left h)
    simp [himp]

/-- Ambient frequencies with free/fixed split relative to `J` matching free set `S`. -/
theorem sum_sq_fourier_of_inter_eq (f : {−1,1}^[n] → ℝ)
    (J : Finset (Fin n)) (S : Finset (Fin n)) (hS : S ⊆ J) :
    ∑ T : Finset (FixedIndex J),
        fourierCoeff f
          (liftFreeFrequency (freeFrequencyPart J S) ∪ liftFixedFrequency T) ^ 2 =
      ∑ U : Finset (Fin n),
        (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) := by
  classical
  have hliftS : liftFreeFrequency (freeFrequencyPart J S) = S :=
    liftFreeFrequency_freeFrequencyPart_of_subset hS
  simp_rw [hliftS]
  -- Left sum is over T of ̂f(S ∪ lift T)^2
  have hright :
      ∑ U : Finset (Fin n), (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) =
        ∑ U ∈ Finset.univ.filter (fun U ↦ U ∩ J = S), fourierCoeff f U ^ 2 := by
    simp only [Finset.sum_filter]
  rw [hright]
  let e : Finset (FixedIndex J) → Finset (Fin n) := fun T ↦ S ∪ liftFixedFrequency T
  have he_inter (T : Finset (FixedIndex J)) : e T ∩ J = S := by
    ext i
    constructor
    · intro hi
      have hiJ : i ∈ J := (Finset.mem_inter.mp hi).2
      have hiSL : i ∈ S ∪ liftFixedFrequency T := (Finset.mem_inter.mp hi).1
      rcases Finset.mem_union.mp hiSL with hiS | hiT
      · exact hiS
      · obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hiT
        exact absurd hiJ t.property
    · intro hiS
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hiS, hS hiS⟩
  have hinj {T₁ T₂ : Finset (FixedIndex J)} (h : e T₁ = e T₂) : T₁ = T₂ := by
    have d1 : Disjoint S (liftFixedFrequency T₁) := by
      rw [Finset.disjoint_left]
      intro i hiS hiT
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hiT
      exact t.property (hS hiS)
    have d2 : Disjoint S (liftFixedFrequency T₂) := by
      rw [Finset.disjoint_left]
      intro i hiS hiT
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hiT
      exact t.property (hS hiS)
    have hlift : liftFixedFrequency T₁ = liftFixedFrequency T₂ := by
      have h1 : liftFixedFrequency T₁ = e T₁ \ S :=
        (Finset.union_sdiff_cancel_left d1).symm
      have h2 : liftFixedFrequency T₂ = e T₂ \ S :=
        (Finset.union_sdiff_cancel_left d2).symm
      rw [h1, h2, h]
    ext t
    have ht_mem (T : Finset (FixedIndex J)) :
        t ∈ T ↔ (t : Fin n) ∈ liftFixedFrequency T := by
      simp only [liftFixedFrequency, Finset.mem_map, Function.Embedding.coe_subtype]
      constructor
      · intro ht; exact ⟨t, ht, rfl⟩
      · rintro ⟨t', ht', hval⟩
        have : t' = t := Subtype.ext hval
        rwa [← this]
    constructor
    · intro ht
      exact (ht_mem T₂).2 (hlift ▸ (ht_mem T₁).1 ht)
    · intro ht
      exact (ht_mem T₁).2 (hlift.symm ▸ (ht_mem T₂).1 ht)
  refine Finset.sum_bij (fun T _ ↦ e T)
    (fun T _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_inter T⟩)
    (fun T₁ _ T₂ _ h ↦ hinj h)
    (fun U hU ↦ by
      have hJS : U ∩ J = S := (Finset.mem_filter.mp hU).2
      refine ⟨fixedFrequencyPart J U, Finset.mem_univ _, ?_⟩
      have hfree : freeFrequencyPart J U = freeFrequencyPart J S := by
        ext i
        simp only [mem_freeFrequencyPart]
        constructor
        · intro hiU
          have : (i : Fin n) ∈ U ∩ J := Finset.mem_inter.mpr ⟨hiU, i.property⟩
          rwa [hJS] at this
        · intro hiS
          have : (i : Fin n) ∈ U ∩ J := by rw [hJS]; exact hiS
          exact (Finset.mem_inter.mp this).1
      calc
        e (fixedFrequencyPart J U) = S ∪ liftFixedFrequency (fixedFrequencyPart J U) := rfl
        _ = liftFreeFrequency (freeFrequencyPart J S) ∪
              liftFixedFrequency (fixedFrequencyPart J U) := by rw [hliftS]
        _ = liftFreeFrequency (freeFrequencyPart J U) ∪
              liftFixedFrequency (fixedFrequencyPart J U) := by rw [hfree]
        _ = U := liftFreeFrequencyPart_union_liftFixedFrequencyPart J U)
    (fun T _ ↦ rfl)

/-- O'Donnell, Proposition 4.17 (second moment). -/
theorem expect_sq_fourierCoeff_randomRestriction
    (f : {−1,1}^[n] → ℝ) (δ : ℝ) (S : Finset (Fin n)) :
    expectRandomRestriction n δ (fun J z ↦
      ambientRestrictionFourierCoeff f J S z ^ 2) =
      ∑ U : Finset (Fin n),
        (if S ⊆ U then
          δ ^ S.card * (1 - δ) ^ (U \ S).card
        else 0) * fourierCoeff f U ^ 2 := by
  classical
  simp only [expectRandomRestriction]
  have hpoint (J : Finset (Fin n)) :
      (𝔼 z : FixedSignCube J, ambientRestrictionFourierCoeff f J S z ^ 2) =
        ∑ U : Finset (Fin n),
          (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) := by
    rw [expect_sq_ambientRestrictionFourierCoeff]
    split_ifs with hS
    · exact sum_sq_fourier_of_inter_eq f J S hS
    · have himp (U : Finset (Fin n)) : U ∩ J ≠ S := fun h ↦
        hS (subset_of_inter_eq h)
      simp [himp]
  simp_rw [hpoint]
  -- Expand double sum and swap order.
  have hswap :
      ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          ∑ U : Finset (Fin n),
            (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) =
        ∑ U : Finset (Fin n),
          ∑ J : Finset (Fin n),
            deltaRandomSubsetWeight n δ J *
              (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl ?_
  intro U _
  have hfactor :
      ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J *
            (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) =
        (∑ J : Finset (Fin n),
          (if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0)) *
          fourierCoeff f U ^ 2 := by
    have hterm (J : Finset (Fin n)) :
        deltaRandomSubsetWeight n δ J *
            (if U ∩ J = S then fourierCoeff f U ^ 2 else 0) =
          (if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0) *
            fourierCoeff f U ^ 2 := by
      split_ifs <;> ring
    simp_rw [hterm]
    exact (Finset.sum_mul (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun J : Finset (Fin n) ↦
        if U ∩ J = S then deltaRandomSubsetWeight n δ J else (0 : ℝ))
      (a := fourierCoeff f U ^ 2)).symm
  rw [hfactor, sum_deltaRandomSubsetWeight_inter_eq]

/-! ## Corollary 4.18 (Fourier-free, Exercise 4.9 style) -/

/-- Weight of free sets containing a fixed coordinate equals `δ`. -/
theorem sum_deltaRandomSubsetWeight_mem (n : ℕ) (δ : ℝ) (i : Fin n) :
    ∑ J : Finset (Fin n),
      (if i ∈ J then deltaRandomSubsetWeight n δ J else 0) = δ := by
  classical
  let rest := (univ : Finset (Fin n)).erase i
  have hfilter :
      (∑ J : Finset (Fin n), (if i ∈ J then deltaRandomSubsetWeight n δ J else 0)) =
        ∑ J ∈ Finset.univ.filter (i ∈ ·), deltaRandomSubsetWeight n δ J := by
    simp only [Finset.sum_filter]
  rw [hfilter]
  calc
    ∑ J ∈ Finset.univ.filter (i ∈ ·), deltaRandomSubsetWeight n δ J =
        ∑ K ∈ rest.powerset, deltaRandomSubsetWeight n δ (insert i K) := by
      refine Finset.sum_bij (fun J _ ↦ J.erase i)
        (fun J hJ ↦ by
          refine Finset.mem_powerset.mpr ?_
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          exact Finset.mem_erase.mpr ⟨hx'.1, Finset.mem_univ _⟩)
        (fun J₁ hJ₁ J₂ hJ₂ hEq ↦ by
          have hi1 : i ∈ J₁ := (Finset.mem_filter.mp hJ₁).2
          have hi2 : i ∈ J₂ := (Finset.mem_filter.mp hJ₂).2
          -- hEq : J₁.erase i = J₂.erase i
          change J₁.erase i = J₂.erase i at hEq
          ext x
          by_cases hx : x = i
          · subst x; simp [hi1, hi2]
          · constructor
            · intro hx1
              have hx1' : x ∈ J₁.erase i := Finset.mem_erase.mpr ⟨hx, hx1⟩
              have hx2' : x ∈ J₂.erase i := hEq ▸ hx1'
              exact (Finset.mem_erase.mp hx2').2
            · intro hx2
              have hx2' : x ∈ J₂.erase i := Finset.mem_erase.mpr ⟨hx, hx2⟩
              have hx1' : x ∈ J₁.erase i := hEq.symm ▸ hx2'
              exact (Finset.mem_erase.mp hx1').2)
        (fun K hK ↦ by
          refine ⟨insert i K, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self i K⟩
          · have hiK : i ∉ K := by
              have hKsub : K ⊆ rest := Finset.mem_powerset.mp hK
              intro hi
              exact (Finset.mem_erase.mp (hKsub hi)).1 rfl
            exact Finset.erase_insert hiK)
        (fun J hJ ↦ by
          have hi : i ∈ J := (Finset.mem_filter.mp hJ).2
          have hEq : J = insert i (J.erase i) := (Finset.insert_erase hi).symm
          convert congrArg (deltaRandomSubsetWeight n δ) hEq using 1)
    _ = ∑ K ∈ rest.powerset,
          δ ^ (K.card + 1) * (1 - δ) ^ (rest.card - K.card) := by
      refine Finset.sum_congr rfl ?_
      intro K hK
      have hKsub : K ⊆ rest := Finset.mem_powerset.mp hK
      have hiK : i ∉ K := by
        intro hi
        exact (Finset.mem_erase.mp (hKsub hi)).1 rfl
      have hcard : (insert i K).card = K.card + 1 := by
        rw [Finset.card_insert_of_notMem hiK, add_comm]
      have hdiff : n - (insert i K).card = rest.card - K.card := by
        have hrest : rest.card = n - 1 := by
          simp only [rest]
          rw [card_erase_of_mem (Finset.mem_univ i), card_univ, Fintype.card_fin]
        have hKle : K.card ≤ rest.card := Finset.card_le_card hKsub
        rw [hcard, hrest]
        omega
      -- deltaRandomSubsetWeight uses n - card, convert via hcard and hdiff
      dsimp [deltaRandomSubsetWeight]
      have hdiff' : n - (K.card + 1) = rest.card - K.card := by
        rwa [← hcard]
      rw [hcard, hdiff']
    _ = δ * ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) := by
      have hform (K : Finset (Fin n)) :
          δ ^ (K.card + 1) * (1 - δ) ^ (rest.card - K.card) =
            δ * (δ ^ K.card * (1 - δ) ^ (rest.card - K.card)) := by
        rw [pow_succ']; ring
      simp_rw [hform]
      exact (Finset.mul_sum _ _ δ).symm
    _ = δ * 1 := by
      have hbin :
          ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) = 1 := by
        calc
          ∑ K ∈ rest.powerset, δ ^ K.card * (1 - δ) ^ (rest.card - K.card) =
              ∑ K ∈ rest.powerset, (∏ j ∈ K, δ) * ∏ j ∈ rest \ K, (1 - δ) := by
            refine Finset.sum_congr rfl ?_
            intro K hK
            have hKsub : K ⊆ rest := Finset.mem_powerset.mp hK
            rw [prod_const, prod_const, card_sdiff_of_subset hKsub]
          _ = ∏ j ∈ rest, (δ + (1 - δ)) :=
            (prod_add (fun _ : Fin n ↦ δ) (fun _ : Fin n ↦ 1 - δ) rest).symm
          _ = 1 := by simp
      rw [hbin]
    _ = δ := by ring

/-- Free-coordinate discrete derivative of an extension equals that of `f`. -/
theorem discreteDerivative_extendedSignRestriction_of_mem
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (i : Fin n) (hi : i ∈ J) (x : {−1,1}^[n]) :
    discreteDerivative i (extendedSignRestriction f J z) x =
      discreteDerivative i f
        (combineSignCube J (fun j : J ↦ x (j : Fin n)) z) := by
  classical
  -- Unfold discrete derivatives
  change
    (f (combineSignCube J (fun j : J ↦ setCoordinate x i 1 (j : Fin n)) z) -
      f (combineSignCube J (fun j : J ↦ setCoordinate x i (-1) (j : Fin n)) z)) / 2 =
    (f (setCoordinate (combineSignCube J (fun j : J ↦ x j) z) i 1) -
      f (setCoordinate (combineSignCube J (fun j : J ↦ x j) z) i (-1))) / 2
  -- Key: updating a free coordinate in the free assignment is setCoordinate on the combine
  have hset (b : Sign) :
      combineSignCube J (fun j : J ↦ setCoordinate x i b (j : Fin n)) z =
        setCoordinate (combineSignCube J (fun j : J ↦ x (j : Fin n)) z) i b := by
    apply funext
    intro k
    simp only [combineSignCube, signCubeSplitEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
      setCoordinate, Function.update]
    split_ifs <;> first | rfl | (rename_i h1 h2; exact False.elim (h1 (h2 ▸ hi)))
  rw [hset 1, hset (-1)]

/-- Free assignment extracted from a full cube string. -/
def freePart (J : Finset (Fin n)) (x : {−1,1}^[n]) : FreeSignCube J :=
  fun j ↦ x (j : Fin n)

@[simp] theorem freePart_eq_split (J : Finset (Fin n)) (x : {−1,1}^[n]) :
    freePart J x = (signCubeSplitEquiv J x).1 := by
  funext j
  simp [freePart, signCubeSplitEquiv, Equiv.piEquivPiSubtypeProd_apply]

/-- Averaging a squared discrete derivative that depends only on free coordinates. -/
theorem expect_sq_discreteDerivative_combine
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (i : Fin n) (z : FixedSignCube J) :
    (𝔼 x : {−1,1}^[n],
        discreteDerivative i f (combineSignCube J (freePart J x) z) ^ 2) =
      𝔼 y : FreeSignCube J,
        discreteDerivative i f (combineSignCube J y z) ^ 2 := by
  classical
  -- Split x; the fixed half is dummy and averages to 1.
  have hsplit :
      (𝔼 x : {−1,1}^[n],
          discreteDerivative i f (combineSignCube J (freePart J x) z) ^ 2) =
        𝔼 p : FreeSignCube J × FixedSignCube J,
          discreteDerivative i f (combineSignCube J p.1 z) ^ 2 := by
    apply Fintype.expect_equiv (signCubeSplitEquiv J)
    intro x
    simp only [freePart_eq_split]
  rw [hsplit]
  -- Product average = iterated average; then drop the dummy fixed factor.
  -- Goal: E_p [D(p.1)]² = E_y [D(y)]².
  let g : FreeSignCube J → FixedSignCube J → ℝ := fun y _w ↦
    discreteDerivative i f (combineSignCube J y z) ^ 2
  -- expect_product' (with univ product): E_p g = E_y E_w g
  have hprod :
      (𝔼 p : FreeSignCube J × FixedSignCube J, g p.1 p.2) =
        𝔼 y : FreeSignCube J, 𝔼 w : FixedSignCube J, g y w := by
    simpa [Finset.univ_product_univ] using
      (Finset.expect_product' (Finset.univ : Finset (FreeSignCube J))
        (Finset.univ : Finset (FixedSignCube J)) g)
  calc
    (𝔼 p : FreeSignCube J × FixedSignCube J,
        discreteDerivative i f (combineSignCube J p.1 z) ^ 2) =
        𝔼 p : FreeSignCube J × FixedSignCube J, g p.1 p.2 := rfl
    _ = 𝔼 y : FreeSignCube J, 𝔼 w : FixedSignCube J, g y w := hprod
    _ = 𝔼 y : FreeSignCube J, discreteDerivative i f (combineSignCube J y z) ^ 2 := by
      refine Finset.expect_congr rfl ?_
      intro y _
      exact Finset.expect_const Finset.univ_nonempty _

/-- Free/fixed product measure recovers ambient influence. -/
theorem expect_sq_discreteDerivative_product
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (i : Fin n) :
    (𝔼 y : FreeSignCube J, 𝔼 z : FixedSignCube J,
        discreteDerivative i f (combineSignCube J y z) ^ 2) =
      influence f i := by
  classical
  have hprod :
      (𝔼 y : FreeSignCube J, 𝔼 z : FixedSignCube J,
          discreteDerivative i f (combineSignCube J y z) ^ 2) =
        𝔼 p : FreeSignCube J × FixedSignCube J,
          discreteDerivative i f (combineSignCube J p.1 p.2) ^ 2 := by
    simpa [Finset.univ_product_univ] using
      (Finset.expect_product' (Finset.univ : Finset (FreeSignCube J))
        (Finset.univ : Finset (FixedSignCube J))
        (fun (y : FreeSignCube J) (z : FixedSignCube J) ↦
          discreteDerivative i f (combineSignCube J y z) ^ 2)).symm
  rw [hprod]
  have hcube :
      (𝔼 p : FreeSignCube J × FixedSignCube J,
          discreteDerivative i f (combineSignCube J p.1 p.2) ^ 2) =
        𝔼 x : {−1,1}^[n], discreteDerivative i f x ^ 2 := by
    apply Fintype.expect_equiv (signCubeSplitEquiv J).symm
    intro p
    rfl
  rw [hcube]
  rfl

/-- Conditional expected influence equals original when the coordinate is free. -/
theorem expect_influence_extendedSignRestriction_of_mem
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (i : Fin n) (hi : i ∈ J) :
    (𝔼 z : FixedSignCube J, influence (extendedSignRestriction f J z) i) =
      influence f i := by
  classical
  -- Expand influence as E[(D_i)²]
  change (𝔼 z, 𝔼 x, discreteDerivative i (extendedSignRestriction f J z) x ^ 2) =
    influence f i
  -- Replace D_i ext by D_i f ∘ combine
  have hpoint (z : FixedSignCube J) :
      (𝔼 x, discreteDerivative i (extendedSignRestriction f J z) x ^ 2) =
        𝔼 y : FreeSignCube J,
          discreteDerivative i f (combineSignCube J y z) ^ 2 := by
    calc
      (𝔼 x, discreteDerivative i (extendedSignRestriction f J z) x ^ 2) =
          𝔼 x, discreteDerivative i f (combineSignCube J (freePart J x) z) ^ 2 := by
        apply Finset.expect_congr rfl
        intro x _
        rw [discreteDerivative_extendedSignRestriction_of_mem f J z i hi]
        rfl
      _ = 𝔼 y, discreteDerivative i f (combineSignCube J y z) ^ 2 :=
        expect_sq_discreteDerivative_combine f J i z
  -- Swap order: E_z E_y = E_y E_z
  have hswap :
      (𝔼 z, 𝔼 y : FreeSignCube J,
          discreteDerivative i f (combineSignCube J y z) ^ 2) =
        𝔼 y : FreeSignCube J, 𝔼 z,
          discreteDerivative i f (combineSignCube J y z) ^ 2 := by
    exact Finset.expect_comm (Finset.univ : Finset (FixedSignCube J))
      (Finset.univ : Finset (FreeSignCube J)) _
  calc
    (𝔼 z, 𝔼 x, discreteDerivative i (extendedSignRestriction f J z) x ^ 2) =
        𝔼 z, 𝔼 y : FreeSignCube J,
          discreteDerivative i f (combineSignCube J y z) ^ 2 := by
      simp_rw [hpoint]
    _ = 𝔼 y : FreeSignCube J, 𝔼 z,
          discreteDerivative i f (combineSignCube J y z) ^ 2 := hswap
    _ = influence f i := expect_sq_discreteDerivative_product f J i

/-- O'Donnell, Corollary 4.18. -/
theorem expect_influence_extended_randomRestriction
    (f : {−1,1}^[n] → ℝ) (δ : ℝ) (i : Fin n) :
    expectRandomRestriction n δ (fun J z ↦
      influence (extendedSignRestriction f J z) i) =
      δ * influence f i := by
  classical
  simp only [expectRandomRestriction]
  calc
    ∑ J, deltaRandomSubsetWeight n δ J *
        (𝔼 z, influence (extendedSignRestriction f J z) i) =
        ∑ J, deltaRandomSubsetWeight n δ J *
          (if i ∈ J then influence f i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro J _
      by_cases hi : i ∈ J
      · rw [if_pos hi, expect_influence_extendedSignRestriction_of_mem f J i hi]
      · have h0 (z : FixedSignCube J) :
            influence (extendedSignRestriction f J z) i = 0 :=
          influence_extendedSignRestriction_of_not_mem f J z i hi
        simp [hi, h0]
    _ = influence f i *
          ∑ J, (if i ∈ J then deltaRandomSubsetWeight n δ J else 0) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro J _
      split_ifs <;> ring
    _ = influence f i * δ := by rw [sum_deltaRandomSubsetWeight_mem]
    _ = δ * influence f i := by ring

/-- O'Donnell, Corollary 4.18 for total influence. -/
theorem expect_totalInfluence_extended_randomRestriction
    (f : {−1,1}^[n] → ℝ) (δ : ℝ) :
    expectRandomRestriction n δ (fun J z ↦
      totalInfluence (extendedSignRestriction f J z)) =
      δ * totalInfluence f := by
  classical
  simp only [expectRandomRestriction, totalInfluence]
  have hswap (J : Finset (Fin n)) :
      (𝔼 z, ∑ i, influence (extendedSignRestriction f J z) i) =
        ∑ i, 𝔼 z, influence (extendedSignRestriction f J z) i := by
    rw [Finset.expect_sum_comm]
  simp_rw [hswap]
  calc
    ∑ J, deltaRandomSubsetWeight n δ J *
        ∑ i, 𝔼 z, influence (extendedSignRestriction f J z) i =
        ∑ i, δ * influence f i := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [expectRandomRestriction] using
        expect_influence_extended_randomRestriction f δ i
    _ = δ * ∑ i, influence f i := by simp [Finset.mul_sum]

/-! ## Lemma 4.19 -/

/-- Local weight that a literal is not fixed to False is `3/4`. -/
theorem literal_not_falsified_local_weight (ℓ : Literal n) :
    ∑ c : CoordRestriction,
      coordRestrictionWeight c * (if ℓ.isFalsified (fun _ ↦ c) then (0 : ℝ) else 1) =
      (3 : ℝ) / 4 := by
  have hfree : Literal.isFalsified ℓ (fun _ ↦ .free) = false := by
    simp [Literal.isFalsified]
  have huniv : (Finset.univ : Finset CoordRestriction) =
      insert .free (insert .fixOne {CoordRestriction.fixNegOne}) := by
    ext c; cases c <;> simp
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rcases Int.units_eq_one_or ℓ.required with hr | hr
  · have h1 : Literal.isFalsified ℓ (fun _ ↦ .fixOne) = false := by
      simp [Literal.isFalsified, hr]
    have h2 : Literal.isFalsified ℓ (fun _ ↦ .fixNegOne) = true := by
      simp [Literal.isFalsified, hr]
    simp [coordRestrictionWeight, hfree, h1, h2]
    norm_num
  · have h1 : Literal.isFalsified ℓ (fun _ ↦ .fixOne) = true := by
      simp [Literal.isFalsified, hr]
    have h2 : Literal.isFalsified ℓ (fun _ ↦ .fixNegOne) = false := by
      simp [Literal.isFalsified, hr]
    simp [coordRestrictionWeight, hfree, h1, h2]
    norm_num

/-- Per-coordinate local factor for non-falsification of a term. -/
noncomputable def DNFTerm.localNotFalsifiedFactor (T : DNFTerm n) (i : Fin n)
    (c : CoordRestriction) : ℝ :=
  if h : i ∈ T.support then
    if (T.literalAt i h).isFalsified (fun _ ↦ c) then 0 else 1
  else
    1

theorem DNFTerm.localNotFalsifiedFactor_sum (T : DNFTerm n) (i : Fin n) :
    ∑ c : CoordRestriction,
      coordRestrictionWeight c * T.localNotFalsifiedFactor i c =
      if i ∈ T.support then (3 : ℝ) / 4 else 1 := by
  classical
  by_cases hi : i ∈ T.support
  · simp only [hi, ↓reduceIte, localNotFalsifiedFactor]
    simpa [Literal.isFalsified] using literal_not_falsified_local_weight (T.literalAt i hi)
  · simp only [hi, ↓reduceIte, localNotFalsifiedFactor]
    simp [sum_coordRestrictionWeight]

/-- Non-falsification indicator factors over coordinates via local factors. -/
theorem DNFTerm.notFalsified_indicator_eq_prod (T : DNFTerm n)
    (ρ : Fin n → CoordRestriction) :
    (if T.notFalsified ρ then (1 : ℝ) else 0) =
      ∏ i, T.localNotFalsifiedFactor i (ρ i) := by
  classical
  by_cases hok : T.notFalsified ρ = true
  · have hall : ∀ ℓ ∈ T.literals, ℓ.isFalsified ρ = false := (T.notFalsified_iff ρ).1 hok
    have hprod : ∀ i, T.localNotFalsifiedFactor i (ρ i) = 1 := by
      intro i
      by_cases hi : i ∈ T.support
      · simp only [localNotFalsifiedFactor, hi]
        have hℓ := hall (T.literalAt i hi) (T.literalAt_mem i hi)
        have : (T.literalAt i hi).isFalsified (fun _ ↦ ρ i) = false := by
          simpa [Literal.isFalsified, DNFTerm.literalAt_index] using hℓ
        simp [this]
      · simp [localNotFalsifiedFactor, hi]
    simp [hok, hprod]
  · have hany : ∃ ℓ ∈ T.literals, ℓ.isFalsified ρ = true := by
      have : T.notFalsified ρ = false := by
        cases h : T.notFalsified ρ <;> simp_all
      simpa [notFalsified, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq] using this
    obtain ⟨ℓ, hℓmem, hℓ⟩ := hany
    have hi : ℓ.index ∈ T.support := T.mem_support_of_mem_literals hℓmem
    have hlit : T.literalAt ℓ.index hi = ℓ := T.literalAt_eq hℓmem
    have hfactor0 : T.localNotFalsifiedFactor ℓ.index (ρ ℓ.index) = 0 := by
      simp only [localNotFalsifiedFactor, hi, hlit]
      have : ℓ.isFalsified (fun _ ↦ ρ ℓ.index) = true := by
        simpa [Literal.isFalsified] using hℓ
      simp [this]
    have hprod0 : (∏ i, T.localNotFalsifiedFactor i (ρ i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ℓ.index) hfactor0
    have : (if T.notFalsified ρ then (1 : ℝ) else 0) = 0 := by simp [hok]
    simp [this, hprod0]

/-- Weight that a term is not falsified equals `(3/4)^{width}`. -/
theorem term_not_falsified_weight (T : DNFTerm n) :
    ∑ ρ : Fin n → CoordRestriction,
      restrictionAssignmentWeight ρ *
        (if T.notFalsified ρ then (1 : ℝ) else 0) =
      ((3 : ℝ) / 4) ^ T.width := by
  classical
  have hrewrite :
      ∑ ρ : Fin n → CoordRestriction,
          restrictionAssignmentWeight ρ *
            (if T.notFalsified ρ then (1 : ℝ) else 0) =
        ∑ ρ : Fin n → CoordRestriction,
          ∏ i, coordRestrictionWeight (ρ i) * T.localNotFalsifiedFactor i (ρ i) := by
    refine Finset.sum_congr rfl ?_
    intro ρ _
    rw [T.notFalsified_indicator_eq_prod ρ, restrictionAssignmentWeight,
      ← Finset.prod_mul_distrib]
  rw [hrewrite]
  have hprod :=
    Fintype.prod_sum
      (f := fun (i : Fin n) (c : CoordRestriction) ↦
        coordRestrictionWeight c * T.localNotFalsifiedFactor i c)
  have hswap :
      ∑ ρ : Fin n → CoordRestriction,
          ∏ i, coordRestrictionWeight (ρ i) * T.localNotFalsifiedFactor i (ρ i) =
        ∏ i, ∑ c : CoordRestriction,
          coordRestrictionWeight c * T.localNotFalsifiedFactor i c := by
    simpa using hprod.symm
  rw [hswap]
  have hpoint (i : Fin n) :
      ∑ c : CoordRestriction,
          coordRestrictionWeight c * T.localNotFalsifiedFactor i c =
        if i ∈ T.support then (3 : ℝ) / 4 else 1 :=
    T.localNotFalsifiedFactor_sum i
  simp_rw [hpoint]
  classical
  calc
    ∏ i, (if i ∈ T.support then (3 : ℝ) / 4 else 1) =
        (∏ i ∈ T.support, (3 : ℝ) / 4) * ∏ i ∈ T.supportᶜ, (1 : ℝ) := by
      rw [← Finset.prod_mul_prod_compl (s := T.support)
        (f := fun i ↦ if i ∈ T.support then (3 : ℝ) / 4 else 1)]
      refine congrArg₂ (· * ·) ?_ ?_
      · refine Finset.prod_congr rfl ?_
        intro i hi; simp [hi]
      · refine Finset.prod_congr rfl ?_
        intro i hi
        have : i ∉ T.support := by
          simpa [Finset.mem_compl] using hi
        simp [this]
    _ = ((3 : ℝ) / 4) ^ T.support.card := by
      rw [prod_const, prod_const, one_pow, mul_one]
    _ = ((3 : ℝ) / 4) ^ T.width := by
      rw [T.card_support]

/-- O'Donnell, Lemma 4.19. -/
theorem restrictedWidth_ge_probability_le (T : DNFTerm n) (w : ℕ) :
    ∑ ρ : Fin n → CoordRestriction,
      restrictionAssignmentWeight ρ *
        (if w ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤
      ((3 : ℝ) / 4) ^ w := by
  classical
  by_cases hw : w = 0
  · subst w
    have hle :
        ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if 0 ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤
          ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ := by
      refine Finset.sum_le_sum ?_
      intro ρ _
      have hbit : (if 0 ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> norm_num
      exact mul_le_of_le_one_right (restrictionAssignmentWeight_nonneg ρ) hbit
    have hsum := sum_restrictionAssignmentWeight (n := n)
    have : ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
        (if 0 ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤ 1 := by
      convert hle using 2
      exact hsum.symm
    simpa [pow_zero] using this
  · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
    have hpoint (ρ : Fin n → CoordRestriction) :
        (if w ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤
          (if T.notFalsified ρ then (1 : ℝ) else 0) := by
      split_ifs with h1 h2
      · exact le_rfl
      · have := T.restrictedWidthOf_ge_implies_notFalsified ρ h1 hwpos
        exact absurd this (by simpa using h2)
      · exact zero_le_one
      · exact le_rfl
    have hle :
        ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if w ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤
          ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if T.notFalsified ρ then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum ?_
      intro ρ _
      exact mul_le_mul_of_nonneg_left (hpoint ρ) (restrictionAssignmentWeight_nonneg ρ)
    by_cases hTw : T.width < w
    · have hzero (ρ : Fin n → CoordRestriction) : ¬ w ≤ T.restrictedWidthOf ρ := by
        intro hle'
        have hbound := (T.restrictedWidthOf_le_width ρ).trans_lt hTw
        exact Nat.not_le_of_gt hbound hle'
      have : ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
          (if w ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro ρ _
        simp [hzero ρ]
      rw [this]
      exact pow_nonneg (by norm_num) _
    · have hge : w ≤ T.width := Nat.le_of_not_gt hTw
      have hpow : ((3 : ℝ) / 4) ^ T.width ≤ ((3 : ℝ) / 4) ^ w :=
        pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
          (by norm_num : (3 : ℝ) / 4 ≤ 1) hge
      calc
        ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
            (if w ≤ T.restrictedWidthOf ρ then (1 : ℝ) else 0) ≤
            ∑ ρ : Fin n → CoordRestriction, restrictionAssignmentWeight ρ *
              (if T.notFalsified ρ then (1 : ℝ) else 0) := hle
        _ = ((3 : ℝ) / 4) ^ T.width := term_not_falsified_weight T
        _ ≤ ((3 : ℝ) / 4) ^ w := hpow

/-! ## Logarithmic total influence of small DNF formulas -/


variable {n : ℕ}

theorem sum_inverse_two_pow_succ_Ico_le (m n : ℕ) :
    (∑ k ∈ Finset.Ico m n, ((2 : ℝ) ^ (k + 1))⁻¹) ≤ ((2 : ℝ) ^ m)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    (∑ k ∈ Finset.range (n - m), ((2 : ℝ) ^ (m + k + 1))⁻¹) =
        ((2 : ℝ) ^ m)⁻¹ * ((1 / 2 : ℝ) *
          ∑ k ∈ Finset.range (n - m), (1 / 2 : ℝ) ^ k) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show m + k + 1 = m + (k + 1) by omega, pow_add, pow_succ]
      field_simp
      rw [← mul_pow]
      norm_num
    _ ≤ ((2 : ℝ) ^ m)⁻¹ * ((1 / 2 : ℝ) * 2) := by
      gcongr
      exact sum_geometric_two_le (n - m)
    _ = ((2 : ℝ) ^ m)⁻¹ := by ring

namespace DNFFormula

/-- A canonical satisfied term, with the empty term used when the DNF evaluates to `1`. -/
noncomputable def selectedTerm (φ : DNFFormula n) (x : {−1,1}^[n]) : DNFTerm n :=
  if h : φ.eval x = -1 then Classical.choose ((φ.eval_eq_neg_one_iff x).1 h)
  else DNFTerm.empty

/-- Width of the selected satisfied term. -/
noncomputable def selectedWidth (φ : DNFFormula n) (x : {−1,1}^[n]) : ℕ :=
  (φ.selectedTerm x).width

theorem selectedTerm_mem (φ : DNFFormula n) (x : {−1,1}^[n])
    (hx : φ.eval x = -1) : φ.selectedTerm x ∈ φ.terms := by
  rw [selectedTerm, dif_pos hx]
  exact (Classical.choose_spec ((φ.eval_eq_neg_one_iff x).1 hx)).1

theorem selectedTerm_eval (φ : DNFFormula n) (x : {−1,1}^[n])
    (hx : φ.eval x = -1) : (φ.selectedTerm x).eval x = -1 := by
  rw [selectedTerm, dif_pos hx]
  exact (Classical.choose_spec ((φ.eval_eq_neg_one_iff x).1 hx)).2

theorem selectedWidth_eq_zero_of_eval_ne (φ : DNFFormula n) (x : {−1,1}^[n])
    (hx : φ.eval x ≠ -1) : φ.selectedWidth x = 0 := by
  simp [selectedWidth, selectedTerm, hx]

theorem selectedWidth_le_dimension (φ : DNFFormula n) (x : {−1,1}^[n]) :
    φ.selectedWidth x ≤ n :=
  (φ.selectedTerm x).width_le_dimension

end DNFFormula

theorem card_negOnePivotal_le_selectedWidth (φ : DNFFormula n) (x : {−1,1}^[n]) :
    (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x).card ≤
      φ.selectedWidth x := by
  classical
  by_cases hx : φ.eval x = -1
  · exact card_negOnePivotal_le_term_width φ x (φ.selectedTerm x)
      (φ.selectedTerm_mem x hx) (φ.selectedTerm_eval x hx)
  · have hempty :
        (Finset.univ.filter fun i ↦ IsNegOnePivotal φ.toBooleanFunction i x) = ∅ := by
      ext i
      simp [IsNegOnePivotal, DNFFormula.toBooleanFunction, hx]
    simp [hempty]

theorem selectedWidth_tail_probability_le (φ : DNFFormula n) (k : ℕ) (hk : 0 < k) :
    uniformProbability (fun x ↦ k ≤ φ.selectedWidth x) ≤
      (φ.size : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  classical
  let indicators := fun x : {−1,1}^[n] ↦
    φ.terms.map fun T ↦ if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0
  have hpoint (x : {−1,1}^[n]) :
      (if k ≤ φ.selectedWidth x then (1 : ℝ) else 0) ≤ (indicators x).sum := by
    by_cases hxw : k ≤ φ.selectedWidth x
    · rw [if_pos hxw]
      have hφx : φ.eval x = -1 := by
        by_contra hne
        have hzero := φ.selectedWidth_eq_zero_of_eval_ne x hne
        omega
      let T := φ.selectedTerm x
      have hTmem : T ∈ φ.terms := φ.selectedTerm_mem x hφx
      have hTeval : T.eval x = -1 := φ.selectedTerm_eval x hφx
      have hTw : k ≤ T.width := hxw
      have hmem : (if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0) ∈
          indicators x := List.mem_map_of_mem hTmem
      have hnonneg : ∀ y ∈ indicators x, 0 ≤ y := by
        intro y hy
        obtain ⟨U, _, rfl⟩ := List.mem_map.mp hy
        split_ifs <;> norm_num
      simpa [hTeval, hTw] using List.single_le_sum hnonneg _ hmem
    · rw [if_neg hxw]
      exact List.sum_nonneg fun y hy ↦ by
        obtain ⟨T, _, rfl⟩ := List.mem_map.mp hy
        split_ifs <;> norm_num
  have hexpect :
      uniformProbability (fun x ↦ k ≤ φ.selectedWidth x) ≤
        𝔼 x, (indicators x).sum :=
    Finset.expect_le_expect fun x _ ↦ hpoint x
  have hterm (T : DNFTerm n) :
      (𝔼 x, if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0) ≤
        ((2 : ℝ) ^ k)⁻¹ := by
    by_cases hTk : k ≤ T.width
    · have hprob :
          (𝔼 x, if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0) =
            ((2 : ℝ) ^ T.width)⁻¹ := by
          simpa [hTk, uniformProbability] using uniformProbability_DNFTerm_eval_neg_one T
      rw [hprob]
      exact inv_anti₀ (pow_pos (by norm_num) _)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hTk)
    · simp [hTk]
  calc
    uniformProbability (fun x ↦ k ≤ φ.selectedWidth x) ≤
        𝔼 x, (indicators x).sum := hexpect
    _ = (φ.terms.map fun T ↦
          𝔼 x, if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0).sum :=
      expect_sum_list_map φ.terms
        (fun T x ↦ if T.eval x = -1 ∧ k ≤ T.width then (1 : ℝ) else 0)
    _ ≤ (φ.terms.map fun _ : DNFTerm n ↦ ((2 : ℝ) ^ k)⁻¹).sum :=
      List.sum_le_sum fun T _ ↦ hterm T
    _ = (φ.size : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by simp [DNFFormula.size]

theorem uniformProbability_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] : uniformProbability P ≤ 1 := by
  rw [uniformProbability]
  calc
    (𝔼 x, if P x then (1 : ℝ) else 0) ≤ 𝔼 _x : Ω, (1 : ℝ) :=
      Finset.expect_le_expect fun x _ ↦ by split_ifs <;> norm_num
    _ = 1 := Fintype.expect_const 1

theorem expect_selectedWidth_eq_sum_tail (φ : DNFFormula n) :
    (𝔼 x, (φ.selectedWidth x : ℝ)) =
      ∑ k ∈ Finset.range n,
        uniformProbability (fun x ↦ k + 1 ≤ φ.selectedWidth x) := by
  classical
  have hpoint (x : {−1,1}^[n]) :
      (φ.selectedWidth x : ℝ) =
        ∑ k ∈ Finset.range n,
          (if k + 1 ≤ φ.selectedWidth x then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    have hfilter :
        (Finset.range n).filter (fun k ↦ k + 1 ≤ φ.selectedWidth x) =
          Finset.range (φ.selectedWidth x) := by
      ext k
      have hw := φ.selectedWidth_le_dimension x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter, Finset.card_range]
  calc
    (𝔼 x, (φ.selectedWidth x : ℝ)) =
        𝔼 x, ∑ k ∈ Finset.range n,
          (if k + 1 ≤ φ.selectedWidth x then (1 : ℝ) else 0) :=
      Finset.expect_congr rfl fun x _ ↦ hpoint x
    _ = ∑ k ∈ Finset.range n,
          𝔼 x, (if k + 1 ≤ φ.selectedWidth x then (1 : ℝ) else 0) := by
      rw [Finset.expect_sum_comm]
    _ = ∑ k ∈ Finset.range n,
          uniformProbability (fun x ↦ k + 1 ≤ φ.selectedWidth x) := rfl

theorem expect_selectedWidth_le_clog_add_one
    (φ : DNFFormula n) {s : ℕ} (hsize : φ.size ≤ s) :
    (𝔼 x, (φ.selectedWidth x : ℝ)) ≤ (Nat.clog 2 s : ℝ) + 1 := by
  classical
  let m := Nat.clog 2 s
  let q : ℕ → ℝ := fun k ↦
    uniformProbability (fun x ↦ k + 1 ≤ φ.selectedWidth x)
  have hq_one (k : ℕ) : q k ≤ 1 := uniformProbability_le_one _
  have hq_tail (k : ℕ) : q k ≤ (s : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
    calc
      q k ≤ (φ.size : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ :=
        selectedWidth_tail_probability_le φ (k + 1) (by omega)
      _ ≤ (s : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize)
          (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  have hs_pow : (s : ℝ) * ((2 : ℝ) ^ m)⁻¹ ≤ 1 := by
    have hnat : s ≤ 2 ^ m := Nat.le_pow_clog (by norm_num) s
    have hreal : (s : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hnat
    calc
      (s : ℝ) * ((2 : ℝ) ^ m)⁻¹ ≤
          (2 : ℝ) ^ m * ((2 : ℝ) ^ m)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  rw [expect_selectedWidth_eq_sum_tail]
  change (∑ k ∈ Finset.range n, q k) ≤ (m : ℝ) + 1
  by_cases hnm : n ≤ m
  · calc
      (∑ k ∈ Finset.range n, q k) ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ ↦ hq_one k
      _ = (n : ℝ) := by simp
      _ ≤ (m : ℝ) := by exact_mod_cast hnm
      _ ≤ (m : ℝ) + 1 := by linarith
  · have hmn : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hnm)
    rw [← Finset.sum_range_add_sum_Ico q hmn]
    have hhead : (∑ k ∈ Finset.range m, q k) ≤ (m : ℝ) := by
      calc
        (∑ k ∈ Finset.range m, q k) ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ ↦ hq_one k
        _ = (m : ℝ) := by simp
    have htail : (∑ k ∈ Finset.Ico m n, q k) ≤ 1 := by
      calc
        (∑ k ∈ Finset.Ico m n, q k) ≤
            ∑ k ∈ Finset.Ico m n, (s : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹ :=
          Finset.sum_le_sum fun k _ ↦ hq_tail k
        _ = (s : ℝ) * ∑ k ∈ Finset.Ico m n, ((2 : ℝ) ^ (k + 1))⁻¹ := by
          rw [Finset.mul_sum]
        _ ≤ (s : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
          gcongr
          exact sum_inverse_two_pow_succ_Ico_le m n
        _ ≤ 1 := hs_pow
    linarith

/-- O'Donnell, Theorem 4.20, with an explicit logarithmic bound. -/
theorem totalInfluence_le_two_mul_clog_add_one_of_hasDNFSizeLE
    {f : BooleanFunction n} {s : ℕ} (hf : HasDNFSizeLE f s) :
    totalInfluence f.toReal ≤ 2 * ((Nat.clog 2 s : ℝ) + 1) := by
  classical
  obtain ⟨φ, hsize, rfl⟩ := hf
  rw [totalInfluence_eq_two_mul_expect_card_negOnePivotal]
  have hpoint (x : {−1,1}^[n]) :
      ((Finset.univ.filter fun i ↦
          IsNegOnePivotal φ.toBooleanFunction i x).card : ℝ) ≤
        (φ.selectedWidth x : ℝ) := by
    exact_mod_cast card_negOnePivotal_le_selectedWidth φ x
  have hexpect :
      (𝔼 x, ((Finset.univ.filter fun i ↦
          IsNegOnePivotal φ.toBooleanFunction i x).card : ℝ)) ≤
        𝔼 x, (φ.selectedWidth x : ℝ) :=
    Finset.expect_le_expect fun x _ ↦ hpoint x
  have hwidth := expect_selectedWidth_le_clog_add_one φ hsize
  nlinarith


end FABL
