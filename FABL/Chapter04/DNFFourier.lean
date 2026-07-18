/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.HastadSwitching
public import FABL.Chapter03.GoldreichLevin.RestrictedWeights
public import FABL.Chapter03.LearningTheory.LowDegree

/-!
# Fourier consequences for bounded-width DNF formulas

Book items: Exercise 4.11, Lemma 4.21, Theorem 4.22, Lemma 4.23, Theorem 4.24,
and Theorem 4.25.

This module keeps the restriction/Fourier identities, switching-tail estimates, low-degree
one-norm argument, and sparse-spectrum conclusion in one proof narrative.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

/-! ## Restriction/Fourier identities and Lemma 4.23 -/


variable {n : ℕ}

/-! ## Fourier coefficients of an extended restriction -/

/-- Extending a restricted function by dummy fixed coordinates preserves every Fourier
coefficient supported on the free coordinates. -/
theorem fourierCoeff_extendedSignRestriction_liftFree
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (S : Finset J) :
    fourierCoeff (extendedSignRestriction f J z) (liftFreeFrequency S) =
      restrictionFourierCoeff f J S z := by
  classical
  change
    (𝔼 x : {−1,1}^[n],
      f (combineSignCube J (fun i : J ↦ x (i : Fin n)) z) *
        monomial (liftFreeFrequency S) x) =
      𝔼 y : FreeSignCube J,
        f (combineSignCube J y z) * indexedMonomial S y
  calc
    (𝔼 x : {−1,1}^[n],
        f (combineSignCube J (fun i : J ↦ x (i : Fin n)) z) *
          monomial (liftFreeFrequency S) x) =
        𝔼 x : {−1,1}^[n],
          f (combineSignCube J ((signCubeSplitEquiv J x).1) z) *
            indexedMonomial S ((signCubeSplitEquiv J x).1) := by
      apply Finset.expect_congr rfl
      intro x _
      have hfree : (fun i : J ↦ x (i : Fin n)) = (signCubeSplitEquiv J x).1 := by
        change freePart J x = (signCubeSplitEquiv J x).1
        exact freePart_eq_split J x
      rw [hfree]
      rw [← monomial_liftFreeFrequency_combine S
        ((signCubeSplitEquiv J x).1) ((signCubeSplitEquiv J x).2)]
      have hx : combineSignCube J ((signCubeSplitEquiv J x).1)
          ((signCubeSplitEquiv J x).2) = x :=
        (signCubeSplitEquiv J).symm_apply_apply x
      rw [hx]
    _ = 𝔼 y : FreeSignCube J,
          f (combineSignCube J y z) * indexedMonomial S y :=
      expect_freeProjection_signCubeSplitEquiv J
        (fun y ↦ f (combineSignCube J y z) * indexedMonomial S y)

/-- The ambient coefficient convention agrees with the ordinary coefficient of the extended
restricted function. -/
theorem fourierCoeff_extendedSignRestriction
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J)
    (S : Finset (Fin n)) :
    fourierCoeff (extendedSignRestriction f J z) S =
      ambientRestrictionFourierCoeff f J S z := by
  classical
  by_cases hS : S ⊆ J
  · rw [ambientRestrictionFourierCoeff, if_pos hS]
    have hlift : liftFreeFrequency (freeFrequencyPart J S) = S :=
      liftFreeFrequency_freeFrequencyPart_of_subset hS
    calc
      fourierCoeff (extendedSignRestriction f J z) S =
          fourierCoeff (extendedSignRestriction f J z)
            (liftFreeFrequency (freeFrequencyPart J S)) := by rw [hlift]
      _ = restrictionFourierCoeff f J (freeFrequencyPart J S) z :=
        fourierCoeff_extendedSignRestriction_liftFree
          f J z (freeFrequencyPart J S)
  · rw [ambientRestrictionFourierCoeff, if_neg hS]
    obtain ⟨i, hiS, hiJ⟩ : ∃ i, i ∈ S ∧ i ∉ J := by
      simpa only [Finset.not_subset] using hS
    have hinfluence : influence (extendedSignRestriction f J z) i = 0 :=
      influence_extendedSignRestriction_of_not_mem f J z i hiJ
    rw [influence_eq_sum_sq_fourierCoeff] at hinfluence
    have hsquare : fourierCoeff (extendedSignRestriction f J z) S ^ 2 = 0 := by
      have hterm :
          fourierCoeff (extendedSignRestriction f J z) S ^ 2 ≤
            ∑ T : Finset (Fin n) with i ∈ T,
              fourierCoeff (extendedSignRestriction f J z) T ^ 2 :=
        Finset.single_le_sum (fun T _ ↦ sq_nonneg _) (by simp [hiS])
      rw [hinfluence] at hterm
      exact le_antisymm hterm (sq_nonneg _)
    nlinarith

/-- Summing ambient restriction coefficients is exactly the Fourier one-norm of the extended
restriction. -/
theorem sum_abs_ambientRestrictionFourierCoeff
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    ∑ S : Finset (Fin n), |ambientRestrictionFourierCoeff f J S z| =
      fourierOneNorm (extendedSignRestriction f J z) := by
  unfold fourierOneNorm
  apply Finset.sum_congr rfl
  intro S _
  rw [fourierCoeff_extendedSignRestriction]

/-! ## Exercise 4.11 -/

/-- O'Donnell, Exercise 4.11: the Fourier one-norm of a Boolean function is at most two to
the minimum decision-tree depth. Applied here to the Boolean function induced by a restriction. -/
theorem exercise4_11_restriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    fourierOneNorm (extendedSignRestriction f.toReal J z) ≤
      ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ) := by
  obtain ⟨T, hT, hdepth⟩ :=
    F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth
      (restrictedBinaryFunction f J z)
  let R : DecisionTree n ℝ := T.mapOutputs signValue
  have hR : R.Computes
      (fun x ↦ extendedSignRestriction f.toReal J z (binaryCubeSignEquiv n x)) := by
    apply (F₂DecisionTree.computes_iff R _).2
    intro x
    rw [F₂DecisionTree.eval_mapOutputs,
      (F₂DecisionTree.computes_iff T _).1 hT]
    rfl
  rw [fourierOneNorm_eq_spectralPNorm_one]
  have hbound :=
    R.spectralPNorm_one_le_infinityNorm_mul_two_pow_depth_of_computes
      (fun x ↦ extendedSignRestriction f.toReal J z (binaryCubeSignEquiv n x)) hR
  calc
    spectralPNorm 1
        (fun x ↦ extendedSignRestriction f.toReal J z (binaryCubeSignEquiv n x)) ≤
        binaryFunctionInfinityNorm
            (fun x ↦ extendedSignRestriction f.toReal J z (binaryCubeSignEquiv n x)) *
          ((2 ^ R.depth : ℕ) : ℝ) := hbound
    _ = ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ) := by
      have hinfty :
          binaryFunctionInfinityNorm
              (fun x ↦ extendedSignRestriction f.toReal J z (binaryCubeSignEquiv n x)) = 1 := by
        unfold binaryFunctionInfinityNorm
        apply Finset.sup'_eq_of_forall
        intro x _
        change |signValue (extendedSignRestriction f J z (binaryCubeSignEquiv n x))| = 1
        rcases signValue_eq_neg_one_or_one
          (extendedSignRestriction f J z (binaryCubeSignEquiv n x)) with hvalue | hvalue
        · rw [hvalue]
          norm_num
        · rw [hvalue]
          norm_num
      rw [hinfty, one_mul]
      simp only [R, F₂DecisionTree.depth_mapOutputs]
      rw [hdepth]
      rfl

/-! ## Lemma 4.23 -/

/-- Triangle inequality for the finite random-restriction expectation. -/
theorem abs_expectRandomRestriction_le_expect_abs
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (g : (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    |expectRandomRestriction n δ g| ≤
      expectRandomRestriction n δ (fun J z ↦ |g J z|) := by
  classical
  unfold expectRandomRestriction
  calc
    |∑ J : Finset (Fin n),
        deltaRandomSubsetWeight n δ J * (𝔼 z : FixedSignCube J, g J z)| ≤
        ∑ J : Finset (Fin n),
          |deltaRandomSubsetWeight n δ J * (𝔼 z : FixedSignCube J, g J z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J * |𝔼 z : FixedSignCube J, g J z| := by
      apply Finset.sum_congr rfl
      intro J _
      rw [abs_mul, abs_of_nonneg (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)]
    _ ≤ ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J *
            (𝔼 z : FixedSignCube J, |g J z|) := by
      apply Finset.sum_le_sum
      intro J _
      exact mul_le_mul_of_nonneg_left (Finset.abs_expect_le _ _)
        (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)

/-- Finite sums commute with the random-restriction expectation. -/
theorem sum_expectRandomRestriction
    {ι : Type*} [Fintype ι]
    (δ : ℝ) (g : ι → (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    ∑ a : ι, expectRandomRestriction n δ (g a) =
      expectRandomRestriction n δ (fun J z ↦ ∑ a : ι, g a J z) := by
  classical
  unfold expectRandomRestriction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.expect_sum_comm, Finset.mul_sum]

/-- Monotonicity of random-restriction expectation for genuine probability parameters. -/
theorem expectRandomRestriction_mono
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {g h : (J : Finset (Fin n)) → FixedSignCube J → ℝ}
    (hgh : ∀ J z, g J z ≤ h J z) :
    expectRandomRestriction n δ g ≤ expectRandomRestriction n δ h := by
  classical
  unfold expectRandomRestriction
  apply Finset.sum_le_sum
  intro J _
  exact mul_le_mul_of_nonneg_left
    (Finset.expect_le_expect fun z _ ↦ hgh J z)
    (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)

/-- O'Donnell, Lemma 4.23: the weighted Fourier one-norm is bounded by the expected
`2 ^ DT-depth` of a random restriction. -/
theorem lemma4_23
    (f : BooleanFunction n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∑ S : Finset (Fin n), δ ^ S.card * |fourierCoeff f.toReal S|) ≤
      expectRandomRestriction n δ (fun J z ↦
        ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) := by
  classical
  calc
    (∑ S : Finset (Fin n), δ ^ S.card * |fourierCoeff f.toReal S|) =
        ∑ S : Finset (Fin n),
          |expectRandomRestriction n δ (fun J z ↦
            ambientRestrictionFourierCoeff f.toReal J S z)| := by
      apply Finset.sum_congr rfl
      intro S _
      rw [expect_fourierCoeff_randomRestriction]
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 _)]
    _ ≤ ∑ S : Finset (Fin n),
          expectRandomRestriction n δ (fun J z ↦
            |ambientRestrictionFourierCoeff f.toReal J S z|) := by
      apply Finset.sum_le_sum
      intro S _
      exact abs_expectRandomRestriction_le_expect_abs hδ0 hδ1 _
    _ = expectRandomRestriction n δ (fun J z ↦
          ∑ S : Finset (Fin n),
            |ambientRestrictionFourierCoeff f.toReal J S z|) :=
      sum_expectRandomRestriction δ
        (fun S J z ↦ |ambientRestrictionFourierCoeff f.toReal J S z|)
    _ = expectRandomRestriction n δ (fun J z ↦
          fourierOneNorm (extendedSignRestriction f.toReal J z)) := by
      congr 1
      funext J z
      exact sum_abs_ambientRestrictionFourierCoeff f.toReal J z
    _ ≤ expectRandomRestriction n δ (fun J z ↦
          ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) :=
      expectRandomRestriction_mono hδ0 hδ1
        (fun J z ↦ exercise4_11_restriction f J z)


/-! ## Lemma 4.21 and low-degree concentration -/


variable {n : ℕ}

/-! ## A finite Bernoulli lower-tail bound -/

/-- Probability that a `δ`-random free set meets `U` in at least `k` coordinates. -/
noncomputable def deltaRandomIntersectionTail
    (n : ℕ) (δ : ℝ) (U : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
    if k ≤ (U ∩ J).card then 1 else 0

theorem card_inter_eq_sum_memIndicator (U J : Finset (Fin n)) :
    ((U ∩ J).card : ℝ) = ∑ i ∈ U, if i ∈ J then (1 : ℝ) else 0 := by
  classical
  have hfilter : U.filter (· ∈ J) = U ∩ J := by
    ext i
    simp
  calc
    ((U ∩ J).card : ℝ) = ((U.filter (· ∈ J)).card : ℝ) := by
      rw [hfilter]
    _ = ∑ i ∈ U, if i ∈ J then (1 : ℝ) else 0 := by simp [hfilter]

theorem sum_deltaRandomSubsetWeight_pair_mem (n : ℕ) (δ : ℝ) (i j : Fin n) :
    ∑ J : Finset (Fin n),
        (if i ∈ J ∧ j ∈ J then deltaRandomSubsetWeight n δ J else 0) =
      if i = j then δ else δ ^ 2 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa using sum_deltaRandomSubsetWeight_supset n δ ({i} : Finset (Fin n))
  · simpa [Finset.insert_subset_iff, hij] using
      sum_deltaRandomSubsetWeight_supset n δ ({i, j} : Finset (Fin n))

/-- First moment of the size of the intersection with a `δ`-random free set. -/
theorem sum_deltaRandomSubsetWeight_mul_card_inter
    (n : ℕ) (δ : ℝ) (U : Finset (Fin n)) :
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J * ((U ∩ J).card : ℝ) =
      δ * U.card := by
  classical
  simp_rw [card_inter_eq_sum_memIndicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i ∈ U, ∑ J : Finset (Fin n),
        deltaRandomSubsetWeight n δ J * (if i ∈ J then (1 : ℝ) else 0)) =
        ∑ i ∈ U, δ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ∑ J : Finset (Fin n),
            deltaRandomSubsetWeight n δ J * (if i ∈ J then (1 : ℝ) else 0) =
            ∑ J : Finset (Fin n),
              if i ∈ J then deltaRandomSubsetWeight n δ J else 0 := by
          apply Finset.sum_congr rfl
          intro J _
          split_ifs <;> ring
        _ = δ := sum_deltaRandomSubsetWeight_mem n δ i
    _ = δ * U.card := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem sq_card_inter_eq_sum_pairIndicator (U J : Finset (Fin n)) :
    ((U ∩ J).card : ℝ) ^ 2 =
      ∑ i ∈ U, ∑ j ∈ U, if i ∈ J ∧ j ∈ J then (1 : ℝ) else 0 := by
  classical
  rw [pow_two, card_inter_eq_sum_memIndicator, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J <;> simp [hi, hj]

theorem sum_pairDiagonalWeight (δ : ℝ) (U : Finset (Fin n)) :
    ∑ i ∈ U, ∑ j ∈ U, (if i = j then δ else δ ^ 2) =
      δ ^ 2 * (U.card : ℝ) ^ 2 + δ * (1 - δ) * U.card := by
  classical
  have hinner (i : Fin n) (hi : i ∈ U) :
      ∑ j ∈ U, (if i = j then δ else δ ^ 2) =
        δ ^ 2 * U.card + (δ - δ ^ 2) := by
    calc
      ∑ j ∈ U, (if i = j then δ else δ ^ 2) =
          ∑ j ∈ U, (δ ^ 2 + if i = j then δ - δ ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = δ ^ 2 * U.card + (δ - δ ^ 2) := by
        simp [Finset.sum_add_distrib, hi]
        ring
  calc
    ∑ i ∈ U, ∑ j ∈ U, (if i = j then δ else δ ^ 2) =
        ∑ i ∈ U, (δ ^ 2 * U.card + (δ - δ ^ 2)) := by
      apply Finset.sum_congr rfl
      exact hinner
    _ = δ ^ 2 * (U.card : ℝ) ^ 2 + δ * (1 - δ) * U.card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Second moment of the size of the intersection with a `δ`-random free set. -/
theorem sum_deltaRandomSubsetWeight_mul_sq_card_inter
    (n : ℕ) (δ : ℝ) (U : Finset (Fin n)) :
    ∑ J : Finset (Fin n),
        deltaRandomSubsetWeight n δ J * ((U ∩ J).card : ℝ) ^ 2 =
      δ ^ 2 * (U.card : ℝ) ^ 2 + δ * (1 - δ) * U.card := by
  classical
  simp_rw [sq_card_inter_eq_sum_pairIndicator, Finset.mul_sum]
  calc
    (∑ J : Finset (Fin n), ∑ i ∈ U, ∑ j ∈ U,
        deltaRandomSubsetWeight n δ J *
          (if i ∈ J ∧ j ∈ J then (1 : ℝ) else 0)) =
        ∑ i ∈ U, ∑ j ∈ U, ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J *
            (if i ∈ J ∧ j ∈ J then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i ∈ U, ∑ j ∈ U, (if i = j then δ else δ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
            (if i ∈ J ∧ j ∈ J then (1 : ℝ) else 0) =
            ∑ J : Finset (Fin n),
              if i ∈ J ∧ j ∈ J then deltaRandomSubsetWeight n δ J else 0 := by
          apply Finset.sum_congr rfl
          intro J _
          split_ifs <;> ring
        _ = if i = j then δ else δ ^ 2 :=
          sum_deltaRandomSubsetWeight_pair_mem n δ i j
    _ = δ ^ 2 * (U.card : ℝ) ^ 2 + δ * (1 - δ) * U.card :=
      sum_pairDiagonalWeight δ U

/-- Variance identity for the size of the intersection with a `δ`-random free set. -/
theorem sum_deltaRandomSubsetWeight_mul_sq_card_inter_sub_mean
    (n : ℕ) (δ : ℝ) (U : Finset (Fin n)) :
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
        (((U ∩ J).card : ℝ) - δ * U.card) ^ 2 =
      δ * (1 - δ) * U.card := by
  classical
  let μ : ℝ := δ * U.card
  have hpoint (J : Finset (Fin n)) :
      deltaRandomSubsetWeight n δ J * (((U ∩ J).card : ℝ) - μ) ^ 2 =
        deltaRandomSubsetWeight n δ J * ((U ∩ J).card : ℝ) ^ 2 -
          2 * μ * (deltaRandomSubsetWeight n δ J * ((U ∩ J).card : ℝ)) +
          μ ^ 2 * deltaRandomSubsetWeight n δ J := by
    ring
  simp_rw [show δ * (U.card : ℝ) = μ by rfl, hpoint,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_deltaRandomSubsetWeight_mul_sq_card_inter,
    sum_deltaRandomSubsetWeight_mul_card_inter, sum_deltaRandomSubsetWeight]
  dsimp [μ]
  ring

/-- If the expected intersection size exceeds `3k`, at least one third of the random free
sets meet `U` in at least `k` coordinates. -/
theorem one_third_le_deltaRandomIntersectionTail
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk : 0 < k)
    (U : Finset (Fin n)) (hU : 3 * (k : ℝ) / δ < U.card) :
    (1 / 3 : ℝ) ≤ deltaRandomIntersectionTail n δ U k := by
  classical
  let μ : ℝ := δ * U.card
  let a : ℝ := μ - k + 1
  let q : ℝ := ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
    if (U ∩ J).card < k then 1 else 0
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hμ : 3 * (k : ℝ) < μ := by
    dsimp [μ]
    have := (div_lt_iff₀ hδ0).1 hU
    nlinarith
  have ha : 0 < a := by
    dsimp [a]
    nlinarith
  have hweight (J : Finset (Fin n)) : 0 ≤ deltaRandomSubsetWeight n δ J :=
    deltaRandomSubsetWeight_nonneg n hδ0.le hδ1 J
  have hvariance : δ * (1 - δ) * (U.card : ℝ) ≤ μ := by
    have hδcard : 0 ≤ δ * (U.card : ℝ) :=
      mul_nonneg hδ0.le (Nat.cast_nonneg U.card)
    calc
      δ * (1 - δ) * (U.card : ℝ) = (1 - δ) * (δ * U.card) := by ring
      _ ≤ 1 * (δ * U.card) := by gcongr; linarith
      _ = μ := by simp [μ]
  have hquadratic : 3 * μ ≤ 2 * a ^ 2 := by
    have hd : 0 ≤ μ - 3 * (k : ℝ) := sub_nonneg.mpr hμ.le
    have hkd : 0 ≤ (k : ℝ) * (μ - 3 * (k : ℝ)) :=
      mul_nonneg (by positivity) hd
    have hkquad : 0 ≤ 8 * (k : ℝ) ^ 2 - k := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
    have hdquad : 0 ≤ (μ - 3 * (k : ℝ)) ^ 2 := sq_nonneg _
    dsimp [a]
    nlinarith
  have hthreeVariance :
      3 * (δ * (1 - δ) * (U.card : ℝ)) ≤ 2 * a ^ 2 := by
    nlinarith
  have hchebyshev : a ^ 2 * q ≤ δ * (1 - δ) * U.card := by
    calc
      a ^ 2 * q = ∑ J : Finset (Fin n), a ^ 2 *
          (deltaRandomSubsetWeight n δ J *
            if (U ∩ J).card < k then 1 else 0) := by
        dsimp [q]
        rw [Finset.mul_sum]
      _ ≤ ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          (((U ∩ J).card : ℝ) - μ) ^ 2 := by
        apply Finset.sum_le_sum
        intro J _
        by_cases hfail : (U ∩ J).card < k
        · rw [if_pos hfail]
          have hcard : (((U ∩ J).card : ℝ)) + 1 ≤ (k : ℝ) := by
            exact_mod_cast Nat.succ_le_iff.mpr hfail
          have hgap : a ≤ μ - ((U ∩ J).card : ℝ) := by
            dsimp [a]
            linarith
          have hgapNonneg : 0 ≤ μ - ((U ∩ J).card : ℝ) := ha.le.trans hgap
          have hsquare : a ^ 2 ≤ (((U ∩ J).card : ℝ) - μ) ^ 2 := by
            have hsquare' : a ^ 2 ≤ (μ - ((U ∩ J).card : ℝ)) ^ 2 :=
              (sq_le_sq₀ ha.le hgapNonneg).2 hgap
            nlinarith
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left hsquare (hweight J)
        · rw [if_neg hfail]
          simpa using mul_nonneg (hweight J) (sq_nonneg _)
      _ = δ * (1 - δ) * U.card := by
        simpa [μ] using
          sum_deltaRandomSubsetWeight_mul_sq_card_inter_sub_mean n δ U
  have hq : q ≤ 2 / 3 := by
    have haSquare : 0 < a ^ 2 := sq_pos_of_pos ha
    have hscaled : a ^ 2 * (3 * q) ≤ a ^ 2 * 2 := by
      calc
        a ^ 2 * (3 * q) = 3 * (a ^ 2 * q) := by ring
        _ ≤ 3 * (δ * (1 - δ) * U.card) := by gcongr
        _ ≤ 2 * a ^ 2 := hthreeVariance
        _ = a ^ 2 * 2 := by ring
    have := (mul_le_mul_iff_right₀ haSquare).1 hscaled
    nlinarith
  have hpartition : deltaRandomIntersectionTail n δ U k + q = 1 := by
    unfold deltaRandomIntersectionTail
    dsimp [q]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ J : Finset (Fin n),
          (deltaRandomSubsetWeight n δ J *
              (if k ≤ (U ∩ J).card then 1 else 0) +
            deltaRandomSubsetWeight n δ J *
              if (U ∩ J).card < k then 1 else 0) =
          ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J := by
        apply Finset.sum_congr rfl
        intro J _
        by_cases hsuccess : k ≤ (U ∩ J).card
        · simp [hsuccess, not_lt_of_ge hsuccess]
        · have hfail : (U ∩ J).card < k := Nat.lt_of_not_ge hsuccess
          simp [hsuccess, hfail]
      _ = 1 := sum_deltaRandomSubsetWeight n δ
  linarith

theorem deltaRandomIntersectionTail_nonneg
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (U : Finset (Fin n)) (k : ℕ) :
    0 ≤ deltaRandomIntersectionTail n δ U k := by
  unfold deltaRandomIntersectionTail
  apply Finset.sum_nonneg
  intro J _
  exact mul_nonneg (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J) (by split_ifs <;> norm_num)

/-- Binomial expansion of the intersection-tail probability, in the form needed by
Proposition 4.17. -/
theorem deltaRandomIntersectionTail_eq_sum
    (n : ℕ) (δ : ℝ) (U : Finset (Fin n)) (k : ℕ) :
    deltaRandomIntersectionTail n δ U k =
      ∑ S : Finset (Fin n),
        if k ≤ S.card then
          if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0
        else 0 := by
  classical
  unfold deltaRandomIntersectionTail
  calc
    (∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
        if k ≤ (U ∩ J).card then 1 else 0) =
        ∑ J : Finset (Fin n), ∑ S : Finset (Fin n),
          if k ≤ S.card then
            if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro J _
      have hterm (S : Finset (Fin n)) :
          (if k ≤ S.card then
              if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0
            else 0) =
            if S = U ∩ J then
              (if k ≤ (U ∩ J).card then deltaRandomSubsetWeight n δ J else 0)
            else 0 := by
        by_cases hS : S = U ∩ J
        · subst S
          simp
        · have hne : U ∩ J ≠ S := Ne.symm hS
          simp [hS, hne]
      simp_rw [hterm]
      simp
    _ = ∑ S : Finset (Fin n), ∑ J : Finset (Fin n),
          if k ≤ S.card then
            if U ∩ J = S then deltaRandomSubsetWeight n δ J else 0
          else 0 := Finset.sum_comm
    _ = ∑ S : Finset (Fin n),
          if k ≤ S.card then
            if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : k ≤ S.card
      · simp only [if_pos hcard]
        exact sum_deltaRandomSubsetWeight_inter_eq n δ S U
      · simp [hcard]

/-! ## High-degree weight of a restricted function -/

/-- Fourier weight of a restriction in degrees at least `k`, using the ambient-frequency
convention of Proposition 4.17. -/
noncomputable def restrictedFourierWeightAtLeast
    (f : BooleanFunction n) (k : ℕ) (J : Finset (Fin n)) (z : FixedSignCube J) : ℝ :=
  ∑ S : Finset (Fin n),
    if k ≤ S.card then ambientRestrictionFourierCoeff f.toReal J S z ^ 2 else 0

/-- A restricted Boolean function has Fourier degree at most its minimum decision-tree depth. -/
theorem fourierDegree_extendedSignRestriction_le_restrictedDecisionTreeDepth
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    fourierDegree (extendedSignRestriction f.toReal J z) ≤
      restrictedDecisionTreeDepth f J z := by
  obtain ⟨T, hT, hdepth⟩ :=
    F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth
      (restrictedBinaryFunction f J z)
  let R : DecisionTree n ℝ := T.mapOutputs signValue
  let target : BooleanFunction n := extendedSignRestriction f J z
  have hR : R.Computes fun x ↦ target.toReal (binaryCubeSignEquiv n x) := by
    rw [F₂DecisionTree.computes_iff]
    intro x
    rw [F₂DecisionTree.eval_mapOutputs,
      (F₂DecisionTree.computes_iff T _).1 hT]
    rfl
  have hdegree := fourierDegree_toReal_le_depth_of_decisionTree target R hR
  dsimp only [target, R] at hdegree
  rw [F₂DecisionTree.depth_mapOutputs, hdepth] at hdegree
  have htoReal :
      BooleanFunction.toReal (extendedSignRestriction f J z) =
        extendedSignRestriction f.toReal J z := by
    funext x
    rfl
  rw [htoReal] at hdegree
  exact hdegree

/-- The high-degree Fourier weight of a restriction is bounded by the indicator that its
decision-tree depth reaches `k`. -/
theorem restrictedFourierWeightAtLeast_le_switchingFailureIndicator
    (f : BooleanFunction n) (k : ℕ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictedFourierWeightAtLeast f k J z ≤ switchingFailureIndicator f k J z := by
  classical
  unfold restrictedFourierWeightAtLeast switchingFailureIndicator
  by_cases hfailure : k ≤ restrictedDecisionTreeDepth f J z
  · rw [if_pos hfailure]
    calc
      (∑ S : Finset (Fin n),
          if k ≤ S.card then ambientRestrictionFourierCoeff f.toReal J S z ^ 2 else 0) ≤
          ∑ S : Finset (Fin n),
            fourierCoeff (extendedSignRestriction f.toReal J z) S ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        by_cases hcard : k ≤ S.card
        · rw [if_pos hcard, ← fourierCoeff_extendedSignRestriction]
        · rw [if_neg hcard]
          positivity
      _ = 1 := by
        have htoReal :
            BooleanFunction.toReal (extendedSignRestriction f J z) =
              extendedSignRestriction f.toReal J z := by
          funext x
          rfl
        rw [← htoReal]
        exact sum_sq_fourierCoeff_eq_one (extendedSignRestriction f J z)
  · rw [if_neg hfailure]
    apply Finset.sum_nonpos
    intro S _
    by_cases hcard : k ≤ S.card
    · rw [if_pos hcard, ← fourierCoeff_extendedSignRestriction]
      have hdegree :=
        fourierDegree_extendedSignRestriction_le_restrictedDecisionTreeDepth f J z
      have hdepth : restrictedDecisionTreeDepth f J z < S.card :=
        lt_of_lt_of_le (Nat.lt_of_not_ge hfailure) hcard
      rw [(fourierDegree_le_iff _ _).1 hdegree S hdepth]
      norm_num
    · rw [if_neg hcard]

/-- Expected high-degree restricted Fourier weight is controlled by switching failure. -/
theorem expect_restrictedFourierWeightAtLeast_le_switchingFailureProbability
    (f : BooleanFunction n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    expectRandomRestriction n δ (restrictedFourierWeightAtLeast f k) ≤
      switchingFailureProbability f δ k := by
  rw [switchingFailureProbability]
  exact expectRandomRestriction_mono hδ0 hδ1
    (restrictedFourierWeightAtLeast_le_switchingFailureIndicator f k)

/-- Proposition 4.17 identifies expected restricted high-degree weight with ambient Fourier
weight multiplied by the corresponding random-intersection tail probability. -/
theorem expect_restrictedFourierWeightAtLeast_eq_sum_intersectionTail
    (f : BooleanFunction n) (δ : ℝ) (k : ℕ) :
    expectRandomRestriction n δ (restrictedFourierWeightAtLeast f k) =
      ∑ U : Finset (Fin n),
        deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2 := by
  classical
  unfold restrictedFourierWeightAtLeast
  calc
    expectRandomRestriction n δ (fun J z ↦
        ∑ S : Finset (Fin n),
          if k ≤ S.card then ambientRestrictionFourierCoeff f.toReal J S z ^ 2 else 0) =
        ∑ S : Finset (Fin n), expectRandomRestriction n δ (fun J z ↦
          if k ≤ S.card then ambientRestrictionFourierCoeff f.toReal J S z ^ 2 else 0) :=
      (sum_expectRandomRestriction δ _).symm
    _ = ∑ S : Finset (Fin n),
        if k ≤ S.card then
          ∑ U : Finset (Fin n),
            (if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0) *
              fourierCoeff f.toReal U ^ 2
        else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : k ≤ S.card
      · rw [if_pos hcard]
        simpa [hcard] using expect_sq_fourierCoeff_randomRestriction f.toReal δ S
      · simp [hcard, expectRandomRestriction]
    _ = ∑ U : Finset (Fin n),
        (∑ S : Finset (Fin n),
          if k ≤ S.card then
            if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0
          else 0) * fourierCoeff f.toReal U ^ 2 := by
      have hpush (S : Finset (Fin n)) :
          (if k ≤ S.card then
              ∑ U : Finset (Fin n),
                (if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0) *
                  fourierCoeff f.toReal U ^ 2
            else 0) =
            ∑ U : Finset (Fin n),
              if k ≤ S.card then
                (if S ⊆ U then δ ^ S.card * (1 - δ) ^ (U \ S).card else 0) *
                  fourierCoeff f.toReal U ^ 2
              else 0 := by
        by_cases hcard : k ≤ S.card <;> simp [hcard]
      simp_rw [hpush]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring
    _ = ∑ U : Finset (Fin n),
        deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2 := by
      apply Finset.sum_congr rfl
      intro U _
      rw [deltaRandomIntersectionTail_eq_sum]

/-! ## Lemma 4.21 and the switching-bound bridge -/

/-- O'Donnell, Lemma 4.21: if a `δ`-random restriction has decision-tree depth at least
`k` with probability `ε`, then the Fourier spectrum is `3ε`-concentrated through the exact
real cutoff `3k / δ`. -/
theorem lemma4_21 (f : BooleanFunction n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    IsFourierSpectrumConcentratedUpTo f.toReal
      (3 * switchingFailureProbability f δ k) (3 * (k : ℝ) / δ) := by
  unfold IsFourierSpectrumConcentratedUpTo
  have hweightedUpper :
      (∑ U : Finset (Fin n),
          deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2) ≤
        switchingFailureProbability f δ k := by
    rw [← expect_restrictedFourierWeightAtLeast_eq_sum_intersectionTail]
    exact expect_restrictedFourierWeightAtLeast_le_switchingFailureProbability
      f hδ0.le hδ1 k
  have hweightedLower :
      (1 / 3 : ℝ) * fourierWeightAboveReal (3 * (k : ℝ) / δ) f.toReal ≤
        ∑ U : Finset (Fin n),
          deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2 := by
    calc
      (1 / 3 : ℝ) * fourierWeightAboveReal (3 * (k : ℝ) / δ) f.toReal =
          ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦
            3 * (k : ℝ) / δ < (U.card : ℝ)),
              (1 / 3 : ℝ) * fourierCoeff f.toReal U ^ 2 := by
        rw [fourierWeightAboveReal, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        rfl
      _ ≤ ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦
            3 * (k : ℝ) / δ < (U.card : ℝ)),
              deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2 := by
        apply Finset.sum_le_sum
        intro U hU
        have htail : (1 / 3 : ℝ) ≤ deltaRandomIntersectionTail n δ U k :=
          one_third_le_deltaRandomIntersectionTail hδ0 hδ1 hk U
            (Finset.mem_filter.mp hU).2
        exact mul_le_mul_of_nonneg_right htail (sq_nonneg _)
      _ ≤ ∑ U : Finset (Fin n),
          deltaRandomIntersectionTail n δ U k * fourierCoeff f.toReal U ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro U _ _
        exact mul_nonneg (deltaRandomIntersectionTail_nonneg hδ0.le hδ1 U k) (sq_nonneg _)
  nlinarith

/-- Exact quantitative implication behind Theorem 4.22, parameterized by any independently
proved switching bound rather than assuming a particular Håstad declaration. -/
theorem theorem4_22_of_switchingFailureProbability_le
    (f : BooleanFunction n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {k : ℕ} (hk : 0 < k) {ε : ℝ}
    (hswitch : switchingFailureProbability f δ k ≤ ε / 3) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε (3 * (k : ℝ) / δ) := by
  apply (lemma4_21 f hδ0 hδ1 hk).mono_error
  linarith


/-! ## Switching tails and exponential moments -/


variable {n : ℕ}

/-- Restricted decision-tree depth never exceeds the ambient dimension. -/
theorem restrictedDecisionTreeDepth_le_dimension
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    restrictedDecisionTreeDepth f J z ≤ n := by
  obtain ⟨T, _, hdepth⟩ :=
    F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth
      (restrictedBinaryFunction f J z)
  unfold restrictedDecisionTreeDepth
  rw [← hdepth]
  exact T.depth_le_dimension

/-- Random-restriction expectation preserves constants. -/
theorem expectRandomRestriction_const (δ c : ℝ) :
    expectRandomRestriction n δ (fun _ _ ↦ c) = c := by
  unfold expectRandomRestriction
  simp_rw [Fintype.expect_const]
  rw [← Finset.sum_mul, sum_deltaRandomSubsetWeight, one_mul]

/-- Random-restriction expectation is additive. -/
theorem expectRandomRestriction_add (δ : ℝ)
    (g h : (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    expectRandomRestriction n δ (fun J z ↦ g J z + h J z) =
      expectRandomRestriction n δ g + expectRandomRestriction n δ h := by
  unfold expectRandomRestriction
  simp_rw [Finset.expect_add_distrib, mul_add]
  exact Finset.sum_add_distrib

/-- Constants factor out of random-restriction expectation. -/
theorem expectRandomRestriction_const_mul (δ c : ℝ)
    (g : (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    expectRandomRestriction n δ (fun J z ↦ c * g J z) =
      c * expectRandomRestriction n δ g := by
  unfold expectRandomRestriction
  calc
    (∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
        (𝔼 z : FixedSignCube J, c * g J z)) =
        ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          (c * (𝔼 z : FixedSignCube J, g J z)) := by
      apply Finset.sum_congr rfl
      intro J _
      exact congrArg (fun t : ℝ ↦ deltaRandomSubsetWeight n δ J * t)
        (Finset.mul_expect Finset.univ (g J) c).symm
    _ = c * ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          (𝔼 z : FixedSignCube J, g J z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring

/-- Finite sums commute with random-restriction expectation. -/
theorem expectRandomRestriction_sum {ι : Type*} (δ : ℝ) (s : Finset ι)
    (g : ι → (J : Finset (Fin n)) → FixedSignCube J → ℝ) :
    expectRandomRestriction n δ (fun J z ↦ ∑ a ∈ s, g a J z) =
      ∑ a ∈ s, expectRandomRestriction n δ (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectRandomRestriction_const]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [expectRandomRestriction_add, ih]

/-- Finite geometric expansion of `2 ^ d`. -/
theorem two_pow_eq_one_add_sum_range (d : ℕ) :
    ((2 ^ d : ℕ) : ℝ) = 1 + ∑ j ∈ Finset.range d, ((2 ^ j : ℕ) : ℝ) := by
  have hnat :
      (2 ^ d : ℕ) = 1 + ∑ j ∈ Finset.range d, (2 ^ j : ℕ) := by
    simpa [add_comm] using (geom_sum_mul_add (1 : ℕ) d).symm
  exact_mod_cast hnat

/-- The same expansion expressed through tail indicators up to any known upper bound. -/
theorem two_pow_eq_one_add_sum_tailIndicators {d N : ℕ} (hd : d ≤ N) :
    ((2 ^ d : ℕ) : ℝ) =
      1 + ∑ j ∈ Finset.range N,
        ((2 ^ j : ℕ) : ℝ) * if j + 1 ≤ d then 1 else 0 := by
  rw [two_pow_eq_one_add_sum_range]
  congr 1
  calc
    (∑ j ∈ Finset.range d, ((2 ^ j : ℕ) : ℝ)) =
        ∑ j ∈ (Finset.range N).filter (fun j ↦ j + 1 ≤ d),
          ((2 ^ j : ℕ) : ℝ) := by
      congr 1
      ext j
      simp
      omega
    _ = ∑ j ∈ Finset.range N,
        ((2 ^ j : ℕ) : ℝ) * if j + 1 ≤ d then 1 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp_all

/-- Pointwise tail-indicator expansion of the restricted decision-tree exponential. -/
theorem two_pow_restrictedDecisionTreeDepth_eq_tailIndicators
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FixedSignCube J) :
    ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ) =
      1 + ∑ j ∈ Finset.range n,
        ((2 ^ j : ℕ) : ℝ) * switchingFailureIndicator f (j + 1) J z := by
  rw [two_pow_eq_one_add_sum_tailIndicators
    (restrictedDecisionTreeDepth_le_dimension f J z)]
  apply congrArg (fun t : ℝ ↦ 1 + t)
  apply Finset.sum_congr rfl
  intro j _
  unfold switchingFailureIndicator
  rfl

/-- Exact tail-sum formula for the expected restricted decision-tree exponential. -/
theorem expect_two_pow_restrictedDecisionTreeDepth_eq_failureSum
    (f : BooleanFunction n) (δ : ℝ) :
    expectRandomRestriction n δ (fun J z ↦
        ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) =
      1 + ∑ j ∈ Finset.range n,
        ((2 ^ j : ℕ) : ℝ) * switchingFailureProbability f δ (j + 1) := by
  calc
    expectRandomRestriction n δ (fun J z ↦
        ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) =
        expectRandomRestriction n δ (fun J z ↦
          1 + ∑ j ∈ Finset.range n,
            ((2 ^ j : ℕ) : ℝ) * switchingFailureIndicator f (j + 1) J z) := by
      congr 1
      funext J z
      exact two_pow_restrictedDecisionTreeDepth_eq_tailIndicators f J z
    _ = expectRandomRestriction n δ (fun _ _ ↦ 1) +
        expectRandomRestriction n δ (fun J z ↦
          ∑ j ∈ Finset.range n,
            ((2 ^ j : ℕ) : ℝ) * switchingFailureIndicator f (j + 1) J z) :=
      expectRandomRestriction_add δ _ _
    _ = 1 + ∑ j ∈ Finset.range n,
        expectRandomRestriction n δ (fun J z ↦
          ((2 ^ j : ℕ) : ℝ) * switchingFailureIndicator f (j + 1) J z) := by
      rw [expectRandomRestriction_const,
        expectRandomRestriction_sum δ (Finset.range n)]
    _ = 1 + ∑ j ∈ Finset.range n,
        ((2 ^ j : ℕ) : ℝ) * switchingFailureProbability f δ (j + 1) := by
      apply congrArg (fun t : ℝ ↦ 1 + t)
      apply Finset.sum_congr rfl
      intro j _
      rw [expectRandomRestriction_const_mul]
      rfl

theorem two_pow_mul_quarter_pow_succ (j : ℕ) :
    ((2 ^ j : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (j + 1) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j := by
  push_cast
  rw [pow_succ]
  calc
    (2 : ℝ) ^ j * ((1 / 4 : ℝ) ^ j * (1 / 4 : ℝ)) =
        (1 / 4 : ℝ) * ((2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j) := by ring
    _ = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j := by
      rw [← mul_pow]
      norm_num

/-- A `(1 / 4) ^ k` switching tail bounds the expected `2 ^ DT` by `2`. -/
theorem expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter
    (f : BooleanFunction n) (δ : ℝ)
    (hfailure : ∀ k : ℕ,
      switchingFailureProbability f δ k ≤ (1 / 4 : ℝ) ^ k) :
    expectRandomRestriction n δ (fun J z ↦
        ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) ≤ 2 := by
  rw [expect_two_pow_restrictedDecisionTreeDepth_eq_failureSum]
  calc
    1 + ∑ j ∈ Finset.range n,
        ((2 ^ j : ℕ) : ℝ) * switchingFailureProbability f δ (j + 1) ≤
        1 + ∑ j ∈ Finset.range n,
          ((2 ^ j : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (j + 1) := by
      gcongr with j hj
      exact hfailure (j + 1)
    _ = 1 + (1 / 4 : ℝ) *
        ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [two_pow_mul_quarter_pow_succ]
    _ ≤ 1 + (1 / 4 : ℝ) * 2 := by
      gcongr
      exact sum_geometric_two_le n
    _ ≤ 2 := by norm_num


/-! ## Low-degree Fourier one-norm -/


variable {n : ℕ}

/-- Lemma 4.23 converts an upper bound on the expected restricted `2 ^ DT` into a low-degree
Fourier one-norm bound. -/
theorem lowDegreeFourierOneNorm_le_two_mul_inv_pow_of_expected_two_pow_le
    (f : BooleanFunction n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (k : ℕ)
    (hmoment : expectRandomRestriction n δ (fun J z ↦
      ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) ≤ 2) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
      |fourierCoeff f.toReal S|) ≤ 2 * δ⁻¹ ^ k := by
  have hweighted := lemma4_23 f hδ0.le hδ1
  have hscaled :
      δ ^ k *
          (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
            |fourierCoeff f.toReal S|) ≤
        ∑ S : Finset (Fin n), δ ^ S.card * |fourierCoeff f.toReal S| := by
    calc
      δ ^ k *
          (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
            |fourierCoeff f.toReal S|) =
          ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
            δ ^ k * |fourierCoeff f.toReal S| := by rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
            δ ^ S.card * |fourierCoeff f.toReal S| := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hδ0.le hδ1 (Finset.mem_filter.mp hS).2)
          (abs_nonneg _)
      _ ≤ ∑ S : Finset (Fin n), δ ^ S.card * |fourierCoeff f.toReal S| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _
        positivity
  have hproduct :
      δ ^ k *
          (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
            |fourierCoeff f.toReal S|) ≤ 2 :=
    hscaled.trans (hweighted.trans hmoment)
  have hdivide :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
        |fourierCoeff f.toReal S|) ≤ 2 / δ ^ k := by
    apply (le_div_iff₀ (pow_pos hδ0 k)).2
    nlinarith
  simpa [div_eq_mul_inv, inv_pow] using hdivide

/-- Exact quantitative implication behind Theorem 4.24. The positive-width hypothesis is
necessary at the endpoint: the printed formula is false for `w = 0` and `k > 0`. -/
theorem theorem4_24_of_switchingFailureProbability_le_quarter
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w) (k : ℕ)
    (hfailure : ∀ d : ℕ,
      switchingFailureProbability f (1 / (20 * (w : ℝ))) d ≤
        (1 / 4 : ℝ) ^ d) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
      |fourierCoeff f.toReal S|) ≤ 2 * (20 * (w : ℝ)) ^ k := by
  let δ : ℝ := 1 / (20 * (w : ℝ))
  have hwReal : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hdenominator : (1 : ℝ) ≤ 20 * (w : ℝ) := by nlinarith
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenominator
  have hmoment :
      expectRandomRestriction n δ (fun J z ↦
        ((2 ^ restrictedDecisionTreeDepth f J z : ℕ) : ℝ)) ≤ 2 :=
    expect_two_pow_restrictedDecisionTreeDepth_le_two_of_failure_le_quarter
      f δ (by simpa [δ] using hfailure)
  have hbound :=
    lowDegreeFourierOneNorm_le_two_mul_inv_pow_of_expected_two_pow_le
      f hδ0 hδ1 k hmoment
  simpa [δ, one_div] using hbound


/-! ## Explicit concentration degree for Theorem 4.22 -/


variable {n : ℕ}

/-- Decision-tree threshold used in the explicit form of Theorem 4.22. -/
noncomputable def dnfSwitchingDepth (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (3 / ε)⌉₊

/-- The selected threshold makes a dyadic switching tail at most `ε / 3`. -/
theorem half_pow_dnfSwitchingDepth_le {ε : ℝ} (hε : 0 < ε) :
    (1 / 2 : ℝ) ^ dnfSwitchingDepth ε ≤ ε / 3 := by
  let ratio : ℝ := 3 / ε
  have hratio : 0 < ratio := div_pos (by norm_num) hε
  have hlog : Real.logb 2 ratio ≤ (dnfSwitchingDepth ε : ℝ) := Nat.le_ceil _
  have hratioPow : ratio ≤ (2 : ℝ) ^ dnfSwitchingDepth ε := by
    have hrpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hratio).1 hlog
    simpa [Real.rpow_natCast] using hrpow
  have hthree : (3 : ℝ) ≤ ε * (2 : ℝ) ^ dnfSwitchingDepth ε := by
    have := (div_le_iff₀ hε).1 hratioPow
    simpa [ratio, mul_comm] using this
  have hscaled : (3 : ℝ) * (1 / 2 : ℝ) ^ dnfSwitchingDepth ε ≤ ε := by
    have hpow : (0 : ℝ) < (2 : ℝ) ^ dnfSwitchingDepth ε := by positivity
    have := (div_le_iff₀ hpow).2 hthree
    simpa [div_eq_mul_inv, one_div, inv_pow, mul_comm, mul_left_comm, mul_assoc] using this
  linarith

/-- The selected threshold is positive throughout the usual error range `(0, 1]`. -/
theorem dnfSwitchingDepth_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < dnfSwitchingDepth ε := by
  apply Nat.ceil_pos.mpr
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  apply (lt_div_iff₀ hε0).2
  linarith

/-- Exact implication behind Theorem 4.22 from a `(1 / 2) ^ d` switching tail. -/
theorem theorem4_22_of_switchingFailureProbability_le_half_pow
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hfailure : ∀ d : ℕ,
      switchingFailureProbability f (1 / (10 * (w : ℝ))) d ≤
        (1 / 2 : ℝ) ^ d) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε
      (30 * (w : ℝ) * dnfSwitchingDepth ε) := by
  let δ : ℝ := 1 / (10 * (w : ℝ))
  let k := dnfSwitchingDepth ε
  have hwReal : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hdenominator : (1 : ℝ) ≤ 10 * (w : ℝ) := by nlinarith
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenominator
  have hk : 0 < k := dnfSwitchingDepth_pos hε0 hε1
  have hbase : switchingFailureProbability f δ k ≤ (1 / 2 : ℝ) ^ k := by
    simpa [δ] using hfailure k
  have hswitch : switchingFailureProbability f δ k ≤ ε / 3 :=
    hbase.trans (half_pow_dnfSwitchingDepth_le hε0)
  have hconcentration :=
    theorem4_22_of_switchingFailureProbability_le f hδ0 hδ1 hk hswitch
  norm_num [δ, k, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] at hconcentration ⊢
  exact hconcentration


/-! ## Low-degree approximation and concentration transfer -/


variable {n : ℕ}

/-- The low-degree part is the sparse Fourier approximation on frequencies of degree at most
`k`. -/
theorem lowDegreePart_eq_sparseFourierApproximation (k : ℕ)
    (f : {−1,1}^[n] → ℝ) :
    lowDegreePart k f =
      sparseFourierApproximation
        (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k)
        (fourierCoeff f) := by
  rfl

/-- Fourier coefficients of the low-degree part are the original coefficients up to degree `k`
and vanish above it. -/
theorem fourierCoeff_lowDegreePart (k : ℕ) (f : {−1,1}^[n] → ℝ)
    (T : Finset (Fin n)) :
    fourierCoeff (lowDegreePart k f) T =
      if T.card ≤ k then fourierCoeff f T else 0 := by
  rw [lowDegreePart_eq_sparseFourierApproximation,
    fourierCoeff_sparseFourierApproximation]
  simp

/-- The Fourier one-norm of the low-degree part is exactly the low-degree coefficient sum. -/
theorem fourierOneNorm_lowDegreePart (k : ℕ) (f : {−1,1}^[n] → ℝ) :
    fourierOneNorm (lowDegreePart k f) =
      ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
        |fourierCoeff f S| := by
  classical
  unfold fourierOneNorm
  simp_rw [fourierCoeff_lowDegreePart]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ k <;> simp [hS]

/-- The squared normalized `L²` error of Fourier truncation is exactly the high-degree Fourier
tail. -/
theorem uniformLpNorm_sub_lowDegreePart_sq (k : ℕ) (f : {−1,1}^[n] → ℝ) :
    uniformLpNorm 2 (fun x ↦ f x - lowDegreePart k f x) ^ 2 =
      fourierWeightAbove k f := by
  classical
  rw [lowDegreePart_eq_sparseFourierApproximation,
    uniformLpNorm_sub_sparseFourierApproximation_sq]
  simp [fourierWeightAbove, fourierWeight, not_le]

/-- Squared normalized `L²` distance is symmetric. -/
theorem uniformLpNorm_sub_sq_comm (f g : {−1,1}^[n] → ℝ) :
    uniformLpNorm 2 (fun x ↦ f x - g x) ^ 2 =
      uniformLpNorm 2 (fun x ↦ g x - f x) ^ 2 := by
  simp_rw [uniformLpNorm_two_sq_eq_expect_sq]
  apply Finset.expect_congr rfl
  intro x _
  ring

/-- The explicit Fourier family obtained by applying Exercise 3.16 to a low-degree part. -/
noncomputable def lowDegreeL1ConcentratingFourierFamily
    (f : {−1,1}^[n] → ℝ) (k : ℕ) (ε : ℝ) : Finset (Finset (Fin n)) :=
  l1ConcentratingFourierFamily (lowDegreePart k f) (ε / 4)

/-- Concentration of the low-degree part transfers to the original function when its Fourier tail
uses the other quarter of the error budget. -/
theorem isFourierSpectrumConcentratedOn_lowDegreeL1ConcentratingFourierFamily
    (f : {−1,1}^[n] → ℝ) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (htail : fourierWeightAbove k f ≤ ε / 4) :
    IsFourierSpectrumConcentratedOn f ε
      (↑(lowDegreeL1ConcentratingFourierFamily f k ε) : Set (Finset (Fin n))) := by
  have hpart :=
    isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily
      (lowDegreePart k f) (by positivity : 0 < ε / 4)
  have herror :
      uniformLpNorm 2 (fun x ↦ lowDegreePart k f x - f x) ^ 2 ≤ ε / 4 := by
    rw [uniformLpNorm_sub_sq_comm, uniformLpNorm_sub_lowDegreePart_sq]
    exact htail
  have htransfer :=
    hpart.transfer_of_uniformLpNorm_sub_sq_le
      (lowDegreePart k f) f
      (↑(lowDegreeL1ConcentratingFourierFamily f k ε) : Set (Finset (Fin n))) herror
  change IsFourierSpectrumConcentratedOn f ε
    (↑(l1ConcentratingFourierFamily (lowDegreePart k f) (ε / 4)) :
      Set (Finset (Fin n)))
  convert htransfer using 1 <;> first | rfl | ring

/-- The explicit low-degree concentrating family inherits the standard Fourier one-norm cardinality
bound. -/
theorem card_lowDegreeL1ConcentratingFourierFamily_le
    (f : {−1,1}^[n] → ℝ) (k : ℕ) {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hnorm : fourierOneNorm (lowDegreePart k f) ≤ L) :
    ((lowDegreeL1ConcentratingFourierFamily f k ε).card : ℝ) ≤
      4 * L ^ 2 / ε := by
  have hcard :=
    card_l1ConcentratingFourierFamily_le
      (lowDegreePart k f) (by positivity : 0 < ε / 4)
  have hnormNonneg := fourierOneNorm_nonneg (lowDegreePart k f)
  have hsquare : fourierOneNorm (lowDegreePart k f) ^ 2 ≤ L ^ 2 := by
    nlinarith
  calc
    ((lowDegreeL1ConcentratingFourierFamily f k ε).card : ℝ) ≤
        fourierOneNorm (lowDegreePart k f) ^ 2 / (ε / 4) := by
      simpa [lowDegreeL1ConcentratingFourierFamily] using hcard
    _ ≤ L ^ 2 / (ε / 4) := by gcongr
    _ = 4 * L ^ 2 / ε := by field_simp

/-- Exact quantitative form of the low-degree truncation argument in Theorem 4.25. -/
theorem exists_fourierConcentratingFamily_of_lowDegree_bounds
    (f : {−1,1}^[n] → ℝ) (k : ℕ) {ε L : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (htail : IsFourierSpectrumConcentratedUpTo f (ε / 4) (k : ℝ))
    (hnorm :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
        |fourierCoeff f S|) ≤ L) :
    ∃ 𝓕 : Finset (Finset (Fin n)),
      IsFourierSpectrumConcentratedOn f ε (↑𝓕 : Set (Finset (Fin n))) ∧
      (𝓕.card : ℝ) ≤ 4 * L ^ 2 / ε := by
  let 𝓕 := lowDegreeL1ConcentratingFourierFamily f k ε
  refine ⟨𝓕, ?_, ?_⟩
  · apply isFourierSpectrumConcentratedOn_lowDegreeL1ConcentratingFourierFamily f k hε
    simpa [IsFourierSpectrumConcentratedUpTo, fourierWeightAboveReal_natCast] using htail
  · apply card_lowDegreeL1ConcentratingFourierFamily_le f k hε hL
    simpa [fourierOneNorm_lowDegreePart] using hnorm


/-! ## Sparse spectral family for Theorem 4.25 -/


variable {n : ℕ}

/-- Explicit natural degree used in the quantitative form of Theorem 4.25. -/
noncomputable def dnfSpectralConcentrationDegree (w : ℕ) (ε : ℝ) : ℕ :=
  30 * w * dnfSwitchingDepth (ε / 4)

/-- Explicit cardinality bound furnished by the proof of Theorem 4.25. -/
noncomputable def dnfSpectralFamilySizeBound (w : ℕ) (ε : ℝ) : ℝ :=
  4 * (2 * (20 * (w : ℝ)) ^ dnfSpectralConcentrationDegree w ε) ^ 2 / ε

/-- Exact quantitative implication behind Theorem 4.25, parameterized by the two instances of
Håstad's switching bound used by Theorems 4.22 and 4.24. -/
theorem theorem4_25_of_switchingFailureProbability_bounds
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hhalf : ∀ d : ℕ,
      switchingFailureProbability f (1 / (10 * (w : ℝ))) d ≤
        (1 / 2 : ℝ) ^ d)
    (hquarter : ∀ d : ℕ,
      switchingFailureProbability f (1 / (20 * (w : ℝ))) d ≤
        (1 / 4 : ℝ) ^ d) :
    ∃ 𝓕 : Finset (Finset (Fin n)),
      IsFourierSpectrumConcentratedOn f.toReal ε
        (↑𝓕 : Set (Finset (Fin n))) ∧
      (𝓕.card : ℝ) ≤ dnfSpectralFamilySizeBound w ε := by
  let k := dnfSpectralConcentrationDegree w ε
  let L : ℝ := 2 * (20 * (w : ℝ)) ^ k
  have hεquarter0 : 0 < ε / 4 := by positivity
  have hεquarter1 : ε / 4 ≤ 1 := by linarith
  have hconcentration :
      IsFourierSpectrumConcentratedUpTo f.toReal (ε / 4) (k : ℝ) := by
    have h := theorem4_22_of_switchingFailureProbability_le_half_pow
      f hw hεquarter0 hεquarter1 hhalf
    simpa [k, dnfSpectralConcentrationDegree] using h
  have honeNorm :
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
        |fourierCoeff f.toReal S|) ≤ L := by
    exact theorem4_24_of_switchingFailureProbability_le_quarter f hw k hquarter
  obtain ⟨𝓕, h𝓕, hcard⟩ :=
    exists_fourierConcentratingFamily_of_lowDegree_bounds
      f.toReal k hε0 (by positivity : 0 ≤ L) hconcentration honeNorm
  refine ⟨𝓕, h𝓕, ?_⟩
  simpa [dnfSpectralFamilySizeBound, k, L] using hcard


/-! ## Exact Håstad specializations and book-facing conclusions -/

/-- Håstad's lemma at restriction rate `1 / (10w)`. -/
theorem hastadHalfSwitchingBound
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w)
    (hf : HasDNFWidthLE f w ∨ HasCNFWidthLE f w) (d : ℕ) :
    switchingFailureProbability f (1 / (10 * (w : ℝ))) d ≤
      (1 / 2 : ℝ) ^ d := by
  have hwReal : (0 : ℝ) < w := by exact_mod_cast hw
  have hδ0 : (0 : ℝ) ≤ 1 / (10 * (w : ℝ)) := by positivity
  have hδ1 : (1 : ℝ) / (10 * (w : ℝ)) ≤ 1 := by
    have hwOne : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hden : (1 : ℝ) ≤ 10 * (w : ℝ) := by nlinarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hbound := hastadSwitchingLemma (k := d) hδ0 hδ1 hf
  calc
    switchingFailureProbability f (1 / (10 * (w : ℝ))) d ≤
        (5 * (1 / (10 * (w : ℝ))) * (w : ℝ)) ^ d := hbound
    _ = (1 / 2 : ℝ) ^ d := by
      congr 1
      field_simp
      norm_num

/-- Håstad's lemma at restriction rate `1 / (20w)`. -/
theorem hastadQuarterSwitchingBoundForFormula
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w)
    (hf : HasDNFWidthLE f w ∨ HasCNFWidthLE f w) (d : ℕ) :
    switchingFailureProbability f (1 / (20 * (w : ℝ))) d ≤
      (1 / 4 : ℝ) ^ d := by
  have hwReal : (0 : ℝ) < w := by exact_mod_cast hw
  have hδ0 : (0 : ℝ) ≤ 1 / (20 * (w : ℝ)) := by positivity
  have hδ1 : (1 : ℝ) / (20 * (w : ℝ)) ≤ 1 := by
    have hwOne : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hden : (1 : ℝ) ≤ 20 * (w : ℝ) := by nlinarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hbound := hastadSwitchingLemma (k := d) hδ0 hδ1 hf
  calc
    switchingFailureProbability f (1 / (20 * (w : ℝ))) d ≤
        (5 * (1 / (20 * (w : ℝ))) * (w : ℝ)) ^ d := hbound
    _ = (1 / 4 : ℝ) ^ d := by
      congr 1
      field_simp
      norm_num

/-- A constant Boolean function has no Fourier weight above degree zero. -/
theorem isFourierSpectrumConcentratedUpTo_zero_of_constant
    (f : BooleanFunction n) (hconstant : ∀ x y, f x = f y)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε 0 := by
  classical
  unfold IsFourierSpectrumConcentratedUpTo fourierWeightAboveReal fourierWeight
  calc
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
        (0 : ℝ) < (S.card : ℝ)), fourierCoeff f.toReal S ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hcard : 0 < S.card := by
        exact_mod_cast (Finset.mem_filter.mp hS).2
      have hSempty : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp hcard)
      have hfunction : f.toReal = fun _ ↦ f.toReal default := by
        funext x
        simp only [BooleanFunction.toReal]
        rw [hconstant x default]
      rw [hfunction]
      unfold fourierCoeff
      rw [← Finset.mul_expect, expect_monomial, if_neg hSempty]
      simp
    _ ≤ ε := hε

/-- Positive-width form of Theorem 4.22. -/
theorem theorem4_22_of_pos
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w) (hf : HasDNFWidthLE f w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε
      (30 * (w : ℝ) * dnfSwitchingDepth ε) := by
  exact theorem4_22_of_switchingFailureProbability_le_half_pow
    f hw hε0 hε1 (hastadHalfSwitchingBound f hw (Or.inl hf))

/-- O'Donnell, Theorem 4.22, with an explicit natural degree cutoff and the constant
width-zero endpoint included. -/
theorem theorem4_22
    (f : BooleanFunction n) {w : ℕ} (hf : HasDNFWidthLE f w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsFourierSpectrumConcentratedUpTo f.toReal ε
      (30 * (w : ℝ) * dnfSwitchingDepth ε) := by
  by_cases hwzero : w = 0
  · obtain ⟨φ, hφwidth, rfl⟩ := hf
    have hφzero : φ.width = 0 := Nat.eq_zero_of_le_zero (hwzero ▸ hφwidth)
    simpa [hwzero] using
      (isFourierSpectrumConcentratedUpTo_zero_of_constant φ.toBooleanFunction
        (φ.toBooleanFunction_eq_of_width_eq_zero hφzero) hε0.le)
  · exact theorem4_22_of_pos f (Nat.pos_of_ne_zero hwzero) hf hε0 hε1

/-- O'Donnell, Theorem 4.24, with the necessary endpoint condition `w > 0`. -/
theorem theorem4_24
    (f : BooleanFunction n) {w : ℕ} (hw : 0 < w) (hf : HasDNFWidthLE f w)
    (k : ℕ) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card ≤ k),
      |fourierCoeff f.toReal S|) ≤ 2 * (20 * (w : ℝ)) ^ k := by
  exact theorem4_24_of_switchingFailureProbability_le_quarter f hw k
    (hastadQuarterSwitchingBoundForFormula f hw (Or.inl hf))

/-- O'Donnell, Theorem 4.25, with the proof's finite concentrating family and explicit
cardinality bound. -/
theorem theorem4_25
    (f : BooleanFunction n) {w : ℕ} (hw : 2 ≤ w) (hf : HasDNFWidthLE f w)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ 𝓕 : Finset (Finset (Fin n)),
      IsFourierSpectrumConcentratedOn f.toReal ε
        (↑𝓕 : Set (Finset (Fin n))) ∧
      (𝓕.card : ℝ) ≤ dnfSpectralFamilySizeBound w ε := by
  have hw0 : 0 < w := by omega
  exact theorem4_25_of_switchingFailureProbability_bounds f hw0 hε0 hε1
    (hastadHalfSwitchingBound f hw0 (Or.inl hf))
    (hastadQuarterSwitchingBoundForFormula f hw0 (Or.inl hf))

end FABL
