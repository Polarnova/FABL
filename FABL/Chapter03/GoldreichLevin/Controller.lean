/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevin.PrefixBuckets

/-!
# The pure Goldreich-Levin controller

Book item supported: Goldreich--Levin Theorem.

The capped controller and its local-accuracy invariants.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance glControllerSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance glControllerSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Pure capped Goldreich-Levin controller -/

/-- A rational estimate for every restricted Fourier bucket. -/
abbrev RestrictedFourierWeightEstimate (n : ℕ) :=
  (J : Finset (Fin n)) → Finset J → ℚ

/-- Every bucket estimate is strictly accurate to within `τ²/4`. -/
def IsAccurateRestrictedFourierWeightEstimate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n) : Prop :=
  ∀ J S,
    |(estimate J S : ℝ) - restrictedFourierWeight target.toReal J S| <
      (τ.1 : ℝ) ^ 2 / 4

/-- The two child prefixes obtained by deciding whether the next coordinate is present. -/
def goldreichLevinChildren (i : Fin n) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  {S, insert i S}

/-- All children produced by splitting the current active prefix family. -/
def goldreichLevinCandidates (i : Fin n)
    (active : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  active.biUnion (goldreichLevinChildren i)

/-- Characterization of membership among the two children of active prefixes. -/
theorem mem_goldreichLevinCandidates_iff (i : Fin n)
    (active : Finset (Finset (Fin n))) (T : Finset (Fin n)) :
    T ∈ goldreichLevinCandidates i active ↔
      ∃ S ∈ active, T = S ∨ T = insert i S := by
  simp [goldreichLevinCandidates, goldreichLevinChildren]

/-- Splitting prefixes supported on the first `k` coordinates produces prefixes supported on
the first `k+1` coordinates. -/
theorem goldreichLevinCandidates_subset_prefixCoordinates_succ
    {k : ℕ} (hk : k < n) (active : Finset (Finset (Fin n)))
    (hactive : ∀ S ∈ active, S ⊆ prefixCoordinates n k) :
    ∀ T ∈ goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active,
      T ⊆ prefixCoordinates n (k + 1) := by
  intro T hT
  obtain ⟨S, hS, hTform⟩ :=
    (mem_goldreichLevinCandidates_iff ⟨k, hk⟩ active T).mp hT
  rcases hTform with hTform | hTform
  · subst T
    rw [prefixCoordinates_succ hk]
    exact (hactive S hS).trans (Finset.subset_insert _ _)
  · subst T
    rw [prefixCoordinates_succ hk]
    exact Finset.insert_subset_insert _ (hactive S hS)

/-- Children whose estimated bucket weight exceeds `τ²/2`. -/
def goldreichLevinRetained
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  let J := prefixCoordinates n (k + 1)
  (goldreichLevinCandidates ⟨k, hk⟩ active).filter fun S ↦
    τ.1 ^ 2 / 2 < estimate J (freeFrequencyPart J S)

/-- One capped refinement step; `none` is an explicit overflow abort. -/
def goldreichLevinRefine
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n))) :
    Option (Finset (Finset (Fin n))) :=
  let retained := goldreichLevinRetained τ estimate k hk active
  if retained.card ≤ goldreichLevinActiveCap τ then some retained else none

/-- Run the pure capped prefix controller through the first `k` coordinates. -/
def goldreichLevinRunUpTo
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n) :
    (k : ℕ) → k ≤ n → Option (Finset (Finset (Fin n)))
  | 0, _ => some {∅}
  | k + 1, hk =>
      match goldreichLevinRunUpTo τ estimate k
          (Nat.le_trans (Nat.le_succ k) hk) with
      | none => none
      | some active => goldreichLevinRefine τ estimate k
          (Nat.lt_of_succ_le hk) active

/-- Final output of the pure capped controller after all coordinates. -/
def goldreichLevinOutput
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n) :
    Option (Finset (Finset (Fin n))) :=
  goldreichLevinRunUpTo τ estimate n le_rfl

/-- Under accurate estimates, every retained bucket has true weight strictly greater than
`τ²/4`. -/
theorem restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (S : Finset (Fin n))
    (hS : S ∈ goldreichLevinRetained τ estimate k hk active) :
    (τ.1 : ℝ) ^ 2 / 4 <
      restrictedFourierWeight target.toReal (prefixCoordinates n (k + 1))
        (freeFrequencyPart (prefixCoordinates n (k + 1)) S) := by
  let J := prefixCoordinates n (k + 1)
  let frequency := freeFrequencyPart J S
  have hthresholdRat : τ.1 ^ 2 / 2 < estimate J frequency :=
    (Finset.mem_filter.mp hS).2
  have hthreshold : (τ.1 : ℝ) ^ 2 / 2 < (estimate J frequency : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hthresholdRat
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hcast
    exact hcast
  have herror := haccurate J frequency
  rw [abs_lt] at herror
  nlinarith

/-- The next prefix of any frequency occurs among the children of its current prefix. -/
theorem prefixFrequency_succ_mem_goldreichLevinCandidates
    {k : ℕ} (hk : k < n) (U : Finset (Fin n))
    (active : Finset (Finset (Fin n)))
    (hprefix : prefixFrequency k U ∈ active) :
    prefixFrequency (k + 1) U ∈
      goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active := by
  rw [prefixFrequency_succ hk]
  split_ifs with hcoordinate
  · apply (mem_goldreichLevinCandidates_iff _ _ _).mpr
    exact ⟨prefixFrequency k U, hprefix, Or.inr rfl⟩
  · apply (mem_goldreichLevinCandidates_iff _ _ _).mpr
    exact ⟨prefixFrequency k U, hprefix, Or.inl rfl⟩

/-- A frequency of magnitude at least `τ` survives the next accurate refinement step. -/
theorem heavy_prefix_mem_goldreichLevinRetained
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (U : Finset (Fin n))
    (hheavy : (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U|)
    {k : ℕ} (hk : k < n) (active : Finset (Finset (Fin n)))
    (hprefix : prefixFrequency k U ∈ active) :
    prefixFrequency (k + 1) U ∈
      goldreichLevinRetained τ estimate k hk active := by
  let J := prefixCoordinates n (k + 1)
  let S := prefixFrequency (k + 1) U
  have hcandidates : S ∈ goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active :=
    prefixFrequency_succ_mem_goldreichLevinCandidates hk U active hprefix
  have hcontains : fourierCoeff target.toReal U ^ 2 ≤
      restrictedFourierWeight target.toReal J (freeFrequencyPart J S) := by
    apply sq_fourierCoeff_le_restrictedFourierWeight
    exact (freeFrequencyPart_prefixFrequency (k + 1) U).symm
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  have hcoeff : (τ.1 : ℝ) ^ 2 ≤ fourierCoeff target.toReal U ^ 2 := by
    have hsq := (sq_le_sq₀ hτpos.le (abs_nonneg _)).2 hheavy
    simpa [sq_abs] using hsq
  have herror := haccurate J (freeFrequencyPart J S)
  rw [abs_lt] at herror
  have hestimateReal :
      (τ.1 : ℝ) ^ 2 / 2 < (estimate J (freeFrequencyPart J S) : ℝ) := by
    nlinarith [sq_pos_of_pos hτpos]
  have hestimateRat :
      τ.1 ^ 2 / 2 < estimate J (freeFrequencyPart J S) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    exact hestimateReal
  exact Finset.mem_filter.mpr ⟨hcandidates, hestimateRat⟩

/-- Every successful controller state contains only prefixes supported on the coordinates
processed so far. -/
theorem goldreichLevinRunUpTo_prefixes
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n) :
    ∀ (k : ℕ) (hk : k ≤ n) (active : Finset (Finset (Fin n))),
      goldreichLevinRunUpTo τ estimate k hk = some active →
        ∀ S ∈ active, S ⊆ prefixCoordinates n k := by
  intro k
  induction k with
  | zero =>
      intro hk active hrun S hS
      simp [goldreichLevinRunUpTo] at hrun
      subst active
      have hSzero : S = ∅ := by simpa using hS
      subst S
      simp [prefixCoordinates]
  | succ k ih =>
      intro hk active hrun
      have hklt : k < n := Nat.lt_of_succ_le hk
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      cases hprevious : goldreichLevinRunUpTo τ estimate k hk' with
      | none =>
          simp [goldreichLevinRunUpTo, hprevious] at hrun
      | some previous =>
          have hpreviousPrefixes := ih hk' previous hprevious
          simp only [goldreichLevinRunUpTo, hprevious] at hrun
          let retained := goldreichLevinRetained τ estimate k hklt previous
          change (if retained.card ≤ goldreichLevinActiveCap τ then some retained else none) =
            some active at hrun
          by_cases hcap : retained.card ≤ goldreichLevinActiveCap τ
          · rw [if_pos hcap] at hrun
            simp only [Option.some.injEq] at hrun
            subst active
            intro S hS
            apply goldreichLevinCandidates_subset_prefixCoordinates_succ
              hklt previous hpreviousPrefixes S
            exact (Finset.mem_filter.mp hS).1
          · rw [if_neg hcap] at hrun
            contradiction

/-- Accurate estimates guarantee that the active cap never aborts the controller. -/
theorem goldreichLevinRunUpTo_exists_of_accurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate) :
    ∀ (k : ℕ) (hk : k ≤ n),
      ∃ active, goldreichLevinRunUpTo τ estimate k hk = some active := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact ⟨{∅}, rfl⟩
  | succ k ih =>
      intro hk
      have hklt : k < n := Nat.lt_of_succ_le hk
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨previous, hprevious⟩ := ih hk'
      let retained := goldreichLevinRetained τ estimate k hklt previous
      have hpreviousPrefixes := goldreichLevinRunUpTo_prefixes τ estimate
        k hk' previous hprevious
      have hretainedSubsets :
          ∀ S ∈ retained, S ⊆ prefixCoordinates n (k + 1) := by
        intro S hS
        apply goldreichLevinCandidates_subset_prefixCoordinates_succ
          hklt previous hpreviousPrefixes S
        exact (Finset.mem_filter.mp hS).1
      have hretainedWeight : ∀ S ∈ retained,
          ((τ.1 : ℝ) ^ 2 / 4) ≤
            restrictedFourierWeight target.toReal (prefixCoordinates n (k + 1))
              (freeFrequencyPart (prefixCoordinates n (k + 1)) S) := by
        intro S hS
        exact (restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained
          target τ estimate haccurate k hklt previous S hS).le
      have hcap : retained.card ≤ goldreichLevinActiveCap τ :=
        card_prefixes_le_goldreichLevinActiveCap target
          (prefixCoordinates n (k + 1)) retained τ
          hretainedSubsets hretainedWeight
      refine ⟨retained, ?_⟩
      simp only [goldreichLevinRunUpTo, hprevious]
      unfold goldreichLevinRefine
      rw [if_pos hcap]

/-- Under accurate estimates, every heavy frequency remains in every successful prefix state. -/
theorem heavy_prefix_mem_goldreichLevinRunUpTo
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (U : Finset (Fin n))
    (hheavy : (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U|) :
    ∀ (k : ℕ) (hk : k ≤ n) (active : Finset (Finset (Fin n))),
      goldreichLevinRunUpTo τ estimate k hk = some active →
        prefixFrequency k U ∈ active := by
  intro k
  induction k with
  | zero =>
      intro hk active hrun
      simp [goldreichLevinRunUpTo] at hrun
      subst active
      simp
  | succ k ih =>
      intro hk active hrun
      have hklt : k < n := Nat.lt_of_succ_le hk
      let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      cases hprevious : goldreichLevinRunUpTo τ estimate k hk' with
      | none =>
          simp [goldreichLevinRunUpTo, hprevious] at hrun
      | some previous =>
          have hprefix := ih hk' previous hprevious
          have hretained := heavy_prefix_mem_goldreichLevinRetained
            target τ estimate haccurate U hheavy hklt previous hprefix
          simp only [goldreichLevinRunUpTo, hprevious] at hrun
          let retained := goldreichLevinRetained τ estimate k hklt previous
          change (if retained.card ≤ goldreichLevinActiveCap τ then some retained else none) =
            some active at hrun
          by_cases hcap : retained.card ≤ goldreichLevinActiveCap τ
          · rw [if_pos hcap] at hrun
            simp only [Option.some.injEq] at hrun
            subst active
            exact hretained
          · rw [if_neg hcap] at hrun
            contradiction

/-- Every member of a noninitial successful state was retained in the final refinement step. -/
theorem mem_goldreichLevinRetained_of_runUpTo_succ
    (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    {k : ℕ} (hk : k + 1 ≤ n) (active : Finset (Finset (Fin n)))
    (hrun : goldreichLevinRunUpTo τ estimate (k + 1) hk = some active)
    {S : Finset (Fin n)} (hS : S ∈ active) :
    ∃ previous,
      S ∈ goldreichLevinRetained τ estimate k (Nat.lt_of_succ_le hk) previous := by
  let hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
  cases hprevious : goldreichLevinRunUpTo τ estimate k hk' with
  | none =>
      simp [goldreichLevinRunUpTo, hprevious] at hrun
  | some previous =>
      simp only [goldreichLevinRunUpTo, hprevious] at hrun
      let retained := goldreichLevinRetained τ estimate k (Nat.lt_of_succ_le hk) previous
      change (if retained.card ≤ goldreichLevinActiveCap τ then some retained else none) =
        some active at hrun
      by_cases hcap : retained.card ≤ goldreichLevinActiveCap τ
      · rw [if_pos hcap] at hrun
        simp only [Option.some.injEq] at hrun
        subst active
        exact ⟨previous, hS⟩
      · rw [if_neg hcap] at hrun
        contradiction

/-- Completeness of the pure Goldreich-Levin controller: every coefficient of magnitude at least
`τ` occurs in the output. -/
theorem goldreichLevinOutput_complete_of_accurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (active : Finset (Finset (Fin n)))
    (houtput : goldreichLevinOutput τ estimate = some active)
    (U : Finset (Fin n))
    (hheavy : (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U|) :
    U ∈ active := by
  have hprefix := heavy_prefix_mem_goldreichLevinRunUpTo
    target τ estimate haccurate U hheavy n le_rfl active (by
      simpa [goldreichLevinOutput] using houtput)
  simpa [prefixFrequency_eq_self (n := n) le_rfl U] using hprefix

/-- Soundness of the pure Goldreich-Levin controller: every output coefficient has magnitude
strictly greater than `τ/2`. -/
theorem goldreichLevinOutput_sound_of_accurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (active : Finset (Finset (Fin n)))
    (houtput : goldreichLevinOutput τ estimate = some active)
    (U : Finset (Fin n)) (hU : U ∈ active) :
    (τ.1 : ℝ) / 2 < |fourierCoeff target.toReal U| := by
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  cases n with
  | zero =>
      have hUempty : U = ∅ := by
        ext i
        exact Fin.elim0 i
      subst U
      have hparseval := sum_sq_fourierCoeff_eq_one target
      have hsq : fourierCoeff target.toReal ∅ ^ 2 = 1 := by
        simpa using hparseval
      have habs : |fourierCoeff target.toReal ∅| = 1 := by
        nlinarith [sq_abs (fourierCoeff target.toReal ∅),
          abs_nonneg (fourierCoeff target.toReal ∅)]
      have hτle : (τ.1 : ℝ) ≤ 1 := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr τ.2.2
        norm_num at hcast
        exact hcast
      rw [habs]
      nlinarith
  | succ k =>
      have hrun : goldreichLevinRunUpTo τ estimate (k + 1) le_rfl = some active := by
        simpa [goldreichLevinOutput] using houtput
      obtain ⟨previous, hretained⟩ :=
        mem_goldreichLevinRetained_of_runUpTo_succ τ estimate le_rfl active hrun hU
      have hweight :=
        restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained
          target τ estimate haccurate k (by omega) previous U hretained
      rw [prefixCoordinates_eq_univ (n := k + 1) le_rfl,
        restrictedFourierWeight_univ_freeFrequencyPart] at hweight
      have hsquare : ((τ.1 : ℝ) / 2) ^ 2 <
          |fourierCoeff target.toReal U| ^ 2 := by
        rw [sq_abs]
        nlinarith
      exact (sq_lt_sq₀ (div_nonneg hτpos.le (by norm_num)) (abs_nonneg _)).mp hsquare

/-- Accurate estimates guarantee that the final capped controller returns a finite list. -/
theorem goldreichLevinOutput_exists_of_accurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate) :
    ∃ active, goldreichLevinOutput τ estimate = some active := by
  simpa [goldreichLevinOutput] using
    goldreichLevinRunUpTo_exists_of_accurate target τ estimate haccurate n le_rfl

/-- Parseval's output-size bound `|L| ≤ 4/τ²` for the pure controller. -/
theorem goldreichLevinOutput_card_le
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (active : Finset (Finset (Fin n)))
    (houtput : goldreichLevinOutput τ estimate = some active) :
    (active.card : ℝ) ≤ 4 / (τ.1 : ℝ) ^ 2 := by
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  have hterm : ∀ U ∈ active,
      (τ.1 : ℝ) ^ 2 / 4 ≤ fourierCoeff target.toReal U ^ 2 := by
    intro U hU
    have hsound := goldreichLevinOutput_sound_of_accurate
      target τ estimate haccurate active houtput U hU
    have hsquare := (sq_le_sq₀
      (div_nonneg hτpos.le (by norm_num)) (abs_nonneg _)).2 hsound.le
    rw [sq_abs] at hsquare
    nlinarith
  have hsum :
      (∑ U ∈ active, fourierCoeff target.toReal U ^ 2) ≤ 1 := by
    calc
      (∑ U ∈ active, fourierCoeff target.toReal U ^ 2) ≤
          ∑ U : Finset (Fin n), fourierCoeff target.toReal U ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
          (fun U _ _ ↦ sq_nonneg (fourierCoeff target.toReal U))
      _ = 1 := sum_sq_fourierCoeff_eq_one target
  have hcardMul : (active.card : ℝ) * ((τ.1 : ℝ) ^ 2 / 4) ≤ 1 := by
    calc
      (active.card : ℝ) * ((τ.1 : ℝ) ^ 2 / 4) =
          ∑ _U ∈ active, ((τ.1 : ℝ) ^ 2 / 4) := by simp
      _ ≤ ∑ U ∈ active, fourierCoeff target.toReal U ^ 2 :=
        Finset.sum_le_sum hterm
      _ ≤ 1 := hsum
  rw [le_div_iff₀ (sq_pos_of_pos hτpos)]
  nlinarith

/-! ## Local-accuracy controller invariants -/

/-- Splitting each active prefix into at most two children creates at most twice as many
candidate prefixes. -/
theorem card_goldreichLevinCandidates_le_two_mul
    (i : Fin n) (active : Finset (Finset (Fin n))) :
    (goldreichLevinCandidates i active).card ≤ 2 * active.card := by
  unfold goldreichLevinCandidates
  calc
    (active.biUnion (goldreichLevinChildren i)).card ≤
        ∑ S ∈ active, (goldreichLevinChildren i S).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ active, 2 := by
      apply Finset.sum_le_sum
      intro S _
      simpa [goldreichLevinChildren] using
        (Finset.card_insert_le S ({insert i S} : Finset (Finset (Fin n))))
    _ = 2 * active.card := by simp [mul_comm]

/-- Accuracy only for the candidate buckets actually estimated during one refinement stage. -/
def IsAccurateGoldreichLevinStage
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n))) : Prop :=
  let J := prefixCoordinates n (k + 1)
  ∀ S ∈ goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active,
    |(estimate J (freeFrequencyPart J S) : ℝ) -
        restrictedFourierWeight target.toReal J (freeFrequencyPart J S)| <
      (τ.1 : ℝ) ^ 2 / 4

/-- Global estimator accuracy implies the local accuracy required at every stage. -/
theorem isAccurateGoldreichLevinStage_of_isAccurateRestrictedFourierWeightEstimate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (haccurate : IsAccurateRestrictedFourierWeightEstimate target τ estimate)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n))) :
    IsAccurateGoldreichLevinStage target τ estimate k hk active := by
  intro S _
  exact haccurate (prefixCoordinates n (k + 1))
    (freeFrequencyPart (prefixCoordinates n (k + 1)) S)

/-- Local stage accuracy certifies the true weight of every retained child. -/
theorem restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained_of_stageAccurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (haccurate : IsAccurateGoldreichLevinStage target τ estimate k hk active)
    (S : Finset (Fin n))
    (hS : S ∈ goldreichLevinRetained τ estimate k hk active) :
    (τ.1 : ℝ) ^ 2 / 4 <
      restrictedFourierWeight target.toReal (prefixCoordinates n (k + 1))
        (freeFrequencyPart (prefixCoordinates n (k + 1)) S) := by
  let J := prefixCoordinates n (k + 1)
  let frequency := freeFrequencyPart J S
  have hcandidates :
      S ∈ goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active :=
    (Finset.mem_filter.mp hS).1
  have hthresholdRat : τ.1 ^ 2 / 2 < estimate J frequency :=
    (Finset.mem_filter.mp hS).2
  have hthreshold : (τ.1 : ℝ) ^ 2 / 2 < (estimate J frequency : ℝ) := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hthresholdRat
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hcast
    exact hcast
  have herror :
      |(estimate J frequency : ℝ) -
          restrictedFourierWeight target.toReal J frequency| <
        (τ.1 : ℝ) ^ 2 / 4 :=
    haccurate S hcandidates
  rw [abs_lt] at herror
  nlinarith

/-- Local accuracy on the current candidate family makes a heavy frequency's next prefix
survive. -/
theorem heavy_prefix_mem_goldreichLevinRetained_of_stageAccurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (U : Finset (Fin n))
    (hheavy : (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U|)
    {k : ℕ} (hk : k < n) (active : Finset (Finset (Fin n)))
    (haccurate : IsAccurateGoldreichLevinStage target τ estimate k hk active)
    (hprefix : prefixFrequency k U ∈ active) :
    prefixFrequency (k + 1) U ∈
      goldreichLevinRetained τ estimate k hk active := by
  let J := prefixCoordinates n (k + 1)
  let S := prefixFrequency (k + 1) U
  have hcandidates : S ∈ goldreichLevinCandidates (⟨k, hk⟩ : Fin n) active :=
    prefixFrequency_succ_mem_goldreichLevinCandidates hk U active hprefix
  have hcontains : fourierCoeff target.toReal U ^ 2 ≤
      restrictedFourierWeight target.toReal J (freeFrequencyPart J S) := by
    apply sq_fourierCoeff_le_restrictedFourierWeight
    exact (freeFrequencyPart_prefixFrequency (k + 1) U).symm
  have hτpos : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  have hcoeff : (τ.1 : ℝ) ^ 2 ≤ fourierCoeff target.toReal U ^ 2 := by
    have hsq := (sq_le_sq₀ hτpos.le (abs_nonneg _)).2 hheavy
    simpa [sq_abs] using hsq
  have herror :
      |(estimate J (freeFrequencyPart J S) : ℝ) -
          restrictedFourierWeight target.toReal J (freeFrequencyPart J S)| <
        (τ.1 : ℝ) ^ 2 / 4 :=
    haccurate S hcandidates
  rw [abs_lt] at herror
  have hestimateReal :
      (τ.1 : ℝ) ^ 2 / 2 < (estimate J (freeFrequencyPart J S) : ℝ) := by
    nlinarith [sq_pos_of_pos hτpos]
  have hestimateRat :
      τ.1 ^ 2 / 2 < estimate J (freeFrequencyPart J S) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    exact hestimateReal
  exact Finset.mem_filter.mpr ⟨hcandidates, hestimateRat⟩

/-- The controller invariant at level `k`: active sets are genuine `k`-prefixes, every heavy
frequency's `k`-prefix is active, and every noninitial active bucket has true weight above
`τ²/4`. -/
def GoldreichLevinActiveInvariant
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (k : ℕ) (active : Finset (Finset (Fin n))) : Prop :=
  (∀ S ∈ active, S ⊆ prefixCoordinates n k) ∧
  (∀ U : Finset (Fin n),
    (τ.1 : ℝ) ≤ |fourierCoeff target.toReal U| →
      prefixFrequency k U ∈ active) ∧
  (∀ (_hkpos : 0 < k) (S : Finset (Fin n)), S ∈ active →
    (τ.1 : ℝ) ^ 2 / 4 <
      restrictedFourierWeight target.toReal (prefixCoordinates n k)
        (freeFrequencyPart (prefixCoordinates n k) S))

/-- The singleton root bucket satisfies the level-zero invariant. -/
theorem goldreichLevinActiveInvariant_zero
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold) :
    GoldreichLevinActiveInvariant target τ 0 {∅} := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    have hSempty : S = ∅ := by simpa using hS
    subst S
    simp
  · intro U _
    simp
  · intro hkpos
    omega

/-- One locally accurate stage preserves the active-prefix invariant before applying the cap. -/
theorem goldreichLevinActiveInvariant_retained
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ k active)
    (haccurate : IsAccurateGoldreichLevinStage target τ estimate k hk active) :
    GoldreichLevinActiveInvariant target τ (k + 1)
      (goldreichLevinRetained τ estimate k hk active) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    apply goldreichLevinCandidates_subset_prefixCoordinates_succ
      hk active hinvariant.1 S
    exact (Finset.mem_filter.mp hS).1
  · intro U hheavy
    apply heavy_prefix_mem_goldreichLevinRetained_of_stageAccurate
      target τ estimate U hheavy hk active haccurate
    exact hinvariant.2.1 U hheavy
  · intro _ S hS
    exact restrictedFourierWeight_gt_quarter_of_mem_goldreichLevinRetained_of_stageAccurate
      target τ estimate k hk active haccurate S hS

/-- The retained family from a locally accurate stage satisfies the executable active cap. -/
theorem card_goldreichLevinRetained_le_activeCap_of_stageAccurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ k active)
    (haccurate : IsAccurateGoldreichLevinStage target τ estimate k hk active) :
    (goldreichLevinRetained τ estimate k hk active).card ≤
      goldreichLevinActiveCap τ := by
  let retained := goldreichLevinRetained τ estimate k hk active
  have hnext := goldreichLevinActiveInvariant_retained
    target τ estimate k hk active hinvariant haccurate
  apply card_prefixes_le_goldreichLevinActiveCap target
    (prefixCoordinates n (k + 1)) retained τ hnext.1
  intro S hS
  exact (hnext.2.2 (by omega) S hS).le

/-- Hence a locally accurate stage cannot take the overflow-abort branch. -/
theorem goldreichLevinRefine_eq_some_retained_of_stageAccurate
    (target : BooleanFunction n) (τ : GoldreichLevinThreshold)
    (estimate : RestrictedFourierWeightEstimate n)
    (k : ℕ) (hk : k < n) (active : Finset (Finset (Fin n)))
    (hinvariant : GoldreichLevinActiveInvariant target τ k active)
    (haccurate : IsAccurateGoldreichLevinStage target τ estimate k hk active) :
    goldreichLevinRefine τ estimate k hk active =
      some (goldreichLevinRetained τ estimate k hk active) := by
  unfold goldreichLevinRefine
  rw [if_pos (card_goldreichLevinRetained_le_activeCap_of_stageAccurate
    target τ estimate k hk active hinvariant haccurate)]

end FABL
