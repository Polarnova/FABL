/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.KushilevitzMansour
public import FABL.Chapter06.LearningAndTesting.RestrictedWeightAlgorithm
public import FABL.Chapter06.LearningAndTesting.SmallBiasFourierAlgorithm

/-!
# Deterministic Goldreich--Levin learning

Book item: O'Donnell, Theorem 6.42.

The randomized estimators in the Chapter 3 Goldreich--Levin and
Kushilevitz--Mansour pipeline are replaced by Propositions 6.41 and 6.40.
The prefix controller, its active-family invariant, the concentration
argument, and the finite sparse Fourier hypothesis are reused unchanged.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Finite input and derived estimator accuracies -/

/-- Finite input for Theorem 6.42.  The learning error is the positive
rational encoded by `accuracy`; `fourierBound` is the promised integral
upper bound for the Fourier `1`-norm. -/
structure DeterministicGoldreichLevinInput where
  /-- Dimension and positive rational learning error. -/
  accuracy : SmallBiasInput
  /-- Integral Fourier `1`-norm bound. -/
  fourierBound : ℕ
  /-- The Fourier bound is at least one. -/
  fourierBound_pos : 1 ≤ fourierBound

namespace DeterministicGoldreichLevinInput

/-- The positive rational learning parameter encoded by the finite input. -/
def learningParameter (input : DeterministicGoldreichLevinInput) :
    PositiveLearningParameter := by
  have hdenNat : 0 < input.accuracy.denominator := by
    have htwo : 0 < 2 * input.accuracy.numerator :=
      Nat.mul_pos (by omega) input.accuracy.numerator_pos
    exact htwo.trans_le input.accuracy.twice_numerator_le_denominator
  have hnum : (0 : ℚ) < input.accuracy.numerator := by
    exact_mod_cast input.accuracy.numerator_pos
  have hden : (0 : ℚ) < input.accuracy.denominator := by
    exact_mod_cast hdenNat
  refine ⟨input.accuracy.numerator / input.accuracy.denominator,
    div_pos hnum hden, ?_⟩
  rw [div_le_iff₀ hden]
  have hhalf :
      (2 : ℚ) * input.accuracy.numerator ≤ input.accuracy.denominator := by
    exact_mod_cast input.accuracy.twice_numerator_le_denominator
  nlinarith

/-- The real value of the learning parameter is the input's encoded error. -/
theorem learningParameter_cast (input : DeterministicGoldreichLevinInput) :
    (((input.learningParameter.1 : ℚ) : ℝ)) = input.accuracy.epsilon := by
  simp [learningParameter, SmallBiasInput.epsilon]

/-- The concentrating-family bound reused from Theorem 3.38. -/
noncomputable def familySizeBound
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  fourierOneNormFamilySizeBound (input.fourierBound : ℝ)
    input.learningParameter

theorem familySizeBound_pos (input : DeterministicGoldreichLevinInput) :
    0 < input.familySizeBound :=
  fourierOneNormFamilySizeBound_pos _ _

/-- The exact Kushilevitz--Mansour threshold used by the existing controller. -/
noncomputable def threshold
    (input : DeterministicGoldreichLevinInput) : GoldreichLevinThreshold :=
  kushilevitzMansourThreshold input.learningParameter input.familySizeBound
    input.familySizeBound_pos

/-- Accuracy `τ²/8` for every deterministic restricted-weight call. -/
noncomputable def restrictedWeightBias
    (input : DeterministicGoldreichLevinInput) : SmallBiasInput where
  n := input.accuracy.n
  numerator := input.accuracy.numerator ^ 2
  denominator :=
    8 * (4 * input.familySizeBound * input.accuracy.denominator) ^ 2
  n_pos := input.accuracy.n_pos
  numerator_pos := pow_pos input.accuracy.numerator_pos _
  twice_numerator_le_denominator := by
    have ha_le_b : input.accuracy.numerator ≤ input.accuracy.denominator := by
      exact (Nat.le_mul_of_pos_left input.accuracy.numerator
        (by norm_num : 0 < 2)).trans
          input.accuracy.twice_numerator_le_denominator
    have hM : 1 ≤ input.familySizeBound := input.familySizeBound_pos
    have hb_le : input.accuracy.denominator ≤
        4 * input.familySizeBound * input.accuracy.denominator := by
      simpa [one_mul] using Nat.mul_le_mul_right input.accuracy.denominator
        (show 1 ≤ 4 * input.familySizeBound by omega)
    have hsq : input.accuracy.numerator ^ 2 ≤
        (4 * input.familySizeBound * input.accuracy.denominator) ^ 2 :=
      Nat.pow_le_pow_left (ha_le_b.trans hb_le) 2
    have htwice := Nat.mul_le_mul_left 2 hsq
    omega

/-- The restricted-weight input used at every prefix bucket. -/
noncomputable def restrictedWeightInput
    (input : DeterministicGoldreichLevinInput) : RestrictedWeightInput where
  bias := input.restrictedWeightBias
  fourierBound := input.fourierBound
  fourierBound_pos := input.fourierBound_pos

/-- The selected restricted-weight error is exactly `τ²/8`. -/
theorem restrictedWeightInput_epsilon
    (input : DeterministicGoldreichLevinInput) :
    input.restrictedWeightInput.epsilon =
      (input.threshold.1 : ℝ) ^ 2 / 8 := by
  have hdenNat : input.accuracy.denominator ≠ 0 := by
    have htwo : 0 < 2 * input.accuracy.numerator :=
      Nat.mul_pos (by omega) input.accuracy.numerator_pos
    exact (htwo.trans_le
      input.accuracy.twice_numerator_le_denominator).ne'
  have hM : input.familySizeBound ≠ 0 := input.familySizeBound_pos.ne'
  simp only [restrictedWeightInput, RestrictedWeightInput.epsilon,
    restrictedWeightBias, SmallBiasInput.epsilon, threshold,
    kushilevitzMansourThreshold, learningParameter]
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat]
  field_simp
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Accuracy `ε/(2K)` for the final coefficient estimates, where `K` is
the controller's active-family cap. -/
noncomputable abbrev coefficientBias
    (input : DeterministicGoldreichLevinInput) : SmallBiasInput where
  n := input.accuracy.n
  numerator := input.accuracy.numerator
  denominator := input.accuracy.denominator *
    (2 * goldreichLevinActiveCap input.threshold)
  n_pos := input.accuracy.n_pos
  numerator_pos := input.accuracy.numerator_pos
  twice_numerator_le_denominator := by
    have hcap : 1 ≤ goldreichLevinActiveCap input.threshold :=
      goldreichLevinActiveCap_pos input.threshold
    calc
      2 * input.accuracy.numerator ≤ input.accuracy.denominator :=
        input.accuracy.twice_numerator_le_denominator
      _ ≤ input.accuracy.denominator *
          (2 * goldreichLevinActiveCap input.threshold) := by
        simpa [mul_one] using Nat.mul_le_mul_left input.accuracy.denominator
          (show 1 ≤ 2 * goldreichLevinActiveCap input.threshold by omega)

/-- Proposition 6.40 input for the final finite coefficient family. -/
noncomputable abbrev coefficientInput
    (input : DeterministicGoldreichLevinInput) : SmallBiasFourierInput where
  bias := input.coefficientBias
  fourierBound := input.fourierBound
  fourierBound_pos := input.fourierBound_pos

/-- The final coefficient accuracy is exactly `ε/(2K)`. -/
theorem coefficientInput_epsilon
    (input : DeterministicGoldreichLevinInput) :
    input.coefficientInput.epsilon =
      (input.learningParameter.1 : ℝ) /
        (2 * goldreichLevinActiveCap input.threshold) := by
  have hdenNat : input.accuracy.denominator ≠ 0 := by
    have htwo : 0 < 2 * input.accuracy.numerator :=
      Nat.mul_pos (by omega) input.accuracy.numerator_pos
    exact (htwo.trans_le
      input.accuracy.twice_numerator_le_denominator).ne'
  have hcap : goldreichLevinActiveCap input.threshold ≠ 0 :=
    (goldreichLevinActiveCap_pos input.threshold).ne'
  simp only [SmallBiasFourierInput.epsilon, SmallBiasInput.epsilon,
    learningParameter]
  norm_num only [Rat.cast_div, Rat.cast_natCast]
  field_simp
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  ring

end DeterministicGoldreichLevinInput

/-! ## Rational adapters for Propositions 6.41 and 6.40 -/

/-- Rational form of a subset-indexed Walsh monomial. -/
def rationalIndexedMonomial {ι : Type*}
    (S : Finset ι) (x : IndexedSignCube ι) : ℚ :=
  ∏ i ∈ S, (((x i : Sign) : ℤ) : ℚ)

@[simp] theorem rationalIndexedMonomial_cast {ι : Type*}
    (S : Finset ι) (x : IndexedSignCube ι) :
    (rationalIndexedMonomial S x : ℝ) = indexedMonomial S x := by
  simp [rationalIndexedMonomial, indexedMonomial, signValue]

/-- Exact rational value computed from Proposition 6.41's Boolean answer batch. -/
noncomputable def rationalRestrictedFourierWeightEstimateFromAnswers
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (answers : Fin (deterministicRestrictedWeightQueryCount input) → Sign) : ℚ :=
  (∑ o : Fin input.outerInput.sampleCount,
      ((∑ i : Fin input.innerInput.sampleCount,
          (((answers
              (finProdFinEquiv (m := input.outerInput.sampleCount)
                (n := input.innerInput.sampleCount) (o, i)) : Sign) : ℤ) : ℚ) *
            rationalIndexedMonomial S
              (restrictedWeightFreeAssignment input J i)) /
        input.innerInput.sampleCount) ^ 2) /
    input.outerInput.sampleCount

/-- Casting the rational Boolean estimator gives Proposition 6.41's real output. -/
theorem rationalRestrictedFourierWeightEstimateFromAnswers_cast
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (answers : Fin (deterministicRestrictedWeightQueryCount input) → Sign) :
    (rationalRestrictedFourierWeightEstimateFromAnswers input J S answers : ℝ) =
      deterministicRestrictedWeightEstimateFromAnswers input J S answers := by
  simp [rationalRestrictedFourierWeightEstimateFromAnswers,
    deterministicRestrictedWeightEstimateFromAnswers,
    Fintype.expect_eq_sum_div_card, signValue]

/-- On a Boolean oracle, the rational adapter is exactly the proved real
restricted-weight estimate. -/
theorem rationalRestrictedFourierWeightEstimateFromOracle_cast
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J) :
    (rationalRestrictedFourierWeightEstimateFromAnswers input J S
        (fun q ↦ target (deterministicRestrictedWeightQueryPoint input J q)) : ℝ) =
      restrictedFourierWeightEstimate input target J S := by
  rw [rationalRestrictedFourierWeightEstimateFromAnswers_cast]
  simp [deterministicRestrictedWeightEstimateFromAnswers,
    deterministicRestrictedWeightQueryPoint,
    deterministicRestrictedWeightQueryPair,
    restrictedFourierWeightEstimate,
    restrictedFourierCoefficientEstimate,
    BooleanFunction.toReal]

/-- Rational coefficient produced from Proposition 6.40's deterministic sample. -/
def rationalSmallBiasFourierEstimate
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n))
    (answers : Fin input.sampleCount → Sign) : ℚ :=
  empiricalFourierCoeff U fun i ↦
    (binaryCubeSignEquiv input.generatorInput.n (input.sample i), answers i)

/-- The Boolean specialization casts to Proposition 6.40's real estimator. -/
theorem rationalSmallBiasFourierEstimate_cast
    (input : SmallBiasFourierInput)
    (target : BooleanFunction input.generatorInput.n)
    (U : Finset (Fin input.generatorInput.n)) :
    (rationalSmallBiasFourierEstimate input U
        (fun i ↦ target
          (binaryCubeSignEquiv input.generatorInput.n (input.sample i))) : ℝ) =
      smallBiasFourierEstimate target.toReal input.sample U := by
  rw [rationalSmallBiasFourierEstimate, empiricalFourierCoeff_cast]
  simp [realEmpiricalFourierCoeff, smallBiasFourierEstimate,
    fourierObservation, BooleanFunction.toReal]

/-! ## Deterministic execution of the Chapter 3 prefix controller -/

/-- Records for one controller stage, computed from one Proposition 6.41
answer batch for every current candidate prefix. -/
noncomputable def deterministicGoldreichLevinStageRecordsFromAnswers
    (input : DeterministicGoldreichLevinInput)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n)))
    (answers : Fin (deterministicRestrictedWeightQueryCount
      input.restrictedWeightInput) → Sign) :
    List (GoldreichLevinEstimateRecord input.accuracy.n) :=
  let J := prefixCoordinates input.accuracy.n (k + 1)
  (goldreichLevinCandidates
      (⟨k, hk⟩ : Fin input.accuracy.n) active).toList.map
    fun frequencyPrefix ↦
      ⟨J, frequencyPrefix,
        rationalRestrictedFourierWeightEstimateFromAnswers
          input.restrictedWeightInput J
          (freeFrequencyPart J frequencyPrefix) answers⟩

/-- The records produced at a stage against the target oracle. -/
noncomputable def deterministicGoldreichLevinStageRecords
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    List (GoldreichLevinEstimateRecord input.accuracy.n) :=
  deterministicGoldreichLevinStageRecordsFromAnswers input k hk active
    (fun q ↦ target
      (deterministicRestrictedWeightQueryPoint
        input.restrictedWeightInput
        (prefixCoordinates input.accuracy.n (k + 1)) q))

/-- Every deterministic stage record is strictly accurate enough for the
unchanged Goldreich--Levin controller. -/
theorem deterministicGoldreichLevinStageRecords_isAccurate
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    GoldreichLevinEstimateTrace.IsAccurate
      (deterministicGoldreichLevinStageRecords input target k hk active)
      target input.threshold := by
  intro record hrecord
  rw [deterministicGoldreichLevinStageRecords,
    deterministicGoldreichLevinStageRecordsFromAnswers,
    List.mem_map] at hrecord
  obtain ⟨frequencyPrefix, hfrequency, rfl⟩ := hrecord
  let J := prefixCoordinates input.accuracy.n (k + 1)
  let S := freeFrequencyPart J frequencyPrefix
  have hestimate := abs_restrictedFourierWeightEstimate_sub_le
    input.restrictedWeightInput target J S hnorm
  have hcast := rationalRestrictedFourierWeightEstimateFromOracle_cast
    input.restrictedWeightInput target J S
  unfold GoldreichLevinEstimateRecord.IsAccurate
  change
    |(rationalRestrictedFourierWeightEstimateFromAnswers
        input.restrictedWeightInput J S
        (fun q ↦ target
          (deterministicRestrictedWeightQueryPoint
            input.restrictedWeightInput J q)) : ℝ) -
      restrictedFourierWeight target.toReal J S| <
        (input.threshold.1 : ℝ) ^ 2 / 4
  rw [hcast, abs_sub_comm]
  calc
    |restrictedFourierWeight target.toReal J S -
        restrictedFourierWeightEstimate
          input.restrictedWeightInput target J S| ≤
        input.restrictedWeightInput.epsilon := hestimate
    _ = (input.threshold.1 : ℝ) ^ 2 / 8 :=
      input.restrictedWeightInput_epsilon
    _ < (input.threshold.1 : ℝ) ^ 2 / 4 := by
      have hτ : (0 : ℝ) < (input.threshold.1 : ℝ) :=
        Rat.cast_pos.mpr input.threshold.2.1
      nlinarith [sq_pos_of_pos hτ]

/-- The deterministic record list contains one matching record for every
candidate requested by the controller. -/
theorem deterministicGoldreichLevinStageRecords_covers
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    GoldreichLevinEstimateTrace.Covers
      (deterministicGoldreichLevinStageRecords input target k hk active)
      (prefixCoordinates input.accuracy.n (k + 1))
      (goldreichLevinCandidates
        (⟨k, hk⟩ : Fin input.accuracy.n) active) := by
  intro frequencyPrefix hfrequency
  refine ⟨⟨prefixCoordinates input.accuracy.n (k + 1), frequencyPrefix,
      rationalRestrictedFourierWeightEstimateFromAnswers
        input.restrictedWeightInput
        (prefixCoordinates input.accuracy.n (k + 1))
        (freeFrequencyPart
          (prefixCoordinates input.accuracy.n (k + 1)) frequencyPrefix)
        (fun q ↦ target
          (deterministicRestrictedWeightQueryPoint
            input.restrictedWeightInput
            (prefixCoordinates input.accuracy.n (k + 1)) q))⟩, ?_, ?_⟩
  · rw [deterministicGoldreichLevinStageRecords,
      deterministicGoldreichLevinStageRecordsFromAnswers, List.mem_map]
    exact ⟨frequencyPrefix, by simpa using hfrequency, rfl⟩
  · simp [GoldreichLevinEstimateRecord.Matches]

/-- The deterministic state obtained by repeatedly feeding Proposition 6.41
records to the existing controller transition. -/
noncomputable def deterministicGoldreichLevinState
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) : ℕ →
      GoldreichLevinQueryState input.accuracy.n
  | 0 => ⟨some {∅}, []⟩
  | k + 1 =>
      let previous := deterministicGoldreichLevinState input target k
      if hk : k < input.accuracy.n then
        match previous.active with
        | none => previous
        | some active =>
            if active.card ≤ goldreichLevinActiveCap input.threshold then
              goldreichLevinQueryStep input.threshold k hk previous
                (deterministicGoldreichLevinStageRecords input target k hk active)
            else
              ⟨none, previous.trace⟩
      else
        previous

/-- The deterministic driver preserves the Chapter 3 controller invariant;
its accumulated trace is accurate at every level. -/
theorem deterministicGoldreichLevinState_spec
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound) :
    ∀ (k : ℕ), k ≤ input.accuracy.n →
      let state := deterministicGoldreichLevinState input target k
      state.SatisfiesInvariant target input.threshold k ∧
        GoldreichLevinEstimateTrace.IsAccurate
          state.trace target input.threshold := by
  intro k
  induction k with
  | zero =>
      intro _hk
      exact ⟨goldreichLevinInitialQueryState_satisfiesInvariant
        target input.threshold, by simp [deterministicGoldreichLevinState,
          GoldreichLevinEstimateTrace.IsAccurate]⟩
  | succ k ih =>
      intro hk
      have hklt : k < input.accuracy.n := Nat.lt_of_succ_le hk
      let previous := deterministicGoldreichLevinState input target k
      have hprevious := ih (Nat.le_trans (Nat.le_succ k) hk)
      obtain ⟨active, hactive, hinvariant, hcap⟩ := hprevious.1
      have hrecords := deterministicGoldreichLevinStageRecords_isAccurate
        input target hnorm k (Nat.lt_of_succ_le hk) active
      have htrace : GoldreichLevinEstimateTrace.IsAccurate
          (previous.trace ++
            deterministicGoldreichLevinStageRecords input target k
              (Nat.lt_of_succ_le hk) active) target input.threshold := by
        intro record hrecord
        rw [List.mem_append] at hrecord
        exact hrecord.elim (hprevious.2 record) (hrecords record)
      have hchosen : hprevious.1.choose = active := by
        apply Option.some.inj
        exact hprevious.1.choose_spec.1.symm.trans hactive
      have hcover : GoldreichLevinEstimateTrace.Covers
          (deterministicGoldreichLevinStageRecords input target k
            (Nat.lt_of_succ_le hk) active)
          (prefixCoordinates input.accuracy.n (k + 1))
          (goldreichLevinCandidates
            (⟨k, Nat.lt_of_succ_le hk⟩ : Fin input.accuracy.n)
            hprevious.1.choose) := by
        simpa [hchosen] using
          deterministicGoldreichLevinStageRecords_covers input target k
            (Nat.lt_of_succ_le hk) active
      have hnext := goldreichLevinQueryStep_satisfiesInvariant
        target input.threshold k (Nat.lt_of_succ_le hk) previous
        (deterministicGoldreichLevinStageRecords input target k
          (Nat.lt_of_succ_le hk) active)
        hprevious.1 htrace hcover
      change
        (deterministicGoldreichLevinState input target (k + 1)).SatisfiesInvariant
            target input.threshold (k + 1) ∧
          GoldreichLevinEstimateTrace.IsAccurate
            (deterministicGoldreichLevinState input target (k + 1)).trace
            target input.threshold
      rw [deterministicGoldreichLevinState]
      rw [dif_pos hklt]
      simp only [hactive]
      rw [if_pos hcap]
      refine ⟨hnext, ?_⟩
      simpa [goldreichLevinQueryStep] using htrace

/-- The final deterministic prefix state has the complete, sound,
duplicate-free list and Parseval size guarantees of Goldreich--Levin. -/
theorem deterministicGoldreichLevinState_isCorrectOutput
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound) :
    GoldreichLevinQueryState.IsCorrectOutput
      (deterministicGoldreichLevinState input target input.accuracy.n)
      target input.threshold := by
  have hspec := deterministicGoldreichLevinState_spec
    input target hnorm input.accuracy.n le_rfl
  dsimp only at hspec
  obtain ⟨active, hactive, hinvariant, hcap⟩ := hspec.1
  exact ⟨active, hactive,
    goldreichLevinActiveInvariant_complete
      target input.threshold active hinvariant,
    goldreichLevinActiveInvariant_sound
      target input.threshold active hinvariant,
    hcap,
    goldreichLevinActiveInvariant_card_le
      target input.threshold active hinvariant⟩

/-! ## Visible deterministic oracle program -/

open DeterministicQueryProgram

/-- Uniform local-work charge for one restricted-weight value. -/
noncomputable def deterministicGoldreichLevinRestrictedLocalWork
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  input.restrictedWeightInput.outerCount *
      (input.restrictedWeightInput.innerCount *
        (input.accuracy.n + 2) + 3) + 1

/-- Work used to form every record in one active controller stage. -/
noncomputable def deterministicGoldreichLevinStageLocalWork
    (input : DeterministicGoldreichLevinInput)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) : ℕ :=
  (goldreichLevinCandidates
      (⟨k, hk⟩ : Fin input.accuracy.n) active).card *
    deterministicGoldreichLevinRestrictedLocalWork input

/-- Exact cost of one deterministic estimator stage before the pure
controller transition. -/
noncomputable def deterministicGoldreichLevinStageCost
    (input : DeterministicGoldreichLevinInput)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) : LearningCost :=
  DeterministicQueryProgram.queryBatchCost
      (deterministicRestrictedWeightQueryCount
        input.restrictedWeightInput) +
    ⟨0, 0, deterministicGoldreichLevinStageLocalWork input k hk active⟩

/-- One shared Proposition 6.41 query batch produces all candidate records
at a controller stage. -/
noncomputable def deterministicGoldreichLevinStageProgram
    (input : DeterministicGoldreichLevinInput)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (List (GoldreichLevinEstimateRecord input.accuracy.n)) :=
  let J := prefixCoordinates input.accuracy.n (k + 1)
  .queryBatch
    (deterministicRestrictedWeightQueryCount input.restrictedWeightInput)
    (deterministicRestrictedWeightQueryPoint input.restrictedWeightInput J)
    (fun answers ↦
      .tick (deterministicGoldreichLevinStageLocalWork input k hk active)
        (.pure
          (deterministicGoldreichLevinStageRecordsFromAnswers
            input k hk active answers)))

/-- Exact deterministic output and cost of one estimator stage. -/
theorem DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k < input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinStageProgram input k hk active) =
      (deterministicGoldreichLevinStageRecords input target k hk active,
        deterministicGoldreichLevinStageCost input k hk active) := by
  rfl

/-- One charged transition whose branching and prefix refinement are the
existing Chapter 3 controller operation. -/
noncomputable def deterministicGoldreichLevinStageStepProgram
    (input : DeterministicGoldreichLevinInput)
    (k : ℕ) (hk : k < input.accuracy.n)
    (state : GoldreichLevinQueryState input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (GoldreichLevinQueryState input.accuracy.n) :=
  .tick (goldreichLevinControllerStepWork
      input.accuracy.n input.threshold)
    ((deterministicGoldreichLevinStageProgram input k hk active).map
      (goldreichLevinQueryStep input.threshold k hk state))

/-- A charged stage step returns exactly the existing pure controller transition. -/
theorem DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram_fst
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k < input.accuracy.n)
    (state : GoldreichLevinQueryState input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    (DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinStageStepProgram
        input k hk state active)).1 =
      goldreichLevinQueryStep input.threshold k hk state
        (deterministicGoldreichLevinStageRecords
          input target k hk active) := by
  unfold deterministicGoldreichLevinStageStepProgram
  rw [DeterministicQueryProgram.runWithCost]
  unfold DeterministicQueryProgram.map
  rw [DeterministicQueryProgram.runWithCost_bind,
    DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram]
  rfl

/-- The deterministic adaptive driver schedules the existing controller
for the first `k` coordinates. -/
noncomputable def deterministicGoldreichLevinRunUpToProgram
    (input : DeterministicGoldreichLevinInput) : ℕ →
      DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
        (GoldreichLevinQueryState input.accuracy.n)
  | 0 => .pure ⟨some {∅}, []⟩
  | k + 1 =>
      (deterministicGoldreichLevinRunUpToProgram input k).bind fun state ↦
        if hk : k < input.accuracy.n then
          match state.active with
          | none => .pure state
          | some active =>
              if active.card ≤ goldreichLevinActiveCap input.threshold then
                deterministicGoldreichLevinStageStepProgram input k hk state active
              else
                .pure ⟨none, state.trace⟩
        else
          .pure state

/-- The visible driver computes exactly the mathematical deterministic
controller state. -/
theorem DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinRunUpToProgram_fst
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    ∀ (k : ℕ),
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input k)).1 =
      deterministicGoldreichLevinState input target k := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      let previousProgram :=
        deterministicGoldreichLevinRunUpToProgram input k
      let previousOutcome :=
        DeterministicQueryProgram.runWithCost target previousProgram
      let previousState :=
        deterministicGoldreichLevinState input target k
      have hprevious : previousOutcome.1 = previousState := ih
      rw [deterministicGoldreichLevinRunUpToProgram,
        DeterministicQueryProgram.runWithCost_bind]
      change
        (let second := DeterministicQueryProgram.runWithCost target
          (if hk : k < input.accuracy.n then
            match previousOutcome.1.active with
            | none => .pure previousOutcome.1
            | some active =>
                if active.card ≤ goldreichLevinActiveCap input.threshold then
                  deterministicGoldreichLevinStageStepProgram input k hk
                    previousOutcome.1 active
                else .pure ⟨none, previousOutcome.1.trace⟩
          else .pure previousOutcome.1)
        second.1) = _
      rw [hprevious]
      by_cases hk : k < input.accuracy.n
      · rw [dif_pos hk]
        rw [deterministicGoldreichLevinState, dif_pos hk]
        cases hactive : previousState.active with
        | none =>
            simp only [DeterministicQueryProgram.runWithCost]
            rfl
        | some active =>
            simp only
            by_cases hcap : active.card ≤
                goldreichLevinActiveCap input.threshold
            · rw [if_pos hcap,
                runWithCost_deterministicGoldreichLevinStageStepProgram_fst,
                if_pos hcap]
            · rw [if_neg hcap, if_neg hcap]
              rfl
      · rw [dif_neg hk]
        rw [deterministicGoldreichLevinState, dif_neg hk]
        rfl

/-- The complete deterministic Goldreich--Levin list program constructs
the Proposition 6.41 sample once and then runs all prefix stages. -/
noncomputable def deterministicGoldreichLevinProgram
    (input : DeterministicGoldreichLevinInput) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (GoldreichLevinQueryState input.accuracy.n) :=
  .tick (deterministicRestrictedWeightConstructionWork
      input.restrictedWeightInput)
    (deterministicGoldreichLevinRunUpToProgram input
      input.accuracy.n)

/-- The visible list program has all Goldreich--Levin correctness and
list-size guarantees for every target in the promised class. -/
theorem deterministicGoldreichLevinProgram_isCorrectOutput
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound) :
    (DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinProgram input)).1.IsCorrectOutput
        target input.threshold := by
  rw [deterministicGoldreichLevinProgram,
    DeterministicQueryProgram.runWithCost]
  rw [DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinRunUpToProgram_fst]
  exact deterministicGoldreichLevinState_isCorrectOutput input target hnorm

/-! ## Deterministic finite-family coefficient estimation -/

/-- Conservative local work for one final Fourier coefficient. -/
noncomputable def deterministicGoldreichLevinCoefficientLocalWork
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  smallBiasFourierEstimatorWork input.coefficientInput.sampleCount
    (Finset.univ : Finset (Fin input.accuracy.n))

/-- The sparse rational hypothesis computed from one shared Proposition 6.40
answer batch. -/
noncomputable def deterministicGoldreichLevinHypothesisFromAnswers
    (input : DeterministicGoldreichLevinInput)
    (family : Finset (Finset (Fin input.accuracy.n)))
    (answers : Fin input.coefficientInput.sampleCount → Sign) :
    SparseFourierHypothesis input.accuracy.n :=
  SparseFourierHypothesis.ofCoefficients family fun U ↦
    rationalSmallBiasFourierEstimate input.coefficientInput U.1 answers

/-- Exact cost of the shared deterministic finite-family coefficient batch. -/
noncomputable def deterministicGoldreichLevinCoefficientCost
    (input : DeterministicGoldreichLevinInput)
    (family : Finset (Finset (Fin input.accuracy.n))) : LearningCost :=
  ⟨0, 0, deterministicSmallBiasWork
      input.coefficientInput.generatorInput⟩ +
    (DeterministicQueryProgram.queryBatchCost
      input.coefficientInput.sampleCount +
      ⟨0, 0, family.card *
        deterministicGoldreichLevinCoefficientLocalWork input⟩)

/-- Proposition 6.40 applied simultaneously to a finite output family. -/
noncomputable def deterministicGoldreichLevinCoefficientProgram
    (input : DeterministicGoldreichLevinInput)
    (family : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (SparseFourierHypothesis input.accuracy.n) :=
  .tick (deterministicSmallBiasWork
      input.coefficientInput.generatorInput)
    (.queryBatch input.coefficientInput.sampleCount
      (fun i ↦ binaryCubeSignEquiv input.accuracy.n
        (input.coefficientInput.sample i))
      (fun answers ↦
        .tick (family.card *
          deterministicGoldreichLevinCoefficientLocalWork input)
          (.pure
            (deterministicGoldreichLevinHypothesisFromAnswers
              input family answers))))

/-- Exact output and visible cost of the final coefficient batch. -/
theorem DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (family : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinCoefficientProgram input family) =
      (deterministicGoldreichLevinHypothesisFromAnswers input family
        (fun i ↦ target (binaryCubeSignEquiv input.accuracy.n
          (input.coefficientInput.sample i))),
        deterministicGoldreichLevinCoefficientCost input family) := by
  rfl

/-- Every coefficient in a nonempty capped family meets the accuracy
required by the reused finite-family learning theorem. -/
theorem deterministicGoldreichLevinHypothesis_coefficients_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound)
    (family : Finset (Finset (Fin input.accuracy.n)))
    (hfamily : family.Nonempty)
    (hcap : family.card ≤ goldreichLevinActiveCap input.threshold) :
    ∀ U : family,
      |(rationalSmallBiasFourierEstimate input.coefficientInput U.1
          (fun i ↦ target (binaryCubeSignEquiv input.accuracy.n
            (input.coefficientInput.sample i))) : ℝ) -
        fourierCoeff target.toReal U.1| ≤
        (finiteFamilyCoefficientAccuracy family hfamily
          input.learningParameter).1 := by
  intro U
  have hestimate :=
    abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le
      input.coefficientInput target.toReal U.1 hnorm
  have hcast := rationalSmallBiasFourierEstimate_cast
    input.coefficientInput target U.1
  have hcast' :
      (rationalSmallBiasFourierEstimate input.coefficientInput U.1
          (fun i ↦ target (binaryCubeSignEquiv input.accuracy.n
            (input.coefficientInput.sample i))) : ℝ) =
        smallBiasFourierEstimate target.toReal
          input.coefficientInput.sample U.1 := by
    convert hcast using 1
  have hcardPos : 0 < family.card := Finset.card_pos.mpr hfamily
  have hcapPos : (0 : ℝ) < goldreichLevinActiveCap input.threshold := by
    exact_mod_cast goldreichLevinActiveCap_pos input.threshold
  have hcardLe : (family.card : ℝ) ≤
      goldreichLevinActiveCap input.threshold := by
    exact_mod_cast hcap
  rw [hcast']
  calc
    |smallBiasFourierEstimate target.toReal
        input.coefficientInput.sample U.1 -
          fourierCoeff target.toReal U.1| ≤
        input.coefficientInput.epsilon := hestimate
    _ = (input.learningParameter.1 : ℝ) /
        (2 * goldreichLevinActiveCap input.threshold) :=
      input.coefficientInput_epsilon
    _ ≤ (input.learningParameter.1 : ℝ) / (2 * family.card) := by
      have hε : (0 : ℝ) ≤ (input.learningParameter.1 : ℝ) :=
        Rat.cast_nonneg.mpr input.learningParameter.2.1.le
      gcongr
    _ = (finiteFamilyCoefficientAccuracy family hfamily
          input.learningParameter).1 := by
      norm_num [finiteFamilyCoefficientAccuracy]

/-! ## Deterministic Kushilevitz--Mansour composition -/

/-- The deterministic second stage estimates the coefficients of a capped
Goldreich--Levin family and otherwise returns the empty hypothesis. -/
noncomputable def deterministicGoldreichLevinSecondStage
    (input : DeterministicGoldreichLevinInput)
    (state : GoldreichLevinQueryState input.accuracy.n) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (SparseFourierHypothesis input.accuracy.n) :=
  match state.active with
  | none => .pure (SparseFourierHypothesis.empty input.accuracy.n)
  | some family =>
      if family.card ≤ goldreichLevinActiveCap input.threshold then
        deterministicGoldreichLevinCoefficientProgram input family
      else
        .pure (SparseFourierHypothesis.empty input.accuracy.n)

/-- The complete deterministic learner is the existing prefix controller
followed by one shared Proposition 6.40 coefficient batch. -/
noncomputable def deterministicGoldreichLevinLearner
    (input : DeterministicGoldreichLevinInput) :
    DeterministicQueryProgram {−1,1}^[input.accuracy.n] Sign
      (SparseFourierHypothesis input.accuracy.n) :=
  (deterministicGoldreichLevinProgram input).bind
    (deterministicGoldreichLevinSecondStage input)

/-- The deterministic prefix output carries all but `ε / 2` of the target's
Fourier weight on a nonempty family below the controller cap. -/
theorem deterministicGoldreichLevinProgram_concentrated_family
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound) :
    ∃ family : Finset (Finset (Fin input.accuracy.n)),
      (DeterministicQueryProgram.runWithCost target
          (deterministicGoldreichLevinProgram input)).1.active = some family ∧
      family.Nonempty ∧
      IsFourierSpectrumConcentratedOn target.toReal
        ((input.learningParameter.1 : ℝ) / 2)
        (↑family : Set (Finset (Fin input.accuracy.n))) ∧
      family.card ≤ goldreichLevinActiveCap input.threshold := by
  have hcorrect := deterministicGoldreichLevinProgram_isCorrectOutput
    input target hnorm
  obtain ⟨family, hactive, hcomplete, _hsound, hcap, _hcardReal⟩ :=
    hcorrect
  let initialFamily := l1ConcentratingFourierFamily target.toReal
    ((input.learningParameter.1 : ℝ) / 4)
  have hparameter :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hinitialConcentration :
      IsFourierSpectrumConcentratedOn target.toReal
        ((input.learningParameter.1 : ℝ) / 4)
        (↑initialFamily : Set (Finset (Fin input.accuracy.n))) := by
    exact isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily
      target.toReal (div_pos hparameter.1 (by norm_num))
  have hinitialCard : initialFamily.card ≤ input.familySizeBound := by
    simpa only [initialFamily,
      DeterministicGoldreichLevinInput.familySizeBound] using
        card_l1ConcentratingFourierFamily_le_familySizeBound
          target (input.fourierBound : ℝ) input.learningParameter hnorm
  have hcomplete' : ∀ U : Finset (Fin input.accuracy.n),
      ((kushilevitzMansourThreshold input.learningParameter
        input.familySizeBound input.familySizeBound_pos).1 : ℝ) ≤
          |fourierCoeff target.toReal U| →
        U ∈ family := by
    simpa only [DeterministicGoldreichLevinInput.threshold] using hcomplete
  have hconcentration :=
    isFourierSpectrumConcentratedOn_of_goldreichLevin_complete
      target input.learningParameter input.familySizeBound
      input.familySizeBound_pos initialFamily family hinitialCard
      hinitialConcentration hcomplete'
  have hfamily := finiteFamily_nonempty_of_spectrum_concentrated
    target family input.learningParameter hconcentration
  exact ⟨family, hactive, hfamily, hconcentration, hcap⟩

/-- O'Donnell, Theorem 6.42: every target satisfying the advertised Fourier
`1`-norm promise is learned deterministically to the requested error. -/
theorem deterministicGoldreichLevinLearner_relativeHammingDist_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound) :
    relativeHammingDist target
        (DeterministicQueryProgram.runWithCost target
          (deterministicGoldreichLevinLearner input)).1.evaluate ≤
      (input.learningParameter.1 : ℝ) := by
  let firstOutcome := DeterministicQueryProgram.runWithCost target
    (deterministicGoldreichLevinProgram input)
  obtain ⟨family, hactive, hfamily, hconcentration, hcap⟩ :=
    deterministicGoldreichLevinProgram_concentrated_family
      input target hnorm
  have hcoefficients := deterministicGoldreichLevinHypothesis_coefficients_le
    input target hnorm family hfamily hcap
  have hanalytic :=
    relativeHammingDist_sparseFourierHypothesis_of_coefficients_le
      target family hfamily input.learningParameter
      (fun U ↦ rationalSmallBiasFourierEstimate input.coefficientInput U.1
        (fun i ↦ target (binaryCubeSignEquiv input.accuracy.n
          (input.coefficientInput.sample i))))
      hconcentration hcoefficients
  rw [deterministicGoldreichLevinLearner,
    DeterministicQueryProgram.runWithCost_bind]
  change relativeHammingDist target
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinSecondStage input firstOutcome.1)).1.evaluate ≤
    (input.learningParameter.1 : ℝ)
  dsimp only [firstOutcome] at hactive ⊢
  simp only [deterministicGoldreichLevinSecondStage, hactive]
  rw [if_pos hcap,
    DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram]
  exact hanalytic

/-- Chapter 3 membership-query presentation of the deterministic learner. -/
noncomputable def deterministicGoldreichLevinLearningProgram
    (input : DeterministicGoldreichLevinInput) :
    LearningProgram input.accuracy.n .queries
      (SparseFourierHypothesis input.accuracy.n) :=
  DeterministicQueryProgram.toLearningProgram
    (deterministicGoldreichLevinLearner input)

/-- The Chapter 3 adapter preserves the deterministic learner and its exact
constructor-derived path cost. -/
theorem runWithCost_deterministicGoldreichLevinLearningProgram
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    LearningProgram.runWithCost target
        (deterministicGoldreichLevinLearningProgram input) =
      PMF.pure (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)) := by
  exact DeterministicQueryProgram.runWithCost_toLearningProgram target _

/-- Every execution in the Chapter 3 query model satisfies the deterministic
learning guarantee. -/
theorem deterministicGoldreichLevinLearningProgram_relativeHammingDist_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound)
    (outcome : SparseFourierHypothesis input.accuracy.n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (deterministicGoldreichLevinLearningProgram input)).support) :
    relativeHammingDist target outcome.1.evaluate ≤
      (input.learningParameter.1 : ℝ) := by
  rw [runWithCost_deterministicGoldreichLevinLearningProgram,
    PMF.mem_support_pure_iff] at houtcome
  subst outcome
  exact deterministicGoldreichLevinLearner_relativeHammingDist_le
    input target hnorm

/-! ## Explicit deterministic resources -/

/-- A stage step has the exact estimator, controller output, and additive
cost advertised by its visible constructors. -/
theorem DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k < input.accuracy.n)
    (state : GoldreichLevinQueryState input.accuracy.n)
    (active : Finset (Finset (Fin input.accuracy.n))) :
    DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinStageStepProgram
          input k hk state active) =
      (goldreichLevinQueryStep input.threshold k hk state
          (deterministicGoldreichLevinStageRecords
            input target k hk active),
        ⟨0, 0, goldreichLevinControllerStepWork
          input.accuracy.n input.threshold⟩ +
          deterministicGoldreichLevinStageCost input k hk active) := by
  unfold deterministicGoldreichLevinStageStepProgram
  rw [DeterministicQueryProgram.runWithCost]
  unfold DeterministicQueryProgram.map
  rw [DeterministicQueryProgram.runWithCost_bind,
    DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram]
  rfl

/-- Uniform query allowance for one deterministic prefix stage. -/
noncomputable def deterministicGoldreichLevinStageQueryBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  deterministicRestrictedWeightQueryCount input.restrictedWeightInput

/-- Uniform charged-work allowance for one deterministic prefix stage. -/
noncomputable def deterministicGoldreichLevinStageWorkBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  goldreichLevinControllerStepWork input.accuracy.n input.threshold +
    deterministicGoldreichLevinStageQueryBudget input +
      2 * goldreichLevinActiveCap input.threshold *
        deterministicGoldreichLevinRestrictedLocalWork input

/-- Query budget for all `n` prefix refinements. -/
noncomputable def deterministicGoldreichLevinListQueryBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  input.accuracy.n * deterministicGoldreichLevinStageQueryBudget input

/-- Work budget for sample construction and all prefix refinements. -/
noncomputable def deterministicGoldreichLevinListWorkBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  deterministicRestrictedWeightConstructionWork input.restrictedWeightInput +
    input.accuracy.n * deterministicGoldreichLevinStageWorkBudget input

/-- Query budget of the shared final coefficient batch. -/
noncomputable def deterministicGoldreichLevinCoefficientQueryBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  input.coefficientInput.sampleCount

/-- Work budget of the shared final coefficient batch on a capped family. -/
noncomputable def deterministicGoldreichLevinCoefficientWorkBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  deterministicSmallBiasWork input.coefficientInput.generatorInput +
    input.coefficientInput.sampleCount +
      goldreichLevinActiveCap input.threshold *
        deterministicGoldreichLevinCoefficientLocalWork input

/-- Total membership-query budget of Theorem 6.42. -/
noncomputable def deterministicGoldreichLevinQueryBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  deterministicGoldreichLevinListQueryBudget input +
    deterministicGoldreichLevinCoefficientQueryBudget input

/-- Total charged-work budget of Theorem 6.42. -/
noncomputable def deterministicGoldreichLevinWorkBudget
    (input : DeterministicGoldreichLevinInput) : ℕ :=
  deterministicGoldreichLevinListWorkBudget input +
    deterministicGoldreichLevinCoefficientWorkBudget input

/-- Generic additive projection bound for the deterministic prefix driver. -/
theorem deterministicGoldreichLevinRunUpToProgram_costProjection_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (projection : LearningCost → ℕ)
    (hzero : projection 0 = 0)
    (hadd : ∀ first second,
      projection (first + second) = projection first + projection second)
    (stageBound : ℕ)
    (hstage : ∀ (k : ℕ) (hk : k < input.accuracy.n)
      (active : Finset (Finset (Fin input.accuracy.n))),
      active.card ≤ goldreichLevinActiveCap input.threshold →
      projection
        (⟨0, 0, goldreichLevinControllerStepWork
            input.accuracy.n input.threshold⟩ +
          deterministicGoldreichLevinStageCost input k hk active) ≤
        stageBound) :
    ∀ (k : ℕ), k ≤ input.accuracy.n →
      projection (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input k)).2 ≤
      k * stageBound := by
  intro k
  induction k with
  | zero =>
      intro _hk
      simp [deterministicGoldreichLevinRunUpToProgram,
        DeterministicQueryProgram.runWithCost, hzero]
  | succ k ih =>
      intro hk
      have hklt : k < input.accuracy.n := Nat.lt_of_succ_le hk
      let previousOutcome := DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input k)
      have hprevious : projection previousOutcome.2 ≤ k * stageBound :=
        ih (Nat.le_trans (Nat.le_succ k) hk)
      rw [deterministicGoldreichLevinRunUpToProgram,
        DeterministicQueryProgram.runWithCost_bind]
      change
        (let second := DeterministicQueryProgram.runWithCost target
          (if hk' : k < input.accuracy.n then
            match previousOutcome.1.active with
            | none => .pure previousOutcome.1
            | some active =>
                if active.card ≤ goldreichLevinActiveCap input.threshold then
                  deterministicGoldreichLevinStageStepProgram input k hk'
                    previousOutcome.1 active
                else .pure ⟨none, previousOutcome.1.trace⟩
          else .pure previousOutcome.1)
        projection (previousOutcome.2 + second.2)) ≤
          (k + 1) * stageBound
      rw [dif_pos hklt]
      rw [hadd]
      have hcontinuation :
          projection (DeterministicQueryProgram.runWithCost target
            (match previousOutcome.1.active with
            | none => .pure previousOutcome.1
            | some active =>
                if active.card ≤ goldreichLevinActiveCap input.threshold then
                  deterministicGoldreichLevinStageStepProgram input k hklt
                    previousOutcome.1 active
                else .pure ⟨none, previousOutcome.1.trace⟩)).2 ≤
            stageBound := by
        cases previousOutcome.1.active with
        | none =>
            change projection 0 ≤ stageBound
            rw [hzero]
            exact Nat.zero_le stageBound
        | some active =>
            simp only
            by_cases hcap : active.card ≤
                goldreichLevinActiveCap input.threshold
            · rw [if_pos hcap,
                DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram]
              exact hstage k hklt active hcap
            · rw [if_neg hcap]
              change projection 0 ≤ stageBound
              rw [hzero]
              exact Nat.zero_le stageBound
      calc
        projection previousOutcome.2 +
            projection (DeterministicQueryProgram.runWithCost target
              (match previousOutcome.1.active with
              | none => .pure previousOutcome.1
              | some active =>
                  if active.card ≤
                      goldreichLevinActiveCap input.threshold then
                    deterministicGoldreichLevinStageStepProgram input k hklt
                      previousOutcome.1 active
                  else .pure ⟨none, previousOutcome.1.trace⟩)).2 ≤
            k * stageBound + stageBound :=
          Nat.add_le_add hprevious hcontinuation
        _ = (k + 1) * stageBound := by ring

/-- The deterministic prefix driver issues at most one shared estimator
batch per coordinate. -/
theorem deterministicGoldreichLevinRunUpToProgram_queries_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k ≤ input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinRunUpToProgram input k)).2.queries ≤
      k * deterministicGoldreichLevinStageQueryBudget input := by
  apply deterministicGoldreichLevinRunUpToProgram_costProjection_le
    input target LearningCost.queries rfl (fun _ _ ↦ rfl)
      (deterministicGoldreichLevinStageQueryBudget input)
  · intro stage hstage active _hcap
    unfold deterministicGoldreichLevinStageCost
      deterministicGoldreichLevinStageQueryBudget
      DeterministicQueryProgram.queryBatchCost
    change 0 +
      (deterministicRestrictedWeightQueryCount input.restrictedWeightInput + 0) ≤
        deterministicRestrictedWeightQueryCount input.restrictedWeightInput
    omega
  · exact hk

/-- The deterministic prefix driver obeys the uniform controller and
candidate-estimation work budget at every coordinate. -/
theorem deterministicGoldreichLevinRunUpToProgram_work_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k ≤ input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinRunUpToProgram input k)).2.work ≤
      k * deterministicGoldreichLevinStageWorkBudget input := by
  apply deterministicGoldreichLevinRunUpToProgram_costProjection_le
    input target LearningCost.work rfl (fun _ _ ↦ rfl)
      (deterministicGoldreichLevinStageWorkBudget input)
  · intro stage hstage active hcap
    have hcandidates :=
      (card_goldreichLevinCandidates_le_two_mul
        (⟨stage, hstage⟩ : Fin input.accuracy.n) active).trans
        (Nat.mul_le_mul_left 2 hcap)
    have hlocal := Nat.mul_le_mul_right
      (deterministicGoldreichLevinRestrictedLocalWork input) hcandidates
    change
      goldreichLevinControllerStepWork input.accuracy.n input.threshold +
          (deterministicGoldreichLevinStageQueryBudget input +
            (goldreichLevinCandidates
              (⟨stage, hstage⟩ : Fin input.accuracy.n) active).card *
                deterministicGoldreichLevinRestrictedLocalWork input) ≤
        deterministicGoldreichLevinStageWorkBudget input
    rw [deterministicGoldreichLevinStageWorkBudget]
    omega
  · exact hk

/-- The prefix driver never consumes random examples. -/
theorem deterministicGoldreichLevinRunUpToProgram_randomExamples
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (k : ℕ) (hk : k ≤ input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinRunUpToProgram input k)).2.randomExamples = 0 := by
  have hbound := deterministicGoldreichLevinRunUpToProgram_costProjection_le
    input target LearningCost.randomExamples rfl (fun _ _ ↦ rfl) 0
      (by
        intro stage hstage active _hcap
        unfold deterministicGoldreichLevinStageCost
          DeterministicQueryProgram.queryBatchCost
        change 0 + (0 + 0) ≤ 0
        omega)
      k hk
  exact Nat.eq_zero_of_le_zero (by simpa using hbound)

/-- Complete list construction obeys its explicit target-independent
query and charged-work bounds. -/
theorem deterministicGoldreichLevinProgram_resource_bounds
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinProgram input)).2.randomExamples = 0 ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinProgram input)).2.queries ≤
          deterministicGoldreichLevinListQueryBudget input ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinProgram input)).2.work ≤
          deterministicGoldreichLevinListWorkBudget input := by
  have hrandom := deterministicGoldreichLevinRunUpToProgram_randomExamples
    input target input.accuracy.n le_rfl
  have hqueries := deterministicGoldreichLevinRunUpToProgram_queries_le
    input target input.accuracy.n le_rfl
  have hwork := deterministicGoldreichLevinRunUpToProgram_work_le
    input target input.accuracy.n le_rfl
  constructor
  · rw [deterministicGoldreichLevinProgram,
      DeterministicQueryProgram.runWithCost]
    change 0 +
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input
          input.accuracy.n)).2.randomExamples = 0
    simpa using hrandom
  constructor
  · rw [deterministicGoldreichLevinProgram,
      DeterministicQueryProgram.runWithCost]
    change 0 +
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input
          input.accuracy.n)).2.queries ≤
        deterministicGoldreichLevinListQueryBudget input
    simpa [deterministicGoldreichLevinListQueryBudget] using hqueries
  · have hadd := Nat.add_le_add_left hwork
      (deterministicRestrictedWeightConstructionWork
        input.restrictedWeightInput)
    rw [deterministicGoldreichLevinProgram,
      DeterministicQueryProgram.runWithCost]
    change deterministicRestrictedWeightConstructionWork
        input.restrictedWeightInput +
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinRunUpToProgram input
          input.accuracy.n)).2.work ≤
        deterministicGoldreichLevinListWorkBudget input
    simpa [deterministicGoldreichLevinListWorkBudget] using hadd

/-- A capped final family obeys the shared coefficient-batch resource
bounds. -/
theorem deterministicGoldreichLevinCoefficientProgram_resource_bounds
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (family : Finset (Finset (Fin input.accuracy.n)))
    (hcap : family.card ≤ goldreichLevinActiveCap input.threshold) :
    (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinCoefficientProgram input family)).2.randomExamples = 0 ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinCoefficientProgram input family)).2.queries =
          deterministicGoldreichLevinCoefficientQueryBudget input ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinCoefficientProgram input family)).2.work ≤
          deterministicGoldreichLevinCoefficientWorkBudget input := by
  rw [DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram]
  constructor
  · unfold deterministicGoldreichLevinCoefficientCost
    change 0 + (0 + 0) = 0
    rfl
  constructor
  · unfold deterministicGoldreichLevinCoefficientCost
      deterministicGoldreichLevinCoefficientQueryBudget
      DeterministicQueryProgram.queryBatchCost
    change 0 + (input.coefficientInput.sampleCount + 0) =
      input.coefficientInput.sampleCount
    omega
  · have hlocal := Nat.mul_le_mul_right
      (deterministicGoldreichLevinCoefficientLocalWork input) hcap
    unfold deterministicGoldreichLevinCoefficientCost
      deterministicGoldreichLevinCoefficientWorkBudget
      DeterministicQueryProgram.queryBatchCost
    change deterministicSmallBiasWork
        input.coefficientInput.generatorInput +
          (input.coefficientInput.sampleCount +
            family.card * deterministicGoldreichLevinCoefficientLocalWork input) ≤
      deterministicSmallBiasWork input.coefficientInput.generatorInput +
        input.coefficientInput.sampleCount +
          goldreichLevinActiveCap input.threshold *
            deterministicGoldreichLevinCoefficientLocalWork input
    omega

/-- Every guarded second-stage path obeys the same coefficient budget. -/
theorem deterministicGoldreichLevinSecondStage_resource_bounds
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (state : GoldreichLevinQueryState input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinSecondStage input state)).2.randomExamples = 0 ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinSecondStage input state)).2.queries ≤
          deterministicGoldreichLevinCoefficientQueryBudget input ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinSecondStage input state)).2.work ≤
          deterministicGoldreichLevinCoefficientWorkBudget input := by
  cases hactive : state.active with
  | none =>
      simp only [deterministicGoldreichLevinSecondStage, hactive,
        DeterministicQueryProgram.runWithCost]
      exact ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩
  | some family =>
      simp only [deterministicGoldreichLevinSecondStage, hactive]
      by_cases hcap : family.card ≤
          goldreichLevinActiveCap input.threshold
      · rw [if_pos hcap]
        obtain ⟨hrandom, hqueries, hwork⟩ :=
          deterministicGoldreichLevinCoefficientProgram_resource_bounds
            input target family hcap
        exact ⟨hrandom, hqueries.le, hwork⟩
      · rw [if_neg hcap, DeterministicQueryProgram.runWithCost]
        exact ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩

/-- Every target, including targets outside the promised class, follows a
path below the explicit Theorem 6.42 resource budgets. -/
theorem deterministicGoldreichLevinLearner_resource_bounds
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.randomExamples = 0 ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.queries ≤
          deterministicGoldreichLevinQueryBudget input ∧
      (DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.work ≤
          deterministicGoldreichLevinWorkBudget input := by
  let firstOutcome := DeterministicQueryProgram.runWithCost target
    (deterministicGoldreichLevinProgram input)
  let secondOutcome := DeterministicQueryProgram.runWithCost target
    (deterministicGoldreichLevinSecondStage input firstOutcome.1)
  have hfirst := deterministicGoldreichLevinProgram_resource_bounds
    input target
  have hsecond := deterministicGoldreichLevinSecondStage_resource_bounds
    input target firstOutcome.1
  rw [deterministicGoldreichLevinLearner,
    DeterministicQueryProgram.runWithCost_bind]
  change
    (firstOutcome.2 + secondOutcome.2).randomExamples = 0 ∧
      (firstOutcome.2 + secondOutcome.2).queries ≤
        deterministicGoldreichLevinQueryBudget input ∧
      (firstOutcome.2 + secondOutcome.2).work ≤
        deterministicGoldreichLevinWorkBudget input
  change firstOutcome.2.randomExamples + secondOutcome.2.randomExamples = 0 ∧
    firstOutcome.2.queries + secondOutcome.2.queries ≤
      deterministicGoldreichLevinQueryBudget input ∧
    firstOutcome.2.work + secondOutcome.2.work ≤
      deterministicGoldreichLevinWorkBudget input
  refine ⟨by rw [hfirst.1, hsecond.1], ?_, ?_⟩
  · unfold deterministicGoldreichLevinQueryBudget
    exact Nat.add_le_add hfirst.2.1 hsecond.2.1
  · unfold deterministicGoldreichLevinWorkBudget
    exact Nat.add_le_add hfirst.2.2 hsecond.2.2

/-- The Chapter 3 query-model execution has the same deterministic resource
bounds. -/
theorem deterministicGoldreichLevinLearningProgram_resource_bounds
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (outcome : SparseFourierHypothesis input.accuracy.n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (deterministicGoldreichLevinLearningProgram input)).support) :
    outcome.2.randomExamples = 0 ∧
      outcome.2.queries ≤ deterministicGoldreichLevinQueryBudget input ∧
      outcome.2.work ≤ deterministicGoldreichLevinWorkBudget input := by
  rw [runWithCost_deterministicGoldreichLevinLearningProgram,
    PMF.mem_support_pure_iff] at houtcome
  subst outcome
  exact deterministicGoldreichLevinLearner_resource_bounds input target

/-! ## Polynomial closure in `n`, `s`, and `1 / ε` -/

/-- Ceiling-division scale of a small-bias input, bounded by the real
dimension-to-bias ratio plus one. -/
private theorem smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one
    (bias : SmallBiasInput) :
    (bias.scale : ℝ) ≤ (bias.n : ℝ) / bias.epsilon + 1 := by
  have hmulNat : bias.scale * bias.numerator ≤
      bias.n * bias.denominator + bias.numerator := by
    rw [SmallBiasInput.scale, Nat.ceilDiv_eq_add_pred_div]
    calc
      ((bias.n * bias.denominator + bias.numerator - 1) /
          bias.numerator) * bias.numerator ≤
          bias.n * bias.denominator + bias.numerator - 1 :=
        Nat.div_mul_le_self _ _
      _ ≤ bias.n * bias.denominator + bias.numerator :=
        Nat.sub_le _ _
  have hmulReal :
      (bias.scale : ℝ) * bias.numerator ≤
        (bias.n : ℝ) * bias.denominator + bias.numerator := by
    exact_mod_cast hmulNat
  have hnum : (0 : ℝ) < bias.numerator := by
    exact_mod_cast bias.numerator_pos
  have hnumNe : (bias.numerator : ℝ) ≠ 0 := hnum.ne'
  have hdenNat : 0 < bias.denominator := by
    exact (Nat.mul_pos (by omega) bias.numerator_pos).trans_le
      bias.twice_numerator_le_denominator
  have hdenNe : (bias.denominator : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  calc
    (bias.scale : ℝ) =
        ((bias.scale : ℝ) * bias.numerator) / bias.numerator := by
      field_simp
    _ ≤ ((bias.n : ℝ) * bias.denominator + bias.numerator) /
          bias.numerator :=
      div_le_div_of_nonneg_right hmulReal hnum.le
    _ = (bias.n : ℝ) / bias.epsilon + 1 := by
      rw [SmallBiasInput.epsilon]
      field_simp [hnumNe, hdenNe]

namespace DeterministicGoldreichLevinInput

/-- Book-facing runtime scale.  Its three varying factors are exactly
`n + 1`, `s + 1`, and `1 / ε`. -/
noncomputable def runtimeScale
    (input : DeterministicGoldreichLevinInput) : ℝ :=
  (((input.accuracy.n + 1 : ℕ) : ℝ) *
      ((input.fourierBound + 1 : ℕ) : ℝ)) /
    (input.learningParameter.1 : ℝ)

/-- Each of the three book parameters is dominated by the joint runtime
scale, which is itself at least one. -/
theorem runtimeScale_factor_bounds
    (input : DeterministicGoldreichLevinInput) :
    1 ≤ input.runtimeScale ∧
      ((input.accuracy.n + 1 : ℕ) : ℝ) ≤ input.runtimeScale ∧
      ((input.fourierBound + 1 : ℕ) : ℝ) ≤ input.runtimeScale ∧
      1 / (input.learningParameter.1 : ℝ) ≤ input.runtimeScale := by
  let dimension : ℝ := input.accuracy.n + 1
  let normBound : ℝ := input.fourierBound + 1
  let epsilon : ℝ := input.learningParameter.1
  have hdimension : (1 : ℝ) ≤ dimension := by
    dsimp [dimension]
    norm_num
  have hnormBound : (1 : ℝ) ≤ normBound := by
    dsimp [normBound]
    norm_num
  have hepsilon :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hepsilonOne : epsilon ≤ 1 := by
    dsimp [epsilon]
    exact hepsilon.2.trans (by norm_num)
  have hproduct : (1 : ℝ) ≤ dimension * normBound := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ dimension * normBound :=
        mul_le_mul hdimension hnormBound (by norm_num) (by linarith)
  have hproductScale : dimension * normBound ≤ input.runtimeScale := by
    dsimp [dimension, normBound, epsilon, runtimeScale]
    rw [le_div_iff₀ (by simpa [epsilon] using hepsilon.1)]
    have hmul := mul_le_of_le_one_right
      (mul_nonneg (by positivity : (0 : ℝ) ≤ dimension)
        (by positivity : (0 : ℝ) ≤ normBound)) hepsilonOne
    simpa [dimension, normBound, epsilon] using hmul
  have hdimensionScale : dimension ≤ input.runtimeScale := by
    calc
      dimension = dimension * 1 := by ring
      _ ≤ dimension * normBound :=
        mul_le_mul_of_nonneg_left hnormBound (by positivity)
      _ ≤ input.runtimeScale := hproductScale
  have hnormScale : normBound ≤ input.runtimeScale := by
    calc
      normBound = 1 * normBound := by ring
      _ ≤ dimension * normBound :=
        mul_le_mul_of_nonneg_right hdimension (by positivity)
      _ ≤ input.runtimeScale := hproductScale
  have hinverseScale : 1 / epsilon ≤ input.runtimeScale := by
    dsimp [dimension, normBound, epsilon, runtimeScale]
    apply (div_le_div_iff_of_pos_right hepsilon.1).2
    simpa [dimension, normBound] using hproduct
  exact ⟨hproduct.trans hproductScale,
    by simpa [dimension] using hdimensionScale,
    by simpa [normBound] using hnormScale,
    by simpa [epsilon] using hinverseScale⟩

/-- Real form of the exact Kushilevitz--Mansour threshold selected by the
finite input. -/
theorem threshold_cast (input : DeterministicGoldreichLevinInput) :
    (input.threshold.1 : ℝ) =
      (input.learningParameter.1 : ℝ) /
        (4 * input.familySizeBound) := by
  simp [threshold, kushilevitzMansourThreshold]

/-- The concentrating-family size is cubic in the joint book scale. -/
theorem familySizeBound_add_one_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    ((input.familySizeBound + 1 : ℕ) : ℝ) ≤
      6 * input.runtimeScale ^ 3 := by
  obtain ⟨hscale, _hdimension, hnorm, hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hepsilon :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hfamily := fourierOneNormFamilySizeBound_add_one_cast_le
    (input.fourierBound : ℝ) input.learningParameter (by positivity)
  have hnormSq : ((input.fourierBound : ℝ) + 1) ^ 2 ≤
      input.runtimeScale ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by simpa using hnorm) 2
  calc
    ((input.familySizeBound + 1 : ℕ) : ℝ) ≤
        6 * ((input.fourierBound : ℝ) + 1) ^ 2 /
          (input.learningParameter.1 : ℝ) := by
      simpa [familySizeBound] using hfamily
    _ = 6 * ((input.fourierBound : ℝ) + 1) ^ 2 *
        (1 / (input.learningParameter.1 : ℝ)) := by
      field_simp [hepsilon.1.ne']
    _ ≤ 6 * input.runtimeScale ^ 2 * input.runtimeScale := by
      calc
        6 * ((input.fourierBound : ℝ) + 1) ^ 2 *
            (1 / (input.learningParameter.1 : ℝ)) ≤
            6 * input.runtimeScale ^ 2 *
              (1 / (input.learningParameter.1 : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnormSq (by norm_num))
            (div_nonneg zero_le_one (le_of_lt hepsilon.1))
        _ ≤ 6 * input.runtimeScale ^ 2 * input.runtimeScale :=
          mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = 6 * input.runtimeScale ^ 3 := by ring

/-- The controller's active-family cap is degree eight in the joint book
scale. -/
theorem activeCap_add_one_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) ≤
      2 ^ 13 * input.runtimeScale ^ 8 := by
  obtain ⟨hscale, _hdimension, _hnorm, hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hepsilon :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hfamily := input.familySizeBound_add_one_cast_le_runtimeScale
  have hfamily' : (input.familySizeBound : ℝ) ≤
      6 * input.runtimeScale ^ 3 := by
    calc
      (input.familySizeBound : ℝ) ≤
          ((input.familySizeBound + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ 6 * input.runtimeScale ^ 3 := hfamily
  have hcapRat := goldreichLevinActiveCap_add_one_cast_le input.threshold
  have hcapReal :
      ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) ≤
        9 / (input.threshold.1 : ℝ) ^ 2 := by
    exact_mod_cast hcapRat
  have hfamilySq : (input.familySizeBound : ℝ) ^ 2 ≤
      (6 * input.runtimeScale ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfamily' 2
  have hinverseSq : (1 / (input.learningParameter.1 : ℝ)) ^ 2 ≤
      input.runtimeScale ^ 2 :=
    pow_le_pow_left₀
      (div_nonneg zero_le_one (le_of_lt hepsilon.1)) hinverse 2
  calc
    ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) ≤
        9 / (input.threshold.1 : ℝ) ^ 2 := hcapReal
    _ = 144 * (input.familySizeBound : ℝ) ^ 2 *
        (1 / (input.learningParameter.1 : ℝ)) ^ 2 := by
      rw [input.threshold_cast]
      field_simp [hepsilon.1.ne']
      ring
    _ ≤ 144 * (6 * input.runtimeScale ^ 3) ^ 2 *
        input.runtimeScale ^ 2 := by
      calc
        144 * (input.familySizeBound : ℝ) ^ 2 *
            (1 / (input.learningParameter.1 : ℝ)) ^ 2 ≤
            144 * (6 * input.runtimeScale ^ 3) ^ 2 *
              (1 / (input.learningParameter.1 : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfamilySq (by norm_num))
            (sq_nonneg _)
        _ ≤ 144 * (6 * input.runtimeScale ^ 3) ^ 2 *
            input.runtimeScale ^ 2 :=
          mul_le_mul_of_nonneg_left hinverseSq (by positivity)
    _ = 5184 * input.runtimeScale ^ 8 := by ring
    _ ≤ 2 ^ 13 * input.runtimeScale ^ 8 := by
      gcongr
      norm_num

end DeterministicGoldreichLevinInput

/-- The three primitive charges of Proposition 6.41 are each below its
already proved polynomial budget. -/
theorem deterministicGoldreichLevinRestrictedComponents_le_polynomialBudget
    (input : DeterministicGoldreichLevinInput) :
    deterministicRestrictedWeightConstructionWork
        input.restrictedWeightInput ≤
        input.restrictedWeightInput.polynomialBudget ∧
      deterministicGoldreichLevinStageQueryBudget input ≤
        input.restrictedWeightInput.polynomialBudget ∧
      deterministicGoldreichLevinRestrictedLocalWork input ≤
        input.restrictedWeightInput.polynomialBudget := by
  let J : Finset (Fin input.restrictedWeightInput.bias.n) := Finset.univ
  let S : Finset J := Finset.univ
  have hresource := deterministicRestrictedWeightCost_resource_bounds
    input.restrictedWeightInput J S
  have hqueries := hresource.2.1
  rw [deterministicRestrictedWeightCost_queries] at hqueries
  have hqueries' : deterministicGoldreichLevinStageQueryBudget input ≤
      input.restrictedWeightInput.polynomialBudget := by
    simpa [deterministicGoldreichLevinStageQueryBudget,
      deterministicRestrictedWeightQueryCount] using hqueries
  have hwork := hresource.2.2
  rw [deterministicRestrictedWeightCost_work] at hwork
  have hScard : S.card = input.accuracy.n := by
    dsimp [S]
    rw [Finset.card_attach]
    dsimp [J]
    change Fintype.card (Fin input.accuracy.n) = input.accuracy.n
    exact Fintype.card_fin input.accuracy.n
  have hlocal : deterministicRestrictedWeightLocalWork
      input.restrictedWeightInput S =
      deterministicGoldreichLevinRestrictedLocalWork input := by
    unfold deterministicRestrictedWeightLocalWork
      deterministicGoldreichLevinRestrictedLocalWork
    rw [hScard]
  rw [hlocal] at hwork
  exact ⟨by omega, hqueries', by omega⟩

/-- The construction, query batch, and one-coefficient work of Proposition
6.40 are each below its proved polynomial budget. -/
theorem deterministicGoldreichLevinCoefficientComponents_le_polynomialBudget
    (input : DeterministicGoldreichLevinInput) :
    deterministicSmallBiasWork input.coefficientInput.generatorInput ≤
        input.coefficientInput.polynomialBudget ∧
      input.coefficientInput.sampleCount ≤
        input.coefficientInput.polynomialBudget ∧
      deterministicGoldreichLevinCoefficientLocalWork input ≤
        input.coefficientInput.polynomialBudget := by
  let U : Finset (Fin input.coefficientInput.generatorInput.n) := Finset.univ
  have hresource :=
    deterministicSmallBiasFourierEstimatorCost_resource_bounds
      input.coefficientInput U
  have hqueries := hresource.2.1
  rw [deterministicSmallBiasFourierEstimatorCost_queries] at hqueries
  have hwork := hresource.2.2
  rw [deterministicSmallBiasFourierEstimatorCost_work] at hwork
  have hlocal : smallBiasFourierEstimatorWork
      input.coefficientInput.sampleCount U =
      deterministicGoldreichLevinCoefficientLocalWork input := by
    rfl
  rw [hlocal] at hwork
  exact ⟨by omega, hqueries, by omega⟩

namespace DeterministicGoldreichLevinInput

set_option maxHeartbeats 800000 in
-- Normalizing the explicit rational estimator scale exceeds the default elaboration budget.
/-- Proposition 6.41's two small-bias construction scales are jointly
degree eleven in the book runtime scale. -/
theorem restrictedWeightAlgorithmScale_add_one_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    ((input.restrictedWeightInput.algorithmScale + 1 : ℕ) : ℝ) ≤
      2 ^ 16 * input.runtimeScale ^ 11 := by
  let R := input.runtimeScale
  let epsilon : ℝ := input.learningParameter.1
  let dimension : ℝ := input.accuracy.n
  let normBound : ℝ := input.fourierBound
  let familyBound : ℝ := input.familySizeBound
  obtain ⟨hR, hdimensionOne, hnormOne, hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hRnonneg : (0 : ℝ) ≤ R :=
    (by positivity : (0 : ℝ) ≤ 1).trans hR
  have hepsilon :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hdimension : dimension ≤ R := by
    dsimp [dimension]
    exact (by norm_num : (input.accuracy.n : ℝ) ≤ input.accuracy.n + 1) |>.trans
      (by simpa [R] using hdimensionOne)
  have hnorm : normBound ≤ R := by
    dsimp [normBound]
    exact (by norm_num : (input.fourierBound : ℝ) ≤ input.fourierBound + 1) |>.trans
      (by simpa [R] using hnormOne)
  have hfamily : familyBound ≤ 6 * R ^ 3 := by
    dsimp [familyBound]
    calc
      (input.familySizeBound : ℝ) ≤
          ((input.familySizeBound + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ 6 * input.runtimeScale ^ 3 :=
        input.familySizeBound_add_one_cast_le_runtimeScale
      _ = 6 * R ^ 3 := by rfl
  have hnormNonneg : 0 ≤ normBound := by positivity
  have hfamilyNonneg : 0 ≤ familyBound := by positivity
  have hinverseNonneg : 0 ≤ 1 / epsilon :=
    div_nonneg zero_le_one (by simpa [epsilon] using hepsilon.1.le)
  have hfamilySq : familyBound ^ 2 ≤ (6 * R ^ 3) ^ 2 :=
    pow_le_pow_left₀ hfamilyNonneg hfamily 2
  have hinverseSq : (1 / epsilon) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ hinverseNonneg (by simpa [R, epsilon] using hinverse) 2
  have hinnerEpsilon :
      input.restrictedWeightInput.innerInput.generatorInput.epsilon =
        (input.threshold.1 : ℝ) ^ 2 / (32 * normBound) := by
    calc
      input.restrictedWeightInput.innerInput.generatorInput.epsilon =
          input.restrictedWeightInput.innerInput.epsilon /
            input.restrictedWeightInput.innerInput.fourierBound :=
        SmallBiasFourierInput.generatorInput_epsilon _
      _ = input.restrictedWeightInput.epsilon /
          (4 * (input.restrictedWeightInput.fourierBound : ℝ)) :=
        RestrictedWeightInput.innerInput_biasParameter _
      _ = ((input.threshold.1 : ℝ) ^ 2 / 8) /
          (4 * normBound) := by
        rw [input.restrictedWeightInput_epsilon]
        rfl
      _ = (input.threshold.1 : ℝ) ^ 2 / (32 * normBound) := by ring
  have houterEpsilon :
      input.restrictedWeightInput.outerInput.generatorInput.epsilon =
        (input.threshold.1 : ℝ) ^ 2 / (32 * normBound ^ 2) := by
    calc
      input.restrictedWeightInput.outerInput.generatorInput.epsilon =
          input.restrictedWeightInput.outerInput.epsilon /
            input.restrictedWeightInput.outerInput.fourierBound :=
        SmallBiasFourierInput.generatorInput_epsilon _
      _ = input.restrictedWeightInput.epsilon /
          (4 * (input.restrictedWeightInput.fourierBound : ℝ) ^ 2) :=
        RestrictedWeightInput.outerInput_biasParameter _
      _ = ((input.threshold.1 : ℝ) ^ 2 / 8) /
          (4 * normBound ^ 2) := by
        rw [input.restrictedWeightInput_epsilon]
        rfl
      _ = (input.threshold.1 : ℝ) ^ 2 /
          (32 * normBound ^ 2) := by ring
  have hinnerStart :=
    smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one
      input.restrictedWeightInput.innerInput.generatorInput
  have houterStart :=
    smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one
      input.restrictedWeightInput.outerInput.generatorInput
  have hinnerScale :
      ((input.restrictedWeightInput.innerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
        2 ^ 15 * R ^ 10 := by
    have hstart :
        ((input.restrictedWeightInput.innerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
          dimension /
            input.restrictedWeightInput.innerInput.generatorInput.epsilon + 2 := by
      calc
        ((input.restrictedWeightInput.innerInput.generatorInput.scale + 1 : ℕ) : ℝ) =
            (input.restrictedWeightInput.innerInput.generatorInput.scale : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        _ ≤ (input.restrictedWeightInput.innerInput.generatorInput.n : ℝ) /
            input.restrictedWeightInput.innerInput.generatorInput.epsilon + 2 := by
          linarith [hinnerStart]
        _ = dimension /
            input.restrictedWeightInput.innerInput.generatorInput.epsilon + 2 := by
          rw [show input.restrictedWeightInput.innerInput.generatorInput.n =
            input.accuracy.n by rfl]
    have hns := mul_le_mul hdimension hnorm hnormNonneg hRnonneg
    have hnsM := mul_le_mul hns hfamilySq (sq_nonneg _) (by positivity)
    have hproduct := mul_le_mul hnsM hinverseSq
      (sq_nonneg _) (by positivity)
    have hscaled := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 512)
    calc
      ((input.restrictedWeightInput.innerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
          dimension /
            input.restrictedWeightInput.innerInput.generatorInput.epsilon + 2 := hstart
      _ = 512 * dimension * normBound * familyBound ^ 2 *
          (1 / epsilon) ^ 2 + 2 := by
        rw [hinnerEpsilon, input.threshold_cast]
        dsimp [dimension, normBound, familyBound, epsilon]
        field_simp [hepsilon.1.ne', input.familySizeBound_pos.ne']
        ring
      _ ≤ 512 * R * R * (6 * R ^ 3) ^ 2 * R ^ 2 + 2 := by
        have : 512 * (dimension * normBound * familyBound ^ 2 *
            (1 / epsilon) ^ 2) ≤
            512 * (R * R * (6 * R ^ 3) ^ 2 * R ^ 2) := hscaled
        nlinarith
      _ = 18432 * R ^ 10 + 2 := by ring
      _ ≤ 2 ^ 15 * R ^ 10 := by
        have hpow : (1 : ℝ) ≤ R ^ 10 := one_le_pow₀ hR
        norm_num
        nlinarith
  have houterScale :
      ((input.restrictedWeightInput.outerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
        2 ^ 15 * R ^ 11 := by
    have hstart :
        ((input.restrictedWeightInput.outerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
          dimension /
            input.restrictedWeightInput.outerInput.generatorInput.epsilon + 2 := by
      calc
        ((input.restrictedWeightInput.outerInput.generatorInput.scale + 1 : ℕ) : ℝ) =
            (input.restrictedWeightInput.outerInput.generatorInput.scale : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        _ ≤ (input.restrictedWeightInput.outerInput.generatorInput.n : ℝ) /
            input.restrictedWeightInput.outerInput.generatorInput.epsilon + 2 := by
          linarith [houterStart]
        _ = dimension /
            input.restrictedWeightInput.outerInput.generatorInput.epsilon + 2 := by
          rw [show input.restrictedWeightInput.outerInput.generatorInput.n =
            input.accuracy.n by rfl]
    have hnormSq : normBound ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ hnormNonneg hnorm 2
    have hns := mul_le_mul hdimension hnormSq (sq_nonneg _) hRnonneg
    have hnsM := mul_le_mul hns hfamilySq (sq_nonneg _) (by positivity)
    have hproduct := mul_le_mul hnsM hinverseSq
      (sq_nonneg _) (by positivity)
    have hscaled := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 512)
    calc
      ((input.restrictedWeightInput.outerInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
          dimension /
            input.restrictedWeightInput.outerInput.generatorInput.epsilon + 2 := hstart
      _ = 512 * dimension * normBound ^ 2 * familyBound ^ 2 *
          (1 / epsilon) ^ 2 + 2 := by
        rw [houterEpsilon, input.threshold_cast]
        dsimp [dimension, normBound, familyBound, epsilon]
        field_simp [hepsilon.1.ne', input.familySizeBound_pos.ne']
        ring
      _ ≤ 512 * R * R ^ 2 * (6 * R ^ 3) ^ 2 * R ^ 2 + 2 := by
        have : 512 * (dimension * normBound ^ 2 * familyBound ^ 2 *
            (1 / epsilon) ^ 2) ≤
            512 * (R * R ^ 2 * (6 * R ^ 3) ^ 2 * R ^ 2) := hscaled
        nlinarith
      _ = 18432 * R ^ 11 + 2 := by ring
      _ ≤ 2 ^ 15 * R ^ 11 := by
        have hpow : (1 : ℝ) ≤ R ^ 11 := one_le_pow₀ hR
        norm_num
        nlinarith
  have hRpow : R ^ 10 ≤ R ^ 11 :=
    pow_le_pow_right₀ hR (by omega)
  have hinnerScale' :
      (input.restrictedWeightInput.innerInput.generatorInput.scale : ℝ) + 1 ≤
        2 ^ 15 * R ^ 10 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hinnerScale
  have houterScale' :
      (input.restrictedWeightInput.outerInput.generatorInput.scale : ℝ) + 1 ≤
        2 ^ 15 * R ^ 11 := by
    simpa only [Nat.cast_add, Nat.cast_one] using houterScale
  unfold RestrictedWeightInput.algorithmScale
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    (input.restrictedWeightInput.innerInput.generatorInput.scale : ℝ) +
        input.restrictedWeightInput.outerInput.generatorInput.scale + 1 ≤
        ((input.restrictedWeightInput.innerInput.generatorInput.scale : ℝ) + 1) +
          ((input.restrictedWeightInput.outerInput.generatorInput.scale : ℝ) + 1) := by
      linarith
    _ ≤ 2 ^ 15 * R ^ 10 + 2 ^ 15 * R ^ 11 :=
      add_le_add hinnerScale' houterScale'
    _ ≤ 2 ^ 16 * R ^ 11 := by
      nlinarith [mul_le_mul_of_nonneg_left hRpow (by norm_num : (0 : ℝ) ≤ 2 ^ 15)]

/-- Proposition 6.41's reused degree-eight budget becomes a degree-88
polynomial in the book runtime scale. -/
theorem restrictedWeightPolynomialBudget_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    (input.restrictedWeightInput.polynomialBudget : ℝ) ≤
      2 ^ 148 * input.runtimeScale ^ 88 := by
  have hscale := input.restrictedWeightAlgorithmScale_add_one_cast_le_runtimeScale
  have hpow := pow_le_pow_left₀ (by positivity) hscale 8
  have hpow' :
      ((input.restrictedWeightInput.algorithmScale : ℝ) + 1) ^ 8 ≤
        (2 ^ 16 * input.runtimeScale ^ 11) ^ 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpow
  unfold RestrictedWeightInput.polynomialBudget
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  calc
    (2 : ℝ) ^ 20 *
        ((input.restrictedWeightInput.algorithmScale : ℝ) + 1) ^ 8 ≤
        2 ^ 20 * (2 ^ 16 * input.runtimeScale ^ 11) ^ 8 :=
      mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ = 2 ^ 148 * input.runtimeScale ^ 88 := by
      ring

/-- Proposition 6.40's coefficient construction scale is degree eleven in
the book runtime scale. -/
theorem coefficientGeneratorScale_add_one_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    ((input.coefficientInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
      2 ^ 15 * input.runtimeScale ^ 11 := by
  let R := input.runtimeScale
  let epsilon : ℝ := input.learningParameter.1
  let dimension : ℝ := input.accuracy.n
  let normBound : ℝ := input.fourierBound
  let activeCap : ℝ := goldreichLevinActiveCap input.threshold
  obtain ⟨hR, hdimensionOne, hnormOne, hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hRnonneg : (0 : ℝ) ≤ R :=
    (by positivity : (0 : ℝ) ≤ 1).trans hR
  have hepsilon :=
    positiveLearningParameter_toReal_mem_Ioc input.learningParameter
  have hdimension : dimension ≤ R := by
    dsimp [dimension]
    exact (by norm_num : (input.accuracy.n : ℝ) ≤ input.accuracy.n + 1) |>.trans
      (by simpa [R] using hdimensionOne)
  have hnorm : normBound ≤ R := by
    dsimp [normBound]
    exact (by norm_num : (input.fourierBound : ℝ) ≤ input.fourierBound + 1) |>.trans
      (by simpa [R] using hnormOne)
  have hcap : activeCap ≤ 2 ^ 13 * R ^ 8 := by
    dsimp [activeCap]
    calc
      (goldreichLevinActiveCap input.threshold : ℝ) ≤
          ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ 2 ^ 13 * input.runtimeScale ^ 8 :=
        input.activeCap_add_one_cast_le_runtimeScale
      _ = 2 ^ 13 * R ^ 8 := by rfl
  have hcoefficientEpsilon :
      input.coefficientInput.generatorInput.epsilon =
        epsilon / (2 * activeCap * normBound) := by
    calc
      input.coefficientInput.generatorInput.epsilon =
          input.coefficientInput.epsilon /
            input.coefficientInput.fourierBound :=
        SmallBiasFourierInput.generatorInput_epsilon _
      _ = ((input.learningParameter.1 : ℝ) /
          (2 * goldreichLevinActiveCap input.threshold)) /
            (input.fourierBound : ℝ) := by
        rw [input.coefficientInput_epsilon]
      _ = epsilon / (2 * activeCap * normBound) := by
        dsimp [epsilon, activeCap, normBound]
        ring
  have hstart :=
    smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one
      input.coefficientInput.generatorInput
  have hnormNonneg : 0 ≤ normBound := by positivity
  have hcapNonneg : 0 ≤ activeCap := by positivity
  have hinverseNonneg : 0 ≤ 1 / epsilon :=
    div_nonneg zero_le_one (by simpa [epsilon] using hepsilon.1.le)
  have hdn := mul_le_mul hdimension hcap hcapNonneg hRnonneg
  have hdns := mul_le_mul hdn hnorm hnormNonneg (by positivity)
  have hproduct := mul_le_mul hdns (by simpa [R, epsilon] using hinverse)
    hinverseNonneg (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℝ) ≤ 2)
  have hbound :
      ((input.coefficientInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
        2 * dimension * activeCap * normBound * (1 / epsilon) + 2 := by
    calc
      ((input.coefficientInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
          dimension / input.coefficientInput.generatorInput.epsilon + 2 := by
        calc
          ((input.coefficientInput.generatorInput.scale + 1 : ℕ) : ℝ) =
              (input.coefficientInput.generatorInput.scale : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          _ ≤ (input.coefficientInput.generatorInput.n : ℝ) /
              input.coefficientInput.generatorInput.epsilon + 2 := by
            linarith [hstart]
          _ = dimension / input.coefficientInput.generatorInput.epsilon + 2 := by
            rw [show input.coefficientInput.generatorInput.n =
              input.accuracy.n by rfl]
      _ = 2 * dimension * activeCap * normBound * (1 / epsilon) + 2 := by
        rw [hcoefficientEpsilon]
        dsimp [dimension, activeCap, normBound, epsilon]
        have hcapNe : (goldreichLevinActiveCap input.threshold : ℝ) ≠ 0 := by
          exact_mod_cast (goldreichLevinActiveCap_pos input.threshold).ne'
        have hnormNe : (input.fourierBound : ℝ) ≠ 0 := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
            input.fourierBound_pos).ne'
        field_simp [hepsilon.1.ne', hcapNe, hnormNe]
  calc
    ((input.coefficientInput.generatorInput.scale + 1 : ℕ) : ℝ) ≤
        2 * dimension * activeCap * normBound * (1 / epsilon) + 2 := hbound
    _ ≤ 2 * R * (2 ^ 13 * R ^ 8) * R * R + 2 := by
      have : 2 * (dimension * activeCap * normBound * (1 / epsilon)) ≤
          2 * (R * (2 ^ 13 * R ^ 8) * R * R) := hscaled
      nlinarith
    _ = 2 ^ 14 * R ^ 11 + 2 := by ring
    _ ≤ 2 ^ 15 * R ^ 11 := by
      have hpow : (1 : ℝ) ≤ R ^ 11 := one_le_pow₀ hR
      norm_num
      nlinarith

/-- Proposition 6.40's reused degree-eight budget becomes a degree-88
polynomial in the book runtime scale. -/
theorem coefficientPolynomialBudget_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    (input.coefficientInput.polynomialBudget : ℝ) ≤
      2 ^ 138 * input.runtimeScale ^ 88 := by
  have hscale := input.coefficientGeneratorScale_add_one_cast_le_runtimeScale
  have hpow := pow_le_pow_left₀ (by positivity) hscale 8
  have hpow' :
      ((input.coefficientInput.generatorInput.scale : ℝ) + 1) ^ 8 ≤
        (2 ^ 15 * input.runtimeScale ^ 11) ^ 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpow
  unfold SmallBiasFourierInput.polynomialBudget
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  calc
    (2 : ℝ) ^ 18 *
        ((input.coefficientInput.generatorInput.scale : ℝ) + 1) ^ 8 ≤
        2 ^ 18 * (2 ^ 15 * input.runtimeScale ^ 11) ^ 8 :=
      mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ = 2 ^ 138 * input.runtimeScale ^ 88 := by
      ring

end DeterministicGoldreichLevinInput

/-- Proposition 6.41's construction, shared query batch, and per-candidate
work all obey the same book-parameter polynomial envelope. -/
theorem deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    (deterministicRestrictedWeightConstructionWork
        input.restrictedWeightInput : ℝ) ≤
        2 ^ 148 * input.runtimeScale ^ 88 ∧
      (deterministicGoldreichLevinStageQueryBudget input : ℝ) ≤
        2 ^ 148 * input.runtimeScale ^ 88 ∧
      (deterministicGoldreichLevinRestrictedLocalWork input : ℝ) ≤
        2 ^ 148 * input.runtimeScale ^ 88 := by
  obtain ⟨hconstruction, hqueries, hlocal⟩ :=
    deterministicGoldreichLevinRestrictedComponents_le_polynomialBudget input
  have hbudget := input.restrictedWeightPolynomialBudget_cast_le_runtimeScale
  have hconstructionCast :
      (deterministicRestrictedWeightConstructionWork
          input.restrictedWeightInput : ℝ) ≤
        (input.restrictedWeightInput.polynomialBudget : ℝ) := by
    exact_mod_cast hconstruction
  have hqueriesCast :
      (deterministicGoldreichLevinStageQueryBudget input : ℝ) ≤
        (input.restrictedWeightInput.polynomialBudget : ℝ) := by
    exact_mod_cast hqueries
  have hlocalCast :
      (deterministicGoldreichLevinRestrictedLocalWork input : ℝ) ≤
        (input.restrictedWeightInput.polynomialBudget : ℝ) := by
    exact_mod_cast hlocal
  exact ⟨hconstructionCast.trans hbudget,
    hqueriesCast.trans hbudget, hlocalCast.trans hbudget⟩

/-- Proposition 6.40's construction, shared query batch, and per-coefficient
work all obey the same book-parameter polynomial envelope. -/
theorem deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale
    (input : DeterministicGoldreichLevinInput) :
    (deterministicSmallBiasWork input.coefficientInput.generatorInput : ℝ) ≤
        2 ^ 138 * input.runtimeScale ^ 88 ∧
      (input.coefficientInput.sampleCount : ℝ) ≤
        2 ^ 138 * input.runtimeScale ^ 88 ∧
      (deterministicGoldreichLevinCoefficientLocalWork input : ℝ) ≤
        2 ^ 138 * input.runtimeScale ^ 88 := by
  obtain ⟨hconstruction, hqueries, hlocal⟩ :=
    deterministicGoldreichLevinCoefficientComponents_le_polynomialBudget input
  have hbudget := input.coefficientPolynomialBudget_cast_le_runtimeScale
  have hconstructionCast :
      (deterministicSmallBiasWork input.coefficientInput.generatorInput : ℝ) ≤
        (input.coefficientInput.polynomialBudget : ℝ) := by
    exact_mod_cast hconstruction
  have hqueriesCast : (input.coefficientInput.sampleCount : ℝ) ≤
      (input.coefficientInput.polynomialBudget : ℝ) := by
    exact_mod_cast hqueries
  have hlocalCast :
      (deterministicGoldreichLevinCoefficientLocalWork input : ℝ) ≤
        (input.coefficientInput.polynomialBudget : ℝ) := by
    exact_mod_cast hlocal
  exact ⟨hconstructionCast.trans hbudget,
    hqueriesCast.trans hbudget, hlocalCast.trans hbudget⟩

namespace DeterministicGoldreichLevinInput

/-- One common explicit polynomial envelope for both resource components. -/
noncomputable def polynomialRuntimeBound
    (input : DeterministicGoldreichLevinInput) : ℝ :=
  2 ^ 170 * input.runtimeScale ^ 100

/-- The exact target-independent query budget is polynomial in `n`, `s`,
and `1 / ε`. -/
theorem queryBudget_cast_le_polynomialRuntimeBound
    (input : DeterministicGoldreichLevinInput) :
    (deterministicGoldreichLevinQueryBudget input : ℝ) ≤
      input.polynomialRuntimeBound := by
  let R := input.runtimeScale
  obtain ⟨hR, hdimensionOne, _hnormOne, _hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hRnonneg : (0 : ℝ) ≤ R :=
    (by positivity : (0 : ℝ) ≤ 1).trans hR
  have hdimension : (input.accuracy.n : ℝ) ≤ R :=
    (by norm_num : (input.accuracy.n : ℝ) ≤ input.accuracy.n + 1) |>.trans
      (by simpa [R] using hdimensionOne)
  obtain ⟨_hconstruction, hstageQueries, _hlocal⟩ :=
    deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale input
  obtain ⟨_hcoefficientConstruction, hcoefficientQueries, _hcoefficientLocal⟩ :=
    deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale input
  have hfirst := mul_le_mul hdimension hstageQueries (by positivity) hRnonneg
  have hR88_89 : R ^ 88 ≤ R ^ 89 := pow_le_pow_right₀ hR (by omega)
  have hR89_100 : R ^ 89 ≤ R ^ 100 := pow_le_pow_right₀ hR (by omega)
  have hsecond : (2 ^ 138 : ℝ) * R ^ 88 ≤ 2 ^ 138 * R ^ 89 :=
    mul_le_mul_of_nonneg_left hR88_89
      (by positivity : (0 : ℝ) ≤ 2 ^ 138)
  unfold deterministicGoldreichLevinQueryBudget
    deterministicGoldreichLevinListQueryBudget
    deterministicGoldreichLevinCoefficientQueryBudget
    polynomialRuntimeBound
  simp only [Nat.cast_add, Nat.cast_mul]
  calc
    (input.accuracy.n : ℝ) *
          deterministicGoldreichLevinStageQueryBudget input +
        input.coefficientInput.sampleCount ≤
        R * (2 ^ 148 * R ^ 88) + 2 ^ 138 * R ^ 88 :=
      add_le_add hfirst hcoefficientQueries
    _ = 2 ^ 148 * R ^ 89 + 2 ^ 138 * R ^ 88 := by ring
    _ ≤ 2 ^ 148 * R ^ 89 + 2 ^ 138 * R ^ 89 :=
      add_le_add le_rfl hsecond
    _ = (2 ^ 148 + 2 ^ 138) * R ^ 89 := by ring
    _ ≤ 2 ^ 149 * R ^ 89 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 89)
    _ ≤ 2 ^ 149 * R ^ 100 :=
      mul_le_mul_of_nonneg_left hR89_100 (by positivity)
    _ ≤ 2 ^ 170 * R ^ 100 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 100)

set_option maxHeartbeats 800000 in
-- Normalizing this explicit degree-100 work envelope exceeds the default elaboration budget.
set_option maxRecDepth 2000 in
/-- The exact target-independent charged-work budget is polynomial in `n`,
`s`, and `1 / ε`. -/
theorem workBudget_cast_le_polynomialRuntimeBound
    (input : DeterministicGoldreichLevinInput) :
    (deterministicGoldreichLevinWorkBudget input : ℝ) ≤
      input.polynomialRuntimeBound := by
  let R := input.runtimeScale
  obtain ⟨hR, hdimensionOne, _hnormOne, _hinverse⟩ :=
    input.runtimeScale_factor_bounds
  have hRnonneg : (0 : ℝ) ≤ R :=
    (by positivity : (0 : ℝ) ≤ 1).trans hR
  have hdimension : (input.accuracy.n : ℝ) ≤ R :=
    (by norm_num : (input.accuracy.n : ℝ) ≤ input.accuracy.n + 1) |>.trans
      (by simpa [R] using hdimensionOne)
  have hdimensionSucc : ((input.accuracy.n + 1 : ℕ) : ℝ) ≤ R := by
    simpa [R] using hdimensionOne
  have hcapSucc := input.activeCap_add_one_cast_le_runtimeScale
  have hcap : (goldreichLevinActiveCap input.threshold : ℝ) ≤
      2 ^ 13 * R ^ 8 := by
    calc
      (goldreichLevinActiveCap input.threshold : ℝ) ≤
          ((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ 2 ^ 13 * input.runtimeScale ^ 8 := hcapSucc
      _ = 2 ^ 13 * R ^ 8 := by rfl
  obtain ⟨hrestrictedConstruction, hstageQueries, hrestrictedLocal⟩ :=
    deterministicGoldreichLevinRestrictedComponents_cast_le_runtimeScale input
  obtain ⟨hcoefficientConstruction, hcoefficientQueries, hcoefficientLocal⟩ :=
    deterministicGoldreichLevinCoefficientComponents_cast_le_runtimeScale input
  have hdimensionSq :
      (((input.accuracy.n + 1 : ℕ) : ℝ) ^ 2) ≤ R ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdimensionSucc 2
  have hcapSuccSq :
      (((goldreichLevinActiveCap input.threshold + 1 : ℕ) : ℝ) ^ 2) ≤
        (2 ^ 13 * R ^ 8) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (by simpa [R] using hcapSucc) 2
  have hcontroller :
      (goldreichLevinControllerStepWork input.accuracy.n input.threshold : ℝ) ≤
        2 ^ 30 * R ^ 18 := by
    unfold goldreichLevinControllerStepWork
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    have hproduct := mul_le_mul hdimensionSq hcapSuccSq
      (sq_nonneg _) (by positivity)
    have hproduct' :
        ((input.accuracy.n : ℝ) + 1) ^ 2 *
            ((goldreichLevinActiveCap input.threshold : ℝ) + 1) ^ 2 ≤
          R ^ 2 * (2 ^ 13 * R ^ 8) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hproduct
    calc
      16 * ((input.accuracy.n : ℝ) + 1) ^ 2 *
          ((goldreichLevinActiveCap input.threshold : ℝ) + 1) ^ 2 =
          16 * (((input.accuracy.n : ℝ) + 1) ^ 2 *
            ((goldreichLevinActiveCap input.threshold : ℝ) + 1) ^ 2) := by
        ring
      _ ≤
          16 * (R ^ 2 * (2 ^ 13 * R ^ 8) ^ 2) :=
        mul_le_mul_of_nonneg_left hproduct'
          (by norm_num : (0 : ℝ) ≤ 16)
      _ = 2 ^ 30 * R ^ 18 := by ring
  have hcapLocal := mul_le_mul hcap hrestrictedLocal
    (by positivity) (by positivity)
  have htwiceCapLocal :=
    mul_le_mul_of_nonneg_left hcapLocal (by norm_num : (0 : ℝ) ≤ 2)
  have htwiceCapLocal' :
      2 * (goldreichLevinActiveCap input.threshold : ℝ) *
          deterministicGoldreichLevinRestrictedLocalWork input ≤
        2 * (2 ^ 13 * R ^ 8) * (2 ^ 148 * R ^ 88) := by
    simpa only [mul_assoc] using htwiceCapLocal
  have hR18_96 : R ^ 18 ≤ R ^ 96 := pow_le_pow_right₀ hR (by omega)
  have hR88_96 : R ^ 88 ≤ R ^ 96 := pow_le_pow_right₀ hR (by omega)
  have hstageWork :
      (deterministicGoldreichLevinStageWorkBudget input : ℝ) ≤
        2 ^ 163 * R ^ 96 := by
    unfold deterministicGoldreichLevinStageWorkBudget
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      (goldreichLevinControllerStepWork input.accuracy.n input.threshold : ℝ) +
          deterministicGoldreichLevinStageQueryBudget input +
            2 * goldreichLevinActiveCap input.threshold *
              deterministicGoldreichLevinRestrictedLocalWork input ≤
          2 ^ 30 * R ^ 18 + 2 ^ 148 * R ^ 88 +
            2 * (2 ^ 13 * R ^ 8) * (2 ^ 148 * R ^ 88) :=
        add_le_add (add_le_add hcontroller hstageQueries) htwiceCapLocal'
      _ = 2 ^ 30 * R ^ 18 + 2 ^ 148 * R ^ 88 + 2 ^ 162 * R ^ 96 := by ring
      _ ≤ 2 ^ 30 * R ^ 96 + 2 ^ 148 * R ^ 96 + 2 ^ 162 * R ^ 96 :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hR18_96 (by positivity))
          (mul_le_mul_of_nonneg_left hR88_96 (by positivity))) le_rfl
      _ = (2 ^ 30 + 2 ^ 148 + 2 ^ 162) * R ^ 96 := by ring
      _ ≤ 2 ^ 163 * R ^ 96 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 96)
  have hdimensionStage := mul_le_mul hdimension hstageWork
    (by positivity) hRnonneg
  have hR88_97 : R ^ 88 ≤ R ^ 97 := pow_le_pow_right₀ hR (by omega)
  have hfirstList : (2 ^ 148 : ℝ) * R ^ 88 ≤ 2 ^ 148 * R ^ 97 :=
    mul_le_mul_of_nonneg_left hR88_97
      (by positivity : (0 : ℝ) ≤ 2 ^ 148)
  have hlistWork :
      (deterministicGoldreichLevinListWorkBudget input : ℝ) ≤
        2 ^ 164 * R ^ 97 := by
    unfold deterministicGoldreichLevinListWorkBudget
    simp only [Nat.cast_add, Nat.cast_mul]
    calc
      (deterministicRestrictedWeightConstructionWork
          input.restrictedWeightInput : ℝ) +
          input.accuracy.n * deterministicGoldreichLevinStageWorkBudget input ≤
          2 ^ 148 * R ^ 88 + R * (2 ^ 163 * R ^ 96) :=
        add_le_add hrestrictedConstruction hdimensionStage
      _ = 2 ^ 148 * R ^ 88 + 2 ^ 163 * R ^ 97 := by ring
      _ ≤ 2 ^ 148 * R ^ 97 + 2 ^ 163 * R ^ 97 :=
        add_le_add hfirstList le_rfl
      _ = (2 ^ 148 + 2 ^ 163) * R ^ 97 := by ring
      _ ≤ 2 ^ 164 * R ^ 97 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 97)
  have hcoefficientCapLocal := mul_le_mul hcap hcoefficientLocal
    (by positivity) (by positivity)
  have hcoefficientCapLocal' :
      (goldreichLevinActiveCap input.threshold : ℝ) *
          deterministicGoldreichLevinCoefficientLocalWork input ≤
        2 ^ 151 * R ^ 96 := by
    calc
      (goldreichLevinActiveCap input.threshold : ℝ) *
          deterministicGoldreichLevinCoefficientLocalWork input ≤
          (2 ^ 13 * R ^ 8) * (2 ^ 138 * R ^ 88) := hcoefficientCapLocal
      _ = 2 ^ 151 * R ^ 96 := by ring
  have hcoefficientWork :
      (deterministicGoldreichLevinCoefficientWorkBudget input : ℝ) ≤
        2 ^ 152 * R ^ 96 := by
    unfold deterministicGoldreichLevinCoefficientWorkBudget
    simp only [Nat.cast_add, Nat.cast_mul]
    calc
      (deterministicSmallBiasWork input.coefficientInput.generatorInput : ℝ) +
          input.coefficientInput.sampleCount +
            goldreichLevinActiveCap input.threshold *
              deterministicGoldreichLevinCoefficientLocalWork input ≤
          2 ^ 138 * R ^ 88 + 2 ^ 138 * R ^ 88 + 2 ^ 151 * R ^ 96 :=
        add_le_add (add_le_add hcoefficientConstruction hcoefficientQueries)
          hcoefficientCapLocal'
      _ ≤ 2 ^ 138 * R ^ 96 + 2 ^ 138 * R ^ 96 + 2 ^ 151 * R ^ 96 :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hR88_96 (by positivity))
          (mul_le_mul_of_nonneg_left hR88_96 (by positivity))) le_rfl
      _ = (2 ^ 138 + 2 ^ 138 + 2 ^ 151) * R ^ 96 := by ring
      _ ≤ 2 ^ 152 * R ^ 96 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 96)
  have hR96_97 : R ^ 96 ≤ R ^ 97 := pow_le_pow_right₀ hR (by omega)
  have hR97_100 : R ^ 97 ≤ R ^ 100 := pow_le_pow_right₀ hR (by omega)
  have hsecondWork : (2 ^ 152 : ℝ) * R ^ 96 ≤ 2 ^ 152 * R ^ 97 :=
    mul_le_mul_of_nonneg_left hR96_97
      (by positivity : (0 : ℝ) ≤ 2 ^ 152)
  unfold deterministicGoldreichLevinWorkBudget polynomialRuntimeBound
  simp only [Nat.cast_add]
  calc
    (deterministicGoldreichLevinListWorkBudget input : ℝ) +
        deterministicGoldreichLevinCoefficientWorkBudget input ≤
        2 ^ 164 * R ^ 97 + 2 ^ 152 * R ^ 96 :=
      add_le_add hlistWork hcoefficientWork
    _ ≤ 2 ^ 164 * R ^ 97 + 2 ^ 152 * R ^ 97 :=
      add_le_add le_rfl hsecondWork
    _ = (2 ^ 164 + 2 ^ 152) * R ^ 97 := by ring
    _ ≤ 2 ^ 165 * R ^ 97 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 97)
    _ ≤ 2 ^ 165 * R ^ 100 :=
      mul_le_mul_of_nonneg_left hR97_100 (by positivity)
    _ ≤ 2 ^ 170 * R ^ 100 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hRnonneg 100)

end DeterministicGoldreichLevinInput

/-- Actual deterministic query execution obeys the book-parameter query
polynomial. -/
theorem deterministicGoldreichLevinLearner_queries_polynomial_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    ((DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinLearner input)).2.queries : ℝ) ≤
        input.polynomialRuntimeBound := by
  have hresource := deterministicGoldreichLevinLearner_resource_bounds input target
  have hcast :
      ((DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.queries : ℝ) ≤
        (deterministicGoldreichLevinQueryBudget input : ℝ) := by
    exact_mod_cast hresource.2.1
  exact hcast.trans input.queryBudget_cast_le_polynomialRuntimeBound

/-- Actual deterministic query execution obeys the book-parameter work
polynomial. -/
theorem deterministicGoldreichLevinLearner_work_polynomial_le
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n) :
    ((DeterministicQueryProgram.runWithCost target
      (deterministicGoldreichLevinLearner input)).2.work : ℝ) ≤
        input.polynomialRuntimeBound := by
  have hresource := deterministicGoldreichLevinLearner_resource_bounds input target
  have hcast :
      ((DeterministicQueryProgram.runWithCost target
        (deterministicGoldreichLevinLearner input)).2.work : ℝ) ≤
        (deterministicGoldreichLevinWorkBudget input : ℝ) := by
    exact_mod_cast hresource.2.2
  exact hcast.trans input.workBudget_cast_le_polynomialRuntimeBound

/-- Book-facing Theorem 6.42 conclusion in the Chapter 3 query model: every
execution is accurate, deterministic, query-polynomial, and work-polynomial. -/
theorem deterministicGoldreichLevinLearningProgram_spec
    (input : DeterministicGoldreichLevinInput)
    (target : BooleanFunction input.accuracy.n)
    (hnorm : fourierOneNorm target.toReal ≤ input.fourierBound)
    (outcome : SparseFourierHypothesis input.accuracy.n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (deterministicGoldreichLevinLearningProgram input)).support) :
    relativeHammingDist target outcome.1.evaluate ≤
        (input.learningParameter.1 : ℝ) ∧
      outcome.2.randomExamples = 0 ∧
      (outcome.2.queries : ℝ) ≤ input.polynomialRuntimeBound ∧
      (outcome.2.work : ℝ) ≤ input.polynomialRuntimeBound := by
  have haccuracy :=
    deterministicGoldreichLevinLearningProgram_relativeHammingDist_le
      input target hnorm outcome houtcome
  have hresource := deterministicGoldreichLevinLearningProgram_resource_bounds
    input target outcome houtcome
  have hqueryCast : (outcome.2.queries : ℝ) ≤
      (deterministicGoldreichLevinQueryBudget input : ℝ) := by
    exact_mod_cast hresource.2.1
  have hworkCast : (outcome.2.work : ℝ) ≤
      (deterministicGoldreichLevinWorkBudget input : ℝ) := by
    exact_mod_cast hresource.2.2
  exact ⟨haccuracy, hresource.1,
    hqueryCast.trans input.queryBudget_cast_le_polynomialRuntimeBound,
    hworkCast.trans input.workBudget_cast_le_polynomialRuntimeBound⟩

/-- A complete finite Theorem 6.42 task, including the varying input and
its dimension-compatible target oracle. -/
abbrev DeterministicGoldreichLevinTask :=
  Σ input : DeterministicGoldreichLevinInput,
    BooleanFunction input.accuracy.n

/-- Genuine asymptotic scale of a complete task. -/
noncomputable def deterministicGoldreichLevinTaskScale
    (task : DeterministicGoldreichLevinTask) : ℝ :=
  task.1.runtimeScale

set_option maxRecDepth 2000 in
/-- Actual membership-query complexity is polynomial in `n`, `s`, and
`1 / ε`. -/
theorem deterministicGoldreichLevinLearner_queries_isBigO :
    Asymptotics.IsBigO
      (Filter.comap deterministicGoldreichLevinTaskScale Filter.atTop)
      (fun task : DeterministicGoldreichLevinTask ↦
        ((DeterministicQueryProgram.runWithCost task.2
          (deterministicGoldreichLevinLearner task.1)).2.queries : ℝ))
      (fun task : DeterministicGoldreichLevinTask ↦
        deterministicGoldreichLevinTaskScale task ^ 100) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 170 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  have hbound := deterministicGoldreichLevinLearner_queries_polynomial_le
    task.1 task.2
  have hscaleNonneg : 0 ≤ deterministicGoldreichLevinTaskScale task := by
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans
      task.1.runtimeScale_factor_bounds.1
  rw [Real.norm_of_nonneg (by positivity : 0 ≤
      ((DeterministicQueryProgram.runWithCost task.2
        (deterministicGoldreichLevinLearner task.1)).2.queries : ℝ)),
    Real.norm_of_nonneg (pow_nonneg hscaleNonneg 100)]
  simpa [DeterministicGoldreichLevinInput.polynomialRuntimeBound,
    deterministicGoldreichLevinTaskScale] using hbound

set_option maxRecDepth 2000 in
/-- Actual charged local work is polynomial in `n`, `s`, and `1 / ε`. -/
theorem deterministicGoldreichLevinLearner_work_isBigO :
    Asymptotics.IsBigO
      (Filter.comap deterministicGoldreichLevinTaskScale Filter.atTop)
      (fun task : DeterministicGoldreichLevinTask ↦
        ((DeterministicQueryProgram.runWithCost task.2
          (deterministicGoldreichLevinLearner task.1)).2.work : ℝ))
      (fun task : DeterministicGoldreichLevinTask ↦
        deterministicGoldreichLevinTaskScale task ^ 100) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 170 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  have hbound := deterministicGoldreichLevinLearner_work_polynomial_le
    task.1 task.2
  have hscaleNonneg : 0 ≤ deterministicGoldreichLevinTaskScale task := by
    exact (zero_le_one : (0 : ℝ) ≤ 1).trans
      task.1.runtimeScale_factor_bounds.1
  rw [Real.norm_of_nonneg (by positivity : 0 ≤
      ((DeterministicQueryProgram.runWithCost task.2
        (deterministicGoldreichLevinLearner task.1)).2.work : ℝ)),
    Real.norm_of_nonneg (pow_nonneg hscaleNonneg 100)]
  simpa [DeterministicGoldreichLevinInput.polynomialRuntimeBound,
    deterministicGoldreichLevinTaskScale] using hbound

end FABL
