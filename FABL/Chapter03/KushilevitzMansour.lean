/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.GoldreichLevinAlgorithm
public import FABL.Chapter03.QueryLearning

/-!
# The Kushilevitz--Mansour algorithm

Book items: Theorem 3.37, Theorem 3.38, Exercise 3.38, Exercise 3.39.

Composition of Goldreich--Levin with the finite-family query learner, including Theorems 3.37 and
3.38 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

variable {n : ℕ}

def oneTwentiethLearningParameter : PositiveLearningParameter := by
  exact ⟨1 / 20, by norm_num, by norm_num⟩

def kushilevitzMansourThreshold
    (ε : PositiveLearningParameter) (M : ℕ) (hM : 0 < M) :
    GoldreichLevinThreshold := by
  have hdenominator : (0 : ℚ) < 4 * M := by positivity
  refine ⟨ε.1 / (4 * M), div_pos ε.2.1 hdenominator, ?_⟩
  rw [div_le_iff₀ hdenominator]
  have hMone : (1 : ℚ) ≤ M := by exact_mod_cast hM
  nlinarith [ε.2.2]

theorem isFourierSpectrumConcentratedOn_of_goldreichLevin_complete
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (initialFamily outputFamily : Finset (Finset (Fin n)))
    (hcard : initialFamily.card ≤ M)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 4) (↑initialFamily : Set (Finset (Fin n))))
    (hcomplete : ∀ U : Finset (Fin n),
      ((kushilevitzMansourThreshold ε M hM).1 : ℝ) ≤
          |fourierCoeff target.toReal U| →
        U ∈ outputFamily) :
    IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 2) (↑outputFamily : Set (Finset (Fin n))) := by
  let outsideOutput :=
    Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ outputFamily
  let outsideInitial :=
    Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ initialFamily
  let missedInitial := initialFamily.filter fun S ↦ S ∉ outputFamily
  have hsubset : outsideOutput ⊆ outsideInitial ∪ missedInitial := by
    intro S hS
    have hnotOutput : S ∉ outputFamily := (Finset.mem_filter.mp hS).2
    by_cases hInitial : S ∈ initialFamily
    · exact Finset.mem_union_right outsideInitial
        (Finset.mem_filter.mpr ⟨hInitial, hnotOutput⟩)
    · exact Finset.mem_union_left missedInitial
        (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hInitial⟩)
  have hdisjoint : Disjoint outsideInitial missedInitial := by
    refine Finset.disjoint_left.mpr ?_
    intro S houtside hmissed
    exact (Finset.mem_filter.mp houtside).2 (Finset.mem_filter.mp hmissed).1
  have hmissedTerm : ∀ S ∈ missedInitial,
      fourierWeight target.toReal S ≤
        ((kushilevitzMansourThreshold ε M hM).1 : ℝ) ^ 2 := by
    intro S hS
    have hnotOutput : S ∉ outputFamily := (Finset.mem_filter.mp hS).2
    have hsmall : |fourierCoeff target.toReal S| <
        ((kushilevitzMansourThreshold ε M hM).1 : ℝ) := by
      exact lt_of_not_ge fun h ↦ hnotOutput (hcomplete S h)
    unfold fourierWeight
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (Rat.cast_nonneg.mpr
      (kushilevitzMansourThreshold ε M hM).2.1.le)).2 hsmall.le
  have hmissedCard : missedInitial.card ≤ M :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have hmissedWeight :
      (∑ S ∈ missedInitial, fourierWeight target.toReal S) ≤
        (ε.1 : ℝ) / 4 := by
    calc
      (∑ S ∈ missedInitial, fourierWeight target.toReal S) ≤
          ∑ _S ∈ missedInitial,
            ((kushilevitzMansourThreshold ε M hM).1 : ℝ) ^ 2 :=
        Finset.sum_le_sum hmissedTerm
      _ = (missedInitial.card : ℝ) *
          ((kushilevitzMansourThreshold ε M hM).1 : ℝ) ^ 2 := by simp
      _ ≤ (M : ℝ) *
          ((kushilevitzMansourThreshold ε M hM).1 : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hmissedCard
        · positivity
      _ ≤ (ε.1 : ℝ) / 4 := by
        have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
        have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
        have hε := positiveLearningParameter_toReal_mem_Ioc ε
        change (M : ℝ) * (((ε.1 : ℚ) / (4 * M) : ℚ) : ℝ) ^ 2 ≤
          (ε.1 : ℝ) / 4
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
          Rat.cast_natCast]
        field_simp
        have hεle : (ε.1 : ℝ) ≤ 4 * M := by nlinarith [hε.2]
        have hmul := mul_le_mul_of_nonneg_left hεle hε.1.le
        nlinarith
  unfold IsFourierSpectrumConcentratedOn fourierWeightOutside at hconcentration
  have houtsideInitial :
      (∑ S ∈ outsideInitial, fourierWeight target.toReal S) ≤
        (ε.1 : ℝ) / 4 := by
    simpa [outsideInitial] using hconcentration
  have hbound :
      (∑ S ∈ outsideOutput, fourierWeight target.toReal S) ≤
        (ε.1 : ℝ) / 2 := by
    calc
      (∑ S ∈ outsideOutput, fourierWeight target.toReal S) ≤
          ∑ S ∈ outsideInitial ∪ missedInitial,
            fourierWeight target.toReal S := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun S _ _ ↦ by unfold fourierWeight; positivity)
      _ = (∑ S ∈ outsideInitial, fourierWeight target.toReal S) +
          ∑ S ∈ missedInitial, fourierWeight target.toReal S := by
        rw [Finset.sum_union hdisjoint]
      _ ≤ (ε.1 : ℝ) / 2 := by linarith
  simpa [IsFourierSpectrumConcentratedOn, fourierWeightOutside, outsideOutput] using hbound

def SparseFourierHypothesis.empty (n : ℕ) : SparseFourierHypothesis n :=
  ⟨∅, fun S ↦ isEmptyElim S⟩

noncomputable def kushilevitzMansourSecondStage
    (ε : PositiveLearningParameter) (M : ℕ) (hM : 0 < M)
    (state : GoldreichLevinQueryState n) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  match state.active with
  | none => .pure (SparseFourierHypothesis.empty n)
  | some family =>
      if family.card ≤
          goldreichLevinActiveCap (kushilevitzMansourThreshold ε M hM) then
        if hfamily : family.Nonempty then
          queriedFiniteFamilyFourierEstimatorProgramWithConfidence
            family hfamily ε oneTwentiethLearningParameter
        else
          .pure (SparseFourierHypothesis.empty n)
      else
        .pure (SparseFourierHypothesis.empty n)

noncomputable def kushilevitzMansourProgram
    (ε : PositiveLearningParameter) (M : ℕ) (hM : 0 < M) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  LearningProgram.bind (kushilevitzMansourSecondStage ε M hM)
    (goldreichLevinQueryProgram (kushilevitzMansourThreshold ε M hM))

theorem kushilevitzMansourProgram_failureProbability_le_one_tenth
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (initialFamily : Finset (Finset (Fin n)))
    (hcard : initialFamily.card ≤ M)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 4) (↑initialFamily : Set (Finset (Fin n)))) :
    LearningProgram.eventProbability (kushilevitzMansourProgram ε M hM) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      1 / 10 := by
  let τ := kushilevitzMansourThreshold ε M hM
  have hcombined := LearningProgram.eventProbability_bind_le_add
    target (goldreichLevinQueryProgram τ)
    (kushilevitzMansourSecondStage ε M hM)
    (fun state ↦ ¬state.IsCorrectOutput target τ)
    (fun hypothesis ↦
      (ε.1 : ℝ) < relativeHammingDist target hypothesis.evaluate)
    (1 / 20) (1 / 20) (by norm_num) (by norm_num)
    (goldreichLevinQueryProgram_incorrectProbability_le_one_twentieth target τ)
    (by
      intro state hstate
      have hcorrect : state.IsCorrectOutput target τ := by
        exact not_not.mp hstate
      obtain ⟨family, hactive, hcomplete, hsound, hcap, hcardReal⟩ := hcorrect
      have hfamilyConcentration :=
        isFourierSpectrumConcentratedOn_of_goldreichLevin_complete
          target ε M hM initialFamily family hcard hconcentration hcomplete
      have hfamilyNonempty := finiteFamily_nonempty_of_spectrum_concentrated
        target family ε hfamilyConcentration
      dsimp [τ] at hcap
      simp only [kushilevitzMansourSecondStage, hactive]
      rw [if_pos hcap, dif_pos hfamilyNonempty]
      simpa [oneTwentiethLearningParameter] using
        queriedFiniteFamilyFourierEstimatorProgramWithConfidence_failureProbability_le
          target family hfamilyNonempty ε oneTwentiethLearningParameter
          hfamilyConcentration)
  have hsum : (1 / 20 : ℝ) + 1 / 20 = 1 / 10 := by norm_num
  rw [hsum] at hcombined
  simpa [kushilevitzMansourProgram, τ] using hcombined

/-- In the nontrivial accuracy range, a family carrying all but `ε/4` Fourier weight cannot have
cardinality bounded by zero. -/
theorem positive_familyBound_of_spectrum_concentrated
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (family : Finset (Finset (Fin n)))
    (hcard : family.card ≤ M)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 4) (↑family : Set (Finset (Fin n)))) :
    0 < M := by
  by_contra hM
  have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
  have hcardZero : family.card = 0 := by omega
  have hfamilyEmpty : family = ∅ := Finset.card_eq_zero.mp hcardZero
  rw [hfamilyEmpty] at hconcentration
  have htotal : fourierWeightOutside target.toReal
      (∅ : Set (Finset (Fin n))) = 1 := by
    simp [fourierWeightOutside, fourierWeight, sum_sq_fourierCoeff_eq_one]
  have hone : (1 : ℝ) ≤ (ε.1 : ℝ) / 4 := by
    simpa [IsFourierSpectrumConcentratedOn, htotal] using hconcentration
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  norm_num at hone
  nlinarith [hε.2]

/-- Target-independent KM program for a stated family-size bound; the zero-bound branch is a
zero-cost fallback and is vacuous under the theorem's concentration premise. -/
noncomputable def kushilevitzMansourProgramForBound
    (ε : PositiveLearningParameter) (M : ℕ) :
    LearningProgram n .queries (SparseFourierHypothesis n) :=
  if hM : 0 < M then
    kushilevitzMansourProgram ε M hM
  else
    .pure (SparseFourierHypothesis.empty n)

/-- Theorem 3.37 without an extra positivity assumption on the advertised family-size bound. -/
theorem kushilevitzMansourProgramForBound_failureProbability_le_one_tenth
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (initialFamily : Finset (Finset (Fin n)))
    (hcard : initialFamily.card ≤ M)
    (hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 4) (↑initialFamily : Set (Finset (Fin n)))) :
    LearningProgram.eventProbability
        (kushilevitzMansourProgramForBound ε M) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      1 / 10 := by
  have hM := positive_familyBound_of_spectrum_concentrated
    target ε M initialFamily hcard hconcentration
  rw [kushilevitzMansourProgramForBound, dif_pos hM]
  exact kushilevitzMansourProgram_failureProbability_le_one_tenth
    target ε M hM initialFamily hcard hconcentration

noncomputable def fourierOneNormFamilySizeBound
    (s : ℝ) (ε : PositiveLearningParameter) : ℕ :=
  max 1 (Nat.ceil (4 * s ^ 2 / (ε.1 : ℝ)))

theorem fourierOneNormFamilySizeBound_pos
    (s : ℝ) (ε : PositiveLearningParameter) :
    0 < fourierOneNormFamilySizeBound s ε := by
  simp [fourierOneNormFamilySizeBound]

theorem card_l1ConcentratingFourierFamily_le_familySizeBound
    (target : BooleanFunction n) (s : ℝ) (ε : PositiveLearningParameter)
    (hnorm : fourierOneNorm target.toReal ≤ s) :
    (l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)).card ≤
      fourierOneNormFamilySizeBound s ε := by
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  have hη : (0 : ℝ) < (ε.1 : ℝ) / 4 := div_pos hε.1 (by norm_num)
  have hnormNonneg := fourierOneNorm_nonneg target.toReal
  have hsNonneg : 0 ≤ s := hnormNonneg.trans hnorm
  have hsquare : fourierOneNorm target.toReal ^ 2 ≤ s ^ 2 :=
    (sq_le_sq₀ hnormNonneg hsNonneg).2 hnorm
  have hcardReal := card_l1ConcentratingFourierFamily_le target.toReal hη
  have hcardBound :
      ((l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)).card : ℝ) ≤
        4 * s ^ 2 / (ε.1 : ℝ) := by
    calc
      ((l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)).card : ℝ) ≤
          fourierOneNorm target.toReal ^ 2 / ((ε.1 : ℝ) / 4) := hcardReal
      _ = 4 * fourierOneNorm target.toReal ^ 2 / (ε.1 : ℝ) := by ring
      _ ≤ 4 * s ^ 2 / (ε.1 : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hε.1.le
  have hceilReal :
      ((l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)).card : ℝ) ≤
        (Nat.ceil (4 * s ^ 2 / (ε.1 : ℝ)) : ℝ) :=
    hcardBound.trans (Nat.le_ceil _)
  have hceilNat :
      (l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)).card ≤
        Nat.ceil (4 * s ^ 2 / (ε.1 : ℝ)) := by
    exact_mod_cast hceilReal
  exact hceilNat.trans (Nat.le_max_right _ _)

theorem fourierOneNormClass_queryLearnable
    (target : BooleanFunction n) (s : ℝ) (ε : PositiveLearningParameter)
    (hnorm : fourierOneNorm target.toReal ≤ s) :
    LearningProgram.eventProbability
        (kushilevitzMansourProgramForBound ε
          (fourierOneNormFamilySizeBound s ε)) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      1 / 10 := by
  let family :=
    l1ConcentratingFourierFamily target.toReal ((ε.1 : ℝ) / 4)
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  have hconcentration : IsFourierSpectrumConcentratedOn target.toReal
      ((ε.1 : ℝ) / 4) (↑family : Set (Finset (Fin n))) := by
    exact isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily
      target.toReal (div_pos hε.1 (by norm_num))
  exact kushilevitzMansourProgramForBound_failureProbability_le_one_tenth
    target ε (fourierOneNormFamilySizeBound s ε) family
    (card_l1ConcentratingFourierFamily_le_familySizeBound target s ε hnorm)
    hconcentration

/-- A sign-cube Boolean function represented by a binary decision tree has Fourier one-norm at
most the tree's number of leaves. -/
theorem fourierOneNorm_le_leafCount_of_decisionTree
    {available : Finset (Fin n)}
    (target : BooleanFunction n)
    (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes (fun x ↦ target.toReal (binaryCubeSignEquiv n x))) :
    fourierOneNorm target.toReal ≤ (T.leafCount : ℝ) := by
  rw [fourierOneNorm_eq_spectralPNorm_one]
  have hbound :=
    T.spectralPNorm_one_le_infinityNorm_mul_leafCount_of_computes
      (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) hT
  calc
    spectralPNorm 1 (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) ≤
        binaryFunctionInfinityNorm
            (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) * (T.leafCount : ℝ) :=
      hbound
    _ = (T.leafCount : ℝ) := by
      have hinfty :
          binaryFunctionInfinityNorm
              (fun x ↦ target.toReal (binaryCubeSignEquiv n x)) = 1 := by
        unfold binaryFunctionInfinityNorm
        apply Finset.sup'_eq_of_forall
        intro x hx
        change |signValue (target (binaryCubeSignEquiv n x))| = 1
        rcases signValue_eq_neg_one_or_one
          (target (binaryCubeSignEquiv n x)) with hvalue | hvalue
        · rw [hvalue]
          norm_num
        · rw [hvalue]
          norm_num
      rw [hinfty, one_mul]

theorem decisionTreeSizeClass_queryLearnable
    {available : Finset (Fin n)}
    (target : BooleanFunction n) (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes (fun x ↦ target.toReal (binaryCubeSignEquiv n x)))
    (s : ℕ) (hsize : T.leafCount ≤ s) (ε : PositiveLearningParameter) :
    LearningProgram.eventProbability
        (kushilevitzMansourProgramForBound ε
          (fourierOneNormFamilySizeBound (s : ℝ) ε)) target
        (fun outcome ↦
          (ε.1 : ℝ) < relativeHammingDist target outcome.1.evaluate) ≤
      1 / 10 := by
  apply fourierOneNormClass_queryLearnable
  exact (fourierOneNorm_le_leafCount_of_decisionTree target T hT).trans (by
    exact_mod_cast hsize)

/-- A second-stage execution either takes a zero-cost fallback or runs the guarded finite-family
query learner on a nonempty family below the Goldreich--Levin cap. -/
theorem kushilevitzMansourSecondStage_cost_cases
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M) (state : GoldreichLevinQueryState n)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourSecondStage ε M hM state)).support) :
    outcome.2 = 0 ∨
      ∃ family, ∃ hnonempty : family.Nonempty,
        state.active = some family ∧
        family.card ≤ goldreichLevinActiveCap
          (kushilevitzMansourThreshold ε M hM) ∧
        outcome.2 = queriedFiniteFamilyFourierEstimatorCost (n := n) family
          (queriedFiniteFamilySamplesPerCoefficient family hnonempty ε
            oneTwentiethLearningParameter) := by
  cases hactive : state.active with
  | none =>
      rw [kushilevitzMansourSecondStage, hactive,
        LearningProgram.runWithCost, PMF.mem_support_pure_iff] at houtcome
      subst outcome
      exact Or.inl rfl
  | some family =>
      rw [kushilevitzMansourSecondStage, hactive] at houtcome
      simp only at houtcome
      by_cases hcap : family.card ≤
          goldreichLevinActiveCap (kushilevitzMansourThreshold ε M hM)
      · rw [if_pos hcap] at houtcome
        by_cases hnonempty : family.Nonempty
        · rw [dif_pos hnonempty] at houtcome
          exact Or.inr ⟨family, hnonempty, rfl, hcap,
            queriedFiniteFamilyFourierEstimatorProgramWithConfidence_cost_eq
              target family hnonempty ε oneTwentiethLearningParameter
              outcome houtcome⟩
        · rw [dif_neg hnonempty, LearningProgram.runWithCost,
            PMF.mem_support_pure_iff] at houtcome
          subst outcome
          exact Or.inl rfl
      · rw [if_neg hcap, LearningProgram.runWithCost,
          PMF.mem_support_pure_iff] at houtcome
        subst outcome
        exact Or.inl rfl

/-- Exact cost decomposition of the two sequential KM stages. -/
theorem kushilevitzMansourProgram_cost_decomposition
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgram ε M hM)).support) :
    ∃ firstOutcome secondOutcome,
      firstOutcome ∈ (LearningProgram.runWithCost target
        (goldreichLevinQueryProgram
          (kushilevitzMansourThreshold ε M hM))).support ∧
      secondOutcome ∈ (LearningProgram.runWithCost target
        (kushilevitzMansourSecondStage ε M hM firstOutcome.1)).support ∧
      outcome.1 = secondOutcome.1 ∧
      outcome.2 = firstOutcome.2 + secondOutcome.2 := by
  rw [kushilevitzMansourProgram,
    LearningProgram.runWithCost_bind] at houtcome
  rw [PMF.mem_support_bind_iff] at houtcome
  obtain ⟨firstOutcome, hfirst, houtcome⟩ := houtcome
  rw [PMF.mem_support_map_iff] at houtcome
  obtain ⟨secondOutcome, hsecond, rfl⟩ := houtcome
  exact ⟨firstOutcome, secondOutcome, hfirst, hsecond, rfl, rfl⟩

/-- At total failure budget `1/20`, the binary confidence scheduler uses at most forty bits per
member of the nonempty family. -/
theorem fourierEstimatorFailureBits_oneTwentieth_per_family_le
    (𝓕 : Finset (Finset (Fin n))) (h𝓕 : 𝓕.Nonempty) :
    fourierEstimatorFailureBits
        (finiteFamilyCoefficientConfidenceForTotal
          𝓕 h𝓕 oneTwentiethLearningParameter) ≤
      40 * 𝓕.card := by
  unfold fourierEstimatorFailureBits
  have hvalue :
      (2 : ℚ) /
          (finiteFamilyCoefficientConfidenceForTotal
            𝓕 h𝓕 oneTwentiethLearningParameter).1 =
        (40 * 𝓕.card : ℕ) := by
    have hcard : (𝓕.card : ℚ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr h𝓕).ne'
    change (2 : ℚ) / ((1 / 20 : ℚ) / 𝓕.card) = (40 * 𝓕.card : ℕ)
    field_simp
    norm_num
  have hceil :
      Nat.ceil ((2 : ℚ) /
          (finiteFamilyCoefficientConfidenceForTotal
            𝓕 h𝓕 oneTwentiethLearningParameter).1) =
        40 * 𝓕.card := by
    rw [hvalue]
    exact Nat.ceil_natCast (40 * 𝓕.card)
  rw [hceil]
  exact Nat.clog_le_of_le_pow
    (show 40 * 𝓕.card ≤ 2 ^ (40 * 𝓕.card) from Nat.lt_two_pow_self.le)

/-- Uniform rational membership-query bound for every guarded KM second-stage execution. -/
theorem kushilevitzMansourSecondStage_queries_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M) (state : GoldreichLevinQueryState n)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourSecondStage ε M hM state)).support) :
    (outcome.2.queries : ℚ) ≤
      640 * (goldreichLevinActiveCap
        (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 / ε.1 ^ 2 := by
  rcases kushilevitzMansourSecondStage_cost_cases
    target ε M hM state outcome houtcome with hzero | hfamily
  · rw [hzero]
    positivity
  · obtain ⟨family, hnonempty, hactive, hcap, hcost⟩ := hfamily
    have hprogram : outcome ∈ (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence
          family hnonempty ε oneTwentiethLearningParameter)).support := by
      rw [kushilevitzMansourSecondStage, hactive] at houtcome
      simp only at houtcome
      rw [if_pos hcap, dif_pos hnonempty] at houtcome
      exact houtcome
    have hbound :=
      queriedFiniteFamilyFourierEstimatorProgramWithConfidence_queries_cast_le
        target family hnonempty ε oneTwentiethLearningParameter outcome hprogram
    have hbits :=
      fourierEstimatorFailureBits_oneTwentieth_per_family_le family hnonempty
    have hcard : (family.card : ℚ) ≤
        goldreichLevinActiveCap
          (kushilevitzMansourThreshold ε M hM) := by
      exact_mod_cast hcap
    have hbitsCast : (fourierEstimatorFailureBits
        (finiteFamilyCoefficientConfidenceForTotal
          family hnonempty oneTwentiethLearningParameter) : ℚ) ≤
        40 * family.card := by exact_mod_cast hbits
    calc
      (outcome.2.queries : ℚ) ≤
          16 * (family.card : ℚ) ^ 3 *
              fourierEstimatorFailureBits
                (finiteFamilyCoefficientConfidenceForTotal
                  family hnonempty oneTwentiethLearningParameter) /
            ε.1 ^ 2 := hbound
      _ ≤ 16 * (family.card : ℚ) ^ 3 * (40 * family.card) / ε.1 ^ 2 := by
        gcongr
      _ = 640 * (family.card : ℚ) ^ 4 / ε.1 ^ 2 := by ring
      _ ≤ 640 * (goldreichLevinActiveCap
          (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 / ε.1 ^ 2 := by
        gcongr

/-- Uniform rational charged-work bound for every guarded KM second-stage execution. -/
theorem kushilevitzMansourSecondStage_work_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M) (state : GoldreichLevinQueryState n)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourSecondStage ε M hM state)).support) :
    (outcome.2.work : ℚ) ≤
      1280 * (goldreichLevinActiveCap
        (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 := by
  rcases kushilevitzMansourSecondStage_cost_cases
    target ε M hM state outcome houtcome with hzero | hfamily
  · rw [hzero]
    positivity
  · obtain ⟨family, hnonempty, hactive, hcap, hcost⟩ := hfamily
    have hprogram : outcome ∈ (LearningProgram.runWithCost target
        (queriedFiniteFamilyFourierEstimatorProgramWithConfidence
          family hnonempty ε oneTwentiethLearningParameter)).support := by
      rw [kushilevitzMansourSecondStage, hactive] at houtcome
      simp only at houtcome
      rw [if_pos hcap, dif_pos hnonempty] at houtcome
      exact houtcome
    have hbound :=
      queriedFiniteFamilyFourierEstimatorProgramWithConfidence_work_cast_le
        target family hnonempty ε oneTwentiethLearningParameter outcome hprogram
    have hbits :=
      fourierEstimatorFailureBits_oneTwentieth_per_family_le family hnonempty
    have hcard : (family.card : ℚ) ≤
        goldreichLevinActiveCap
          (kushilevitzMansourThreshold ε M hM) := by
      exact_mod_cast hcap
    have hbitsCast : (fourierEstimatorFailureBits
        (finiteFamilyCoefficientConfidenceForTotal
          family hnonempty oneTwentiethLearningParameter) : ℚ) ≤
        40 * family.card := by exact_mod_cast hbits
    calc
      (outcome.2.work : ℚ) ≤
          32 * (family.card : ℚ) ^ 3 * (n + 1) *
              fourierEstimatorFailureBits
                (finiteFamilyCoefficientConfidenceForTotal
                  family hnonempty oneTwentiethLearningParameter) /
            ε.1 ^ 2 := hbound
      _ ≤ 32 * (family.card : ℚ) ^ 3 * (n + 1) *
          (40 * family.card) / ε.1 ^ 2 := by
        gcongr
      _ = 1280 * (family.card : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 := by ring
      _ ≤ 1280 * (goldreichLevinActiveCap
          (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 := by
        gcongr

/-- Target-independent query bound for the complete two-stage KM program before eliminating its
Goldreich--Levin threshold. -/
theorem kushilevitzMansourProgram_queries_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgram ε M hM)).support) :
    (outcome.2.queries : ℚ) ≤
      (goldreichLevinQueryBudget n
        (kushilevitzMansourThreshold ε M hM) : ℚ) +
      640 * (goldreichLevinActiveCap
        (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 / ε.1 ^ 2 := by
  obtain ⟨first, second, hfirst, hsecond, hout, hcost⟩ :=
    kushilevitzMansourProgram_cost_decomposition
      target ε M hM outcome houtcome
  have hfirstBound := goldreichLevinQueryProgram_queries_le
    target (kushilevitzMansourThreshold ε M hM) first hfirst
  have hfirstCast : (first.2.queries : ℚ) ≤
      goldreichLevinQueryBudget n
        (kushilevitzMansourThreshold ε M hM) := by
    exact_mod_cast hfirstBound
  have hsecondBound := kushilevitzMansourSecondStage_queries_cast_le
    target ε M hM first.1 second hsecond
  calc
    (outcome.2.queries : ℚ) =
        (first.2.queries : ℚ) + (second.2.queries : ℚ) := by
      rw [hcost]
      change ((first.2.queries + second.2.queries : ℕ) : ℚ) = _
      push_cast
      rfl
    _ ≤ _ := add_le_add hfirstCast hsecondBound

/-- Target-independent charged-work bound for the complete two-stage KM program before eliminating
its Goldreich--Levin threshold. -/
theorem kushilevitzMansourProgram_work_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgram ε M hM)).support) :
    (outcome.2.work : ℚ) ≤
      (goldreichLevinWorkBudget n
        (kushilevitzMansourThreshold ε M hM) : ℚ) +
      1280 * (goldreichLevinActiveCap
        (kushilevitzMansourThreshold ε M hM) : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 := by
  obtain ⟨first, second, hfirst, hsecond, hout, hcost⟩ :=
    kushilevitzMansourProgram_cost_decomposition
      target ε M hM outcome houtcome
  have hfirstBound := goldreichLevinQueryProgram_work_le
    target (kushilevitzMansourThreshold ε M hM) first hfirst
  have hfirstCast : (first.2.work : ℚ) ≤
      goldreichLevinWorkBudget n
        (kushilevitzMansourThreshold ε M hM) := by
    exact_mod_cast hfirstBound
  have hsecondBound := kushilevitzMansourSecondStage_work_cast_le
    target ε M hM first.1 second hsecond
  calc
    (outcome.2.work : ℚ) =
        (first.2.work : ℚ) + (second.2.work : ℚ) := by
      rw [hcost]
      change ((first.2.work + second.2.work : ℕ) : ℚ) = _
      push_cast
      rfl
    _ ≤ _ := add_le_add hfirstCast hsecondBound

/-- The complete KM membership-query count is polynomial in `n`, `M`, and `1 / ε`. -/
theorem kushilevitzMansourProgram_queries_polynomial_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgram ε M hM)).support) :
    (outcome.2.queries : ℚ) ≤
      2 ^ 40 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
  let τ := kushilevitzMansourThreshold ε M hM
  have hcombined :=
    kushilevitzMansourProgram_queries_cast_le target ε M hM outcome houtcome
  have hgl := goldreichLevinQueryBudget_cast_le n τ
  have hcap := goldreichLevinActiveCap_cast_le τ
  have hεpos : (0 : ℚ) < ε.1 := ε.2.1
  have hεne : ε.1 ≠ 0 := ne_of_gt hεpos
  have hMne : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hεsq : ε.1 ^ 2 ≤ (1 : ℚ) := by
    have hεhalf : ε.1 ≤ (1 : ℚ) := ε.2.2.trans (by norm_num)
    nlinarith [mul_nonneg ε.2.1.le (sub_nonneg.mpr hεhalf)]
  have hn : (n : ℚ) ≤ n + 1 := by norm_num
  have hnOne : (1 : ℚ) ≤ n + 1 := by norm_num
  have hnOneSq : (1 : ℚ) ≤ (n + 1 : ℚ) ^ 2 := one_le_pow₀ hnOne
  have hMpow : (M : ℚ) ^ 8 ≤ (M + 1 : ℚ) ^ 8 := by
    exact pow_le_pow_left₀ (by positivity) (by norm_num) 8
  have hfirst :
      (goldreichLevinQueryBudget n τ : ℚ) ≤
        2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
    calc
      (goldreichLevinQueryBudget n τ : ℚ) ≤
          2 ^ 21 * n * (n + 1) / τ.1 ^ 8 := hgl
      _ = 2 ^ 37 * n * (n + 1) * M ^ 8 / ε.1 ^ 8 := by
        change 2 ^ 21 * n * (n + 1) /
          (ε.1 / (4 * M)) ^ 8 = _
        field_simp
        ring
      _ = 2 ^ 37 * n * (n + 1) * M ^ 8 * ε.1 ^ 2 / ε.1 ^ 10 := by
        field_simp
      _ ≤ 2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hproduct :
            (n : ℚ) * (n + 1) * M ^ 8 * ε.1 ^ 2 ≤
              (n + 1) ^ 2 * (M + 1) ^ 8 := by
          calc
            (n : ℚ) * (n + 1) * M ^ 8 * ε.1 ^ 2 =
                n * ((n + 1) * M ^ 8 * ε.1 ^ 2) := by ring
            _ ≤ (n + 1) * ((n + 1) * M ^ 8 * ε.1 ^ 2) :=
              mul_le_mul_of_nonneg_right hn (by positivity)
            _ = ((n + 1) ^ 2 * ε.1 ^ 2) * M ^ 8 := by ring
            _ ≤ ((n + 1) ^ 2 * ε.1 ^ 2) * (M + 1) ^ 8 :=
              mul_le_mul_of_nonneg_left hMpow (by positivity)
            _ = ((n + 1) ^ 2 * (M + 1) ^ 8) * ε.1 ^ 2 := by ring
            _ ≤ ((n + 1) ^ 2 * (M + 1) ^ 8) * 1 :=
              mul_le_mul_of_nonneg_left hεsq (by positivity)
            _ = (n + 1) ^ 2 * (M + 1) ^ 8 := by ring
        let X : ℚ := (n : ℚ) * (n + 1) * M ^ 8 * ε.1 ^ 2
        let A : ℚ := (n + 1) ^ 2 * (M + 1) ^ 8
        have hXA : X ≤ A := by simpa [X, A] using hproduct
        have hbound : (2 ^ 37 : ℚ) * X ≤ (2 ^ 39 : ℚ) * A :=
          (mul_le_mul_of_nonneg_left hXA (by norm_num)).trans
            (mul_le_mul_of_nonneg_right (by norm_num) (by dsimp [A]; positivity))
        simpa [X, A, mul_assoc] using hbound
  have hsecond :
      640 * (goldreichLevinActiveCap τ : ℚ) ^ 4 / ε.1 ^ 2 ≤
        2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
    calc
      640 * (goldreichLevinActiveCap τ : ℚ) ^ 4 / ε.1 ^ 2 ≤
          640 * (8 / τ.1 ^ 2) ^ 4 / ε.1 ^ 2 := by gcongr
      _ = 171798691840 * M ^ 8 / ε.1 ^ 10 := by
        change 640 * (8 / (ε.1 / (4 * M)) ^ 2) ^ 4 / ε.1 ^ 2 = _
        field_simp
        ring
      _ ≤ 2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hproduct : (M : ℚ) ^ 8 ≤ (n + 1) ^ 2 * (M + 1) ^ 8 := by
          calc
            (M : ℚ) ^ 8 ≤ (1 : ℚ) * ((M : ℚ) + 1) ^ 8 := by simpa using hMpow
            _ ≤ ((n : ℚ) + 1) ^ 2 * ((M : ℚ) + 1) ^ 8 :=
              mul_le_mul_of_nonneg_right hnOneSq (by positivity)
        let X : ℚ := (M : ℚ) ^ 8
        let A : ℚ := (n + 1) ^ 2 * (M + 1) ^ 8
        have hXA : X ≤ A := by simpa [X, A] using hproduct
        have hbound : (171798691840 : ℚ) * X ≤ (2 ^ 39 : ℚ) * A :=
          (mul_le_mul_of_nonneg_left hXA (by norm_num)).trans
            (mul_le_mul_of_nonneg_right (by norm_num) (by dsimp [A]; positivity))
        simpa [X, A, mul_assoc] using hbound
  calc
    (outcome.2.queries : ℚ) ≤
        (goldreichLevinQueryBudget n τ : ℚ) +
          640 * (goldreichLevinActiveCap τ : ℚ) ^ 4 / ε.1 ^ 2 := by
      simpa [τ] using hcombined
    _ ≤ 2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 +
        2 ^ 39 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 :=
      add_le_add hfirst hsecond
    _ = 2 ^ 40 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by ring

/-- The complete KM charged-work count is polynomial in `n`, `M`, and `1 / ε`. -/
theorem kushilevitzMansourProgram_work_polynomial_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter)
    (M : ℕ) (hM : 0 < M)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgram ε M hM)).support) :
    (outcome.2.work : ℚ) ≤
      2 ^ 42 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
  let τ := kushilevitzMansourThreshold ε M hM
  have hcombined :=
    kushilevitzMansourProgram_work_cast_le target ε M hM outcome houtcome
  have hgl := goldreichLevinWorkBudget_cast_le n τ
  have hcap := goldreichLevinActiveCap_cast_le τ
  have hεpos : (0 : ℚ) < ε.1 := ε.2.1
  have hεne : ε.1 ≠ 0 := ne_of_gt hεpos
  have hMne : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hεsq : ε.1 ^ 2 ≤ (1 : ℚ) := by
    have hεhalf : ε.1 ≤ (1 : ℚ) := ε.2.2.trans (by norm_num)
    nlinarith [mul_nonneg ε.2.1.le (sub_nonneg.mpr hεhalf)]
  have hn : (n : ℚ) ≤ n + 1 := by norm_num
  have hnOne : (1 : ℚ) ≤ n + 1 := by norm_num
  have hnCube : (n + 1 : ℚ) ≤ (n + 1) ^ 3 :=
    le_self_pow₀ hnOne (by norm_num)
  have hMpow : (M : ℚ) ^ 8 ≤ (M + 1 : ℚ) ^ 8 := by
    exact pow_le_pow_left₀ (by positivity) (by norm_num) 8
  have hfirst :
      (goldreichLevinWorkBudget n τ : ℚ) ≤
        2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
    calc
      (goldreichLevinWorkBudget n τ : ℚ) ≤
          2 ^ 25 * n * (n + 1) ^ 2 / τ.1 ^ 8 := hgl
      _ = 2 ^ 41 * n * (n + 1) ^ 2 * M ^ 8 / ε.1 ^ 8 := by
        change 2 ^ 25 * n * (n + 1) ^ 2 /
          (ε.1 / (4 * M)) ^ 8 = _
        field_simp
        ring
      _ = 2 ^ 41 * n * (n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2 / ε.1 ^ 10 := by
        field_simp
      _ ≤ 2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hproduct :
            (n : ℚ) * (n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2 ≤
              (n + 1) ^ 3 * (M + 1) ^ 8 := by
          calc
            (n : ℚ) * (n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2 =
                n * ((n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2) := by ring
            _ ≤ (n + 1) * ((n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2) :=
              mul_le_mul_of_nonneg_right hn (by positivity)
            _ = ((n + 1) ^ 3 * ε.1 ^ 2) * M ^ 8 := by ring
            _ ≤ ((n + 1) ^ 3 * ε.1 ^ 2) * (M + 1) ^ 8 :=
              mul_le_mul_of_nonneg_left hMpow (by positivity)
            _ = ((n + 1) ^ 3 * (M + 1) ^ 8) * ε.1 ^ 2 := by ring
            _ ≤ ((n + 1) ^ 3 * (M + 1) ^ 8) * 1 :=
              mul_le_mul_of_nonneg_left hεsq (by positivity)
            _ = (n + 1) ^ 3 * (M + 1) ^ 8 := by ring
        let X : ℚ := (n : ℚ) * (n + 1) ^ 2 * M ^ 8 * ε.1 ^ 2
        let A : ℚ := (n + 1) ^ 3 * (M + 1) ^ 8
        have hXA : X ≤ A := by simpa [X, A] using hproduct
        have hbound : (2 ^ 41 : ℚ) * X ≤ (2 ^ 41 : ℚ) * A :=
          mul_le_mul_of_nonneg_left hXA (by norm_num)
        simpa [X, A, mul_assoc] using hbound
  have hsecond :
      1280 * (goldreichLevinActiveCap τ : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 ≤
        2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
    calc
      1280 * (goldreichLevinActiveCap τ : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 ≤
          1280 * (8 / τ.1 ^ 2) ^ 4 * (n + 1) / ε.1 ^ 2 := by gcongr
      _ = 343597383680 * (n + 1) * M ^ 8 / ε.1 ^ 10 := by
        change 1280 * (8 / (ε.1 / (4 * M)) ^ 2) ^ 4 * (n + 1) /
          ε.1 ^ 2 = _
        field_simp
        ring
      _ ≤ 2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hproduct : (n + 1 : ℚ) * M ^ 8 ≤
            (n + 1) ^ 3 * (M + 1) ^ 8 := by
          calc
            (n + 1 : ℚ) * M ^ 8 ≤ (n + 1) * (M + 1) ^ 8 :=
              mul_le_mul_of_nonneg_left hMpow (by positivity)
            _ ≤ (n + 1) ^ 3 * (M + 1) ^ 8 :=
              mul_le_mul_of_nonneg_right hnCube (by positivity)
        let X : ℚ := (n + 1 : ℚ) * M ^ 8
        let A : ℚ := (n + 1 : ℚ) ^ 3 * (M + 1 : ℚ) ^ 8
        have hXA : X ≤ A := by simpa [X, A] using hproduct
        have hbound : (343597383680 : ℚ) * X ≤ (2 ^ 41 : ℚ) * A :=
          (mul_le_mul_of_nonneg_left hXA (by norm_num)).trans
            (mul_le_mul_of_nonneg_right (by norm_num) (by dsimp [A]; positivity))
        simpa [X, A, mul_assoc] using hbound
  calc
    (outcome.2.work : ℚ) ≤
        (goldreichLevinWorkBudget n τ : ℚ) +
          1280 * (goldreichLevinActiveCap τ : ℚ) ^ 4 * (n + 1) / ε.1 ^ 2 := by
      simpa [τ] using hcombined
    _ ≤ 2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 +
        2 ^ 41 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 :=
      add_le_add hfirst hsecond
    _ = 2 ^ 42 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by ring

/-- Target-independent polynomial query bound for the zero-safe Theorem 3.37 wrapper. -/
theorem kushilevitzMansourProgramForBound_queries_polynomial_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter) (M : ℕ)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε M)).support) :
    (outcome.2.queries : ℚ) ≤
      2 ^ 40 * (n + 1) ^ 2 * (M + 1) ^ 8 / ε.1 ^ 10 := by
  by_cases hM : 0 < M
  · rw [kushilevitzMansourProgramForBound, dif_pos hM] at houtcome
    exact kushilevitzMansourProgram_queries_polynomial_cast_le
      target ε M hM outcome houtcome
  · rw [kushilevitzMansourProgramForBound, dif_neg hM,
      LearningProgram.runWithCost, PMF.mem_support_pure_iff] at houtcome
    subst outcome
    positivity

/-- Target-independent polynomial charged-work bound for the zero-safe Theorem 3.37 wrapper. -/
theorem kushilevitzMansourProgramForBound_work_polynomial_cast_le
    (target : BooleanFunction n) (ε : PositiveLearningParameter) (M : ℕ)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε M)).support) :
    (outcome.2.work : ℚ) ≤
      2 ^ 42 * (n + 1) ^ 3 * (M + 1) ^ 8 / ε.1 ^ 10 := by
  by_cases hM : 0 < M
  · rw [kushilevitzMansourProgramForBound, dif_pos hM] at houtcome
    exact kushilevitzMansourProgram_work_polynomial_cast_le
      target ε M hM outcome houtcome
  · rw [kushilevitzMansourProgramForBound, dif_neg hM,
      LearningProgram.runWithCost, PMF.mem_support_pure_iff] at houtcome
    subst outcome
    positivity

/-- The Fourier-one-norm family-size bound is polynomial in `s` and `1 / ε`. -/
theorem fourierOneNormFamilySizeBound_add_one_cast_le
    (s : ℝ) (ε : PositiveLearningParameter) (hs : 0 ≤ s) :
    ((fourierOneNormFamilySizeBound s ε + 1 : ℕ) : ℝ) ≤
      6 * (s + 1) ^ 2 / (ε.1 : ℝ) := by
  let x : ℝ := 4 * s ^ 2 / (ε.1 : ℝ)
  have hε := positiveLearningParameter_toReal_mem_Ioc ε
  have hx : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) hε.1.le
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx).le
  have hone : (1 : ℝ) ≤ x + 1 := by linarith
  have hmax : (max 1 (Nat.ceil x) : ℕ) ≤ x + 1 := by
    exact_mod_cast max_le hone hceil
  calc
    ((fourierOneNormFamilySizeBound s ε + 1 : ℕ) : ℝ) =
        (max 1 (Nat.ceil x) : ℕ) + 1 := by
      simp [fourierOneNormFamilySizeBound, x]
    _ ≤ x + 2 := by
      linarith
    _ ≤ 6 * (s + 1) ^ 2 / (ε.1 : ℝ) := by
      rw [le_div_iff₀ hε.1]
      dsimp [x]
      calc
        (4 * s ^ 2 / (ε.1 : ℝ) + 2) * (ε.1 : ℝ) =
            4 * s ^ 2 + 2 * (ε.1 : ℝ) := by
          field_simp [ne_of_gt hε.1]
        _ ≤ 6 * (s + 1) ^ 2 := by
          have hεle : (ε.1 : ℝ) ≤ 1 / 2 := hε.2
          ring_nf
          nlinarith [sq_nonneg s]

/-- Theorem 3.38's Fourier-one-norm learner has an explicit polynomial membership-query bound. -/
theorem fourierOneNormClass_queries_polynomial_le
    (target : BooleanFunction n) (s : ℝ) (ε : PositiveLearningParameter)
    (hs : 0 ≤ s) (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε
        (fourierOneNormFamilySizeBound s ε))).support) :
    (outcome.2.queries : ℝ) ≤
      2 ^ 64 * (n + 1) ^ 2 * (s + 1) ^ 16 / (ε.1 : ℝ) ^ 18 := by
  let M := fourierOneNormFamilySizeBound s ε
  have hq := kushilevitzMansourProgramForBound_queries_polynomial_cast_le
    target ε M outcome (by simpa [M] using houtcome)
  have hqReal : (outcome.2.queries : ℝ) ≤
      2 ^ 40 * (n + 1) ^ 2 * (M + 1) ^ 8 / (ε.1 : ℝ) ^ 10 := by
    exact_mod_cast hq
  have hM := fourierOneNormFamilySizeBound_add_one_cast_le s ε hs
  have hMpow : ((M + 1 : ℕ) : ℝ) ^ 8 ≤
      (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by simpa [M] using hM) 8
  have hMpow' : ((M : ℝ) + 1) ^ 8 ≤
      (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hMpow
  have hεpos : (0 : ℝ) < (ε.1 : ℝ) :=
    (positiveLearningParameter_toReal_mem_Ioc ε).1
  calc
    (outcome.2.queries : ℝ) ≤
        2 ^ 40 * (n + 1) ^ 2 * (M + 1) ^ 8 / (ε.1 : ℝ) ^ 10 := hqReal
    _ ≤ 2 ^ 40 * (n + 1) ^ 2 *
        (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 / (ε.1 : ℝ) ^ 10 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hMpow' (by positivity)
    _ = (2 ^ 40 * 6 ^ 8) * (n + 1) ^ 2 * (s + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
      field_simp
    _ ≤ 2 ^ 64 * (n + 1) ^ 2 * (s + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
      gcongr
      norm_num

/-- Theorem 3.38's Fourier-one-norm learner has an explicit polynomial charged-work bound. -/
theorem fourierOneNormClass_work_polynomial_le
    (target : BooleanFunction n) (s : ℝ) (ε : PositiveLearningParameter)
    (hs : 0 ≤ s) (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε
        (fourierOneNormFamilySizeBound s ε))).support) :
    (outcome.2.work : ℝ) ≤
      2 ^ 66 * (n + 1) ^ 3 * (s + 1) ^ 16 / (ε.1 : ℝ) ^ 18 := by
  let M := fourierOneNormFamilySizeBound s ε
  have hw := kushilevitzMansourProgramForBound_work_polynomial_cast_le
    target ε M outcome (by simpa [M] using houtcome)
  have hwReal : (outcome.2.work : ℝ) ≤
      2 ^ 42 * (n + 1) ^ 3 * (M + 1) ^ 8 / (ε.1 : ℝ) ^ 10 := by
    exact_mod_cast hw
  have hM := fourierOneNormFamilySizeBound_add_one_cast_le s ε hs
  have hMpow : ((M + 1 : ℕ) : ℝ) ^ 8 ≤
      (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by simpa [M] using hM) 8
  have hMpow' : ((M : ℝ) + 1) ^ 8 ≤
      (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hMpow
  have hεpos : (0 : ℝ) < (ε.1 : ℝ) :=
    (positiveLearningParameter_toReal_mem_Ioc ε).1
  calc
    (outcome.2.work : ℝ) ≤
        2 ^ 42 * (n + 1) ^ 3 * (M + 1) ^ 8 / (ε.1 : ℝ) ^ 10 := hwReal
    _ ≤ 2 ^ 42 * (n + 1) ^ 3 *
        (6 * (s + 1) ^ 2 / (ε.1 : ℝ)) ^ 8 / (ε.1 : ℝ) ^ 10 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hMpow' (by positivity)
    _ = (2 ^ 42 * 6 ^ 8) * (n + 1) ^ 3 * (s + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
      field_simp
    _ ≤ 2 ^ 66 * (n + 1) ^ 3 * (s + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
      gcongr
      norm_num

/-- Exercise 3.39's decision-tree learner inherits the Fourier-one-norm polynomial query bound. -/
theorem decisionTreeSizeClass_queries_polynomial_le
    {available : Finset (Fin n)}
    (target : BooleanFunction n) (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes (fun x ↦ target.toReal (binaryCubeSignEquiv n x)))
    (s : ℕ) (hsize : T.leafCount ≤ s) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε
        (fourierOneNormFamilySizeBound (s : ℝ) ε))).support) :
    (outcome.2.queries : ℝ) ≤
      2 ^ 64 * (n + 1) ^ 2 * ((s : ℝ) + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
  have hnorm : fourierOneNorm target.toReal ≤ (s : ℝ) :=
    (fourierOneNorm_le_leafCount_of_decisionTree target T hT).trans (by
      exact_mod_cast hsize)
  exact fourierOneNormClass_queries_polynomial_le
    target s ε ((fourierOneNorm_nonneg target.toReal).trans hnorm) outcome houtcome

/-- Exercise 3.39's decision-tree learner inherits the Fourier-one-norm polynomial work bound. -/
theorem decisionTreeSizeClass_work_polynomial_le
    {available : Finset (Fin n)}
    (target : BooleanFunction n) (T : F₂DecisionTree n ℝ available)
    (hT : T.Computes (fun x ↦ target.toReal (binaryCubeSignEquiv n x)))
    (s : ℕ) (hsize : T.leafCount ≤ s) (ε : PositiveLearningParameter)
    (outcome : SparseFourierHypothesis n × LearningCost)
    (houtcome : outcome ∈ (LearningProgram.runWithCost target
      (kushilevitzMansourProgramForBound ε
        (fourierOneNormFamilySizeBound (s : ℝ) ε))).support) :
    (outcome.2.work : ℝ) ≤
      2 ^ 66 * (n + 1) ^ 3 * ((s : ℝ) + 1) ^ 16 /
        (ε.1 : ℝ) ^ 18 := by
  have hnorm : fourierOneNorm target.toReal ≤ (s : ℝ) :=
    (fourierOneNorm_le_leafCount_of_decisionTree target T hT).trans (by
      exact_mod_cast hsize)
  exact fourierOneNormClass_work_polynomial_le
    target s ε ((fourierOneNorm_nonneg target.toReal).trans hnorm) outcome houtcome

end FABL
