/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.LearningAndTesting.DecisionTreeHypotheses
import FABL.Chapter06.LearningAndTesting.LowDegreeJuntaLearning

/-!
# The low-degree junta learning algorithm

Book item: Theorem 6.36, packaged through the finite hypothesis language and learning-algorithm
interface of Definition 3.27.

The exact recursive learner returns an optional dependently indexed decision tree.  This module
erases successful trees into the total finite hypothesis language and maps explicit algorithmic
failure to a fixed total hypothesis.  The latter is only an output adapter: failure remains part of
the probability analysis and is never represented as a hypothesis code.
-/

open Finset MeasureTheory Set
open scoped BooleanCube ENNReal

set_option autoImplicit false

namespace FABL

universe u

variable {n : ℕ}

/-- The fixed Theorem 6.36 failure budget; its success probability is stronger than Definition
3.27's required threshold `9 / 10`. -/
def lowDegreeJuntaLearningFailure : PositiveLearningParameter :=
  ⟨1 / 16, by norm_num, by norm_num⟩

/-- Total raw hypothesis produced at the boundary of the optional exact learner. -/
def lowDegreeJuntaHypothesisOfOutput {n : ℕ} :
    Option (DecisionTree n Sign) → DecisionTreeHypothesis n
  | none => .leaf 1
  | some tree => DecisionTreeHypothesis.ofF₂DecisionTree tree

/-- Definition 3.27 program obtained by erasing the exact learner's dependent tree index. -/
noncomputable def lowDegreeJuntaLearningProgram
    (n k : ℕ) (_accuracy : LearningAccuracy) :
    LearningProgram n .randomExamples (DecisionTreeHypothesis n) :=
  LearningProgram.map lowDegreeJuntaHypothesisOfOutput
    (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure)

/-- The concept class of sign-valued functions depending on at most `k` coordinates. -/
def kJuntaConceptClass (n k : ℕ) : Set (BooleanFunction n) :=
  {target | IsKJunta target k}

/-- Erasing a successful exact tree preserves its target function. -/
theorem evaluate_lowDegreeJuntaHypothesisOfOutput_eq
    (target : BooleanFunction n) (tree : DecisionTree n Sign)
    (hcomputes : DecisionTreeComputesTarget tree target) :
    DecisionTreeHypothesis.evaluate
        (lowDegreeJuntaHypothesisOfOutput (some tree)) =
      target := by
  funext x
  change (DecisionTreeHypothesis.ofF₂DecisionTree tree).eval
      ((binaryCubeSignEquiv n).symm x) = target x
  rw [DecisionTreeHypothesis.eval_ofF₂DecisionTree]
  simpa using hcomputes ((binaryCubeSignEquiv n).symm x)

/-- Every nonfailed exact-learner output is accurate for every requested nonnegative error. -/
theorem lowDegreeJuntaHypothesisOfOutput_accurate_of_not_bad
    (target : BooleanFunction n) (accuracy : LearningAccuracy)
    (output : Option (DecisionTree n Sign))
    (hgood : ¬ JuntaLearnerOutputBad target output) :
    relativeHammingDist target
        (DecisionTreeHypothesis.evaluate
          (lowDegreeJuntaHypothesisOfOutput output)) ≤
      (accuracy.1 : ℝ) := by
  classical
  cases output with
  | none =>
      simp [JuntaLearnerOutputBad] at hgood
  | some tree =>
      have hcomputes : DecisionTreeComputesTarget tree target := by
        simpa [JuntaLearnerOutputBad] using hgood
      rw [evaluate_lowDegreeJuntaHypothesisOfOutput_eq target tree hcomputes]
      have haccuracy : (0 : ℝ) ≤ (accuracy.1 : ℝ) := by
        exact_mod_cast accuracy.2.1
      simpa [relativeHammingDist] using haccuracy

/-- Two output-only events covering every execution have probabilities whose sum is at least
one.  The proof uses only finite `PMF` outer-measure semantics and hence needs no measurable-space
structure on the output language. -/
private theorem one_le_eventProbability_add_of_output_cover
    {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    (first second : α → Prop)
    (hcover : ∀ output, first output ∨ second output) :
    1 ≤
      LearningProgram.eventProbability program target
          (fun outcome ↦ first outcome.1) +
        LearningProgram.eventProbability program target
          (fun outcome ↦ second outcome.1) := by
  let law := LearningProgram.runWithCost target program
  let firstSet : Set (α × LearningCost) := {outcome | first outcome.1}
  let secondSet : Set (α × LearningCost) := {outcome | second outcome.1}
  have hsets : (Set.univ : Set (α × LearningCost)) ⊆ firstSet ∪ secondSet := by
    intro outcome _
    simpa [firstSet, secondSet] using hcover outcome.1
  have houter : (1 : ℝ≥0∞) ≤
      law.toOuterMeasure firstSet + law.toOuterMeasure secondSet := by
    calc
      (1 : ℝ≥0∞) = law.toOuterMeasure Set.univ := by
        simp [PMF.toOuterMeasure_apply, law.tsum_coe]
      _ ≤ law.toOuterMeasure (firstSet ∪ secondSet) :=
        law.toOuterMeasure.mono hsets
      _ ≤ law.toOuterMeasure firstSet + law.toOuterMeasure secondSet :=
        measure_union_le _ _
  have hfirstTop : law.toOuterMeasure firstSet ≠ ∞ :=
    pmfToOuterMeasure_ne_top law firstSet
  have hsecondTop : law.toOuterMeasure secondSet ≠ ∞ :=
    pmfToOuterMeasure_ne_top law secondSet
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hfirstTop, hsecondTop⟩) houter
  unfold LearningProgram.eventProbability
  change 1 ≤
    (law.toOuterMeasure firstSet).toReal +
      (law.toOuterMeasure secondSet).toReal
  simpa only [ENNReal.toReal_one,
    ENNReal.toReal_add hfirstTop hsecondTop] using hreal

/-- The exact junta learner as an honest Definition 3.27 random-example learning algorithm. -/
noncomputable def lowDegreeJuntaLearningAlgorithm (n k : ℕ) :
    LearningAlgorithm n .randomExamples
      (DecisionTreeHypothesis.finiteRepresentation n) where
  program := lowDegreeJuntaLearningProgram n k
  successProbability := fun target accuracy ↦
    LearningProgram.eventProbability
      (lowDegreeJuntaLearningProgram n k accuracy) target fun outcome ↦
        relativeHammingDist target
          (DecisionTreeHypothesis.evaluate outcome.1) ≤ (accuracy.1 : ℝ)
  randomExampleCost := fun _ ↦
    juntaTreeCallCount k *
      lowDegreeJuntaNodeRandomExampleBound n k
        (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure)
  queryCost := fun _ ↦ 0
  workCost := fun _ ↦
    juntaTreeCallCount k *
      lowDegreeJuntaNodeUniformWorkBound n k
        (juntaTreePerCallFailure k lowDegreeJuntaLearningFailure)
  successProbability_eq := by
    intro target accuracy
    rfl
  cost_le := by
    intro target accuracy outcome houtcome
    rw [lowDegreeJuntaLearningProgram, LearningProgram.runWithCost_map,
      PMF.mem_support_map_iff] at houtcome
    obtain ⟨source, hsource, rfl⟩ := houtcome
    obtain ⟨hrandom, hquery, hwork⟩ :=
      lowDegreeJuntaLearnerProgram_cost_le target k
        lowDegreeJuntaLearningFailure source hsource
    exact ⟨hrandom, hquery.le, hwork⟩

/-- Every `k`-junta is output accurately with Definition 3.27 probability at least `9 / 10`. -/
theorem lowDegreeJuntaLearningAlgorithm_successProbability_ge
    (target : BooleanFunction n) (k : ℕ) (hjunta : IsKJunta target k)
    (accuracy : LearningAccuracy) :
    (9 / 10 : ℝ) ≤
      (lowDegreeJuntaLearningAlgorithm n k).successProbability target accuracy := by
  let accurate : Option (DecisionTree n Sign) → Prop := fun output ↦
    relativeHammingDist target
        (DecisionTreeHypothesis.evaluate
          (lowDegreeJuntaHypothesisOfOutput output)) ≤
      (accuracy.1 : ℝ)
  have hcover : ∀ output,
      JuntaLearnerOutputBad target output ∨ accurate output := by
    intro output
    by_cases hbad : JuntaLearnerOutputBad target output
    · exact Or.inl hbad
    · exact Or.inr (by
        simpa [accurate] using
          lowDegreeJuntaHypothesisOfOutput_accurate_of_not_bad
            target accuracy output hbad)
  have htotal := one_le_eventProbability_add_of_output_cover
    (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure)
    target (JuntaLearnerOutputBad target) accurate hcover
  have hbad := lowDegreeJuntaLearnerProgram_failureProbability_le
    target k hjunta lowDegreeJuntaLearningFailure
  have hbadValue :
      LearningProgram.eventProbability
          (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure) target
          (fun outcome ↦ JuntaLearnerOutputBad target outcome.1) ≤
        (1 / 16 : ℝ) := by
    simpa [lowDegreeJuntaLearningFailure] using hbad
  have haccurate : (9 / 10 : ℝ) ≤
      LearningProgram.eventProbability
        (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure) target
        (fun outcome ↦ accurate outcome.1) := by
    nlinarith
  change (9 / 10 : ℝ) ≤
    LearningProgram.eventProbability
      (lowDegreeJuntaLearningProgram n k accuracy) target
      (fun outcome ↦
        relativeHammingDist target
          (DecisionTreeHypothesis.evaluate outcome.1) ≤ (accuracy.1 : ℝ))
  unfold lowDegreeJuntaLearningProgram
  calc
    (9 / 10 : ℝ) ≤
        LearningProgram.eventProbability
          (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure)
          target (fun outcome ↦ accurate outcome.1) :=
      haccurate
    _ = LearningProgram.eventProbability
        (LearningProgram.map lowDegreeJuntaHypothesisOfOutput
          (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure))
        target
        (fun outcome ↦
          relativeHammingDist target
            (DecisionTreeHypothesis.evaluate outcome.1) ≤
              (accuracy.1 : ℝ)) := by
      symm
      simpa only [accurate] using
        (eventProbability_map_output_eq target
          (lowDegreeJuntaLearnerProgram n k lowDegreeJuntaLearningFailure)
          lowDegreeJuntaHypothesisOfOutput
          (fun hypothesis ↦
            relativeHammingDist target
              (DecisionTreeHypothesis.evaluate hypothesis) ≤
                (accuracy.1 : ℝ)))

/-- The concrete Definition 3.27 algorithm learns the class of `k`-juntas at every requested
uniform-distribution error. -/
theorem lowDegreeJuntaLearningAlgorithm_learns
    (n k : ℕ) (accuracy : LearningAccuracy) :
    LearnsConceptClassWithError (lowDegreeJuntaLearningAlgorithm n k)
      (kJuntaConceptClass n k) accuracy := by
  intro target htarget
  exact lowDegreeJuntaLearningAlgorithm_successProbability_ge
    target k (by simpa [kJuntaConceptClass] using htarget) accuracy

end FABL
