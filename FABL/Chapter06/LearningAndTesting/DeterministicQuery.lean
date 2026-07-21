/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.QueryLearning

/-!
# Finite deterministic query programs

Computation-model support for Propositions 6.40 and 6.41.

The syntax is polymorphic in both the oracle domain and answer type, so it can express the
real-valued oracle in Proposition 6.40.  Query counts come only from visible finite-batch
constructors and local computation is charged by explicit `tick` nodes.  The sign-valued
specialization has a semantics-preserving adapter to the Chapter 3 query-learning model.
-/

set_option autoImplicit false

open scoped BooleanCube

@[expose] public section

namespace FABL

universe u v w z

/-- A finite deterministic oracle computation with constructor-derived query and work costs. -/
inductive DeterministicQueryProgram
    (Query : Type u) (Answer : Type v) (Output : Type w) :
    Type (max u v w) where
  /-- Return a pure output. -/
  | pure (output : Output) :
      DeterministicQueryProgram Query Answer Output
  /-- Query a visible finite batch and continue with all answers. -/
  | queryBatch (count : ℕ) (inputs : Fin count → Query)
      (next : (Fin count → Answer) →
        DeterministicQueryProgram Query Answer Output) :
      DeterministicQueryProgram Query Answer Output
  /-- Charge a visible number of local computation steps. -/
  | tick (steps : ℕ)
      (next : DeterministicQueryProgram Query Answer Output) :
      DeterministicQueryProgram Query Answer Output

namespace DeterministicQueryProgram

/-- The cost contributed by a batch of membership queries. -/
def queryBatchCost (count : ℕ) : LearningCost :=
  ⟨0, count, count⟩

/-- Sequential composition preserves every finite query batch and local-work node. -/
def bind {Query : Type u} {Answer : Type v}
    {Output : Type w} {Result : Type z}
    (next : Output → DeterministicQueryProgram Query Answer Result) :
    DeterministicQueryProgram Query Answer Output →
      DeterministicQueryProgram Query Answer Result
  | .pure output => next output
  | .queryBatch count inputs branch =>
      .queryBatch count inputs fun answers ↦ bind next (branch answers)
  | .tick steps program => .tick steps (bind next program)

/-- Map a pure function over the output of a deterministic query program. -/
def map {Query : Type u} {Answer : Type v}
    {Output : Type w} {Result : Type z}
    (f : Output → Result)
    (program : DeterministicQueryProgram Query Answer Output) :
    DeterministicQueryProgram Query Answer Result :=
  bind (fun output ↦ .pure (f output)) program

/-- Pure semantics of a deterministic query program, including its exact path cost. -/
def runWithCost {Query : Type u} {Answer : Type v} {Output : Type w}
    (oracle : Query → Answer) :
    DeterministicQueryProgram Query Answer Output → Output × LearningCost
  | .pure output => (output, 0)
  | .queryBatch count inputs next =>
      let outcome := runWithCost oracle (next fun i ↦ oracle (inputs i))
      (outcome.1, queryBatchCost count + outcome.2)
  | .tick steps next =>
      let outcome := runWithCost oracle next
      (outcome.1, ⟨0, 0, steps⟩ + outcome.2)

/-- Pure semantics respects sequential composition and adds the two path costs. -/
theorem runWithCost_bind {Query : Type u} {Answer : Type v}
    {Output : Type w} {Result : Type z}
    (oracle : Query → Answer)
    (next : Output → DeterministicQueryProgram Query Answer Result)
    (program : DeterministicQueryProgram Query Answer Output) :
    runWithCost oracle (bind next program) =
      let first := runWithCost oracle program
      let second := runWithCost oracle (next first.1)
      (second.1, first.2 + second.2) := by
  induction program with
  | pure output =>
      simp [bind, runWithCost]
  | queryBatch count inputs branch ih =>
      simp only [bind, runWithCost]
      rw [ih]
      simp only [add_assoc]
  | tick steps program ih =>
      simp only [bind, runWithCost]
      rw [ih]
      simp only [add_assoc]

/-- Convert a sign-valued deterministic query program to the Chapter 3 membership-query syntax. -/
def toLearningProgram {n : ℕ} {Output : Type} :
    DeterministicQueryProgram {−1,1}^[n] Sign Output →
      LearningProgram n .queries Output
  | .pure output => .pure output
  | .queryBatch count inputs next =>
      LearningProgram.bind
        (fun labeled : Fin count → ({−1,1}^[n] × Sign) ↦
          toLearningProgram (next fun i ↦ (labeled i).2))
        (queryInputBatchProgram count inputs)
  | .tick steps next => .tick steps (toLearningProgram next)

/-- The Chapter 3 adapter preserves the deterministic output and exact path cost. -/
theorem runWithCost_toLearningProgram {n : ℕ} {Output : Type}
    (target : BooleanFunction n)
    (program : DeterministicQueryProgram {−1,1}^[n] Sign Output) :
    LearningProgram.runWithCost target (toLearningProgram program) =
      PMF.pure (runWithCost target program) := by
  induction program with
  | pure output =>
      simp [toLearningProgram, LearningProgram.runWithCost, runWithCost]
  | queryBatch count inputs next ih =>
      rw [toLearningProgram, LearningProgram.runWithCost_bind,
        runWithCost_queryInputBatchProgram, PMF.pure_bind]
      rw [ih (fun i ↦ target (inputs i))]
      simp only [PMF.pure_map, LearningProgram.addOutcomeCost, runWithCost]
      rfl
  | tick steps next ih =>
      rw [toLearningProgram, LearningProgram.runWithCost, ih, PMF.pure_map]
      rfl

end DeterministicQueryProgram

end FABL
