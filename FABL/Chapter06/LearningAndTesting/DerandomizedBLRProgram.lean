/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.GoldreichLevin.RestrictedWeights
public import FABL.Chapter03.LearningTheory.Program
public import FABL.Chapter06.Constructions.SmallBiasGenerator
public import FABL.Chapter06.F₂Polynomials.Encoding
public import FABL.Chapter06.LearningAndTesting.DerandomizedBLR

/-!
# The derandomized BLR oracle program

Algorithmic construction supporting the Derandomized BLR Test following Theorem 6.44.

The program exposes every random bit and membership query through the Chapter 3
`LearningProgram` syntax.  It draws `n` uniform bits for `x`, draws `r` uniform seed bits for the
deterministic generator, and makes exactly the three BLR queries at `x`, `y`, and `x + y`.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n r : ℕ}

/-- The canonical identification of a random Boolean bit with a bit in `𝔽₂`. -/
def boolF₂Equiv : Bool ≃ 𝔽₂ :=
  finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv

/-- Coordinatewise identification of `n` random Boolean bits with the additive Boolean cube. -/
def boolVectorF₂CubeEquiv (n : ℕ) : (Fin n → Bool) ≃ F₂Cube n :=
  Equiv.piCongrRight fun _ ↦ boolF₂Equiv

/-- A finite program that draws exactly `bits` independent unbiased random bits. -/
def randomBitVectorProgram (dimension : ℕ) :
    (bits : ℕ) → LearningProgram dimension .queries (Fin bits → Bool)
  | 0 => .pure fun i ↦ Fin.elim0 i
  | bits + 1 =>
      .coin fun head ↦
        LearningProgram.map (Fin.cons head) (randomBitVectorProgram dimension bits)

private theorem uniformPMF_finZeroArrowBool :
    uniformPMF (Fin 0 → Bool) = PMF.pure (fun i ↦ Fin.elim0 i) := by
  classical
  ext bits
  have hbits : bits = (fun i ↦ Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  subst bits
  simp [uniformPMF, PMF.uniformOfFintype_apply]

/-- The bit-vector program has the uniform output law, with its exact constructor-derived cost. -/
theorem runWithCost_randomBitVectorProgram
    (target : BooleanFunction n) (bits : ℕ) :
    LearningProgram.runWithCost target (randomBitVectorProgram n bits) =
      (uniformPMF (Fin bits → Bool)).map fun vector ↦
        (vector, (⟨0, 0, bits⟩ : LearningCost)) := by
  induction bits with
  | zero =>
      rw [randomBitVectorProgram, LearningProgram.runWithCost,
        uniformPMF_finZeroArrowBool, PMF.pure_map]
      congr 1
  | succ bits ih =>
      rw [randomBitVectorProgram, LearningProgram.runWithCost]
      simp_rw [LearningProgram.runWithCost_map, ih, PMF.map_comp]
      have hcost :
          LearningCost.coin + (⟨0, 0, bits⟩ : LearningCost) =
            (⟨0, 0, bits + 1⟩ : LearningCost) := by
        apply LearningCost.toTriple_injective
        change (0 + 0, 0 + 0, 1 + bits) = (0, 0, bits + 1)
        simp [Nat.add_comm]
      change
        (uniformPMF Bool).bind (fun head ↦
            (uniformPMF (Fin bits → Bool)).map fun tail ↦
              (Fin.cons head tail,
                LearningCost.coin + (⟨0, 0, bits⟩ : LearningCost))) =
          (uniformPMF (Fin (bits + 1) → Bool)).map fun vector ↦
            (vector, (⟨0, 0, bits + 1⟩ : LearningCost))
      rw [hcost]
      calc
        (uniformPMF Bool).bind (fun head ↦
            (uniformPMF (Fin bits → Bool)).map fun tail ↦
              (Fin.cons head tail, (⟨0, 0, bits + 1⟩ : LearningCost))) =
            ((uniformPMF Bool).bind (fun head ↦
              (uniformPMF (Fin bits → Bool)).map fun tail ↦ (head, tail))).map
                (fun pair ↦
                  (Fin.cons pair.1 pair.2, (⟨0, 0, bits + 1⟩ : LearningCost))) := by
          rw [PMF.map_bind]
          simp_rw [PMF.map_comp]
          rfl
        _ = (uniformPMF (Bool × (Fin bits → Bool))).map
              (fun pair ↦
                (Fin.cons pair.1 pair.2, (⟨0, 0, bits + 1⟩ : LearningCost))) := by
          rw [uniformPMF_bind_map_pair]
        _ = (uniformPMF (Fin (bits + 1) → Bool)).map fun vector ↦
              (vector, (⟨0, 0, bits + 1⟩ : LearningCost)) := by
          rw [← map_uniformPMF_equiv
            (Fin.consEquiv (fun _ : Fin (bits + 1) ↦ Bool))]
          rw [PMF.map_comp]
          rfl

/-- The Boolean decision returned after the three BLR membership-query answers are collected. -/
def derandomizedBLRDecision
    (target : BooleanFunction n) (x y : F₂Cube n) : Bool :=
  decide (
    booleanFunctionF₂Encoding target x + booleanFunctionF₂Encoding target y =
      booleanFunctionF₂Encoding target (x + y))

/-- The three-query core of the Derandomized BLR Test at fixed points `x` and `y`. -/
def derandomizedBLRQueryProgram (x y : F₂Cube n) :
    LearningProgram n .queries Bool :=
  .query (binaryCubeSignEquiv n x) fun answerX ↦
    .query (binaryCubeSignEquiv n y) fun answerY ↦
      .query (binaryCubeSignEquiv n (x + y)) fun answerXY ↦
        .pure <| decide (
          binarySignEquiv.symm answerX + binarySignEquiv.symm answerY =
            binarySignEquiv.symm answerXY)

/-- The fixed-point BLR core makes exactly three membership queries. -/
theorem runWithCost_derandomizedBLRQueryProgram
    (target : BooleanFunction n) (x y : F₂Cube n) :
    LearningProgram.runWithCost target (derandomizedBLRQueryProgram x y) =
      PMF.pure
        (derandomizedBLRDecision target x y, (⟨0, 3, 3⟩ : LearningCost)) := by
  unfold derandomizedBLRQueryProgram
  simp only [LearningProgram.runWithCost]
  rw [PMF.map_comp, PMF.map_comp, PMF.pure_map]
  congr 1

/-- Explicit local-work charge for materializing `x`, forming `x + y`, and evaluating the BLR
predicate.  This is a mathematical charge in the oracle model, not Lean evaluator runtime. -/
def derandomizedBLRLocalWork (n : ℕ) : ℕ :=
  2 * n + 1

/-- The exact cost of the Derandomized BLR oracle program.  Its work field is the `n + r` random
bits, `2n + 1` charged local steps, and the three membership-query nodes. -/
def derandomizedBLRCost (n r : ℕ) : LearningCost :=
  ⟨0, 3, n + r + derandomizedBLRLocalWork n + 3⟩

/-- The number of unbiased random bits exposed by the Derandomized BLR program. -/
def derandomizedBLRRandomBits (n r : ℕ) : ℕ :=
  n + r

/-- Draw the generator seed after `x` is fixed, charge local work, and execute the three queries. -/
def derandomizedBLRAfterInputProgram
    (seed : (Fin r → Bool) → F₂Cube n) (inputBits : Fin n → Bool) :
    LearningProgram n .queries Bool :=
  LearningProgram.bind
    (fun seedBits ↦
      .tick (derandomizedBLRLocalWork n)
        (derandomizedBLRQueryProgram
          (boolVectorF₂CubeEquiv n inputBits) (seed seedBits)))
    (randomBitVectorProgram n r)

/-- The visible finite oracle program for the Derandomized BLR Test. -/
def derandomizedBLRProgram
    (seed : (Fin r → Bool) → F₂Cube n) : LearningProgram n .queries Bool :=
  LearningProgram.bind (derandomizedBLRAfterInputProgram seed)
    (randomBitVectorProgram n n)

/-- The deterministic result selected by a pair of input and generator bit vectors. -/
def derandomizedBLRProgramResult
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n)
    (bits : (Fin n → Bool) × (Fin r → Bool)) : Bool :=
  derandomizedBLRDecision target (boolVectorF₂CubeEquiv n bits.1) (seed bits.2)

private theorem runWithCost_derandomizedBLRTickQueryProgram
    (target : BooleanFunction n) (x y : F₂Cube n) :
    LearningProgram.runWithCost target
        (.tick (derandomizedBLRLocalWork n)
          (derandomizedBLRQueryProgram x y)) =
      PMF.pure
          (derandomizedBLRDecision target x y,
          (⟨0, 3, derandomizedBLRLocalWork n + 3⟩ : LearningCost)) := by
  have hcost :
      LearningProgram.addOutcomeCost
          (⟨0, 0, derandomizedBLRLocalWork n⟩ : LearningCost)
          (derandomizedBLRDecision target x y, (⟨0, 3, 3⟩ : LearningCost)) =
        (derandomizedBLRDecision target x y,
          (⟨0, 3, derandomizedBLRLocalWork n + 3⟩ : LearningCost)) := by
    apply Prod.ext
    · rfl
    · apply LearningCost.toTriple_injective
      change
        (0 + 0, 0 + 3, derandomizedBLRLocalWork n + 3) =
          (0, 3, derandomizedBLRLocalWork n + 3)
      simp
  rw [LearningProgram.runWithCost,
    runWithCost_derandomizedBLRQueryProgram, PMF.pure_map, hcost]

private theorem runWithCost_derandomizedBLRAfterInputProgram
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n)
    (inputBits : Fin n → Bool) :
    LearningProgram.runWithCost target
        (derandomizedBLRAfterInputProgram seed inputBits) =
      (uniformPMF (Fin r → Bool)).map fun seedBits ↦
        (derandomizedBLRDecision target
            (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
          (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost)) := by
  unfold derandomizedBLRAfterInputProgram
  rw [LearningProgram.runWithCost_bind,
    runWithCost_randomBitVectorProgram]
  calc
    ((uniformPMF (Fin r → Bool)).map fun seedBits ↦
          (seedBits, (⟨0, 0, r⟩ : LearningCost))).bind (fun outcome ↦
        (LearningProgram.runWithCost target
          (.tick (derandomizedBLRLocalWork n)
            (derandomizedBLRQueryProgram
              (boolVectorF₂CubeEquiv n inputBits) (seed outcome.1)))).map
          (LearningProgram.addOutcomeCost outcome.2)) =
        ((uniformPMF (Fin r → Bool)).map fun seedBits ↦
          (seedBits, (⟨0, 0, r⟩ : LearningCost))).bind (fun outcome ↦
            PMF.pure
              (derandomizedBLRDecision target
                  (boolVectorF₂CubeEquiv n inputBits) (seed outcome.1),
                outcome.2 +
                  (⟨0, 3, derandomizedBLRLocalWork n + 3⟩ : LearningCost))) := by
      congr 1
      funext outcome
      rw [runWithCost_derandomizedBLRTickQueryProgram, PMF.pure_map]
      rfl
    _ = (uniformPMF (Fin r → Bool)).bind (fun seedBits ↦
          PMF.pure
            (derandomizedBLRDecision target
                (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
              (⟨0, 0, r⟩ : LearningCost) +
                (⟨0, 3, derandomizedBLRLocalWork n + 3⟩ : LearningCost))) := by
      rw [PMF.bind_map]
      rfl
    _ = (uniformPMF (Fin r → Bool)).map fun seedBits ↦
          (derandomizedBLRDecision target
              (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
            (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost)) := by
      rw [← PMF.bind_pure_comp]
      congr 1

/-- Exact output distribution and pathwise cost of the Derandomized BLR program. -/
theorem runWithCost_derandomizedBLRProgram
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n) :
    LearningProgram.runWithCost target (derandomizedBLRProgram seed) =
      (uniformPMF ((Fin n → Bool) × (Fin r → Bool))).map fun bits ↦
        (derandomizedBLRProgramResult target seed bits,
          derandomizedBLRCost n r) := by
  unfold derandomizedBLRProgram
  rw [LearningProgram.runWithCost_bind,
    runWithCost_randomBitVectorProgram]
  have hcost :
      (⟨0, 0, n⟩ : LearningCost) +
          (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost) =
        derandomizedBLRCost n r := by
    apply LearningCost.toTriple_injective
    change
      (0 + 0, 0 + 3, n + (r + derandomizedBLRLocalWork n + 3)) =
      (0, 3, n + r + derandomizedBLRLocalWork n + 3)
    simp [Nat.add_assoc]
  calc
    ((uniformPMF (Fin n → Bool)).map fun inputBits ↦
          (inputBits, (⟨0, 0, n⟩ : LearningCost))).bind (fun outcome ↦
        (LearningProgram.runWithCost target
          (derandomizedBLRAfterInputProgram seed outcome.1)).map
            (LearningProgram.addOutcomeCost outcome.2)) =
        ((uniformPMF (Fin n → Bool)).map fun inputBits ↦
          (inputBits, (⟨0, 0, n⟩ : LearningCost))).bind (fun outcome ↦
            ((uniformPMF (Fin r → Bool)).map fun seedBits ↦
              (derandomizedBLRDecision target
                  (boolVectorF₂CubeEquiv n outcome.1) (seed seedBits),
                (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost))).map
                  (LearningProgram.addOutcomeCost outcome.2)) := by
      congr 1
      funext outcome
      rw [runWithCost_derandomizedBLRAfterInputProgram]
    _ = ((uniformPMF (Fin n → Bool)).map fun inputBits ↦
          (inputBits, (⟨0, 0, n⟩ : LearningCost))).bind (fun outcome ↦
            (uniformPMF (Fin r → Bool)).map fun seedBits ↦
              (derandomizedBLRDecision target
                  (boolVectorF₂CubeEquiv n outcome.1) (seed seedBits),
                outcome.2 +
                  (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost))) := by
      congr 1
      funext outcome
      rw [PMF.map_comp]
      rfl
    _ = (uniformPMF (Fin n → Bool)).bind (fun inputBits ↦
        (uniformPMF (Fin r → Bool)).map fun seedBits ↦
          (derandomizedBLRDecision target
              (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
            derandomizedBLRCost n r)) := by
      rw [PMF.bind_map]
      change
        (uniformPMF (Fin n → Bool)).bind (fun inputBits ↦
            (uniformPMF (Fin r → Bool)).map fun seedBits ↦
              (derandomizedBLRDecision target
                  (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
                (⟨0, 0, n⟩ : LearningCost) +
                  (⟨0, 3, r + derandomizedBLRLocalWork n + 3⟩ : LearningCost))) =
          (uniformPMF (Fin n → Bool)).bind (fun inputBits ↦
            (uniformPMF (Fin r → Bool)).map fun seedBits ↦
              (derandomizedBLRDecision target
                  (boolVectorF₂CubeEquiv n inputBits) (seed seedBits),
                derandomizedBLRCost n r))
      rw [hcost]
    _ =
        ((uniformPMF (Fin n → Bool)).bind (fun inputBits ↦
          (uniformPMF (Fin r → Bool)).map fun seedBits ↦
            (inputBits, seedBits))).map fun bits ↦
              (derandomizedBLRProgramResult target seed bits,
                derandomizedBLRCost n r) := by
      rw [PMF.map_bind]
      simp_rw [PMF.map_comp]
      rfl
    _ = (uniformPMF ((Fin n → Bool) × (Fin r → Bool))).map fun bits ↦
          (derandomizedBLRProgramResult target seed bits,
            derandomizedBLRCost n r) := by
      rw [uniformPMF_bind_map_pair]

/-- Every execution path makes exactly three membership queries and has the displayed exact cost. -/
theorem derandomizedBLRProgram_cost_eq_of_mem_support
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n)
    (outcome : Bool × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target (derandomizedBLRProgram seed)).support) :
    outcome.2 = derandomizedBLRCost n r := by
  rw [runWithCost_derandomizedBLRProgram, PMF.mem_support_map_iff] at houtcome
  obtain ⟨bits, _, rfl⟩ := houtcome
  rfl

/-- Component form of the exact resource law, including the three-query guarantee and the
`n + r + (2n + 1) + 3` work formula. -/
theorem derandomizedBLRProgram_resources_of_mem_support
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n)
    (outcome : Bool × LearningCost)
    (houtcome : outcome ∈
      (LearningProgram.runWithCost target (derandomizedBLRProgram seed)).support) :
    outcome.2.randomExamples = 0 ∧
      outcome.2.queries = 3 ∧
      outcome.2.work = n + r + (2 * n + 1) + 3 := by
  rw [derandomizedBLRProgram_cost_eq_of_mem_support target seed outcome houtcome]
  simp [derandomizedBLRCost, derandomizedBLRLocalWork]

/-- A linear target is accepted on every execution path. -/
theorem runWithCost_derandomizedBLRProgram_eq_pure_of_isF₂Linear
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n)
    (htarget : IsF₂Linear (booleanFunctionF₂Encoding target)) :
    LearningProgram.runWithCost target (derandomizedBLRProgram seed) =
      PMF.pure (true, derandomizedBLRCost n r) := by
  rw [runWithCost_derandomizedBLRProgram]
  have hconstant :
      (fun bits : (Fin n → Bool) × (Fin r → Bool) ↦
        (derandomizedBLRProgramResult target seed bits,
          derandomizedBLRCost n r)) =
        Function.const _ (true, derandomizedBLRCost n r) := by
    funext bits
    have haccepts :
        blrAccepts (booleanFunctionF₂Encoding target)
          (boolVectorF₂CubeEquiv n bits.1) (seed bits.2) :=
      (htarget (boolVectorF₂CubeEquiv n bits.1) (seed bits.2)).symm
    change
      booleanFunctionF₂Encoding target (boolVectorF₂CubeEquiv n bits.1) +
          booleanFunctionF₂Encoding target (seed bits.2) =
        booleanFunctionF₂Encoding target
          (boolVectorF₂CubeEquiv n bits.1 + seed bits.2) at haccepts
    simp [derandomizedBLRProgramResult, derandomizedBLRDecision, haccepts]
  rw [hconstant, PMF.map_const]

/-- Acceptance probability computed directly from the program's uniform random-bit source. -/
noncomputable def derandomizedBLRProgramAcceptanceProbability
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n) : ℝ :=
  𝔼 bits : (Fin n → Bool) × (Fin r → Bool),
    if derandomizedBLRProgramResult target seed bits then (1 : ℝ) else 0

/-- The program's acceptance probability is the existing semantic Derandomized BLR probability
for the density obtained by pushing uniform seed bits through the generator. -/
theorem derandomizedBLRProgramAcceptanceProbability_eq
    (target : BooleanFunction n) (seed : (Fin r → Bool) → F₂Cube n) :
    derandomizedBLRProgramAcceptanceProbability target seed =
      derandomizedBLRAcceptanceProbability
        (ProbabilityDensity.uniformPushforward seed)
        (booleanFunctionF₂Encoding target) := by
  classical
  unfold derandomizedBLRProgramAcceptanceProbability
  calc
    (𝔼 bits : (Fin n → Bool) × (Fin r → Bool),
        if derandomizedBLRProgramResult target seed bits then (1 : ℝ) else 0) =
        𝔼 inputBits : Fin n → Bool, 𝔼 seedBits : Fin r → Bool,
          if blrAccepts (booleanFunctionF₂Encoding target)
              (boolVectorF₂CubeEquiv n inputBits) (seed seedBits) then
            (1 : ℝ)
          else 0 := by
      rw [show
          (Finset.univ : Finset ((Fin n → Bool) × (Fin r → Bool))) =
            (Finset.univ : Finset (Fin n → Bool)) ×ˢ
              (Finset.univ : Finset (Fin r → Bool)) by
            ext x
            simp,
        Finset.expect_product]
      apply Finset.expect_congr rfl
      intro inputBits _
      apply Finset.expect_congr rfl
      intro seedBits _
      by_cases haccepts :
          blrAccepts (booleanFunctionF₂Encoding target)
            (boolVectorF₂CubeEquiv n inputBits) (seed seedBits)
      · simp [derandomizedBLRProgramResult, derandomizedBLRDecision,
          blrAccepts]
      · simp [derandomizedBLRProgramResult, derandomizedBLRDecision,
          blrAccepts]
    _ = 𝔼 x : F₂Cube n, 𝔼 seedBits : Fin r → Bool,
          if blrAccepts (booleanFunctionF₂Encoding target) x (seed seedBits) then
            (1 : ℝ)
          else 0 := by
      apply Fintype.expect_equiv (boolVectorF₂CubeEquiv n)
      intro inputBits
      rfl
    _ = derandomizedBLRAcceptanceProbability
          (ProbabilityDensity.uniformPushforward seed)
          (booleanFunctionF₂Encoding target) := by
      rw [derandomizedBLRAcceptanceProbability]
      simp_rw [ProbabilityDensity.expectation_uniformPushforward]

end FABL
