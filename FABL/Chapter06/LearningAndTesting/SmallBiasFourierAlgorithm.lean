/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasAlgorithm
public import FABL.Chapter06.LearningAndTesting.SmallBiasFourierEstimator

/-!
# The deterministic small-bias Fourier estimator

Book item: Proposition 6.40.

The executable interface encodes `ε` by the finite rational input already used
by Theorem 6.30 and encodes the Fourier `1`-norm bound by a positive natural
number.  The construction first enumerates a density of bias `ε / s`, then
issues one real-valued membership query at every enumerated point.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

namespace ProbabilityDensity

/--
Small bias is unchanged when a finite uniform seed type is reindexed by an
equivalence.
-/
theorem IsBiased.uniformPushforward_comp_equiv
    {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Ω'] [Nonempty Ω']
    {g : Ω → F₂Cube n} {ε : ℝ}
    (hbiased : (ProbabilityDensity.uniformPushforward g).IsBiased ε)
    (e : Ω' ≃ Ω) :
    (ProbabilityDensity.uniformPushforward (g ∘ e)).IsBiased ε := by
  rw [ProbabilityDensity.isBiased_iff_expectation] at hbiased ⊢
  intro γ hγ
  rw [ProbabilityDensity.expectation_uniformPushforward]
  calc
    |𝔼 i : Ω', vectorWalshCharacter γ ((g ∘ e) i)| =
        |𝔼 ω : Ω, vectorWalshCharacter γ (g ω)| := by
      congr 1
      exact Fintype.expect_equiv e
        (fun i : Ω' ↦ vectorWalshCharacter γ ((g ∘ e) i))
        (fun ω : Ω ↦ vectorWalshCharacter γ (g ω))
        (fun _ ↦ rfl)
    _ ≤ ε := by
      simpa [ProbabilityDensity.expectation_uniformPushforward] using
        hbiased γ hγ

end ProbabilityDensity

/-! ## Finite algorithm input -/

/--
Finite input for Proposition 6.40.  The target accuracy is `bias.epsilon`;
`fourierBound` is an integral upper bound for the Fourier `1`-norm.
-/
structure SmallBiasFourierInput where
  /-- The dimension and positive rational target accuracy. -/
  bias : SmallBiasInput
  /-- An integral upper bound for the target's Fourier `1`-norm. -/
  fourierBound : ℕ
  /-- The Fourier bound is at least one. -/
  fourierBound_pos : 1 ≤ fourierBound

namespace SmallBiasFourierInput

/-- The real target accuracy denoted by the finite input. -/
noncomputable def epsilon (input : SmallBiasFourierInput) : ℝ :=
  input.bias.epsilon

/-- The small-bias construction input with requested bias `ε / s`. -/
abbrev generatorInput (input : SmallBiasFourierInput) : SmallBiasInput where
  n := input.bias.n
  numerator := input.bias.numerator
  denominator := input.bias.denominator * input.fourierBound
  n_pos := input.bias.n_pos
  numerator_pos := input.bias.numerator_pos
  twice_numerator_le_denominator := by
    exact input.bias.twice_numerator_le_denominator.trans (by
      have h := Nat.mul_le_mul_left input.bias.denominator
        input.fourierBound_pos
      simpa using h)

/-- The generator's bias is exactly the target accuracy divided by the norm bound. -/
theorem generatorInput_epsilon (input : SmallBiasFourierInput) :
    input.generatorInput.epsilon =
      input.epsilon / (input.fourierBound : ℝ) := by
  have hboundNat : input.fourierBound ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one input.fourierBound_pos).ne'
  have hbound : (input.fourierBound : ℝ) ≠ 0 := by
    exact_mod_cast hboundNat
  have hdenNat : input.bias.denominator ≠ 0 := by
    have htwice :
        0 < 2 * input.bias.numerator :=
      Nat.mul_pos (by omega) input.bias.numerator_pos
    exact (htwice.trans_le
      input.bias.twice_numerator_le_denominator).ne'
  have hden : (input.bias.denominator : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat
  simp only [SmallBiasInput.epsilon, epsilon]
  field_simp [hbound, hden]
  push_cast
  ring

/-- The number of seed pairs enumerated by the generator. -/
def sampleCount (input : SmallBiasFourierInput) : ℕ :=
  2 ^ input.generatorInput.fieldDegree *
    2 ^ input.generatorInput.fieldDegree

theorem sampleCount_pos (input : SmallBiasFourierInput) :
    0 < input.sampleCount := by
  simp [sampleCount]

/-- The selected deterministic small-bias construction. -/
def construction (input : SmallBiasFourierInput) :
    ExecutableSmallBiasConstruction input.generatorInput.n :=
  deterministicSmallBiasAlgorithm input.generatorInput

/--
The fixed query sample, indexed by the canonical recursive enumeration of
the two binary field seeds.
-/
def sample (input : SmallBiasFourierInput) :
    Fin input.sampleCount → F₂Cube input.generatorInput.n :=
  fun i ↦
    let seeds :=
      binaryVectorPairEnumerationEquiv
        input.generatorInput.fieldDegree i
    executableSmallBiasGenerator input.generatorInput.n
      input.generatorInput.fieldDegree_pos
      (deterministicSmallBiasAlgorithm
        input.generatorInput).fieldModel.implementation
      seeds.1 seeds.2

/-- The probability density induced by the explicitly indexed query sample. -/
noncomputable def sampleDensity (input : SmallBiasFourierInput) :
    ProbabilityDensity input.generatorInput.n :=
  letI : Nonempty (Fin input.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.sampleCount_pos
  ProbabilityDensity.uniformPushforward input.sample

/-- The explicitly indexed query sample has bias `ε / s`. -/
theorem sample_isBiased (input : SmallBiasFourierInput) :
    input.sampleDensity.IsBiased
      (input.epsilon / (input.fourierBound : ℝ)) := by
  letI : Nonempty (Fin input.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.sampleCount_pos
  let generator := input.generatorInput
  let construction := deterministicSmallBiasAlgorithm generator
  have hbiased :=
    (deterministicSmallBiasAlgorithm_spec generator).2.2.1
  change
    (executableSmallBiasGeneratorDensity generator.n
      generator.fieldDegree_pos
      construction.fieldModel.implementation).IsBiased
        generator.epsilon at hbiased
  have hreindexed :=
    hbiased.uniformPushforward_comp_equiv
      (binaryVectorPairEnumerationEquiv generator.fieldDegree)
  rw [← input.generatorInput_epsilon]
  change
    (ProbabilityDensity.uniformPushforward
      ((fun rs : F₂Cube generator.fieldDegree ×
          F₂Cube generator.fieldDegree ↦
        executableSmallBiasGenerator generator.n
          generator.fieldDegree_pos
          construction.fieldModel.implementation rs.1 rs.2) ∘
        binaryVectorPairEnumerationEquiv generator.fieldDegree)).IsBiased
      generator.epsilon
  exact hreindexed

end SmallBiasFourierInput

/-! ## Proposition 6.40 -/

/-- Full cost of constructing the sample and running its query estimator. -/
def deterministicSmallBiasFourierEstimatorCost
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) : LearningCost :=
  ⟨0, 0, deterministicSmallBiasWork input.generatorInput⟩ +
    smallBiasFourierEstimatorCost input.sampleCount U

/--
The deterministic program charges the complete sample construction before
enumerating the real-valued oracle queries.
-/
noncomputable def deterministicSmallBiasFourierEstimatorProgram
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) :
    DeterministicQueryProgram {−1,1}^[input.generatorInput.n] ℝ ℝ :=
  .tick (deterministicSmallBiasWork input.generatorInput)
    (smallBiasFourierEstimatorProgram input.sample U)

/-- The program returns the empirical Fourier estimate with exact visible cost. -/
theorem DeterministicQueryProgram.runWithCost_deterministicSmallBiasFourierEstimatorProgram
    (input : SmallBiasFourierInput)
    (f : {−1,1}^[input.generatorInput.n] → ℝ)
    (U : Finset (Fin input.generatorInput.n)) :
    DeterministicQueryProgram.runWithCost f
        (deterministicSmallBiasFourierEstimatorProgram input U) =
      (smallBiasFourierEstimate f input.sample U,
        deterministicSmallBiasFourierEstimatorCost input U) := by
  rfl

/--
O'Donnell, Proposition 6.40: under the advertised Fourier `1`-norm bound,
the deterministic finite-input program estimates the requested coefficient
to within `ε`.
-/
theorem abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le
    (input : SmallBiasFourierInput)
    (f : {−1,1}^[input.generatorInput.n] → ℝ)
    (U : Finset (Fin input.generatorInput.n))
    (hf : fourierOneNorm f ≤ input.fourierBound) :
    |smallBiasFourierEstimate f input.sample U - fourierCoeff f U| ≤
      input.epsilon := by
  letI : NeZero input.sampleCount :=
    ⟨input.sampleCount_pos.ne'⟩
  letI : Nonempty (Fin input.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.sampleCount_pos
  exact abs_smallBiasFourierEstimate_sub_fourierCoeff_le_parameter
    f input.sample U input.bias.epsilon_pos
      (by simpa [SmallBiasFourierInput.epsilon, one_div] using
        input.bias.epsilon_le_half)
      (by exact_mod_cast input.fourierBound_pos)
      (by simpa [SmallBiasFourierInput.sampleDensity] using
        input.sample_isBiased) hf

/-- The complete deterministic program makes exactly one query per seed pair. -/
theorem deterministicSmallBiasFourierEstimatorCost_queries
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) :
    (deterministicSmallBiasFourierEstimatorCost input U).queries =
      input.sampleCount := by
  change 0 + (input.sampleCount + 0) = input.sampleCount
  omega

/-- The deterministic estimator uses no random examples. -/
theorem deterministicSmallBiasFourierEstimatorCost_randomExamples
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) :
    (deterministicSmallBiasFourierEstimatorCost input U).randomExamples = 0 := by
  rfl

namespace SmallBiasFourierInput

/-- A common polynomial budget in the integral scale `⌈n s / ε⌉`. -/
def polynomialBudget (input : SmallBiasFourierInput) : ℕ :=
  2 ^ 18 * (input.generatorInput.scale + 1) ^ 8

/-- The number of enumerated seed pairs is at most four times the squared scale. -/
theorem sampleCount_le_four_mul_scale_sq
    (input : SmallBiasFourierInput) :
    input.sampleCount ≤ 4 * input.generatorInput.scale ^ 2 := by
  have hfield :=
    input.generatorInput.fieldSize_le_two_scale
  rw [sampleCount]
  calc
    2 ^ input.generatorInput.fieldDegree *
        2 ^ input.generatorInput.fieldDegree ≤
        (2 * input.generatorInput.scale) *
          (2 * input.generatorInput.scale) :=
      Nat.mul_le_mul hfield hfield
    _ = 4 * input.generatorInput.scale ^ 2 := by ring

end SmallBiasFourierInput

/-- Exact local-work decomposition of the complete deterministic estimator. -/
theorem deterministicSmallBiasFourierEstimatorCost_work
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) :
    (deterministicSmallBiasFourierEstimatorCost input U).work =
      deterministicSmallBiasWork input.generatorInput +
        input.sampleCount +
        smallBiasFourierEstimatorWork input.sampleCount U := by
  change
    deterministicSmallBiasWork input.generatorInput +
        (input.sampleCount +
          smallBiasFourierEstimatorWork input.sampleCount U) =
      deterministicSmallBiasWork input.generatorInput +
        input.sampleCount +
        smallBiasFourierEstimatorWork input.sampleCount U
  omega

/--
Every execution obeys one common degree-eight polynomial bound in
`⌈n s / ε⌉`.
-/
theorem deterministicSmallBiasFourierEstimatorCost_resource_bounds
    (input : SmallBiasFourierInput)
    (U : Finset (Fin input.generatorInput.n)) :
    (deterministicSmallBiasFourierEstimatorCost input U).randomExamples = 0 ∧
      (deterministicSmallBiasFourierEstimatorCost input U).queries ≤
        input.polynomialBudget ∧
      (deterministicSmallBiasFourierEstimatorCost input U).work ≤
        input.polynomialBudget := by
  let q := input.generatorInput.scale
  let Q := q + 1
  let m := input.sampleCount
  have hQ : 1 ≤ Q := by simp [Q]
  have hqQ : q ≤ Q := by simp [Q]
  have hnQ : input.generatorInput.n ≤ Q :=
    input.generatorInput.n_le_scale.trans hqQ
  have hcardQ : U.card ≤ Q :=
    (Finset.card_le_univ U).trans (by
      simpa using hnQ)
  have hmQ : m ≤ 4 * Q ^ 2 := by
    exact input.sampleCount_le_four_mul_scale_sq.trans
      (Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left hqQ 2))
  have hQ3Q8 : Q ^ 3 ≤ Q ^ 8 :=
    Nat.pow_le_pow_right hQ (by omega)
  have hQ8 : 1 ≤ Q ^ 8 :=
    Nat.one_le_pow 8 Q hQ
  have hcardThree : U.card + 3 ≤ 4 * Q := by omega
  have htail :
      m * (U.card + 3) + 1 ≤ 2 ^ 17 * Q ^ 8 := by
    calc
      m * (U.card + 3) + 1 ≤
          (4 * Q ^ 2) * (4 * Q) + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul hmQ hcardThree) 1
      _ = 16 * Q ^ 3 + 1 := by ring
      _ ≤ 17 * Q ^ 8 := by
        have hscaled :=
          Nat.mul_le_mul_left 16 hQ3Q8
        omega
      _ ≤ 2 ^ 17 * Q ^ 8 := by
        exact Nat.mul_le_mul_right (Q ^ 8) (by norm_num)
  have hconstruction :
      deterministicSmallBiasWork input.generatorInput ≤
        2 ^ 17 * Q ^ 8 := by
    simpa [SmallBiasInput.polynomialBudget, Q, q] using
      deterministicSmallBiasWork_le_polynomialBudget
        input.generatorInput
  have hwork :
      (deterministicSmallBiasFourierEstimatorCost input U).work ≤
        2 ^ 18 * Q ^ 8 := by
    rw [deterministicSmallBiasFourierEstimatorCost_work,
      smallBiasFourierEstimatorWork]
    have hnormalize :
        deterministicSmallBiasWork input.generatorInput +
            m + (m * (U.card + 2) + 1) =
          deterministicSmallBiasWork input.generatorInput +
            (m * (U.card + 3) + 1) := by ring
    rw [hnormalize]
    exact (Nat.add_le_add hconstruction htail).trans_eq (by ring)
  refine ⟨deterministicSmallBiasFourierEstimatorCost_randomExamples
      input U, ?_, ?_⟩
  · rw [deterministicSmallBiasFourierEstimatorCost_queries]
    calc
      m ≤ 4 * Q ^ 2 := hmQ
      _ ≤ 4 * Q ^ 8 :=
        Nat.mul_le_mul_left 4
          (Nat.pow_le_pow_right hQ (by omega))
      _ ≤ 2 ^ 18 * Q ^ 8 :=
        Nat.mul_le_mul_right (Q ^ 8) (by norm_num)
      _ = input.polynomialBudget := by
        simp [SmallBiasFourierInput.polynomialBudget, Q, q]
  · simpa [SmallBiasFourierInput.polynomialBudget, Q, q] using hwork

/-- A dimension-compatible estimator task for uniform asymptotic statements. -/
abbrev SmallBiasFourierTask :=
  Σ input : SmallBiasFourierInput,
    Finset (Fin input.generatorInput.n)

/-- Scale of a complete Fourier-estimation task. -/
def smallBiasFourierTaskScale (task : SmallBiasFourierTask) : ℕ :=
  task.1.generatorInput.scale

/-- Query complexity is polynomial in `⌈n s / ε⌉`. -/
theorem deterministicSmallBiasFourierEstimator_queries_isBigO :
    Asymptotics.IsBigO
      (Filter.comap smallBiasFourierTaskScale Filter.atTop)
      (fun task : SmallBiasFourierTask ↦
        ((deterministicSmallBiasFourierEstimatorCost
          task.1 task.2).queries : ℝ))
      (fun task : SmallBiasFourierTask ↦
        (((smallBiasFourierTaskScale task + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 18 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast
    (deterministicSmallBiasFourierEstimatorCost_resource_bounds
      task.1 task.2).2.1

/-- Charged local work is polynomial in `⌈n s / ε⌉`. -/
theorem deterministicSmallBiasFourierEstimator_work_isBigO :
    Asymptotics.IsBigO
      (Filter.comap smallBiasFourierTaskScale Filter.atTop)
      (fun task : SmallBiasFourierTask ↦
        ((deterministicSmallBiasFourierEstimatorCost
          task.1 task.2).work : ℝ))
      (fun task : SmallBiasFourierTask ↦
        (((smallBiasFourierTaskScale task + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 18 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast
    (deterministicSmallBiasFourierEstimatorCost_resource_bounds
      task.1 task.2).2.2

end FABL
