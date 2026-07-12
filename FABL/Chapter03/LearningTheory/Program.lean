/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter02.SocialChoiceFunctions
public import FABL.Chapter03.SubspacesAndDecisionTrees
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.Bits
import Mathlib.Logic.Encodable.Pi
import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite learning programs

Book items: Definition 3.27, Proposition 3.30.

The finite oracle-program syntax, cost semantics, and probability API for Section 3.4.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

@[expose] public section

namespace FABL

universe u v

variable {n : ℕ}

local instance learningSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance learningSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- A finite equivalence transports the uniform probability mass function to the uniform
probability mass function. -/
theorem map_uniformPMF_equiv {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniformPMF α).map e = uniformPMF β := by
  classical
  ext b
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [uniformPMF, PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    rw [if_neg]
    intro h
    apply ha
    rw [h]
    simp

/-- A finitely encoded accuracy input in the range used by O'Donnell, Definition 3.27. Rational
inputs give the scheduler finite parameters; mathematical error bounds use their real coercions. -/
abbrev LearningAccuracy := Set.Icc (0 : ℚ) (1 / 2)

/-- A strictly positive finite parameter in the range required by Proposition 3.30. -/
abbrev PositiveLearningParameter := Set.Ioc (0 : ℚ) (1 / 2)

/-- The real value of a positive finite learning parameter is positive and at most `1/2`. -/
theorem positiveLearningParameter_toReal_mem_Ioc (ε : PositiveLearningParameter) :
    ((ε.1 : ℚ) : ℝ) ∈ Set.Ioc 0 (1 / 2) := by
  constructor
  · exact Rat.cast_pos.mpr ε.2.1
  · simpa using
      (Rat.cast_le.mpr ε.2.2 : (ε.1 : ℝ) ≤ (((1 / 2 : ℚ) : ℝ)))

/-- Every positive real parameter admits a positive rational scheduler parameter strictly between
half of `min x (1 / 2)` and `min x (1 / 2)`. -/
theorem exists_positiveLearningParameter_between_half
    (x : ℝ) (hx : 0 < x) :
    ∃ q : PositiveLearningParameter,
      min x (1 / 2) / 2 < ((q.1 : ℚ) : ℝ) ∧
        ((q.1 : ℚ) : ℝ) < min x (1 / 2) := by
  have hmin : 0 < min x (1 / 2 : ℝ) := lt_min hx (by norm_num)
  have hhalf : min x (1 / 2 : ℝ) / 2 < min x (1 / 2 : ℝ) := by
    nlinarith
  obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn hhalf
  have hqPosReal : (0 : ℝ) < (q : ℝ) := by
    exact (div_pos hmin (by norm_num)).trans hqLower
  have hqHalfReal : (q : ℝ) < 1 / 2 :=
    hqUpper.trans_le (min_le_right x (1 / 2 : ℝ))
  refine ⟨⟨q, Rat.cast_pos.mp hqPosReal, ?_⟩, hqLower, hqUpper⟩
  exact (Rat.cast_le (K := ℝ)).mp (by simpa using hqHalfReal.le)

/-- Number of binary confidence bits sufficient to reduce the two-sided failure bound to `δ`. -/
def fourierEstimatorFailureBits (δ : PositiveLearningParameter) : ℕ :=
  Nat.clog 2 (Nat.ceil ((2 : ℚ) / δ.1))

/-- Computable rational sample scheduler for Proposition 3.30. -/
def fourierEstimatorSampleCount
    (ε δ : PositiveLearningParameter) : ℕ :=
  Nat.ceil ((2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2)

/-- The binary confidence scheduler always requests at least one bit. -/
theorem fourierEstimatorFailureBits_pos (δ : PositiveLearningParameter) :
    0 < fourierEstimatorFailureBits δ := by
  apply Nat.clog_pos one_lt_two
  have hδltTwo : δ.1 < (2 : ℚ) := δ.2.2.trans_lt (by norm_num)
  have hquotient : (1 : ℚ) < 2 / δ.1 := by
    rw [lt_div_iff₀ δ.2.1]
    simpa using hδltTwo
  have hceil : (1 : ℚ) < Nat.ceil ((2 : ℚ) / δ.1) :=
    hquotient.trans_le (Nat.le_ceil _)
  exact_mod_cast hceil

/-- The computable Fourier-estimator scheduler draws a positive number of samples. -/
theorem fourierEstimatorSampleCount_pos (ε δ : PositiveLearningParameter) :
    0 < fourierEstimatorSampleCount ε δ := by
  have hpositive :
      (0 : ℚ) < (2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2 :=
    div_pos
      (mul_pos (by norm_num) (by exact_mod_cast fourierEstimatorFailureBits_pos δ))
      (sq_pos_of_pos ε.2.1)
  simpa [fourierEstimatorSampleCount] using
    (Nat.one_le_ceil_iff.mpr hpositive)

/-- The binary confidence schedule reduces a factor-two tail to at most `δ`. -/
theorem two_div_pow_fourierEstimatorFailureBits_le
    (δ : PositiveLearningParameter) :
    (2 : ℚ) / (2 : ℚ) ^ fourierEstimatorFailureBits δ ≤ δ.1 := by
  have hceil :
      (2 : ℚ) / δ.1 ≤ (Nat.ceil ((2 : ℚ) / δ.1) : ℚ) :=
    Nat.le_ceil _
  have hpowNat :
      Nat.ceil ((2 : ℚ) / δ.1) ≤ 2 ^ fourierEstimatorFailureBits δ := by
    exact Nat.le_pow_clog one_lt_two _
  have hpow :
      (Nat.ceil ((2 : ℚ) / δ.1) : ℚ) ≤
        (2 : ℚ) ^ fourierEstimatorFailureBits δ := by
    exact_mod_cast hpowNat
  have hratio := hceil.trans hpow
  have hdenominator : (0 : ℚ) < (2 : ℚ) ^ fourierEstimatorFailureBits δ :=
    pow_pos (by norm_num) _
  rw [div_le_iff₀ hdenominator]
  have hcross := (div_le_iff₀ δ.2.1).mp hratio
  nlinarith

/-- The scheduled sample count makes the Hoeffding exponent at least the confidence-bit count. -/
theorem fourierEstimatorFailureBits_le_sampleExponent
    (ε δ : PositiveLearningParameter) :
    (fourierEstimatorFailureBits δ : ℚ) ≤
      (fourierEstimatorSampleCount ε δ : ℚ) * ε.1 ^ 2 / 2 := by
  have hceil :
      (2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2 ≤
        (fourierEstimatorSampleCount ε δ : ℚ) := by
    simpa [fourierEstimatorSampleCount] using
      (Nat.le_ceil ((2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2))
  have hmul := mul_le_mul_of_nonneg_right hceil (sq_nonneg ε.1)
  have hεne : ε.1 ≠ 0 := ne_of_gt ε.2.1
  have hcancel :
      ((2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2) * ε.1 ^ 2 =
        2 * fourierEstimatorFailureBits δ := by
    field_simp
  rw [hcancel] at hmul
  nlinarith

/-- Explicit polynomial/logarithmic sample bound: the scheduler is at most four times the binary
confidence-bit count divided by `ε²`. The bit count is definitionally
`clog₂ ⌈2 / δ⌉`. -/
theorem fourierEstimatorSampleCount_cast_le
    (ε δ : PositiveLearningParameter) :
    (fourierEstimatorSampleCount ε δ : ℚ) ≤
      4 * fourierEstimatorFailureBits δ / ε.1 ^ 2 := by
  have hεsqPos : (0 : ℚ) < ε.1 ^ 2 := sq_pos_of_pos ε.2.1
  have hk : (1 : ℚ) ≤ fourierEstimatorFailureBits δ := by
    exact_mod_cast fourierEstimatorFailureBits_pos δ
  have hproduct :
      0 ≤ ε.1 * ((1 / 2 : ℚ) - ε.1) :=
    mul_nonneg ε.2.1.le (sub_nonneg.mpr ε.2.2)
  have hεsq : ε.1 ^ 2 ≤ (1 / 4 : ℚ) := by
    nlinarith
  have hhalf :
      (1 / 2 : ℚ) ≤
        (2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2 := by
    rw [le_div_iff₀ hεsqPos]
    nlinarith
  calc
    (fourierEstimatorSampleCount ε δ : ℚ) ≤
        2 * ((2 : ℚ) * fourierEstimatorFailureBits δ / ε.1 ^ 2) := by
      rw [fourierEstimatorSampleCount]
      apply Nat.ceil_le_two_mul
      norm_num at hhalf ⊢
      exact hhalf
    _ = 4 * fourierEstimatorFailureBits δ / ε.1 ^ 2 := by ring

/-- The computable scheduler makes the two-sided Hoeffding bound at most `δ`. -/
theorem two_mul_exp_neg_fourierEstimatorSampleCount_le
    (ε δ : PositiveLearningParameter) :
    2 * Real.exp (-(fourierEstimatorSampleCount ε δ : ℝ) * (ε.1 : ℝ) ^ 2 / 2) ≤
      (δ.1 : ℝ) := by
  have hexponent :
      (fourierEstimatorFailureBits δ : ℝ) ≤
        (fourierEstimatorSampleCount ε δ : ℝ) * (ε.1 : ℝ) ^ 2 / 2 := by
    exact_mod_cast fourierEstimatorFailureBits_le_sampleExponent ε δ
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlogScaled :
      (fourierEstimatorFailureBits δ : ℝ) * Real.log 2 ≤
        (fourierEstimatorSampleCount ε δ : ℝ) * (ε.1 : ℝ) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hlogTwo
      (Nat.cast_nonneg (fourierEstimatorFailureBits δ) : (0 : ℝ) ≤ _)
    norm_num at h
    exact h.trans hexponent
  have hexp :
      Real.exp (-(fourierEstimatorSampleCount ε δ : ℝ) * (ε.1 : ℝ) ^ 2 / 2) ≤
        Real.exp (-(fourierEstimatorFailureBits δ : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexpBits :
      Real.exp (-(fourierEstimatorFailureBits δ : ℝ) * Real.log 2) =
        (2 : ℝ)⁻¹ ^ fourierEstimatorFailureBits δ := by
    calc
      Real.exp (-(fourierEstimatorFailureBits δ : ℝ) * Real.log 2) =
          Real.exp ((fourierEstimatorFailureBits δ : ℕ) * (-Real.log 2)) := by
        congr 1
        ring
      _ = Real.exp (-Real.log 2) ^ fourierEstimatorFailureBits δ :=
        Real.exp_nat_mul _ _
      _ = (2 : ℝ)⁻¹ ^ fourierEstimatorFailureBits δ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hconfidence :
      (2 : ℝ) / (2 : ℝ) ^ fourierEstimatorFailureBits δ ≤ (δ.1 : ℝ) := by
    have hcast :
        (((2 : ℚ) / (2 : ℚ) ^ fourierEstimatorFailureBits δ : ℚ) : ℝ) ≤
          (δ.1 : ℝ) :=
      Rat.cast_le.mpr (two_div_pow_fourierEstimatorFailureBits_le δ)
    norm_num at hcast ⊢
    exact hcast
  calc
    2 * Real.exp (-(fourierEstimatorSampleCount ε δ : ℝ) * (ε.1 : ℝ) ^ 2 / 2) ≤
        2 * Real.exp (-(fourierEstimatorFailureBits δ : ℝ) * Real.log 2) := by
      gcongr
    _ = 2 * (2 : ℝ)⁻¹ ^ fourierEstimatorFailureBits δ := by rw [hexpBits]
    _ = (2 : ℝ) / (2 : ℝ) ^ fourierEstimatorFailureBits δ := by
      rw [inv_pow]
      rfl
    _ ≤ (δ.1 : ℝ) := hconfidence

/-- The real value of a finitely encoded learning-accuracy input lies in `[0, 1/2]`. -/
theorem learningAccuracy_toReal_mem_Icc (ε : LearningAccuracy) :
    ((ε.1 : ℚ) : ℝ) ∈ Set.Icc 0 (1 / 2) := by
  constructor
  · exact Rat.cast_nonneg.mpr ε.2.1
  · simpa using
      (Rat.cast_le.mpr ε.2.2 : (ε.1 : ℝ) ≤ (((1 / 2 : ℚ) : ℝ)))

/-- The two access models in O'Donnell, Definition 3.27. -/
inductive LearningAccess where
  /-- The learner receives independent uniform pairs. -/
  | randomExamples
  /-- The learner requests the target value at an input of its choice. -/
  | queries
deriving DecidableEq

/-- Resource usage of a finite learning computation. -/
structure LearningCost where
  /-- Number of calls to the random-example oracle. -/
  randomExamples : ℕ
  /-- Number of membership queries. -/
  queries : ℕ
  /-- Number of explicitly charged local computation steps. -/
  work : ℕ
deriving DecidableEq

instance : Zero LearningCost :=
  ⟨⟨0, 0, 0⟩⟩

instance : Add LearningCost :=
  ⟨fun a b ↦
    ⟨a.randomExamples + b.randomExamples, a.queries + b.queries, a.work + b.work⟩⟩

/-- Component tuple used to transfer the additive laws to `LearningCost`. -/
def LearningCost.toTriple (cost : LearningCost) : ℕ × ℕ × ℕ :=
  (cost.randomExamples, cost.queries, cost.work)

/-- The component tuple faithfully represents a learning cost. -/
theorem LearningCost.toTriple_injective : Function.Injective LearningCost.toTriple := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  simp only [LearningCost.toTriple, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- Componentwise multiplication of a learning cost by a natural number. -/
instance : SMul ℕ LearningCost where
  smul k cost :=
    ⟨k * cost.randomExamples, k * cost.queries, k * cost.work⟩

/-- Learning costs form a componentwise additive commutative monoid. -/
instance : AddCommMonoid LearningCost :=
  Function.Injective.addCommMonoid LearningCost.toTriple LearningCost.toTriple_injective
    rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The cost of generating one unbiased random bit. -/
def LearningCost.coin : LearningCost :=
  ⟨0, 0, 1⟩

/-- The cost of one random-example call. -/
def LearningCost.example : LearningCost :=
  ⟨1, 0, 1⟩

/-- The cost of one membership-query call. -/
def LearningCost.query : LearningCost :=
  ⟨0, 1, 1⟩

/-- A finite pure randomized computation whose only target-function effects are exposed by its
access-indexed constructors. Branches are finite syntax trees, not opaque functions with claimed
oracle costs. -/
inductive LearningProgram (n : ℕ) : LearningAccess → Type u → Type (u + 1) where
  /-- Return a value. -/
  | pure {access α} (output : α) : LearningProgram n access α
  /-- Draw one unbiased random bit. -/
  | coin {access α} (next : Bool → LearningProgram n access α) :
      LearningProgram n access α
  /-- Draw one independent uniform labeled example. -/
  | randomExample {α}
      (next : ({−1,1}^[n] × Sign) → LearningProgram n .randomExamples α) :
      LearningProgram n .randomExamples α
  /-- Draw exactly `m` independent uniform labeled examples. -/
  | randomExampleBatch {α} (m : ℕ)
      (next : (Fin m → ({−1,1}^[n] × Sign)) →
        LearningProgram n .randomExamples α) :
      LearningProgram n .randomExamples α
  /-- Draw `m` independent uniform cube inputs without calling the target oracle. -/
  | uniformInputBatch {access α} (m : ℕ)
      (next : (Fin m → {−1,1}^[n]) → LearningProgram n access α) :
      LearningProgram n access α
  /-- Draw an `m`-sample batch independently for every element of a finite index type. -/
  | randomExampleMatrix {κ : Type} {α} (indices : Finset κ) (m : ℕ)
      (next : (indices → Fin m → ({−1,1}^[n] × Sign)) →
        LearningProgram n .randomExamples α) :
      LearningProgram n .randomExamples α
  /-- Draw a finite matrix of labeled examples and return a pure function of it with an explicit
  local-work charge. -/
  | randomExampleMatrixOutput {κ : Type} {α} (indices : Finset κ) (m work : ℕ)
      (output : (indices → Fin m → ({−1,1}^[n] × Sign)) → α) :
      LearningProgram n .randomExamples α
  /-- Query the target at a chosen input. -/
  | query {α} (x : {−1,1}^[n]) (next : Sign → LearningProgram n .queries α) :
      LearningProgram n .queries α
  /-- Charge a specified number of local computation steps. -/
  | tick {access α} (steps : ℕ) (next : LearningProgram n access α) :
      LearningProgram n access α

namespace LearningProgram

/-- Add an already incurred cost to a computation outcome. -/
def addOutcomeCost {α : Type u} (extra : LearningCost) (outcome : α × LearningCost) :
    α × LearningCost :=
  (outcome.1, extra + outcome.2)

/-- Sequential composition of finite learning syntax without hiding any oracle node. -/
def bind {access : LearningAccess} {α β : Type u}
    (next : α → LearningProgram n access β) :
    LearningProgram n access α → LearningProgram n access β
  | .pure output => next output
  | .coin branch => .coin fun b ↦ bind next (branch b)
  | .randomExample branch => .randomExample fun sample ↦ bind next (branch sample)
  | .randomExampleBatch m branch =>
      .randomExampleBatch m fun samples ↦ bind next (branch samples)
  | .uniformInputBatch m branch =>
      .uniformInputBatch m fun samples ↦ bind next (branch samples)
  | .randomExampleMatrix indices m branch =>
      .randomExampleMatrix indices m fun samples ↦ bind next (branch samples)
  | .randomExampleMatrixOutput indices m work output =>
      .randomExampleMatrix indices m fun samples ↦ .tick work (next (output samples))
  | .query x branch => .query x fun answer ↦ bind next (branch answer)
  | .tick steps program => .tick steps (bind next program)

/-- Map a pure function over the output of finite learning syntax. -/
def map {access : LearningAccess} {α β : Type u} (f : α → β)
    (program : LearningProgram n access α) : LearningProgram n access β :=
  bind (fun output ↦ .pure (f output)) program

/-- Sequentially execute a finite list of programs in the same access model. -/
def sequence {access : LearningAccess} {α : Type u} :
    List (LearningProgram n access α) → LearningProgram n access (List α)
  | [] => .pure []
  | program :: programs =>
      bind (fun output ↦ map (List.cons output) (sequence programs)) program

/-- Pure output-and-cost map for a finite matrix of random examples. -/
def randomExampleMatrixOutcome {κ : Type} {α : Type u}
    (target : BooleanFunction n) (indices : Finset κ) (m work : ℕ)
    (output : (indices → Fin m → ({−1,1}^[n] × Sign)) → α)
    (sampleInputs : indices → Fin m → {−1,1}^[n]) : α × LearningCost :=
  (output fun k i ↦ (sampleInputs k i, target (sampleInputs k i)),
    ⟨indices.card * m, 0, indices.card * m + work⟩)

/-- Uniform law on a finite matrix of random-example inputs. -/
noncomputable def randomExampleMatrixInputLaw {κ : Type}
    (indices : Finset κ) (m : ℕ) : PMF (indices → Fin m → {−1,1}^[n]) := by
  classical
  exact uniformPMF (indices → Fin m → {−1,1}^[n])

/-- The named matrix input law is definitionally the uniform law on the finite matrix type. -/
theorem randomExampleMatrixInputLaw_eq_uniformPMF {κ : Type} [DecidableEq κ]
    (indices : Finset κ) (m : ℕ) :
    randomExampleMatrixInputLaw (n := n) indices m =
      uniformPMF (indices → Fin m → {−1,1}^[n]) := by
  classical
  ext sampleInputs
  simp [randomExampleMatrixInputLaw, uniformPMF, PMF.uniformOfFintype_apply]

/-- Direct PMF semantics of a pure finite matrix-of-examples output node. -/
noncomputable def randomExampleMatrixOutputLaw {κ : Type} {α : Type u}
    (target : BooleanFunction n) (indices : Finset κ) (m work : ℕ)
    (output : (indices → Fin m → ({−1,1}^[n] × Sign)) → α) :
    PMF (α × LearningCost) := by
  exact (randomExampleMatrixInputLaw indices m).map
    (randomExampleMatrixOutcome target indices m work output)

/-- The direct matrix-output law is the pushforward of the uniform input matrix. -/
theorem randomExampleMatrixOutputLaw_toOuterMeasure_apply {κ : Type} {α : Type u}
    (target : BooleanFunction n) (indices : Finset κ) (m work : ℕ)
    (output : (indices → Fin m → ({−1,1}^[n] × Sign)) → α)
    (event : Set (α × LearningCost)) :
    (randomExampleMatrixOutputLaw target indices m work output).toOuterMeasure event =
      (randomExampleMatrixInputLaw indices m).toOuterMeasure
        (randomExampleMatrixOutcome target indices m work output ⁻¹' event) := by
  unfold randomExampleMatrixOutputLaw
  rw [PMF.toOuterMeasure_map_apply]

/-- Distributional semantics of a finite learning program, including the cost of each execution
path. The target function is observable only at random-example or query nodes. -/
noncomputable def runWithCost {access : LearningAccess} {α : Type u}
    (target : BooleanFunction n) :
    LearningProgram n access α → PMF (α × LearningCost)
  | .pure output => PMF.pure (output, 0)
  | .coin next =>
      (uniformPMF Bool).bind fun b ↦
        (runWithCost target (next b)).map (addOutcomeCost LearningCost.coin)
  | .randomExample next =>
      (uniformPMF {−1,1}^[n]).bind fun x ↦
        (runWithCost target (next (x, target x))).map
          (addOutcomeCost LearningCost.example)
  | .randomExampleBatch m next =>
      (uniformPMF (Fin m → {−1,1}^[n])).bind fun sampleInputs ↦
        (runWithCost target (next fun i ↦ (sampleInputs i, target (sampleInputs i)))).map
          (addOutcomeCost ⟨m, 0, m⟩)
  | .uniformInputBatch m next =>
      (uniformPMF (Fin m → {−1,1}^[n])).bind fun sampleInputs ↦
        (runWithCost target (next sampleInputs)).map
          (addOutcomeCost ⟨0, 0, m * n⟩)
  | .randomExampleMatrix indices m next => by
      classical
      exact (uniformPMF (indices → Fin m → {−1,1}^[n])).bind fun sampleInputs ↦
        (runWithCost target
          (next fun k i ↦ (sampleInputs k i, target (sampleInputs k i)))).map
            (addOutcomeCost ⟨indices.card * m, 0, indices.card * m⟩)
  | .randomExampleMatrixOutput indices m work output => by
      exact randomExampleMatrixOutputLaw target indices m work output
  | .query x next =>
      (runWithCost target (next (target x))).map (addOutcomeCost LearningCost.query)
  | .tick steps next =>
      (runWithCost target next).map
        (addOutcomeCost ⟨0, 0, steps⟩)

/-- Adding zero cost leaves an outcome unchanged. -/
theorem addOutcomeCost_zero {α : Type u} (outcome : α × LearningCost) :
    addOutcomeCost 0 outcome = outcome := by
  rcases outcome with ⟨output, cost⟩
  simp [addOutcomeCost]

/-- Mapping zero additional cost over a probability mass function is the identity. -/
theorem map_addOutcomeCost_zero {α : Type u} (p : PMF (α × LearningCost)) :
    p.map (addOutcomeCost 0) = p := by
  rw [show addOutcomeCost (α := α) 0 = id by
    funext outcome
    exact addOutcomeCost_zero outcome]
  exact p.map_id

/-- Moving a fixed accumulated cost across a probabilistic bind preserves the total path
cost. -/
theorem bind_map_addOutcomeCost_comm {α β : Type u}
    (extra : LearningCost) (p : PMF (α × LearningCost))
    (nextLaw : α → PMF (β × LearningCost)) :
    (p.bind fun outcome ↦
        ((nextLaw outcome.1).map (addOutcomeCost outcome.2)).map
          (addOutcomeCost extra)) =
      (p.map (addOutcomeCost extra)).bind fun outcome ↦
        (nextLaw outcome.1).map (addOutcomeCost outcome.2) := by
  rw [PMF.bind_map]
  congr 1
  funext outcome
  simp only [Function.comp_apply]
  rw [PMF.map_comp]
  congr 1
  funext nextOutcome
  rcases outcome with ⟨output, cost⟩
  rcases nextOutcome with ⟨nextOutput, nextCost⟩
  simp [addOutcomeCost, add_assoc]

/-- Distributional semantics of sequential composition, with componentwise accumulated cost. -/
theorem runWithCost_bind {access : LearningAccess} {α β : Type u}
    (target : BooleanFunction n) (next : α → LearningProgram n access β)
    (program : LearningProgram n access α) :
    runWithCost target (bind next program) =
      (runWithCost target program).bind fun outcome ↦
        (runWithCost target (next outcome.1)).map
          (addOutcomeCost outcome.2) := by
  induction program with
  | pure output =>
      simp only [bind, runWithCost, PMF.pure_bind]
      rw [map_addOutcomeCost_zero]
  | coin branch ih =>
      simp only [bind, runWithCost]
      rw [PMF.bind_bind]
      congr 1
      funext b
      rw [ih b]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm LearningCost.coin
        (runWithCost target (branch b)) (fun output ↦ runWithCost target (next output))
  | randomExample branch ih =>
      simp only [bind, runWithCost]
      rw [PMF.bind_bind]
      congr 1
      funext x
      rw [ih (x, target x)]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm LearningCost.example
        (runWithCost target (branch (x, target x)))
        (fun output ↦ runWithCost target (next output))
  | randomExampleBatch m branch ih =>
      simp only [bind, runWithCost]
      rw [PMF.bind_bind]
      congr 1
      funext inputs
      rw [ih (fun i ↦ (inputs i, target (inputs i)))]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm ⟨m, 0, m⟩
        (runWithCost target (branch fun i ↦ (inputs i, target (inputs i))))
        (fun output ↦ runWithCost target (next output))
  | uniformInputBatch m branch ih =>
      simp only [bind, runWithCost]
      rw [PMF.bind_bind]
      congr 1
      funext inputs
      rw [ih inputs]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm ⟨0, 0, m * n⟩
        (runWithCost target (branch inputs))
        (fun output ↦ runWithCost target (next output))
  | randomExampleMatrix indices m branch ih =>
      simp only [bind, runWithCost]
      rw [PMF.bind_bind]
      congr 1
      funext inputs
      rw [ih (fun k i ↦ (inputs k i, target (inputs k i)))]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm ⟨indices.card * m, 0, indices.card * m⟩
        (runWithCost target
          (branch fun k i ↦ (inputs k i, target (inputs k i))))
        (fun output ↦ runWithCost target (next output))
  | randomExampleMatrixOutput indices m work output =>
      simp only [bind, runWithCost, randomExampleMatrixOutputLaw]
      rw [PMF.bind_map]
      unfold randomExampleMatrixInputLaw
      congr 1
      funext inputs
      simp only [Function.comp_apply, randomExampleMatrixOutcome]
      rw [PMF.map_comp]
      congr 1
      funext outcome
      rcases outcome with ⟨result, cost⟩
      simp only [Function.comp_apply]
      change
        (result, ⟨indices.card * m, 0, indices.card * m⟩ +
            (⟨0, 0, work⟩ + cost)) =
          (result, ⟨indices.card * m, 0, indices.card * m + work⟩ + cost)
      congr 1
      rw [← add_assoc]
      rfl
  | query x branch ih =>
      simp only [bind, runWithCost]
      rw [ih (target x)]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm LearningCost.query
        (runWithCost target (branch (target x)))
        (fun output ↦ runWithCost target (next output))
  | tick steps program ih =>
      simp only [bind, runWithCost]
      rw [ih]
      rw [PMF.map_bind]
      exact bind_map_addOutcomeCost_comm ⟨0, 0, steps⟩
        (runWithCost target program)
        (fun output ↦ runWithCost target (next output))

/-- Mapping a pure output function preserves the path cost in the distributional semantics. -/
theorem runWithCost_map {access : LearningAccess} {α β : Type u}
    (target : BooleanFunction n) (f : α → β)
    (program : LearningProgram n access α) :
    runWithCost target (map f program) =
      (runWithCost target program).map fun outcome ↦ (f outcome.1, outcome.2) := by
  rw [map, runWithCost_bind]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext outcome
  simp only [runWithCost, PMF.pure_map]
  congr 2

/-- Recursive distributional semantics of sequencing one program before a list of programs. -/
theorem runWithCost_sequence_cons
    {access : LearningAccess} {α : Type u}
    (target : BooleanFunction n) (program : LearningProgram n access α)
    (programs : List (LearningProgram n access α)) :
    runWithCost target (sequence (program :: programs)) =
      (runWithCost target program).bind fun head ↦
        (runWithCost target (sequence programs)).map fun tail ↦
          (head.1 :: tail.1, head.2 + tail.2) := by
  rw [sequence, runWithCost_bind]
  congr 1
  funext head
  rw [runWithCost_map]
  rw [PMF.map_comp]
  congr 1

/-- Any additive natural-valued cost projection accumulates linearly across a finite sequence. -/
theorem costProjection_le_of_mem_support_sequence
    {access : LearningAccess} {α : Type u}
    (target : BooleanFunction n) (projection : LearningCost → ℕ)
    (hzero : projection 0 = 0)
    (hadd : ∀ first second,
      projection (first + second) = projection first + projection second)
    (bound : ℕ) :
    ∀ (programs : List (LearningProgram n access α))
      (outcome : List α × LearningCost),
      (∀ program ∈ programs,
        ∀ componentOutcome ∈ (runWithCost target program).support,
          projection componentOutcome.2 ≤ bound) →
      outcome ∈ (runWithCost target (sequence programs)).support →
      projection outcome.2 ≤ programs.length * bound
  | [], outcome, _, houtcome => by
      simp only [sequence, runWithCost, PMF.mem_support_pure_iff] at houtcome
      subst outcome
      simp [hzero]
  | program :: programs, outcome, hcomponents, houtcome => by
      rw [runWithCost_sequence_cons] at houtcome
      rw [PMF.mem_support_bind_iff] at houtcome
      obtain ⟨head, hhead, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨tail, htail, rfl⟩ := houtcome
      rw [hadd, List.length_cons]
      have hheadBound := hcomponents program (by simp) head hhead
      have htailBound := costProjection_le_of_mem_support_sequence
        target projection hzero hadd bound programs tail
        (by
          intro tailProgram htailProgram
          exact hcomponents tailProgram (by simp [htailProgram]))
        htail
      nlinarith

/-- If every component program returns the key that selected it, sequencing preserves the input
key order exactly. -/
theorem map_output_eq_of_mem_support_sequence
    {access : LearningAccess} {κ α : Type u}
    (target : BooleanFunction n) (program : κ → LearningProgram n access α)
    (key : α → κ)
    (hkey : ∀ item outcome,
      outcome ∈ (runWithCost target (program item)).support →
        key outcome.1 = item) :
    ∀ items outcome,
      outcome ∈ (runWithCost target
        (sequence (items.map program))).support →
      outcome.1.map key = items
  | [], outcome, houtcome => by
      simp only [List.map_nil, sequence, runWithCost,
        PMF.mem_support_pure_iff] at houtcome
      subst outcome
      rfl
  | item :: items, outcome, houtcome => by
      simp only [List.map_cons] at houtcome
      rw [runWithCost_sequence_cons] at houtcome
      rw [PMF.mem_support_bind_iff] at houtcome
      obtain ⟨head, hhead, houtcome⟩ := houtcome
      rw [PMF.mem_support_map_iff] at houtcome
      obtain ⟨tail, htail, rfl⟩ := houtcome
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨hkey item head hhead,
        map_output_eq_of_mem_support_sequence
          target program key hkey items tail htail⟩

/-- Probability of an event on the result and cost of a finite learning computation. -/
noncomputable def eventProbability {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    (event : α × LearningCost → Prop) : ℝ :=
  ((runWithCost target program).toOuterMeasure {outcome | event outcome}).toReal

/-- Transport an output-only learning event across an exact pushforward description of the
program's distribution. -/
theorem eventProbability_eq_toMeasure_real_of_runWithCost_eq_map
    {access : LearningAccess} {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (program : LearningProgram n access β) (target : BooleanFunction n)
    (p : PMF α) (output : α → β) (cost : LearningCost)
    (hrun : runWithCost target program = p.map fun input ↦ (output input, cost))
    (event : β → Prop) :
    eventProbability program target (fun outcome ↦ event outcome.1) =
      p.toMeasure.real {input | event (output input)} := by
  unfold eventProbability
  rw [hrun, PMF.toOuterMeasure_map_apply]
  have hpreimage :
      (fun input ↦ (output input, cost)) ⁻¹'
          {outcome | event outcome.1} =
        {input | event (output input)} := rfl
  rw [hpreimage]
  exact congrArg ENNReal.toReal
    (p.toMeasure_apply_eq_toOuterMeasure {input | event (output input)}).symm

end LearningProgram

/-- A sequential PMF can fail either in its first stage or, conditional on first-stage success,
in its continuation. -/
theorem PMF.toOuterMeasure_bind_le_add
    {α β : Type*} (p : PMF α) (q : α → PMF β)
    (firstBad : Set α) (finalBad : Set β) (δ₁ δ₂ : ℝ≥0∞)
    (hp : p.toOuterMeasure firstBad ≤ δ₁)
    (hq : ∀ a ∉ firstBad, (q a).toOuterMeasure finalBad ≤ δ₂) :
    (p.bind q).toOuterMeasure finalBad ≤ δ₁ + δ₂ := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    (∑' a, p a * (q a).toOuterMeasure finalBad) ≤
        ∑' a, p a * (firstBad.indicator (fun _ ↦ (1 : ℝ≥0∞)) a + δ₂) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_right
      by_cases ha : a ∈ firstBad
      · rw [Set.indicator_of_mem ha]
        have hleOne : (q a).toOuterMeasure finalBad ≤ 1 := by
          calc
            (q a).toOuterMeasure finalBad ≤ (q a).toOuterMeasure Set.univ :=
              (q a).toOuterMeasure.mono (Set.subset_univ finalBad)
            _ = 1 := by simp [PMF.toOuterMeasure_apply, (q a).tsum_coe]
        exact hleOne.trans (by simp)
      · rw [Set.indicator_of_notMem ha, zero_add]
        exact hq a ha
    _ = (∑' a, p a * firstBad.indicator (fun _ ↦ (1 : ℝ≥0∞)) a) +
          ∑' a, p a * δ₂ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
    _ = p.toOuterMeasure firstBad + ∑' a, p a * δ₂ := by
      congr 1
    _ = p.toOuterMeasure firstBad + δ₂ := by
      rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
    _ ≤ δ₁ + δ₂ := add_le_add hp le_rfl

namespace LearningProgram

/-- The outer-measure-valued event probability underlying `eventProbability`. -/
noncomputable def outerEventProbability {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    (event : α × LearningCost → Prop) : ℝ≥0∞ :=
  (runWithCost target program).toOuterMeasure {outcome | event outcome}

theorem outerEventProbability_ne_top {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    (event : α × LearningCost → Prop) :
    outerEventProbability program target event ≠ ∞ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  unfold outerEventProbability
  calc
    (runWithCost target program).toOuterMeasure {outcome | event outcome} ≤
        (runWithCost target program).toOuterMeasure Set.univ :=
      (runWithCost target program).toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := by
      simp [PMF.toOuterMeasure_apply, (runWithCost target program).tsum_coe]

theorem outerEventProbability_toReal {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    (event : α × LearningCost → Prop) :
    (outerEventProbability program target event).toReal =
      eventProbability program target event := rfl

/-- Enlarging an event cannot decrease its probability under a learning program. -/
theorem eventProbability_mono {access : LearningAccess} {α : Type u}
    (program : LearningProgram n access α) (target : BooleanFunction n)
    {event₁ event₂ : α × LearningCost → Prop}
    (h : ∀ outcome, event₁ outcome → event₂ outcome) :
    eventProbability program target event₁ ≤
      eventProbability program target event₂ := by
  unfold eventProbability
  apply ENNReal.toReal_mono
  · simpa [outerEventProbability] using
      outerEventProbability_ne_top program target event₂
  · apply (runWithCost target program).toOuterMeasure.mono
    intro outcome houtcome
    exact h outcome houtcome

/-- Sequential learning programs inherit the generic two-stage failure union bound when the
events depend only on the returned values. -/
theorem outerEventProbability_bind_le_add
    {access : LearningAccess} {α β : Type u}
    (target : BooleanFunction n) (program : LearningProgram n access α)
    (next : α → LearningProgram n access β)
    (firstBad : α → Prop) (finalBad : β → Prop) (δ₁ δ₂ : ℝ≥0∞)
    (hp : outerEventProbability program target (fun outcome ↦ firstBad outcome.1) ≤ δ₁)
    (hq : ∀ a, ¬ firstBad a →
      outerEventProbability (next a) target (fun outcome ↦ finalBad outcome.1) ≤ δ₂) :
    outerEventProbability (bind next program) target (fun outcome ↦ finalBad outcome.1) ≤
      δ₁ + δ₂ := by
  unfold outerEventProbability
  rw [runWithCost_bind]
  apply PMF.toOuterMeasure_bind_le_add
      (runWithCost target program)
      (fun outcome ↦
        (runWithCost target (next outcome.1)).map (addOutcomeCost outcome.2))
      {outcome | firstBad outcome.1} {outcome | finalBad outcome.1} δ₁ δ₂ hp
  intro outcome houtcome
  rw [PMF.toOuterMeasure_map_apply]
  have hpreimage :
      addOutcomeCost outcome.2 ⁻¹' {nextOutcome | finalBad nextOutcome.1} =
        {nextOutcome | finalBad nextOutcome.1} := by
    ext nextOutcome
    rfl
  rw [hpreimage]
  apply hq outcome.1
  simpa using houtcome

/-- Real-valued form of the sequential two-stage failure union bound. -/
theorem eventProbability_bind_le_add
    {access : LearningAccess} {α β : Type u}
    (target : BooleanFunction n) (program : LearningProgram n access α)
    (next : α → LearningProgram n access β)
    (firstBad : α → Prop) (finalBad : β → Prop) (δ₁ δ₂ : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hp : eventProbability program target (fun outcome ↦ firstBad outcome.1) ≤ δ₁)
    (hq : ∀ a, ¬ firstBad a →
      eventProbability (next a) target (fun outcome ↦ finalBad outcome.1) ≤ δ₂) :
    eventProbability (bind next program) target (fun outcome ↦ finalBad outcome.1) ≤
      δ₁ + δ₂ := by
  have hpOuter :
      outerEventProbability program target (fun outcome ↦ firstBad outcome.1) ≤
        ENNReal.ofReal δ₁ := by
    apply (ENNReal.le_ofReal_iff_toReal_le
      (outerEventProbability_ne_top program target fun outcome ↦ firstBad outcome.1)
      hδ₁).2
    simpa only [outerEventProbability_toReal] using hp
  have hqOuter : ∀ a, ¬ firstBad a →
      outerEventProbability (next a) target
        (fun outcome ↦ finalBad outcome.1) ≤ ENNReal.ofReal δ₂ := by
    intro a ha
    apply (ENNReal.le_ofReal_iff_toReal_le
      (outerEventProbability_ne_top (next a) target fun outcome ↦ finalBad outcome.1)
      hδ₂).2
    simpa only [outerEventProbability_toReal] using hq a ha
  have hOuter := outerEventProbability_bind_le_add
    target program next firstBad finalBad
    (ENNReal.ofReal δ₁) (ENNReal.ofReal δ₂) hpOuter hqOuter
  have hBound :
      outerEventProbability (bind next program) target
          (fun outcome ↦ finalBad outcome.1) ≤
        ENNReal.ofReal (δ₁ + δ₂) := by
    rw [ENNReal.ofReal_add hδ₁ hδ₂]
    exact hOuter
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
  rw [ENNReal.toReal_ofReal (add_nonneg hδ₁ hδ₂)] at hReal
  simpa only [outerEventProbability_toReal] using hReal

/-- Prepending a successful component output does not change whether a later sequence contains a
bad output. -/
theorem outerEventProbability_map_cons_exists
    {access : LearningAccess} {α : Type u}
    (target : BooleanFunction n) (head : α)
    (program : LearningProgram n access (List α))
    (bad : α → Prop) (hhead : ¬ bad head) :
    outerEventProbability (map (List.cons head) program) target
        (fun outcome ↦ ∃ item ∈ outcome.1, bad item) =
      outerEventProbability program target
        (fun outcome ↦ ∃ item ∈ outcome.1, bad item) := by
  unfold outerEventProbability
  rw [runWithCost_map, PMF.toOuterMeasure_map_apply]
  congr 1
  ext outcome
  simp [hhead]

/-- A uniform component failure bound accumulates linearly when the programs are sequenced. -/
theorem outerEventProbability_sequence_exists_le_nsmul
    {access : LearningAccess} {α : Type u}
    (target : BooleanFunction n) (bad : α → Prop) (δ : ℝ≥0∞) :
    ∀ programs : List (LearningProgram n access α),
      (∀ program ∈ programs,
        outerEventProbability program target (fun outcome ↦ bad outcome.1) ≤ δ) →
      outerEventProbability (sequence programs) target
          (fun outcome ↦ ∃ item ∈ outcome.1, bad item) ≤
        programs.length • δ
  | [], _ => by
      simp [sequence, outerEventProbability, runWithCost]
  | program :: programs, hprograms => by
      rw [sequence]
      simp only [List.length_cons]
      rw [succ_nsmul, add_comm]
      apply outerEventProbability_bind_le_add target program
        (fun head ↦ map (List.cons head) (sequence programs))
        bad (fun output ↦ ∃ item ∈ output, bad item) δ
        (programs.length • δ)
      · exact hprograms program (by simp)
      · intro head hhead
        rw [outerEventProbability_map_cons_exists target head
          (sequence programs) bad hhead]
        apply outerEventProbability_sequence_exists_le_nsmul
        intro tailProgram htailProgram
        exact hprograms tailProgram (by simp [htailProgram])

end LearningProgram

end FABL
